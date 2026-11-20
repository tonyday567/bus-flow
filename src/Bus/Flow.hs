{-# LANGUAGE OverloadedStrings #-}

-- | Pure log analysis for a stamped post log.
--
-- Computes flow metrics from a stamped JSONL log: Re_bus, SNR,
-- posts-per-deliverable, and time-to-quiescence.  Classifications are
-- regex-driven and overridable so old transcripts can be re-analysed.
module Bus.Flow
  ( -- * Rules
    Rules (..),
    defaultRules,
    Classification (..),
    classify,
    isDeliverable,
    isDoneClaim,

    -- * Slicing
    SliceMode (..),
    slicePosts,
    ThreadIndex,
    indexThreads,
    threadComponents,
    lookupPost,
    lookupComponent,
    PostLookup (..),
    ComponentLookup (..),
    ComponentKey (..),
    ThreadComponent (..),
    ThreadPost (..),
    Citation (..),

    -- * Statistics
    Stats (..),
    computeStats,

    -- * Rendering
    renderStats,
    renderStatsJson,
  )
where

import Circuit.Parser.Framing (Stored)
import Circuit.Parser.Json (Json (..), encodeJson)
import Circuit.Post (Post (..), PostId)
import Circuit.Shared (Stamped (..))
import Data.Bifunctor (first)
import Data.List (minimumBy, sort, sortOn)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8)
import Data.Time (NominalDiffTime, UTCTime, addUTCTime, diffUTCTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import Data.Vector qualified as V
import Text.Printf (printf)
import Text.Regex.TDFA ((=~))
import Prelude

-- ---------------------------------------------------------------------------
-- Classification rules
-- ---------------------------------------------------------------------------

-- | Regex-driven classification rules.  Each field is a single regex; the
-- default 'signalRE' combines path, mark, and decision-word alternatives.
data Rules = Rules
  { -- | Regex matching noise (status pings, idle chatter).
    noiseRE :: Text,
    -- | Regex matching signal (paths, marks, decisions).
    signalRE :: Text,
    -- | Regex matching a conductor deliverable mark.
    deliverableRE :: Text
  }
  deriving (Eq, Show)

-- | Sensible defaults decided with the card.
defaultRules :: Rules
defaultRules =
  Rules
    { noiseRE = "standing by|session complete|^ack$|ping|still here|waiting on",
      signalRE = "[^[:space:]]+\\.(md|hs|cabal|jsonl)|🟢|⟝|🚩|decided|fixed|bug|found",
      deliverableRE = "🟢"
    }

-- | Path regex shared between signal detection and DONE-claim detection.
pathRE :: Text
pathRE = "[^[:space:]]+\\.(md|hs|cabal|jsonl)"

-- | A post is signal, noise, or neutral.
data Classification = Signal | Noise | Neutral
  deriving (Eq, Show)

-- | Classify a post.  Signal takes precedence over noise: a post matching the
-- noise regex but carrying a path or mark is counted as signal.
classify :: Rules -> Post Text Text -> Classification
classify rules p
  | matches (signalRE rules) (body p) = Signal
  | matches (noiseRE rules) (body p) = Noise
  | otherwise = Neutral

-- | Whether a post is a conductor deliverable.
isDeliverable :: Rules -> Post Text Text -> Bool
isDeliverable rules p = matches (deliverableRE rules) (body p)

-- | Whether a post claims completion and cites a path.
isDoneClaim :: Post Text Text -> Bool
isDoneClaim p =
  T.isInfixOf "DONE" (T.toUpper (body p)) && matches pathRE (body p)

-- | Case-insensitive regex match against a body.
matches :: Text -> Text -> Bool
matches pat txt = T.unpack txt =~ T.unpack pat

-- ---------------------------------------------------------------------------
-- Time handling
-- ---------------------------------------------------------------------------

-- | Format a timestamp for display.
formatTs :: UTCTime -> Text
formatTs = T.pack . formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S"

-- | Minutes between two timestamps.
minutes :: UTCTime -> UTCTime -> Double
minutes a b = realToFrac (diffUTCTime b a) / 60.0

-- ---------------------------------------------------------------------------
-- Slicing
-- ---------------------------------------------------------------------------

-- | How to partition the log for metric computation.
data SliceMode
  = -- | One slice over the entire log.
    WholeLog
  | -- | Fixed-width time buckets in minutes.
    WindowMinutes Int
  | -- | One slice per thread tree (grouped by root post id).
    --
    -- Cyclic ancestry resolves to the least post id in the cycle, so a
    -- self-ancestor is its own root.
    ByThread
  | -- | One slice per authoring agent.
    ByAgent
  deriving (Eq, Show)

-- | Result of looking up one post id. A collision retains every row in log
-- order; it never selects a last-wins candidate.
data PostLookup
  = PostAbsent
  | PostFound Stored
  | PostCollision [Stored]
  deriving (Eq, Show)

-- | One citation in its original position in the post's @thread@ list.
-- 'PostAbsent' is a phantom citation and 'PostCollision' is an ambiguous one.
data Citation = Citation
  { citationId :: PostId,
    citationLookup :: PostLookup
  }
  deriving (Eq, Show)

-- | A stamped row plus the complete resolution of its citations.
data ThreadPost = ThreadPost
  { threadPost :: Stored,
    threadCitations :: [Citation]
  }
  deriving (Eq, Show)

-- | A resolved root, or the cited id grouping rows whose ancestry has no
-- uniquely resolved parent. An unresolved key is evidence, not a parent guess.
data ComponentKey
  = ResolvedRoot PostId
  | UnresolvedParent PostId
  deriving (Eq, Ord, Show)

-- | One retained thread component. 'componentCollisions' names globally
-- duplicate ids represented in the component, including when all colliding
-- rows share one component.
--
-- 'componentPosts' is in reverse log order, preserving the established
-- 'slicePosts' compatibility order. A renderer must sort explicitly, normally
-- with @sortOn (snd . stamp . threadPost)@, rather than treating this as
-- chronological order. A stable id sort retains reverse log order among rows
-- that share an id.
data ThreadComponent = ThreadComponent
  { componentKey :: ComponentKey,
    componentPosts :: [ThreadPost],
    componentCollisions :: [PostId]
  }
  deriving (Eq, Show)

-- | Result of finding components containing an actual post id. Duplicate rows
-- in one component yield 'ComponentFound' plus a 'componentCollisions' mark;
-- rows in different components yield 'ComponentCollision'.
--
-- 'ComponentFound' means one component, not an unambiguous id. Consumers must
-- also inspect 'componentCollisions' or 'lookupPost' before treating the key as
-- resolved.
data ComponentLookup
  = ComponentAbsent
  | ComponentFound ThreadComponent
  | ComponentCollision [ThreadComponent]
  deriving (Eq, Show)

-- | A pure index of post ids, thread components, and citation evidence. The
-- constructor is hidden so lookups cannot bypass collision handling.
data ThreadIndex = ThreadIndex
  { postRows :: Map.Map PostId [Stored],
    threadComponents :: [ThreadComponent]
  }
  deriving (Eq, Show)

-- | Index every row exactly once. Parent traversal follows only uniquely
-- resolved citations, choosing the least parent id when several resolve (the
-- established slicer rule). If none resolves, the least cited id groups the
-- unresolved component and all citation evidence remains on its rows.
indexThreads :: [Stored] -> ThreadIndex
indexThreads posts =
  ThreadIndex
    { postRows = rows,
      threadComponents = map makeComponent (Map.toList groups)
    }
  where
    frameId p = snd (stamp p)
    rows = Map.fromListWith (flip (++)) [(frameId p, [p]) | p <- posts]
    duplicateIds = Map.keysSet (Map.filter ((> 1) . length) rows)
    lookupRows pid = case Map.lookup pid rows of
      Nothing -> PostAbsent
      Just [p] -> PostFound p
      Just ps -> PostCollision ps
    citationsFor p = [Citation cited (lookupRows cited) | cited <- thread (stamped p)]
    rootOf = go []
      where
        go seen p
          | p `elem` seen =
              ResolvedRoot (minimum (frameId p : map frameId (takeWhile (/= p) seen)))
          | otherwise = case citationsFor p of
              [] -> ResolvedRoot (frameId p)
              citations -> case [parent | Citation _ (PostFound parent) <- citations] of
                [] -> UnresolvedParent (minimum (map citationId citations))
                parents -> go (p : seen) (minimumBy (comparing frameId) parents)
    decorated = [ThreadPost p (citationsFor p) | p <- posts]
    groups = Map.fromListWith (++) [(rootOf p, [decoratedPost]) | (p, decoratedPost) <- zip posts decorated]
    makeComponent (key, componentRows) =
      ThreadComponent
        { componentKey = key,
          componentPosts = componentRows,
          componentCollisions =
            Set.toList $
              Set.intersection duplicateIds $
                Set.fromList (map (frameId . threadPost) componentRows)
        }

-- | Collision-safe lookup of every stamped row carrying an id.
lookupPost :: ThreadIndex -> PostId -> PostLookup
lookupPost index pid = case Map.lookup pid (postRows index) of
  Nothing -> PostAbsent
  Just [p] -> PostFound p
  Just ps -> PostCollision ps

-- | Find every component containing an actual row with the requested id.
-- Unresolved grouping keys alone do not manufacture a matching post.
lookupComponent :: ThreadIndex -> PostId -> ComponentLookup
lookupComponent index pid = case filter contains (threadComponents index) of
  [] -> ComponentAbsent
  [component] -> ComponentFound component
  components -> ComponentCollision components
  where
    contains = any ((== pid) . snd . stamp . threadPost) . componentPosts

-- | Partition stamped posts into slices. Posts without a parseable timestamp
-- are dropped from time-based slicing, but kept for thread slicing (where the
-- id is enough).
--
-- 'ByThread' is a compatibility projection of 'indexThreads'. Its text labels
-- are not unique when a collision and an unresolved branch share an id; a
-- renderer that needs that distinction must consume 'ThreadComponent' instead.
slicePosts :: SliceMode -> [Stored] -> [(Text, [Stored])]
slicePosts WholeLog posts = [("whole", posts)]
slicePosts (WindowMinutes m) posts =
  case timed of
    [] -> []
    _ -> map (first bucketLabel) (Map.toList buckets)
  where
    timed = [(fst (stamp p), p) | p <- posts]
    base = minimum (map fst timed)
    bucket t = floor (minutes base t) `div` m
    buckets = Map.fromListWith (flip (++)) (map (\(t, p) -> (bucket t, [p])) timed)
    bucketLabel k =
      let start = addMinutes base (k * m)
          end = addMinutes start m
       in T.concat [formatTs start, "..", formatTs end]
slicePosts ByThread posts =
  sortOn fst [(componentLabel (componentKey component), map threadPost (componentPosts component)) | component <- threadComponents (indexThreads posts)]
  where
    componentLabel (ResolvedRoot pid) = showt pid
    componentLabel (UnresolvedParent cited) = showt cited
slicePosts ByAgent posts =
  sortOn fst [(k, v) | (k, v) <- Map.toList byAuthor]
  where
    byAuthor = Map.fromListWith (++) [(from (stamped p), [p]) | p <- posts]

addMinutes :: UTCTime -> Int -> UTCTime
addMinutes t n = addUTCTime (fromIntegral (n * 60) :: NominalDiffTime) t

-- ---------------------------------------------------------------------------
-- Statistics
-- ---------------------------------------------------------------------------

-- | Computed metrics for one slice.
data Stats = Stats
  { statSlice :: Text,
    statPosts :: Int,
    statAgents :: Int,
    statDurationMinutes :: Double,
    statPostsPerMinute :: Double,
    statDamping :: Int,
    statReBus :: Double,
    statSignal :: Int,
    statNoise :: Int,
    statUnclassified :: Int,
    statSNR :: Maybe Double,
    statSNRPrime :: Maybe Double,
    statDeliverables :: Int,
    statDoneClaims :: Int,
    statPostsPerDeliverable :: Maybe Double,
    statTimeToQuiescenceMinutes :: Double
  }
  deriving (Eq, Show)

-- | Compute stats for one slice given classification rules and a damping count.
computeStats :: Rules -> Int -> Text -> [Stored] -> Stats
computeStats rules damping label posts =
  Stats
    { statSlice = label,
      statPosts = n,
      statAgents = length agents,
      statDurationMinutes = dur,
      statPostsPerMinute = ppm,
      statDamping = max 1 damping,
      statReBus = reBus,
      statSignal = signalCount,
      statNoise = noiseCount,
      statUnclassified = unclassifiedCount,
      statSNR = snr,
      statSNRPrime = snrPrime,
      statDeliverables = deliverables,
      statDoneClaims = doneClaims,
      statPostsPerDeliverable = ppd,
      statTimeToQuiescenceMinutes = ttq
    }
  where
    n = length posts
    agents = sort $ Map.keys $ Map.fromList [(from (stamped p), ()) | p <- posts]
    timestamps = map (fst . stamp) posts
    (startTime, endTime) = case timestamps of
      [] -> (Nothing, Nothing)
      ts -> (Just (minimum ts), Just (maximum ts))
    dur = maybe 0 (\s -> maybe 0 (minutes s) endTime) startTime
    ppm = if dur > 0 then fromIntegral n / dur else 0
    reBus =
      if dur > 0 && damping > 0
        then fromIntegral (length agents) * ppm / fromIntegral damping
        else 0
    classified = map (classify rules . stamped) posts
    signalCount = length (filter (== Signal) classified)
    noiseCount = length (filter (== Noise) classified)
    unclassifiedCount = n - signalCount - noiseCount
    snr
      | noiseCount > 0 = Just (fromIntegral signalCount / fromIntegral noiseCount)
      | signalCount > 0 = Nothing -- conceptually infinite
      | otherwise = Just 0
    snrPrime
      | unclassifiedCount + noiseCount > 0 =
          Just (fromIntegral signalCount / fromIntegral (unclassifiedCount + noiseCount))
      | signalCount > 0 = Nothing -- conceptually infinite
      | otherwise = Just 0
    deliverables = length (filter (isDeliverable rules . stamped) posts)
    doneClaims = length (filter (isDoneClaim . stamped) posts)
    ppd = if deliverables > 0 then Just (fromIntegral n / fromIntegral deliverables) else Nothing
    ttq = case startTime of
      Nothing -> 0
      Just start ->
        let signalPosts = [p | p <- posts, classify rules (stamped p) == Signal]
            signalTimes = map (fst . stamp) signalPosts
         in case signalTimes of
              [] -> 0
              ts -> minutes start (maximum ts)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

-- | Human-readable plain-text report.
renderStats :: Rules -> [Stats] -> Text
renderStats rules stats =
  T.unlines $
    [ "bus-stats",
      "  noise regex:    " <> noiseRE rules,
      "  signal regex:   " <> signalRE rules,
      "  deliverable:    " <> deliverableRE rules,
      ""
    ]
      ++ concatMap renderSlice stats
  where
    renderSlice s =
      [ "slice: " <> statSlice s,
        "  posts:               " <> showt (statPosts s),
        "  agents:              " <> showt (statAgents s),
        "  duration (min):      " <> showd (statDurationMinutes s),
        "  posts/min:           " <> showd (statPostsPerMinute s),
        "  damping rules:       " <> showt (statDamping s),
        "  Re_bus:              " <> showd (statReBus s),
        "  signal:              " <> showt (statSignal s),
        "  noise:               " <> showt (statNoise s),
        "  unclassified:        " <> showt (statUnclassified s),
        "  SNR:                 " <> maybe "-" showd (statSNR s),
        "  SNR':                " <> maybe "-" showd (statSNRPrime s),
        "  deliverables:        " <> showt (statDeliverables s),
        "  done claims:         " <> showt (statDoneClaims s),
        "  posts/deliverable:   " <> maybe "n/a" showd (statPostsPerDeliverable s),
        "  time to quiescence (min): " <> showd (statTimeToQuiescenceMinutes s),
        ""
      ]

showt :: (Show a) => a -> Text
showt = T.pack . show

showd :: Double -> Text
showd = T.pack . printf "%0.3f"

-- | JSON report.
renderStatsJson :: Rules -> [Stats] -> Text
renderStatsJson rules stats =
  decodeUtf8 (encodeJson (JObject [("rules", rulesObj), ("slices", JArray (V.fromList (map statsObject stats)))]))
  where
    rulesObj =
      JObject
        [ ("noise", JString (noiseRE rules)),
          ("signal", JString (signalRE rules)),
          ("deliverable", JString (deliverableRE rules))
        ]
    statsObject s =
      JObject
        [ ("slice", JString (statSlice s)),
          ("posts", JNumber (fromIntegral (statPosts s))),
          ("agents", JNumber (fromIntegral (statAgents s))),
          ("duration_minutes", jdouble (statDurationMinutes s)),
          ("posts_per_minute", jdouble (statPostsPerMinute s)),
          ("damping_rules", JNumber (fromIntegral (statDamping s))),
          ("re_bus", jdouble (statReBus s)),
          ("signal", JNumber (fromIntegral (statSignal s))),
          ("noise", JNumber (fromIntegral (statNoise s))),
          ("unclassified", JNumber (fromIntegral (statUnclassified s))),
          ("snr", jmaybe jdouble (statSNR s)),
          ("snr_prime", jmaybe jdouble (statSNRPrime s)),
          ("deliverables", JNumber (fromIntegral (statDeliverables s))),
          ("done_claims", JNumber (fromIntegral (statDoneClaims s))),
          ("posts_per_deliverable", jmaybe jdouble (statPostsPerDeliverable s)),
          ("time_to_quiescence_minutes", jdouble (statTimeToQuiescenceMinutes s))
        ]
    jdouble = JNumber . fromRational . toRational
    jmaybe _ Nothing = JNull
    jmaybe f (Just x) = f x
