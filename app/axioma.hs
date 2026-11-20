{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Bus.Flow
import Circuit.Parser.Framing (Stored, decodeRow, encodeRow)
import Circuit.Parser.Json (Json (..), decodeJson)
import Circuit.Post (Post (..), PostId)
import Circuit.Shared (Stamped (..))
import Control.Monad (forM, forM_)
import Data.List (sort, sortOn)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as T
import Data.Time (UTCTime, addUTCTime, defaultTimeLocale, getCurrentTime, parseTimeM)
import Data.Vector qualified as V
import Paths_bus_flow (getDataFileName)
import Prelude

main :: IO ()
main = do
  baselineFlowWitnesses
  threadAncestryWitnesses
  flowTopic
  putStrLn "bus-flow-axioma: all witnesses passed"

assert :: String -> Bool -> IO ()
assert label ok = if ok then pure () else error label

mk :: Text -> Text -> PostId -> Post Text Text
mk b f _ = Post f Nothing [] [] b

mkPosts :: IO [Stored]
mkPosts = do
  now <- getCurrentTime
  let at ts i b f = Stamped (addUTCTime ts now, i) (mk b f i)
  pure
    [ at 0 0 "standing by" "alice",
      at 60 1 "fixed the bug" "bob",
      at 120 2 "ack" "alice",
      at 180 3 "random thought" "carol",
      at 240 4 "DONE: src/Foo.hs" "bob",
      at 300 5 "waiting on results" "alice",
      at 360 6 "🟢 shipped" "bob"
    ]

frameId :: Stamped (UTCTime, PostId) a -> PostId
frameId = snd . stamp

-- | Second-precision UTC, the shape the framing module reads and writes.
parseTimeText :: Text -> Maybe UTCTime
parseTimeText = parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S" . T.unpack

-- The twenty pure assertions moved from free-agent 5990652 Axioma.Bus.
baselineFlowWitnesses :: IO ()
baselineFlowWitnesses = do
  let p = mk "standing by" "a" 0
  assert "baseline: plain status ping is noise" (classify defaultRules p == Noise)
  let withPath = mk "standing by with loom/foo.md" "a" 1
  assert "baseline: noise carrying a path is signal" (classify defaultRules withPath == Signal)
  let decision = mk "decided to keep the current design" "a" 2
  assert "baseline: decision word is signal" (classify defaultRules decision == Signal)
  let done = mk "DONE: stuff/foo.md" "a" 3
  assert "baseline: DONE plus path is a done claim" (isDoneClaim done)
  let notDone = mk "done with the task" "a" 4
  assert "baseline: DONE without path is not a done claim" (not (isDoneClaim notDone))

  let mkStored i ts f t b = case parseTimeText ts of
        Just ts' -> Stamped (ts', i) (Post f Nothing t [] b)
        Nothing -> error ("bad timestamp: " <> show ts)
      posts =
        [ mkStored 0 "2026-08-05T00:00:00" "a" ["b"] "hello",
          mkStored 1 "2026-08-05T00:10:00" "b" ["a"] "ack",
          mkStored 2 "2026-08-05T00:20:00" "a" ["b"] "standing by",
          mkStored 3 "2026-08-05T00:30:00" "a" ["b"] "🟢 card done"
        ]
      slices = slicePosts WholeLog posts
  stats <- case map (uncurry (computeStats defaultRules 1)) slices of
    [s] -> pure s
    _ -> fail "expected exactly one slice"
  assert "baseline: whole log is one slice" (length slices == 1)
  assert "baseline: counts all posts" (statPosts stats == 4)
  assert "baseline: counts agents" (statAgents stats == 2)
  assert "baseline: signal = deliverable mark" (statSignal stats == 1)
  assert "baseline: noise = status pings" (statNoise stats == 2)
  assert "baseline: unclassified = neutral posts" (statUnclassified stats == 1)
  assert "baseline: deliverables = conductor marks" (statDeliverables stats == 1)

  let windowPosts =
        [ mkStored 0 "2026-08-05T00:00:00" "a" ["b"] "hello",
          mkStored 1 "2026-08-05T00:10:00" "b" ["a"] "ack",
          mkStored 2 "2026-08-05T01:05:00" "a" ["b"] "standing by",
          mkStored 3 "2026-08-05T01:20:00" "a" ["b"] "🟢 card done"
        ]
  assert "baseline: 60m window splits four posts into two slices" (length (slicePosts (WindowMinutes 60) windowPosts) == 2)

  let agentPosts =
        [ mkStored 0 "2026-08-05T00:00:00" "a" ["b"] "hello",
          mkStored 1 "2026-08-05T00:10:00" "b" ["a"] "ack",
          mkStored 2 "2026-08-05T00:20:00" "a" ["b"] "standing by",
          mkStored 3 "2026-08-05T00:30:00" "b" ["a"] "🟢 card done"
        ]
      agentSlices = slicePosts ByAgent agentPosts
  assert "baseline: by-agent splits into two author slices" (length agentSlices == 2)
  assert "baseline: author a has two posts" $ case filter ((== "a") . fst) agentSlices of
    [(_, ps)] -> length ps == 2
    _ -> False
  assert "baseline: author b has one signal and one noise post" $ case filter ((== "b") . fst) agentSlices of
    [(_, ps)] ->
      let stats' = computeStats defaultRules 1 "b" ps
       in statSignal stats' == 1 && statNoise stats' == 1
    _ -> False

  let stored i ancestors = case parseTimeText "2026-10-28T00:00:00" of
        Just ts -> Stamped (ts, i) (Post "moka" Nothing [] ancestors "cycle fixture")
        Nothing -> error "bad thread-cycle fixture timestamp"
      cyclePosts =
        [ stored 1 [2],
          stored 2 [3],
          stored 3 [2],
          stored 7 [],
          stored 8 [7],
          stored 9 [9]
        ]
      threadSlices = slicePosts ByThread cyclePosts
      componentIds label = maybe [] (map frameId) (lookup label threadSlices)
  -- Removing cycle detection makes this witness non-terminating.
  assert "baseline: a two-post ancestry cycle keeps its child in one component" (componentIds "2" == [3, 2, 1])
  assert "baseline: ordinary ancestry still resolves to its root" (componentIds "7" == [8, 7])
  assert "baseline: a self-ancestor is its own root" (componentIds "9" == [9])
  assert "baseline: thread slicing accounts for every cyclic and ordinary post" (length threadSlices == 3)

-- Constructed E5 fixtures: duplicate rows remain exact values, not merely ids.
threadAncestryWitnesses :: IO ()
threadAncestryWitnesses = do
  august <- readAncestryFixture "fixtures/collision-august-shape.jsonl" 16
  let index = indexThreads august
      fixtureRow pid label rows = case [p | p <- rows, frameId p == pid, body (stamped p) == label] of
        [p] -> p
        _ -> error ("fixture row not unique: " <> show (pid, label))
      row1 = fixtureRow 1 "NOTE root one" august
      row2 = fixtureRow 2 "REPLY to 1" august
      collisions230 =
        [ fixtureRow 230 "NOTE collision 230 A" august,
          fixtureRow 230 "NOTE collision 230 B" august,
          fixtureRow 230 "NOTE collision 230 C" august
        ]
      row240 = fixtureRow 240 "TASK cites ambiguous 230" august
      row246 = fixtureRow 246 "NOTE cites absent 242" august
      collisions247 =
        [ fixtureRow 247 "NOTE collision 247 A" august,
          fixtureRow 247 "NOTE collision 247 B" august
        ]
      row255 = fixtureRow 255 "TASK cites ambiguous 247" august
      row256 = fixtureRow 256 "DONE cites ambiguous 247" august
      row300 = fixtureRow 300 "NOTE cites reversed 2,1" august
      row301 = fixtureRow 301 "NOTE cites mixed 1,999" august
      row302 = fixtureRow 302 "NOTE cites phantom 999 only" august
      threadPostFor p ix = case [tp | c <- threadComponents ix, tp <- componentPosts c, threadPost tp == p] of
        [tp] -> tp
        _ -> error ("indexed post not unique: " <> show p)
      componentForPost p ix = case [c | c <- threadComponents ix, any ((== p) . threadPost) (componentPosts c)] of
        [c] -> c
        _ -> error ("indexed component not unique: " <> show p)
      componentAt key ix = case filter ((== key) . componentKey) (threadComponents ix) of
        [c] -> c
        _ -> error ("component key not unique: " <> show key)
      storedComponent = map threadPost . componentPosts
      retainedRows ix = sortOn encodeRow [threadPost tp | c <- threadComponents ix, tp <- componentPosts c]
      sourceRows = sortOn encodeRow
      slicedRows rows = sortOn encodeRow (concatMap snd (slicePosts ByThread rows))
      root230 = componentAt (ResolvedRoot 230) index
      unresolved240 = componentForPost row240 index
      unresolved247 = componentAt (UnresolvedParent 247) index

  assert "ANCESTRY-RETENTION: every August-shape row survives exactly once" (retainedRows index == sourceRows august)
  assert "ANCESTRY-SLICE-RETENTION: compatibility slicing drops no duplicate row" (slicedRows august == sourceRows august)
  assert "ANCESTRY-RESOLVABLE: a unique citation retains its exact parent" (threadCitations (threadPostFor row2 index) == [Citation 1 (PostFound row1)])
  assert "ANCESTRY-RESOLVABLE-COMPONENT: a unique child follows its parent" (componentKey (componentForPost row2 index) == ResolvedRoot 1)
  assert "ANCESTRY-COLLISION-LOOKUP: id 230 returns all three rows in log order" (lookupPost index 230 == PostCollision collisions230)
  assert "ANCESTRY-COLLISION-ROWS: one component retains all three exact id-230 rows" (sortOn encodeRow (storedComponent root230) == sortOn encodeRow collisions230)
  assert "ANCESTRY-COLLISION-MARK: a shared component still marks key 230 ambiguous" (componentCollisions root230 == [230])
  assert "ANCESTRY-COLLISION-COMPONENT: same-component duplicates remain findable without guessing" (lookupComponent index 230 == ComponentFound root230)
  assert "ANCESTRY-AMBIGUOUS-CITATION: row 240 retains all id-230 candidates" (threadCitations (threadPostFor row240 index) == [Citation 230 (PostCollision collisions230)])
  assert "ANCESTRY-AMBIGUOUS-COMPONENT: row 240 is grouped by cited id, not attached" (componentKey unresolved240 == UnresolvedParent 230 && storedComponent unresolved240 == [row240])
  assert "ANCESTRY-NO-LAST-WINS: row 240 is absent from the candidate component" (row240 `notElem` storedComponent root230)
  assert "ANCESTRY-AMBIGUOUS-LOOKUP: requesting child 240 finds its unresolved component" (lookupComponent index 240 == ComponentFound unresolved240)
  assert "ANCESTRY-AMBIGUOUS-GROUP: both id-247 children remain grouped by cited id" (sortOn encodeRow (storedComponent unresolved247) == sortOn encodeRow [row255, row256])
  assert "ANCESTRY-AMBIGUOUS-247: both children retain both candidates" (map (threadCitations . (`threadPostFor` index)) [row255, row256] == replicate 2 [Citation 247 (PostCollision collisions247)])
  assert "ANCESTRY-ALL-ABSENT: phantom-only row 302 retains cited id 999" (threadCitations (threadPostFor row302 index) == [Citation 999 PostAbsent])
  assert "ANCESTRY-ALL-ABSENT-COMPONENT: row 302 is unresolved, not promoted to a root" (componentKey (componentForPost row302 index) == UnresolvedParent 999 && storedComponent (componentForPost row302 index) == [row302])
  assert "ANCESTRY-PHANTOM-NOT-POST: an unresolved key does not manufacture post 999" (lookupPost index 999 == PostAbsent && lookupComponent index 999 == ComponentAbsent)
  assert "ANCESTRY-ALL-ABSENT-246: the second phantom-only branch is retained" (componentKey (componentForPost row246 index) == UnresolvedParent 242 && threadCitations (threadPostFor row246 index) == [Citation 242 PostAbsent])
  assert "ANCESTRY-MIXED: row 301 retains resolved 1 and phantom 999 in citation order" (threadCitations (threadPostFor row301 index) == [Citation 1 (PostFound row1), Citation 999 PostAbsent])
  assert "ANCESTRY-MIXED-COMPONENT: a unique parent may resolve without erasing phantom evidence" (componentKey (componentForPost row301 index) == ResolvedRoot 1)
  assert "ANCESTRY-REVERSED-LABELLED: constructed [2,1] citations retain their order" (threadCitations (threadPostFor row300 index) == [Citation 2 (PostFound row2), Citation 1 (PostFound row1)])
  assert "ANCESTRY-REVERSED-RULE: multiple resolved parents still choose the least id" (componentKey (componentForPost row300 index) == ResolvedRoot 1)

  cross <- readAncestryFixture "fixtures/collision-cross-component.jsonl" 5
  let crossIndex = indexThreads cross
      cross2 = fixtureRow 2 "NOTE root two" cross
      cross3Root = fixtureRow 3 "NOTE id 3 root" cross
      cross3Reply = fixtureRow 3 "REPLY id 3 to 2" cross
      cross4 = fixtureRow 4 "REPLY to ambiguous 3" cross
      crossRoot2 = componentAt (ResolvedRoot 2) crossIndex
      crossRoot3 = componentAt (ResolvedRoot 3) crossIndex
      crossUnresolved4 = componentForPost cross4 crossIndex
  assert "ANCESTRY-X-RETENTION: both id-3 rows and all other rows survive exactly once" (retainedRows crossIndex == sourceRows cross)
  assert "ANCESTRY-X-SLICE-RETENTION: compatibility slicing retains both components" (slicedRows cross == sourceRows cross)
  assert "ANCESTRY-X-COLLISION-LOOKUP: id 3 returns root and reply rather than last-wins" (lookupPost crossIndex 3 == PostCollision [cross3Root, cross3Reply])
  assert "ANCESTRY-X-DUPLICATE-COMPONENTS: root and reply remain in separate exact components" (storedComponent crossRoot3 == [cross3Root] && sortOn encodeRow (storedComponent crossRoot2) == sortOn encodeRow [cross2, cross3Reply])
  assert "ANCESTRY-X-COMPONENT-MARKS: both id-3 components mark the ambiguous key" (componentCollisions crossRoot2 == [3] && componentCollisions crossRoot3 == [3])
  assert "ANCESTRY-X-COMPONENT-COLLISION: component lookup returns both candidates" $ case lookupComponent crossIndex 3 of
    ComponentCollision components -> sort (map componentKey components) == [ResolvedRoot 2, ResolvedRoot 3]
    _ -> False
  assert "ANCESTRY-X-AMBIGUOUS-CITATION: child 4 retains both id-3 candidates" (threadCitations (threadPostFor cross4 crossIndex) == [Citation 3 (PostCollision [cross3Root, cross3Reply])])
  assert "ANCESTRY-X-NO-LAST-WINS: child 4 attaches to neither id-3 candidate" (cross4 `notElem` storedComponent crossRoot2 && cross4 `notElem` storedComponent crossRoot3)
  assert "ANCESTRY-X-UNRESOLVED: child 4 has its own cited-id component" (componentKey crossUnresolved4 == UnresolvedParent 3 && storedComponent crossUnresolved4 == [cross4])
  assert "ANCESTRY-X-CHILD-LOOKUP: child 4 remains directly findable" (lookupComponent crossIndex 4 == ComponentFound crossUnresolved4)

flowTopic :: IO ()
flowTopic = do
  let post = mk "standing by" "alice" 1
  assert "FLOW-NOISE: idle status classified as noise" (classify defaultRules post == Noise)
  let sig = mk "fixed the bug" "bob" 2
  assert "FLOW-SIGNAL: path-containing body classified as signal" (classify defaultRules sig == Signal)
  let neither = mk "random thought" "carol" 3
  assert "FLOW-NEUTRAL: unmatched body classified as neutral" (classify defaultRules neither == Neutral)
  let donePost = mk "DONE: src/Foo.hs" "bob" 4
  assert "FLOW-DONE: DONE + path is a done claim" (isDoneClaim donePost)
  let notDone = mk "DONE: nothing to report" "bob" 5
  assert "FLOW-NOT-DONE: DONE without path is not a done claim" (not (isDoneClaim notDone))
  let pathNoDone = mk "edited src/Foo.hs" "bob" 6
  assert "FLOW-NO-DONE: path without DONE is not a done claim" (not (isDoneClaim pathNoDone))
  let green = mk "🟢 all green" "kimi" 7
  assert "FLOW-DELIVERABLE: green circle is a deliverable" (isDeliverable defaultRules green)
  let notDeliv = mk "standing by" "kimi" 8
  assert "FLOW-NOT-DELIVERABLE: idle status is not a deliverable" (not (isDeliverable defaultRules notDeliv))
  let bothRules = defaultRules {noiseRE = "fixed|bug", signalRE = "fixed|bug"}
  assert "FLOW-PRECEDENCE: signal beats noise when both match" (classify bothRules sig == Signal)
  let custom = defaultRules {noiseRE = "random thought"}
  assert "FLOW-CUSTOM: custom noise rule reclassifies neutral post" (classify custom neither == Noise)
  let custom2 = defaultRules {deliverableRE = "SHIPPED"}
  assert "FLOW-CUSTOM-DELIVERABLE: custom deliverable rule works" (isDeliverable custom2 (mk "SHIPPED it" "alice" 9))

  posts <- mkPosts
  let s = computeStats defaultRules 1 "whole" posts
  assert "STATS-SNR: signal=3, noise=3, snr=1" (statSignal s == 3 && statNoise s == 3 && statSNR s == Just 1)
  assert "STATS-SNR': snr' = signal / (noise + neutral)" (statSNRPrime s == Just 0.75)
  assert "STATS-DONE: one done claim in sample" (statDoneClaims s == 1)
  assert "STATS-PPD: 7 posts / 1 deliverable = 7" (statPostsPerDeliverable s == Just 7)
  assert "STATS-AGENTS: three distinct agents" (statAgents s == 3)
  assert "STATS-REBUS: positive Re_bus for multi-agent slice" (statReBus s > 0)

  let whole = slicePosts WholeLog posts
  assert "SLICE-WHOLE: WholeLog returns one slice with all posts" $ case whole of
    [(_, ps)] -> length ps == 7
    _ -> False
  let byAgent = slicePosts ByAgent posts
  assert "SLICE-AGENT: ByAgent groups by from" (length byAgent == 3)
  let aliceSlice = filter ((== "alice") . fst) byAgent
  assert "SLICE-AGENT-COUNT: alice has 3 posts" $ case aliceSlice of
    [(_, ps)] -> length ps == 3
    _ -> False
  let windows = slicePosts (WindowMinutes 2) posts
  assert "SLICE-WINDOW: 2-minute windows partition posts" (sum (map (length . snd) windows) == 7)
  assert "SLICE-WINDOW-ORDER: windows are in chronological order" (map fst windows == sort (map fst windows))
  forM_ [WholeLog, WindowMinutes 2, ByAgent, ByThread] $ \mode -> do
    let slices = slicePosts mode posts
        slicedIds = sort (concatMap (map frameId . snd) slices)
        sourceIds = sort (map frameId posts)
    assert "SLICE-PARTITION: slicing conserves every post exactly once" (slicedIds == sourceIds)

  historical <- readHistorical
  assert "HISTORICAL-DECODE: all fields survive canonical decode" (map encodeRow historical == T.lines historicalFixture)
  assert "HISTORICAL-IDENTITY: real ids are preserved" (map frameId historical == [0, 1, 2, 3, 4, 5, 6, 7, 8, 101, 113, 282, 284, 285])
  assert "HISTORICAL-CHANNEL: channels survive" (mapMaybe (channel . stamped) historical == ["flow-channel", "flow-channel", "flow-channel"])
  assert "HISTORICAL-RECIPIENTS: multiple recipients survive" (map (length . to . stamped) historical == [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 0, 0, 0])
  assert "HISTORICAL-ANCESTRY: empty, simple, and unresolved parent ids survive" (map (thread . stamped) historical == [[], [0], [], [2], [3], [4], [4], [5], [7], [91], [91], [], [], [284]])
  let historicalThreads = slicePosts ByThread historical
      threadIds label = maybe [] (sort . map frameId) (lookup label historicalThreads)
  assert "HISTORICAL-THREAD-ROOT: descendant follows its earliest present ancestor" (threadIds "2" == [2, 3, 4, 5, 6, 7, 8])
  assert "HISTORICAL-THREAD-UNRESOLVED: missing parent still forms a stable slice" (threadIds "91" == [101, 113])
  assert "HISTORICAL-CHANNEL-THREAD: channel ancestry is independent of channel name" (threadIds "284" == [284, 285])
  forM_ [WholeLog, WindowMinutes 60, ByAgent, ByThread] $ \mode -> do
    let slices = slicePosts mode historical
        slicedIds = sort (concatMap (map frameId . snd) slices)
        sourceIds = sort (map frameId historical)
    assert "HISTORICAL-PARTITION: historical slicing conserves every post exactly once" (slicedIds == sourceIds)

  baseline <- T.readFile =<< getDataFileName "fixtures/baseline.txt"
  -- The fixture omits the report's two terminal newlines to keep git diff --check clean.
  assert "HISTORICAL-BASELINE: slicing, statistics, text, and JSON match free-agent 5990652" (baselineReport historical == baseline <> "\n\n")

  let unbounded =
        Stats
          { statSlice = "unbounded",
            statPosts = 4,
            statAgents = 2,
            statDurationMinutes = 12.5,
            statPostsPerMinute = 0.32,
            statDamping = 2,
            statReBus = 1.28,
            statSignal = 3,
            statNoise = 0,
            statUnclassified = 1,
            statSNR = Nothing,
            statSNRPrime = Just 3,
            statDeliverables = 0,
            statDoneClaims = 2,
            statPostsPerDeliverable = Nothing,
            statTimeToQuiescenceMinutes = 9.75
          }
  assert "RENDER-TEXT-GOLDEN: non-empty golden pins labels, unbounded SNR, and n/a posts/deliverable" (renderStats defaultRules [unbounded] == textGolden)
  assert "RENDER-EMPTY: both renderers are defined on empty input" (renderStats defaultRules [] == emptyTextGolden && decodeJson (encodeUtf8 (renderStatsJson defaultRules [])) == Right emptyJson)
  case decodeJson (encodeUtf8 (renderStatsJson defaultRules [unbounded])) of
    Left err -> assert ("RENDER-JSON-DECODE: " <> err) False
    Right (JObject fields) -> do
      assert "RENDER-JSON-TOP: rule and slice field names" (map fst fields == ["rules", "slices"])
      case lookup "rules" fields of
        Just (JObject rules) -> assert "RENDER-JSON-RULES: rule field names and values" (rules == [("noise", JString (noiseRE defaultRules)), ("signal", JString (signalRE defaultRules)), ("deliverable", JString (deliverableRE defaultRules))])
        _ -> assert "RENDER-JSON-RULES: object" False
      case lookup "slices" fields of
        Just (JArray values) -> case V.toList values of
          [JObject slice] -> do
            assert "RENDER-JSON-FIELDS: all statistic field names" (map fst slice == statFieldNames)
            assert "RENDER-JSON-VALUES: numeric and string values" (all (fieldMatches slice) statFieldValues)
            assert "RENDER-JSON-NULL: unbounded SNR and n/a posts/deliverable are null" (lookup "snr" slice == Just JNull && lookup "posts_per_deliverable" slice == Just JNull)
          _ -> assert "RENDER-JSON-SLICES: one slice object" False
        _ -> assert "RENDER-JSON-SLICES: array" False
    Right _ -> assert "RENDER-JSON-TOP: object" False

statFieldNames :: [Text]
statFieldNames =
  [ "slice",
    "posts",
    "agents",
    "duration_minutes",
    "posts_per_minute",
    "damping_rules",
    "re_bus",
    "signal",
    "noise",
    "unclassified",
    "snr",
    "snr_prime",
    "deliverables",
    "done_claims",
    "posts_per_deliverable",
    "time_to_quiescence_minutes"
  ]

statFieldValues :: [(Text, Json)]
statFieldValues =
  [ ("slice", JString "unbounded"),
    ("posts", JNumber 4),
    ("agents", JNumber 2),
    ("duration_minutes", JNumber 12.5),
    ("posts_per_minute", JNumber (fromRational (toRational (0.32 :: Double)))),
    ("damping_rules", JNumber 2),
    ("re_bus", JNumber (fromRational (toRational (1.28 :: Double)))),
    ("signal", JNumber 3),
    ("noise", JNumber 0),
    ("unclassified", JNumber 1),
    ("snr_prime", JNumber 3),
    ("deliverables", JNumber 0),
    ("done_claims", JNumber 2),
    ("time_to_quiescence_minutes", JNumber 9.75)
  ]

fieldMatches :: [(Text, Json)] -> (Text, Json) -> Bool
fieldMatches fields (name, expected) = lookup name fields == Just expected

emptyJson :: Json
emptyJson = JObject [("rules", JObject [("noise", JString (noiseRE defaultRules)), ("signal", JString (signalRE defaultRules)), ("deliverable", JString (deliverableRE defaultRules))]), ("slices", JArray V.empty)]

textGolden :: Text
textGolden =
  T.unlines
    [ "bus-stats",
      "  noise regex:    " <> noiseRE defaultRules,
      "  signal regex:   " <> signalRE defaultRules,
      "  deliverable:    " <> deliverableRE defaultRules,
      "",
      "slice: unbounded",
      "  posts:               4",
      "  agents:              2",
      "  duration (min):      12.500",
      "  posts/min:           0.320",
      "  damping rules:       2",
      "  Re_bus:              1.280",
      "  signal:              3",
      "  noise:               0",
      "  unclassified:        1",
      "  SNR:                 -",
      "  SNR':                3.000",
      "  deliverables:        0",
      "  done claims:         2",
      "  posts/deliverable:   n/a",
      "  time to quiescence (min): 9.750",
      ""
    ]

emptyTextGolden :: Text
emptyTextGolden =
  T.unlines
    [ "bus-stats",
      "  noise regex:    " <> noiseRE defaultRules,
      "  signal regex:   " <> signalRE defaultRules,
      "  deliverable:    " <> deliverableRE defaultRules,
      ""
    ]

historicalFixture :: Text
historicalFixture = T.unlines (map encodeRow expectedHistorical)

expectedHistorical :: [Stored]
expectedHistorical =
  [ Stamped (time "2026-11-12T04:03:38", 0) (Post "seat-a" Nothing ["seat-b"] [] "ordinary historical note"),
    Stamped (time "2026-11-12T04:05:20", 1) (Post "seat-b" Nothing ["seat-a"] [0] "standing by"),
    Stamped (time "2026-11-12T04:09:45", 2) (Post "seat-a" Nothing ["seat-b"] [] "decided to keep the flow boundary"),
    Stamped (time "2026-11-12T04:14:30", 3) (Post "seat-b" Nothing ["seat-a"] [2] "ack"),
    Stamped (time "2026-11-12T04:32:21", 4) (Post "seat-c" Nothing ["seat-b"] [3] "DONE: src/Bus/Flow.hs"),
    Stamped (time "2026-11-12T04:35:07", 5) (Post "seat-c" Nothing ["seat-b"] [4] "ordinary reply"),
    Stamped (time "2026-11-12T04:37:20", 6) (Post "seat-b" Nothing ["seat-c"] [4] "🟢 extraction complete"),
    Stamped (time "2026-11-12T04:40:18", 7) (Post "seat-b" Nothing ["seat-c"] [5] "waiting on the next task"),
    Stamped (time "2026-11-12T04:44:54", 8) (Post "seat-c" Nothing ["seat-b"] [7] "fixed the historical decoder"),
    Stamped (time "2026-11-12T06:53:39", 101) (Post "seat-d" Nothing ["seat-b", "seat-e"] [91] "ordinary multi-recipient note"),
    Stamped (time "2026-11-12T06:57:10", 113) (Post "seat-d" Nothing ["seat-c", "seat-b", "seat-e"] [91] "🟢 multi-recipient delivery"),
    Stamped (time "2026-11-14T01:35:21", 282) (Post "channel-a" (Just "flow-channel") [] [] "ping"),
    Stamped (time "2026-11-14T01:36:32", 284) (Post "channel-b" (Just "flow-channel") [] [] "channel ordinary note"),
    Stamped (time "2026-11-14T01:36:32", 285) (Post "channel-a" (Just "flow-channel") [] [284] "DONE: fixtures/historical.jsonl")
  ]
  where
    time t = fromMaybe (error ("bad historical fixture time: " <> T.unpack t)) (parseTimeText t)

readAncestryFixture :: FilePath -> Int -> IO [Stored]
readAncestryFixture name expectedCount = do
  raw <- T.readFile =<< getDataFileName name
  rows <- forM (zip [1 :: Int ..] (T.lines raw)) $ \(lineNo, line) ->
    case decodeRow line of
      Left why -> fail (name <> " decode failed at row " <> show lineNo <> ": " <> T.unpack why)
      Right post -> pure post
  assert (name <> ": constructed row count") (length rows == expectedCount)
  pure rows

readHistorical :: IO [Stored]
readHistorical = do
  raw <- T.readFile =<< getDataFileName "fixtures/historical.jsonl"
  rows <- forM (zip [1 :: Int ..] (T.lines raw)) $ \(lineNo, line) ->
    case decodeRow line of
      Left why -> fail ("historical fixture decode failed at row " <> show lineNo <> ": " <> T.unpack why)
      Right post -> pure post
  assert "HISTORICAL-FIXTURE-COUNT: fourteen rows" (length rows == 14)
  pure rows

baselineReport :: [Stored] -> Text
baselineReport posts = T.unlines (map modeReport modes)
  where
    modes = [(WholeLog, "whole"), (WindowMinutes 60, "window-60"), (ByAgent, "agent"), (ByThread, "thread")]
    modeReport (mode, label) =
      let slices = slicePosts mode posts
          stats' = map (uncurry (computeStats defaultRules 1)) slices
       in T.unlines
            [ "MODE " <> label,
              T.intercalate "\n" (map sliceSummary (sortOn fst slices)),
              "TEXT\n" <> renderStats defaultRules stats',
              "JSON\n" <> renderStatsJson defaultRules stats'
            ]
    sliceSummary (label, rows) = "SLICE " <> label <> "|" <> T.intercalate "," (map (T.pack . show . frameId) rows)
