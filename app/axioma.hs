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
