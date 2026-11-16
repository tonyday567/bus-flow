# Revision history for bus-flow

## 0.1.0.0 -- 2026-11-16

* Extract pure historical-log classification, slicing, statistics, and
  rendering from free-agent 5990652.
* Add baseline, historical-fixture, text-rendering, and JSON witnesses.
* Build on circuits (`Circuit.Post`, `Circuit.Shared`) and the
  circuits-parser framing row instead of circuits-agent: `Stored` is
  `Stamped (UTCTime, PostId) (Post Text Text)`, and the oracle decodes the
  fixture with `decodeRow` and re-encodes it with `encodeRow`. The version
  stays 0.1.0.0 and no dependency bound moves, so a consumer that still
  annotates with the old alias meets this as compile errors on the `Post`
  identity rather than as a solver refusal.
