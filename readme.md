# bus-flow

Pure historical-log analysis. `Bus.Flow` classifies stamped `Text` posts,
slices them by whole log, time window, author, or ancestry, computes flow
statistics, and renders text or JSON.

Phase 1 is standalone only. The library has no `Free.Agent` namespace or
dependency and no bus runtime, cursors, heartbeats, filesystem, process, or
service code.

```sh
cabal build lib:bus-flow
cabal run exe:bus-flow-axioma
```

The historical fixture uses ids, timestamps, channels, recipient shapes, and
ancestry from selected real coordination rows, with names and bodies replaced
by sanitised values. `fixtures/baseline.txt` was produced by compiling the
333-line `Free.Agent.BusStats.hs` from free-agent commit
`5990652f09423d06fce7147c36ec2c1c0e884caf` against that fixture. The oracle
compares all slicing modes, all statistics, text rendering, and JSON rendering
against that fixed baseline. It also retains the 20 pure statistical/slicing
assertions and adds field-level JSON and non-empty/empty rendering witnesses.
