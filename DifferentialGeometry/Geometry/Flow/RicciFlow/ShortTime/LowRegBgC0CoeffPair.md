# LowRegBgC0CoeffPair

## Role

Merge point of the C0Core split: the first chunk importing all three branches
(`LowRegBgC0Amix` + `LowRegBgC0PairRic` + `LowRegBgC0PairEst`).  Exports the
combined coefficient pair estimates `lowOneAPairH2` and `lowOneIntPairH2`.

Chain position: `{Amix, PairRic, PairEst} → this → LowRegBgC0Integrate`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02 (focused 25.6 s,
build 25 s).  Zero sorry/admit/axiom/whnf/trace.  Light despite the 2.4M/1.6M
scoped heartbeat settings.
