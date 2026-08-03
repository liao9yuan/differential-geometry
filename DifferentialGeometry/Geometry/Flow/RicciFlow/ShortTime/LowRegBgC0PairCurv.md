# LowRegBgC0PairCurv

## Role

Second link of the pair-estimate branch of the C0Core split.  Curvature-block
pair estimates: `aaKerOnePairH2` (the pre-existing 5,000,000-heartbeat
theorem inherited verbatim from the monolith — the high value is NOT new and
must not be retuned; resource work should refactor the proof body instead),
`reindexSubC0`, `fourTracePair`, `aaOnePairH2`.

Chain position: `LowRegBgC0PairBase → this → LowRegBgC0PairDA`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.

## Performance

Hotspot chunk: focused ~298 s, exact build ~298 s, peak RSS ~3.31 GB
(dominated by `aaKerOnePairH2`).  Do not re-run its build unless the source
changes.
