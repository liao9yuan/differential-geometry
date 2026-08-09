# LowRegBgC0PairEst

## Role

The VB branch of the C0Core split (independent of the Pair chain).  Single
export: `vbOnePairH2`, carrying its pre-existing 4,800,000-heartbeat setting
inherited verbatim from the monolith (NOT new; do not retune — refactor the
proof body if resources ever need to improve).

Chain position: `LowRegBgC0One → this → LowRegBgC0CoeffPair`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.

## Performance

The heaviest chunk of the split: focused ~648 s, exact build ~728 s, peak RSS
~4.93 GB, all inside `vbOnePairH2`.  Never re-run its build unless the source
changes.
