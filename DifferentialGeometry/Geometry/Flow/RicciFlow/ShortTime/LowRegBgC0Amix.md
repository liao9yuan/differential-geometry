# LowRegBgC0Amix

## Role

The AMix branch of the C0Core split (independent of the Pair chain and the VB
branch).  Five small square/scale algebra lemmas plus the two heavy theorems
`amixHalfPairH2` (pre-existing 6,400,000-heartbeat setting inherited verbatim
from the monolith — NOT new, do not retune; refactor the proof body if
resources ever need to improve) and `amixOnePairH2` (1,600,000), plus
`jetAddFour`.

Chain position: `LowRegBgC0One → this → LowRegBgC0CoeffPair`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02 (focused ~204 s,
build 185 s).

## Performance

Peak RSS ~4.23 GB, dominated by `amixHalfPairH2`.  On a ~16 GB machine this
needs ≳4.6 GB of free RAM; the 2026-08-02 session had to reclaim ambient
memory (working-set trims of idle apps) before the build would fit.  Never
re-run its build unless the source changes.
