# LowRegOperatorTime

## 2026-08-05 — non-vacuous second-order cutoff

`lowA2_small_one` combines the radius-flexible pair estimate with the existing
uniform Lipschitz cutoff, then shrinks to
`min ρA (1 / (C + 1))`.  It proves `C * ρ < 1` while preserving continuity,
both completed operator bounds, and the commuting inclusion square.

Focused verification passed warning-free, and the direct module refresh passed.
This closes the per-metric contraction-admissibility gap; the coefficient and
radius still need class-uniform witnesses before `(N)` can choose one common
level and horizon.
