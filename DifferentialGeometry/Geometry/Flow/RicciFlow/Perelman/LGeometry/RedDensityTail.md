# RedDensityTail

## Route

`redDensity_tail_le` is the direct complete-slice Gaussian tightness adapter.
It specializes `redDensity_gauss` with `c = decay * tau`, factors the exact
Perelman normalization out of the restricted `lintegral`, and applies
`riem_gauss_tail` to the remaining intrinsic Gaussian.  The quadratic
reduced-length lower bound is the sole geometric input; this module does not
package or assume the future Hamilton--Harnack producer that will establish it.

## Status

Warning-free focused verification is green.  A temporary direct axiom audit
reported only `propext`, `Classical.choice`, and `Quot.sound`; the audit command
was then removed from the source.  The first two-thread check encountered host
allocation pressure, while the compacted proof and one-thread focused checks
completed normally.

The exact named module refresh is GREEN, and the 82-declaration unified P2
audit confirms the same three standard logical axioms.

## Scope

This theorem controls exterior reduced-density mass for one complete time
slice with nonnegative Ricci curvature and an explicitly supplied moving center.
It does not prove the uniform quadratic coercivity, no-mass-loss, asymptotic
shrinker, kappa-solution, or surgery endpoints.

`redDensity_tail_le` and its dedicated adapter machinery are 100% for the
stated conditional exterior-mass estimate.  The uniform moving-center
coercivity theorem remains unstated at 0% because it consumes P3
Hamilton--Harnack inputs.  The broader P2b package theorem remains unstated at
0%, with dedicated machinery roughly 93--95%; the whole P0--P9 infrastructure
remains approximately 15--25%.
