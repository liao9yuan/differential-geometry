# UnifCoreTame

## 2026-08-06 source draft

`smoothN_h1_unif` and `coreN_tame_unif` are written as dimension-three,
class-first transports of the already checked fixed-metric proofs.  Their
radius and tame coefficients are obtained from `rem_h1_unif` before the class
metric `g` is introduced; every consumer metric carries uniform equivalence to
`gBase` and background-covariant metric-jet bounds through order three.

The spectral transport reuses the two existing remainder-to-smooth identities.
The dense-core transport replays the existing symmetrization and
`coreRep_spec` norm comparisons, so it introduces no new analytic assumption
or frontier.

Verification is closed: both theorem bodies contain no `sorry`, the focused
file check and direct module export pass, and the axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The sole source repair was
opening the existing `HCGCompactness` namespace; no theorem interface changed.

Progress accounting: the two adapter theorems are 100% verified.  They do not by themselves prove the
uniform low-regularity producer or `ricci_flow_unif_existence`; those endpoints
remain separate and unproved.
