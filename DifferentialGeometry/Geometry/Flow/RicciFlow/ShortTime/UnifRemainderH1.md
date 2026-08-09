# UnifRemainderH1

## 2026-08-06 source handoff

`rem_h1_unif` is the dimension-three, class-first analogue of the fixed-metric
mixed remainder theorem.  It chooses the top radius/coefficient and both affine
lower coefficient functions before the class metric varies, with DeTurck
background fixed to `gBase`.

The proof directly replays the structural path split used by
`rem_h1_of_jets`; it does not call that metricwise existential.  Its four
inputs are `top_path_h1_unif`, `lower_jet_unif`, `rhs0_path_unif`, and
`rhs1_path_unif`.  The exact lower coefficients are
`B0 R = Clow + Ccoef * (Z0 R + O0 R)` and
`B1 R = Ccoef * (Z1 R + O1 R)`.

Verification is closed: the focused file check and direct module export pass,
and the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The only repairs from the source draft were the direct base import, the path
cast normalization, and namespace/unused-variable scoping; no mathematical
hypothesis or public interface changed.
