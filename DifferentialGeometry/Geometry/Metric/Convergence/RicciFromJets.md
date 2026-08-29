# Ricci and scalar stability from metric jets

## Compact scalar endpoint

The intended next endpoint is `scalarSub_le_dNormOn`: one positive constant
for the scalar-curvature difference estimate at every point of a compact set,
under the same reference-metric lower bound and order-at-most-two covariant-jet
bounds as `scalarSub_le_dNorm`.

The existing pointwise proof is not yet a compact-uniform producer. Its
constant is assembled from the self-centered chart basis at the evaluation
point through `invGram_le_of_low`, `invGram_sub_le`,
`ricciSub_le_dNorm`, and `ricci_abs_le`. In turn these use point-dependent
slot extensions and chart comparison constants.

The fixed-chart order-two jet bridge did not need to be rebuilt:
`chartJet_sub_le` and `chartJet2_sub_le` in `Precompactness.lean` already give
compact-uniform chart-jet differences from the intrinsic reference-metric
covariant norms. The new source theorem `invGram_le_of_lowOn` supplies the
other first fixed-chart input. It proves a family-uniform inverse-Gram entry
bound on a compact chart piece from `u ≥ λ gRef`. Its private producer
`gram_quad_low_on` takes the positive minimum of the continuous reference
Gram quadratic form over the compact product of the chart piece and the
Euclidean unit sphere. This is a genuine finite-dimensional compactness
estimate, not a new convergence assumption.

The downstream `RicciFromJetsCompact.lean` now contains the source-written
fixed-chart Ricci/scalar chain and finite-active POU assembly. This file remains
the lower producer home for `invGram_le_of_lowOn`; it does not import the
downstream module back.

## Verification

The first focused verification failed locally in `gram_quad_low_on`: after
simplifying with `p0.2 = 0`, Lean retained the proposition `0 ∈ S` instead of
unfolding the locally defined unit sphere, so it could not derive `False`.
The source now first records `p0.2 ∈ S` and rewrites `S` by its defining
equation before simplifying. The second focused verification proved the source
but reported one local linter
warning at the repaired zero-vector branch: use `simp ... at hp0S` directly
instead of deriving the contradiction through a `simpa ... using hp0S`
intermediate equality. That exact mechanical cleanup is now applied; the next
warning-free retry is pending. No assumption wrapper, new predicate, placeholder, or
`sorry` was introduced.

The first downstream compact-module check also confirmed that no additional
public declaration is needed here: `partialDeriv` and `chartRicciTensor` are
already public in `DifferentialGeometry.Integral.DivergenceTheorem`, while
`chartGramOnE_contDiffOn_int` is already public in
`DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients`.  The downstream
module now opens/uses those native namespaces directly; this file's only new
public surface remains `invGram_le_of_lowOn`.

## Project position

`scalarSub_le_dNormOn` is source-written downstream but remains 0% verified.
Its dedicated compact-uniform machinery is roughly 80--90% source-implemented
and 0% verified as a complete chain; the warning-free producer retry is pending. P2a
is 100% complete. This remains one producer inside P2b; the whole P0--P9
program is roughly 15--25% complete.
