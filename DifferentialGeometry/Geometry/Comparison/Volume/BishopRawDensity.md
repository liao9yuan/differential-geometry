# BishopRawDensity

## Route

`raw_ratio_anti` is the q=0 radial scalar comparison on a supplied positive
horizon.  Its inputs are exactly raw exponential-domain coverage on the closed
segment, endpoint-fixed minimizing length, a unit launch direction, an
orthonormal perpendicular family of cardinality `finrank E - 1`, and
nonnegative Ricci curvature along that radial segment.

The proof reuses `raw_exp_inj_of_min` and `radialJacobi_li_of` for interior
linear independence, `radial_jacobi_on` and `radial_jacobi_reg` for the Jacobi
and closed-interval regularity data, `wronskian_zero_Ioo` for symmetry,
`curveMean_le_on` and `curveRatio_anti` for the Riccati comparison, and
`radialRatio_pole` for the pole lower bound.

The older `radialJacobi_perp` and `radialJacobi_dperp` only cover the small
normal-radius regime.  The proof instead reuses the canonical
`jacobi_perp_of_init`: the raw radial geodesic equation, Jacobi data, and the
pole initial values supplied by `radial_jacobi_d0` propagate both required
perpendicularities across the whole closed segment.  The former private
duplicate of this propagation argument was removed; no public wrapper or
consumer assumption was added.

`raw_density_le` is the direct pole-normalized corollary: antitonicity and
`radialRatio_pole` bound the raw curve density by `hypDensity 0 d` at every
positive interior time.

For the incomplete-ambient CGT route, the Riccati core is now factored through
the private `raw_ratio_inj`.  It takes the actual positive radial speed and
injectivity of the raw exponential differential at every positive radial time.
The pre-existing `raw_ratio_anti` remains unchanged as a public minimizing
corollary: `rawSpeed_sq` supplies unit speed and `raw_exp_inj_of_min` supplies
the differential injectivity.  Thus no duplicate Riccati or Jacobi hierarchy
was introduced.

`rawDens_le_of_inj` is the new all-launch q=0 pointwise producer.  Its public
inputs are only raw-domain coverage on `[0,1]`, injectivity of the raw
exponential differential at every time in `(0,1)`, and nonnegative radial Ricci
curvature.  It does not assume a metric-norm realization, completeness,
minimality, a unit launch, or a positive-rank premise.  The zero launch closes
directly at the pole.  For a nonzero launch, the proof uses its actual positive
speed in `raw_ratio_inj`, takes the one-sided density limit at time one, and
then applies the existing `rawDens_split` full/transverse Gram factorization.

The conclusion directly bounds the unframed raw chart-basis density used after
the time-one columns are rewritten by `radial_jacobi_dom`.  It is not literally
the normal-frame/`volume`-coordinate integrand of `framed_mul_le_area`.  A
consumer choosing that coordinate form still needs the completeness-free raw
analogue of `expJac_normal_int`: change from `chartModelBasis`/`modelHaar` to
`normalBasis`/`volume` through `normalFrame`, using the existing basis
determinant and `Module.Basis.map_addHaar` argument.  Alternatively a raw area
consumer stated in unframed coordinates can use this theorem after the local
column rewrite and normalize the constant right-hand side with the existing
`normalHaar_eq` measure identity.

`rawDens_eq_trans` identifies the full raw chart-basis density at a positive
rescaled launch with the pole density times the transverse density at the
original radial time.  The proof identifies the radial Jacobi column with the
geodesic velocity through `radial_jacobi_dom`, uses conservation of speed and
the canonical `jacobi_perp_of_init` propagation to split the Gram determinant,
and changes from the chart basis to an orthogonal radial/transverse basis via
`curveDensity_recomb` and `curveDensity_reindex`.  The remaining radial power
comes from `radialJacobi_scale`, raw differential linearity, and a diagonal
`curveDensity_recomb`; no intrinsic exponential or small-radius API is used.

`rawSpeed_sq` is public because the later ball-local Ricci consumer also needs
the constant-speed identity on an arbitrary nonnegative raw-domain segment.
It keeps the same direct hypotheses: raw-domain coverage, raw radial
geodesicity, and the local smoothness already provided by `expMap_contMDiffAt`.

`rawDens_le_zero` is the q=0 pointwise full-density producer.  At a nonzero
launch it normalizes by the metric length, obtains a perpendicular orthonormal
family, transfers the Ricci inequality to the unit raw ray, and derives the
endpoint transverse estimate from `raw_density_le` by one-sided continuity.
`rawDens_eq_trans` and cancellation of the positive radial power then give the
full chart-basis bound.  The zero launch is identified directly with
`normalDensity_radial`.  Competitor minimality is derived from the supplied
distance lower bound using the direct `riemannianEDist_le_arcLength` bridge, so
no completeness assumption or new minimizing predicate is introduced.

## Verification

Focused verification passed without warnings through `rawDens_le_zero`,
including the public `rawSpeed_sq` producer and `rawDens_eq_trans`.  The only
repairs after the canonical perpendicularity bridge landed were local
smoothness-order, within-set, q=0 normalization, finite-cardinality, endpoint
continuity, and affine-reparameterization elaboration details.

The extended file is warning-free focused GREEN through
`rawDens_le_of_inj`.  The first new pass exposed only declaration-local
instance scope, the explicit reflexive zero-dimensional endpoint, and q=0
model-density normalization.  The second pass exposed only an inferred family
argument at the preserved minimizing wrapper and two local linter items.  All
were repaired without changing the public theorem assumptions or conclusion.
No targeted refresh or broader build was run during the parallel window.

## Project position

`rawDens_le_zero` and `rawDens_le_of_inj` are each proved and focused-verified
(100% locally).  P1a is already closed at eight of eight project-used
endpoints.  This new theorem is dedicated P1b machinery only: incomplete-
ambient E1 and E2 remain formally unstated (0%), aggregate P1 remains eleven of
fourteen endpoints (78.6%), and the whole Poincare theorem endpoint remains
unstated (0%).  The raw multiplicity-area theorem and raw CGT collision
assembly remain separate consumers.
