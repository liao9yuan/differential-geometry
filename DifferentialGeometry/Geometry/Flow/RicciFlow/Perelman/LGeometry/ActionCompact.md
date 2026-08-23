# ActionCompact

## Implemented capstone

`ActionCompact.lean` proves `lAction_subseq`: a sequence of regularized L-curves on a fixed compact
parameter interval and compact target manifold has a uniformly convergent subsequence whenever
all curves share one regularized-action upper bound and the natural differentiability and
integrability hypotheses.

The conclusion provides a strictly monotone subsequence and a genuine continuous map
`g : C(Set.Icc a b, M)`, with `TendstoUniformly` on the entire parameter interval. No endpoint
condition is imposed because it is not needed for this weakest compactness theorem.

`lAction_subseq_fix` is the fixed-endpoint corollary needed by a minimizing sequence. If every
curve joins the same two points, pointwise convergence at the two endpoint subtypes and uniqueness
of limits show that the C0 limit joins those points as well.

Focused verification passes without warnings or placeholders. The `lAction_subseq` and
`lAction_subseq_fix` theorems and this C0 compactness capstone are 100% complete.
`exists_lMinimizer` remains unstated and unproved
(0%): compactness of minimizing sequences is now available, but closure of the intended competitor
conditions and lower semicontinuity of the complete regularized action still have to be assembled.
Its dedicated direct-method machinery is approximately 35--45% complete. Dedicated L-geometry
machinery is approximately 68--72% complete; reusable generic prerequisites are approximately
97--99% complete. `redVolume_anti` remains unstated and unproved (0%), P2 remains below 1%, and the
whole Poincare program remains approximately 3--5% complete.

## Proof route

The action-to-energy theorem `lRefEnergy_bound` is invoked once, outside the sequence quantifier.
Consequently one pair of compact-slab constants and one fixed-reference `curveEnergy` budget work
for every curve in the family.

For each ordered subinterval, `curveEnergy_mono` restricts that global budget and
`edistOf_le_budget` gives the intrinsic reference-metric square-root estimate. The function
`r ↦ sqrt r * sqrt B` tends to zero at zero. Combining this filter statement with
`dist_lt_of_riedist` proves uniform equicontinuity in the ambient pseudometric. Reversely ordered
points are handled by swapping the ordered intrinsic estimate and using ambient `dist_comm`; this
avoids comparing whole Riemannian-bundle instances.

Each curve is then restricted to a continuous map on `Set.Icc a b`, and `arzela_subseq_cpt` is
applied with the compact target set `Set.univ`. The fixed-endpoint corollary uses
`TendstoUniformly.tendsto_at` at the two endpoint subtypes and Hausdorff uniqueness of limits.

## Boundary

The implementation introduces no admissibility or minimizer class, no path-space foundation, no
`IsMetricNorm` or `CompleteSpace` assumption, and no supplied equicontinuity hypothesis. It does not
edit the action, Arzela--Ascoli, or Riemannian-distance producer files.
