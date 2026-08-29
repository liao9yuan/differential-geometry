# DistanceBarrier

## Scope and route choice

This file is the minimal producer-facing Laplacian-barrier layer for P1c.  It
does not state a weak Laplacian endpoint, a viscosity limit theorem, or a
Busemann theorem.

Three routes were compared before implementation:

- An epsilon-relaxed upper-barrier predicate is the native first layer.  It
  directly records the smooth Calabi support while allowing the error budget
  needed by later comparison and limit arguments.
- A viscosity predicate is the correct next layer for local-uniform limit
  stability.  It should use smooth test functions touching from below for an
  inequality of the form `Δ u ≤ b`.  The upper barrier then bounds such a test
  through the local-minimum Hessian/Laplacian argument.
- A direct distributional definition is not the first layer: it would
  prematurely couple the Calabi producer to manifold volume, nonnegative
  compactly supported test functions, integration by parts, local
  integrability/Sobolev representatives, and passage to the limit under an
  integral.

Accordingly, `IsLapLEBarrierAt` is an epsilon-relaxed upper-support predicate,
and `IsLapLEBarrierOn` is its pointwise set-level form with a variable
right-hand side.  No stability or weak consequence is claimed by these
definitions.

## Native reuse

`lapBarAt_of_support` converts any exact smooth upper support into the relaxed
predicate.  `dist_lap_barrier` applies that adapter to the existing
`calabiDist_support`; it does not duplicate the Calabi construction or expose
its branch/tail implementation.

The next analytic layer should prove barrier-to-viscosity using the native
local-minimum Laplacian API, then prove local-uniform stability and finally an
intrinsic viscosity/distributional equivalence.  Those are intentionally not
hidden as assumptions or wrapper theorems here.

## Verification and project status

The first focused verification failed locally.  `IsLapLEBarrierAt.mono` used
the wrong addition-side lemma, producing `ε + c ≤ ε + d` where the goal was
`c + ε ≤ d + ε`; the same run reported four unused section instances on
`lapBarAt_of_support`.  Native uses confirm that `add_le_add_left hcd ε` has
the required right-addition shape.  The proof and the exact four linter
`omit`s were repaired statically.  The second focused verification proved all
declarations, but reported the same four unused section instances on
`IsLapLEBarrierAt.mono`.  That declaration now has the same exact `omit` list.
The third focused verification passed without warnings, and the explicitly
named module refresh also passed (`3944/3944`).  The barrier predicate,
generic support adapter, monotonicity lemma, and Calabi distance producer are
therefore verified source infrastructure.

An earlier static elaboration-risk review compared this file with the
focused-green `MinimizingRay` instance discipline.  Smoothness grades are now
explicitly typed as `WithTop ℕ∞`, proof terms avoid fragile order dot notation,
and cross-file producer calls pin the manifold parameter.  The abstract
barrier predicates remain independent of `RiemannianBundle`; only
`dist_lap_barrier` enters the same locally disabled default tangent-norm
instance scope as `calabiDist_support`.

All four P1c endpoints remain unstated/unproved at 0%.  This verified barrier
interface is prerequisite infrastructure only: the barrier-to-viscosity,
local-uniform stability, and intrinsic weak/distributional bridges remain
missing.  Whole-P1c dedicated machinery remains about 15--25%; the
distance/Laplacian dedicated machinery is about 65--70% and must not be counted
as an endpoint.
