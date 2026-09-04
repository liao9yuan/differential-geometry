# MinimalGeodesicNoConjugate

## 2026-08-30 source repair

- `not_conj_of_min_len` and `not_conj_of_min` remain unchanged public theorem
  statements.  This module is a comparison-geometry dependency in the current
  `RiemannianTail` recovery cone.
- The curvature self-cancellation now uses the native antisymmetry equation to
  obtain `R(v,v)v + R(v,v)v = 0`, rewrites this as scalar multiplication by
  two, and cancels the nonzero scalar.  This replaces an invalid module-ring
  normalization attempt.
- Closed-interval `Set.EqOn` facts are applied through their implicit point
  argument; endpoint and interior membership proofs are passed explicitly.
- Private helper boundaries explicitly omit unused section instances without
  changing any public assumptions.
- Focused verification passed without warnings.  The file contains no
  `sorry` or `admit`.

## Progress accounting

- `not_conj_of_min_len`: 100% theorem endpoint; its dedicated machinery in
  this module: 100% and warning-free focused verified.
- This source-repair lane: 100%.  It is one of three disjoint source blockers
  in the current dependency-cone repair, so this result alone accounts for one
  third of that repair gate; exact downstream refresh remains intentionally
  pending until the parallel window closes.
- Broader P2b package theorem: unstated, hence 0%; its recorded dedicated
  machinery is about 62--66%.  Whole P0--P9 infrastructure remains about
  15--25%; this local repair does not change those project-wide estimates.

## 2026-09-01 raw exponential route

### Mathematical route

`raw_exp_inj_of_min` is source-written for a unit-speed raw radial segment on
an arbitrary positive horizon `[0,L]`.  Its public inputs are exactly radial
`expDomain` membership and the endpoint-fixed length-minimizing property up to
`expMap g p (L • u)`, together with the metric hypotheses already required by
the index-form argument.  It does not assume `CompleteSpace M` and introduces
no conjugacy or supplied-variation wrapper.

The proof takes a kernel vector of the raw exponential differential and uses
`radial_jacobi_dom` to turn it into an interior zero of the corresponding raw
radial Jacobi field.  A smooth scalar time clamp globalizes the central curve
without changing its germ on `[0,1]`.  The globalized variation field is
obtained pointwise from `expMap_contMDiffAt` and `varField_smoothAt`; the raw
regularity and Jacobi equation are transported through `radial_jacobi_reg`,
`raw_radial_geo_at`, and `jacobiAt_congr`.

The endpoint orthogonality argument uses only interior Jacobi equations and
closed-interval regularity.  `IsJacobiSolOn.of_Ioo` then restores the two
one-sided endpoint equations for the perpendicular coefficient system.  The
remaining proof is the existing parallel-frame/index-form contradiction:
construct a nonzero perpendicular Jacobi coefficient, smooth its negative
index direction, lift it back to the manifold, and contradict nonnegativity
for an endpoint-fixed minimizing unit-speed geodesic.  Arc length is transferred
from the clamp to the raw radial curve by germ equality under the interval
integral.  The completeness-free realization of the negative field belongs in
`SecondVariationMinimiser`: its wrapper uses the existing compactly supported
flow producer `exists_var_fix_ends`, rather than duplicating the second-
variation tail in this consumer.

### Reuse and boundary

- Reused the canonical raw-domain smoothness and radial-geodesic/Jacobi APIs;
  no consumer-local rescaling or geodesic copy remains.
- Reused the existing perpendicular frame, ODE, smoothing, lifted index-form,
  and second-variation nonnegativity chain.
- The result is a no-conjugacy/nonsingularity producer only.  It does not by
  itself prove raw segment-domain coverage, measurability, or the compact-ball
  Bishop endpoint.

### Verification

The source contains no placeholder.  Focused checking reached the final
index-form call after two local elaboration repairs: scalar linearity of the raw
exponential differential is now explicit, and the two-parameter base point is
typed as `Real × Real`.  The only remaining diagnostic was the old wrapper's
hidden `CompleteSpace M`; a direct source experiment with
`exists_var_fix_ends` confirmed that no completeness is needed.  The duplicate
consumer proof was then removed because the canonical wrapper belongs in
`SecondVariationMinimiser`.  That producer and its completeness-free wrapper
are warning-free focused verified.  Both calls in this file use the shorter
wrapper signature.  The now-unused metric-norm witness was removed from the raw
theorem, and unused tangent-bundle separation instances were explicitly omitted
from the two complete compatibility theorems.  The arbitrary-horizon source
uses `L` in every interval, endpoint, and index-form bound, while derivative
directions and the unit-speed scalar remain `1`.  It reuses the generic
`radial_jacobi_on` theorem directly.  Generic-horizon focused verification
passed without warnings after deleting one redundant `rfl` whose preceding
rewrite already closed the endpoint goal.  No refresh or build was run here.

### Progress accounting

- `raw_exp_inj_of_min`: 100% for the arbitrary-horizon theorem and its dedicated
  proof; focused verification is warning-free.
- The tracked P1a producer gate is now eight of eight verified groups (100%).
  This is infrastructure only: it does not state or prove the compact-closure
  Bishop theorem.
- The compact-closure Bishop theorem remains unstated (0%).  This local source
  brick does not change the broader Poincare-program estimate.
