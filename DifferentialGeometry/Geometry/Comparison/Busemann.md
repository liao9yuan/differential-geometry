# Busemann metric core

## Scope

This file is the first native producer for the P1c Busemann/splitting lane.  It
stays entirely at the metric level and imports the canonical minimizing-ray API
from `MinimizingRay.lean`; it does not define a second ray predicate and does
not assume Ricci curvature, smoothness of distance, or a Laplacian statement.

## Source-written interface

- `busemannApprox` uses poles at the nonnegative integers.
- `busemann` is the infimum of the integer-pole approximations.
- `buseApprox_anti`, `buseApprox_lower`, and `buseApprox_bdd` give monotonicity
  and a finite real lower bound from the minimizing-ray distance identity.
- `busemann_le_approx` and `busemann_tendsto` identify the infimum with the
  monotone limit.
- `buseApprox_dist`, `busemann_sub_le`, and `busemann_dist` give the spatial
  one-Lipschitz estimate.
- `busemann_ray` proves the exact value `-s` on the ray for `0 ≤ s`.

The proofs use only the canonical `IsMinimizingRay` distance equality,
`riemannianEDist_triangle`, symmetry, finiteness of Riemannian extended
distance, and the conditionally complete real-order convergence theorem.

## Verification status

Final durable status: the Busemann metric core passed focused verification
without warnings, and its explicit named module refresh also passed.  All
source-written declarations in `Busemann.lean` are verified and contain no
`sorry`.  This final status supersedes the pending-verification notes in the
iteration history below.

This verifies only the reusable metric producer: integer-pole approximations,
their finite monotone limit, the spatial one-Lipschitz estimate, and the exact
value along a minimizing ray.  The formal P1c Busemann endpoint is not yet
stated and proved and therefore remains 0% complete; weak Laplacian passage and
the later splitting consumers remain separate work.

The first focused check failed on local elaboration shapes: the smoothness grade
notation was inferred as `ENNReal`; the symmetry lemma was incorrectly supplied
explicit point arguments although its points are implicit; and the infimum,
limit-subtraction, and eventually-constant goals needed their functions and
limits exposed explicitly.  These are notation, implicit-argument, order, and
topology/coercion issues, not missing geometric input.

The source has been statically repaired with a notation-free smoothness grade,
the canonical `IsMinimizingRay.edist_eq` projection, explicit real-distance
calculations, and `tendsto_atTop_of_eventually_const`.  Re-verification remains
deferred until the coordinator releases the shared elaboration window.

The second focused check exposed the same tangent-space norm-instance conflict
as `MinimizingRay.lean`: the generic tensor-bundle norm was selected instead of
the norm supplied by the active `RiemannianBundle`, so the first inner-product
obligation failed and later metric goals cascaded.  The whole metric core now
uses one scoped instance policy matching `MinimizingRay.lean`.  The pure
distance-symmetry helper also omits exactly the unused finite-dimensional,
boundaryless, manifold-separation, and sigma-compact section variables reported
by the linter.  This second repair is source-written but not yet rechecked.

The third focused check showed that the instance policy had the right content
but the wrong scope order: the metric typeclass binders were elaborated before
the section-local instance removal took effect.  The metric-core section and
its two instance removals now begin before `ConnectedSpace`,
`RiemannianBundle`, `PseudoEMetricSpace`, `IsRiemannianManifold`, and
`IsContinuousRiemannianBundle` are bound.  No proof or public interface changed
in this structural repair, which has not yet been rechecked.

The fourth focused check confirmed that the earlier cascades were gone.  The
remaining error was a single implicit-point specialization of
`riemannianEDist_comm`; it now supplies `x` and `y` by name.  The real triangle
and ray-distance helpers also omit exactly the unused section variables listed
by that check.  Public definitions and theorem statements are unchanged, and
this local source repair has not yet been rechecked.

The fifth focused check elaborated every definition and proof successfully.
Only `unusedSectionVars` warnings remained.  The symmetry, antitonicity, lower
bound, and spatial-distance declarations now omit exactly the additional
section variables reported by that check.  The proof layer is green; a final
focused rerun is still needed to confirm warning-free status.

The sixth focused pass did not invalidate any proof: it found that three
`omit ... in` commands had been placed after their docstrings, so the parser
tried to attach the documentation to `omit` rather than to the declarations.
Those commands now precede the docstrings, and the new exact unused-variable
lists were applied to antitonicity, the lower bound, spatial distance, and the
bounded-below producer.  This grammar and linter repair has not yet been
rechecked.

The seventh focused pass kept every proof green and reduced the output to three
unused-section-variable warnings.  The bounded-below theorem now additionally
omits the unused pseudo-metric realization classes, while the infimum bound and
monotone-limit theorems omit the exact four geometric section variables listed
by that pass.  Warning-free status still awaits the next focused rerun.

The eighth focused pass again kept every proof green.  The last four reported
warnings were addressed exactly: the infimum-bound and limit theorems now omit
the unused pseudo-metric realization classes, and the one-sided Lipschitz and
ray-value theorems omit the four listed geometric section variables.  A final
rerun is still required before recording warning-free verification.

The ninth focused pass remained proof-green and reported only three final
unused-variable warnings.  The one-sided Lipschitz and ray-value theorems now
omit the unused pseudo-metric realization classes, and the two-sided distance
theorem omits the exact four geometric section variables reported by the pass.
Warning-free verification remains pending one coordinator-run check.

The tenth focused pass reduced the output to one final warning on the
two-sided distance theorem.  It now also omits the unused pseudo-metric
realization classes.  Proofs remain green; warning-free confirmation awaits the
next coordinator-run check.

No theorem-shaped placeholder or additional analytic frontier was introduced.
If elaboration exposes a mismatch, the expected frontier is local order,
coercion, or topology API adaptation rather than missing geometry.

## Project position

The final P1c Busemann/splitting theorem endpoints remain unstated and therefore
0% complete.  This pure metric Busemann core is approximately 40% of the
dedicated Busemann infrastructure; weak Laplacian passage, maximum-principle
input, line production, and splitting remain separate producers.  The
independent Cheeger--Gromoll soul endpoint remains 0% complete and does not use
this metric core directly.  P1c endpoints as a group remain 0% complete, and
the whole Poincare program remains roughly 15--25% complete.
