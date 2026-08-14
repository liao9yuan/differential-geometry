# Busemann

## Scope

This module is the metric first layer of the Morgan--Tian nonnegative-curvature
package.  It intentionally contains no curvature, weak Laplacian, elliptic
regularity, or splitting hypothesis.

The implemented normal form is:

- `IsMinRay`: exact intrinsic distance along nonnegative ray parameters;
- `IsMinLine`, together with its positive and reversed-negative rays;
- `IsMinRayOf g` and `busemannOf g`, thin metric-explicit forms that install
  the bundle metric induced by `g`;
- `buseApprox`: the distance-minus-time approximants;
- `busemann`: their infimum over nonnegative time;
- monotonicity, convergence of the approximants to that infimum, a uniform
  origin-distance lower bound, the intrinsic
  one-Lipschitz estimate, continuity, and the exact value along the ray;
- nonnegativity of the sum of the two Busemann functions of a minimizing line,
  and vanishing of that sum at every point of the line.

The project has no separate real-valued Riemannian distance definition.  This
module follows the established convention and writes
`(riemannianEDist I x y).toReal`, with finiteness supplied by connectedness and
`riemannianEDist_ne_top`.

## Route ruling

Morgan--Tian defines the same approximants as a pointwise monotone limit.  The
Lean definition uses the infimum of the approximant range.  The theorem
`buseApprox_tendsto` now proves that the original approximants converge to
this infimum at positive infinity, so later finite-distance comparison
inequalities can pass to the Busemann limit without changing definitions.

Do not try to prove the splitting theorem immediately from smoothness and
unit gradient of a Busemann function.  The missing invariant step is the
Bochner argument giving `Hess b = 0`, followed by completeness of the gradient
flow and the isometric product construction.

## Next frontier

`Ray.lean` now connects intrinsic minimizing geodesics to `IsMinRay`, including
the stronger closed totally-convex-set escape producer needed by the Soul
compactness argument.  For splitting, the first genuine analytic frontier is the weak
barrier/distributional inequality `Delta b <= 0` under nonnegative Ricci
curvature.  It requires a local weak-Laplacian interface for Lipschitz
functions; this must not be hidden as a consumer assumption in the splitting
theorem.

The metric half of the line argument is now ready: `buse_sum_nonneg` is the
global inequality and `buse_sum_line` is its equality on the line.  The later
strong maximum-principle step must consume an honestly produced weak
Laplacian statement for each summand.

For the Soul lane, the next genuine curvature theorem is geodesic concavity of
`busemann` under `NonnegSecMetric`.  The checked endpoint Jacobi comparison is
available, but selected-branch Hessian comparison, Calabi support at the cut
locus, and the one-dimensional barrier passage are still missing.  Applying
the endpoint comparison to the existing time-one intrinsic branch first needs
its routine unit-speed reparameterization and minimizing-tail bridge.

## Verification

Focused verification passed with no warnings or placeholders, and the
full-project build passed.  The new public endpoints use only the standard
foundational axioms reported by Lean.
