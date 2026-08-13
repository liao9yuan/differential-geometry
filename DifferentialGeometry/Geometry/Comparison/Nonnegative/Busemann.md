# Busemann

## Scope

This module is the metric first layer of the Morgan--Tian nonnegative-curvature
package.  It intentionally contains no curvature, weak Laplacian, elliptic
regularity, or splitting hypothesis.

The implemented normal form is:

- `IsMinRay`: exact intrinsic distance along nonnegative ray parameters;
- `IsMinLine`, together with its positive and reversed-negative rays;
- `buseApprox`: the distance-minus-time approximants;
- `busemann`: their infimum over nonnegative time;
- monotonicity, a uniform origin-distance lower bound, the intrinsic
  one-Lipschitz estimate, continuity, and the exact value along the ray;
- nonnegativity of the sum of the two Busemann functions of a minimizing line,
  and vanishing of that sum at every point of the line.

The project has no separate real-valued Riemannian distance definition.  This
module follows the established convention and writes
`(riemannianEDist I x y).toReal`, with finiteness supplied by connectedness and
`riemannianEDist_ne_top`.

## Route ruling

Morgan--Tian defines the same approximants as a pointwise monotone limit.  The
Lean definition uses the infimum of the approximant range.  This avoids a
noncanonical selected limit while remaining definitionally close to the
monotone-limit proof.

Do not try to prove the splitting theorem immediately from smoothness and
unit gradient of a Busemann function.  The missing invariant step is the
Bochner argument giving `Hess b = 0`, followed by completeness of the gradient
flow and the isometric product construction.

## Next frontier

The next producer should connect an intrinsic minimizing geodesic ray to
`IsMinRay`.  After that, the first genuine analytic frontier is the weak
barrier/distributional inequality `Delta b <= 0` under nonnegative Ricci
curvature.  It requires a local weak-Laplacian interface for Lipschitz
functions; this must not be hidden as a consumer assumption in the splitting
theorem.

The metric half of the line argument is now ready: `buse_sum_nonneg` is the
global inequality and `buse_sum_line` is its equality on the line.  The later
strong maximum-principle step must consume an honestly produced weak
Laplacian statement for each summand.

## Verification

Focused verification passed with no warnings or placeholders.
