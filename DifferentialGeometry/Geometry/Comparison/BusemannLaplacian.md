# BusemannLaplacian

## Role

This file supplies the P1c distributional Laplacian comparison for the
Busemann function of a minimizing ray under nonnegative Ricci curvature.

## Route

- Apply `dist_lap_distrib` at the escaping integer poles `γ n`.
- Remove the constant part of `busemannApprox` using the compact-support
  divergence integral.
- Pass the left side to the Busemann limit by dominated convergence, dominated
  by the distance from `γ 0` times the norm of the test-function Laplacian.
- Bound the distance from `γ 0` on the compact test support. The public
  `buseApprox_lower` estimate then makes the integer poles eventually avoid that
  support and gives a uniform positive denominator there.
- Pass the comparison side to zero by squeezing its nonnegative integral below
  the scalar multiple `d / (n - R) * ∫ φ`, which tends to zero.

The public endpoint is `busemann_lap`. Its hypotheses are exactly a minimizing
ray, positive `finrank ℝ E - 1`, nonnegative Ricci curvature, completeness, and
the ambient Riemannian metric compatibility already required by
`dist_lap_distrib`; no new analytic assumptions are exposed.

## Lessons

The first monolithic proof hit the default heartbeat limit. Splitting the two
limit arguments and the shifted distance comparison into private mathematical
helpers removed that elaboration bottleneck. No heartbeat override is retained.
The right-side squeeze is shorter and more stable than global dominated
convergence because it never needs to discuss measurability of reciprocal
distance at the moving pole.

## Verification

Focused verification passed without warnings.

## Project status

`busemann_lap`: 100% (stated, proved, and focused-verified). Its dedicated
integer-pole limit machinery: 100%. The larger Busemann comparison phase is
approximately 25%, since barrier/maximum-principle consumers remain separate;
the whole Poincare formalization program is approximately 8% complete. These
larger percentages deliberately exclude infrastructure from any theorem that
has not itself been stated and proved.
