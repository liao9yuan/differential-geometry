# HessianAlongGeodesic

## 2026-07-14 checked result

`deriv2_comp_geo` identifies the second derivative of a smooth scalar along a
smooth geodesic with its Riemannian Hessian on the geodesic velocity.
`deriv2_comp_geo_on` is the local-germ form used by cut-locus-free squared
distance functions, and `strictConvex_geo` converts a positive Hessian on the
interior of a real convex domain into `StrictConvexOn`.

The proof uses the gradient first-derivative formula, metric compatibility,
the covariant chain rule, vanishing geodesic acceleration, and the existing
Hessian/gradient bridge. The local theorem uses `exists_smooth_germ`; no
global extension hypothesis is exposed to consumers. Focused verification
and exact target refresh passed without a local warning or `sorry`.

This comparison-layer API is complete for current B/C use. It is
infrastructure, not a compactness endpoint.

## 2026-07-27 local-geodesic refinement

The calculation is now factored at its actual hypothesis boundary:
`deriv2_comp_geo_at` consumes one `HasGeodesicEquationAt`, and
`deriv2_geo_on_at` combines that pointwise equation with a smooth scalar germ.
`strictConvex_geo_on` consequently needs the geodesic equation only on the
interior of the convex parameter set.  The old `deriv2_comp_geo`,
`deriv2_comp_geo_on`, and `strictConvex_geo` declarations remain compatibility
wrappers with unchanged statements.

The new declarations are focused- and exact-green with no diagnostics,
`sorry`, `admit`, or new assumption.
This closes the local-interval Hessian API needed by the canonical CGT
subtype-valued join; it does not itself prove the CGT Jensen or injectivity
theorem.
