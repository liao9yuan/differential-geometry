# RadialGram

## Raw radial pole density

`radialDensity_pole` gives the Euclidean pole normalization of the Gram density
of a finite family of raw radial Jacobi fields.  It is indexed by an arbitrary
finite type and assumes only that the initial vectors are orthonormal for the
Riemannian metric at the pole.

The proof writes the initial family in the fixed model basis, transports its
Gram matrix through the continuous normal-coordinate Gram matrix, and uses the
radial scaling identities to factor out `t ^ (2 * card ι)`.  Unlike the older
intrinsic specialization, it has no intrinsic/raw agreement layer, metric-norm
hypothesis, pseudometric instance, or completeness assumption on the manifold.
The existing Hausdorff instance on the tangent bundle is retained because the
normal-coordinate Gram continuity API consumes it directly; focused checking
confirmed that it is not an unused wrapper assumption.

`radialJacobi_li_of` is the raw-domain linear-independence adapter.  It scales
an initially independent family by a nonzero radial time, maps it through an
assumed-injective raw exponential differential, and identifies the resulting
vectors with the raw radial Jacobi fields using `radial_jacobi_dom`.  It does
not require the normal-chart source, the small `expMapC2Radius` bound,
completeness, or a new conjugacy predicate.

`radialRatio_pole` combines this raw normalization with `hypDensity_pole` to
give unit pole limit for the raw density divided by the hyperbolic model
density.  It is valid for every real model parameter: at positive time the
model denominator is nonzero whether the parameter is zero, positive, or
negative, so no sign hypothesis is needed.

Focused verification of the full file passed without warnings, including
`radialJacobi_li_of`, `radialDensity_pole`, and `radialRatio_pole`.  The earlier
stale-import failures for `radial_jacobi_dom` and `hypDensity_pole` no longer
occur.  No refresh or broader build was run during the parallel-task window.
Integration into the local Bishop volume endpoint is separate and remains
unstated (0%).
