# Raw even-cover fiber comparison

## Purpose

`rawFiber` is the fiber of the raw framed exponential inside a centered model
ball.  `rawFiber_encard_le` compares the pole fiber with a nearby fiber after
enlarging the radius by the length allowance used to reach the nearby point.
It is the first bounded raw multiplicity producer needed by the CGT collision
route.

## Route

A short flat path joins the pole to the target point.  Each element of the pole
fiber supplies a raw radial loop; append the common short path and lift it with
`exists_raw_lift`.  `rawLift_norm_le` places the endpoint in the enlarged ball.
If two lifted endpoints agree, map-generic `IsLiftOn` uniqueness first cancels
the common appended path and then identifies the two canonical radial lifts,
so the original pole-fiber elements agree.

The only append/midpoint/cancellation helper is private and formulated directly
for `IsLiftOn`.  No `RawFrameLift`, intrinsic exponential API, completeness,
connectedness, sigma-compactness, or positive-dimension assumption is used.

## Verification

Source-written without `sorry`.  The first focused pass exposed a native norm-
instance boundary: `rawFlatPath_len` and the Riemannian distance API selected
the `RiemannianBundle` tangent norm, while `rawLift_norm_le` and
`exists_raw_lift` had baked in the canonical `Tensor0SBundle` tangent norm.
Removing the local instance selection instead broke the matching continuous
Riemannian inner-product structure, so this was a lower-layer API issue rather
than a local coercion repair.

`TangentNormDiamond.tensor0SBundle_enorm_eq_riemannianBundle_enorm` proves the
metric norm formula after installing a metric-derived local Riemannian bundle,
but it does not identify the two already-elaborated `pathELength` expressions.
Neither an `@id` transport nor a theorem-local instance scope can change the
norm instance baked into an imported declaration.  The issue was closed at its
canonical layers by making the existing `lift_norm_le`, `rawLift_norm_le`, and
`exists_raw_lift` declarations explicitly polymorphic in their already-used
target tangent norm families.  After their exact refreshes, this file passed
focused verification warning-free.

## Accounting

`rawFiber_encard_le` is formally stated, proved, and focused GREEN (100% for
this local theorem).  Its append/cancellation and fiber-embedding machinery is
also complete.  This local producer does not itself state either P1b endpoint,
so the endpoint and whole-Poincare percentages remain unchanged.
