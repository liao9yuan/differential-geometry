# Parallel fields and intrinsic geodesics

## Canonical home

The endpoint is placed in the exponential layer because it is stated directly
for `intrinsicGeodesic`, whose construction, global existence, initial velocity,
and smoothness producers live under `Geometry/Exponential`.  Placing it under
the lower geodesic layer would reverse that dependency.

## Mathematical route

For the intrinsic geodesic launched from `x` with velocity `X x`, compare two
fields along the curve: the restriction `X ∘ γ` of the supplied smooth
ambient field and the geodesic velocity.  The theorem `covAlong_sec` identifies
the first covariant derivative with the Levi-Civita derivative of `X`, hence it
vanishes.  The geodesic equation makes the velocity field parallel.  Both
fields have differentiable chart representatives and agree at time zero, so
`parallel_transport_unique_of_eq_at_point` makes them equal on every compact
interval containing zero and the requested time.  Equality of the velocity at
`1 : ℝ` determines the full one-dimensional manifold derivative and yields
the integral-curve equation.

## Native API reused

- `covAlong_sec`
- `MFDerivAlongCurve.velocity_coord_diff`
- `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2`
- `parallel_transport_unique_of_eq_at_point`
- `intrinsicGeodesic_isGeodesic`
- `intrinsicGeodesic_continuous`
- `intrinsicGeodesic_zero`
- `intrinsicGeodesic_mfderiv_zero`

The public endpoint is `intrinsic_intCurve`.  It adds no unit-length condition
and no completeness assumption beyond the one already required to define the
global intrinsic geodesic.  It retains the positive-finrank instance already
required by the native intrinsic-geodesic API; the P1c Busemann consumer derives
that instance from its stronger dimension hypothesis.  The ambient parallelism hypothesis is the native
vanishing of the complete Levi-Civita covariant derivative, not a new wrapper
predicate.

## Verification and accounting

The first focused check stopped before the proof body because the source used a
wrong model-notation glyph, omitted the native positive-finrank instance, and
did not open the namespace containing `LeviCivita`.  These source-shape issues
were corrected without changing the theorem route.  A second parser pass found
one remaining occurrence of the same wrong model glyph in the finite-order
smoothness witness; it was corrected mechanically.  Its parallel-transport
uniqueness and intrinsic-geodesic inputs are existing project machinery.  The
next elaboration pass reached the proof body and exposed only local shapes: use
the already constructed `C²` witness directly, rewrite the dependent time-zero
fiber before applying the initial-velocity theorem, and type the real scalar in
the one-dimensional continuous-linear-map extensionality proof.  These were
repaired without changing the route.  The following pass left only the standard
`map_smul` normal form for a real one-dimensional derivative; it is now supplied
as an explicit `ContinuousLinearMap.map_smul` equality.  Because Mathlib keeps
`TangentSpace` intentionally opaque, the theorem uses the same local
definitional-equality transparency option as the native integral-curve calculus.
With that local setting, the focused check passed without warnings.  The
explicitly named module refresh also completed successfully, so
`intrinsic_intCurve` is a verified reusable producer.

This is reusable ODE machinery for the later P1c parallel-gradient flow.  It
does not itself prove that the Busemann gradient is parallel, construct the
flow diffeomorphisms, or establish the final product isometry.
