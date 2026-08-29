# SegmentIntegral

## Mathematical route

The set-level area formula `riemVol_exp_image_eq` is promoted to a measure
identity: on any measurable set where the intrinsic exponential map is
injective, the Jacobian-weighted model Haar measure pushes forward to the
Riemannian volume measure restricted to the image.  Integrating against this
measure identity gives a weighted change-of-variables theorem, specialized to
the measurable and injective interior segment domain `SegInt`.
`segInt_polar` then composes this specialization with
`setLIntegral_polar`, yielding the nonnegative function-level
sphere-by-radius formula.  The signed layer consists of `expJac_integrable`,
`expJac_integral`, `segInt_integral`, and `segInt_int_polar`; it transports
Bochner integrability through the same measure identity and then applies the
signed polar/Fubini formula.  `segBall_int_polar` provides the same signed
formula after intersecting the source with a metric tangent ball, which is the
localization needed before using the full-measure regular segment-ball image.
Only almost-everywhere strong measurability on the exponential image is
required by the general integral identities.

This is the first reusable producer for the direct polar proof of the weak
distance-Laplacian comparison.  It is not the weak comparison theorem itself:
the remaining route must express the test-function pairing radially, use the
Ricci/Jacobian differential inequality on each minimizing ray, and justify the
nonnegative endpoint contribution at the cut radius.

## Verification

The original nonnegative declarations and the new signed declarations all pass
focused verification without warnings and the complete module passes its
explicit named refresh.
The initial failures were
local elaboration issues: the ENNReal scope selected the wrong infinity
notation, the density module was not imported explicitly, and the irreducible
`TangentSpace` model needed the `SegInt` specialization separated from the
weaker normed-space theorem section.  No mathematical assumptions were added
to the two general change-of-variables theorems.

The new segment-ball specialization is source-written and awaits focused
verification.

The interior signed section now uses the smooth manifold grade actually needed
by its proofs.  The earlier outer-top binder accidentally exported the stronger
analytic grade and blocked the smooth segment-ball and radial consumers.
Focused reverification passes without warnings, and the downstream-required
targeted named refresh also passes.

## Project status

All four formal P1c endpoints remain unstated and therefore 0% complete.  This
weighted area formula advances dedicated Laplacian-comparison machinery only;
it does not alter whole-project endpoint accounting.
