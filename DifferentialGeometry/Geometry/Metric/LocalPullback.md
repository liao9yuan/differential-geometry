# Local pullback metrics

## Mathematical route

The canonical immersion construction pulls the ambient smooth Riemannian inner
product through `mfderiv`.  Pointwise injectivity of `mfderiv` turns ambient
positive definiteness into positive definiteness on the source tangent space.
Finite dimensionality then supplies the bounded-unit-ball field through the
existing `Geometry.posDef_isVonNBounded` theorem.  Smoothness reuses the
existing tangent-map section argument already used by the local-diffeomorphism
case.

## API changes

- `immersionPullMetric` constructs the smooth pullback metric from a smooth map
  whose manifold derivative is injective at every point.  Its
  `SigmaCompactSpace` and `T2Space` source assumptions are the weakest signature
  currently supported by the global smooth-section extension API used in the
  proof.  For the intended regular closed zero-level source, these instances
  are inherited locally from the ambient manifold and do not strengthen the
  splitting endpoint assumptions.
- `immersionPull_inner` is the evaluation theorem for that metric.
- `localPull_smooth` exposes smoothness of the underlying pulled-back bilinear
  section so other canonical metric constructors can reuse it directly.
- `localPullMetric` keeps its existing declaration and assumptions, and is now
  the local-diffeomorphism specialization of `immersionPullMetric`.

No boundary-specific induced-metric hierarchy is duplicated, and no new
structure or assumption is introduced.

## Verification

The first focused check failed because the initially proposed signature did not
expose the global extension instances required by
`cotangentCov_clmSection_smooth_aux`.  After those assumptions were restored, a
second check isolated boundedness to typeclass transparency for the tangent
fiber.  The boundedness theorem now receives the definitionally equal model
space `E` explicitly, matching the established metric-construction pattern.
A subsequent focused elaboration passed and exposed only an unused source
manifold instance in the private boundedness helper.  That instance was omitted
while retaining the explicit model-space parameter.  Final focused verification
then passed without warnings.  Once the downstream product-metric producer
began consuming the new declarations, the explicit named refresh also passed.
The later `localPull_smooth` extraction initially retained an unused ambient
finite-dimensional instance; that dependency was explicitly omitted.  The
focused check and the downstream-required named refresh then both passed
without warnings.
