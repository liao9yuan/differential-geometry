# CotangentRiemannian

## 2026-07-08 flat-sharp bridge

Added the generic bridge `cotangentSharp_dualToCotangent_tangentFlat_gen`:
raising the one-form obtained by metric-lowering a tangent vector recovers the
original tangent vector.  Also added
`cotangentInner_dualToCotangent_tangentFlat_gen`, which rewrites the cotangent
metric of two lowered tangent vectors back to the original tangent metric.

This supports the volume-comparison curvature-term route: the next usable
bridge should lower the vector term `R(J, V) V` to a `(0,1)` tensor before
using intrinsic fibre-norm APIs, rather than trying to state an unavailable
model/operator-norm bound for nested tangent-space continuous linear maps.

Verification passed for the focused `CotangentRiemannian` check and the
targeted `Tensor.RSTensor.CotangentRiemannian` build.
