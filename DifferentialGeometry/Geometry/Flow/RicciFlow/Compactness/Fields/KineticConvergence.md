# KineticConvergence

## Role

`ConvOut.kinetic_convOn` is the compactness-field producer that converts
zeroth-order compact-uniform convergence of the extended pointed metrics into
uniform convergence of their quadratic kinetic terms along one fixed `C¹`
curve.

## Route

- The compact spatial set is the image of the compact parameter interval.
- The reference-metric kinetic energy of a `C¹` curve is continuous and hence
  uniformly bounded on that interval.
- `ConvOut.conv` is used only at derivative order zero.
- `metricQuadFormDiff_le_metricDerivNorm` and `derivNorm_le_sup` turn that
  zeroth-order metric estimate into the desired scalar quadratic-form estimate.

No curvature-jet bound, metric lower bound, or new convergence assumption is
introduced.  The separate varying-source-domain adapter to the actual mapped
curve remains in the pointed L-action layer.

`ConvOut.chartGram_convOn` extends the same order-zero argument to raw
fixed-chart Gram operators along uniformly convergent coordinate paths.  The
coordinate paths stay eventually in one compact chart set; its inverse-chart
image is the compact manifold set used by `ConvOut.conv`.  The proof splits the
operator error into the metric error at the moving point and the motion error
for the fixed limit family.  The first is controlled by the uniform
`chartGramOp_diff_le` constant and `derivNorm_le_sup`; the second is exactly
`chartGramOp_unif`.  The only extra input is smoothness of the limit metric
family on the ambient flow interval, needed by that fixed-family continuity
theorem; convergence is not restated.

`ConvOut.chartKin_liminf` combines that uniform operator convergence with weak
convergence of the time derivatives.  Continuity of each sequence coefficient
comes from `gSeqExt_gram_cont`, while continuity of the limit coefficient comes
from `chartGramOp_cont` and the stated smoothness of the limit family.  Compact
time intervals supply the individual operator bounds required by
`timeQuad_weak_unif`; no bound uniform in the sequence index is needed.  The
result is the lower-semicontinuity inequality for the raw fixed-chart kinetic
integrals along compact-confined varying paths.

## Verification

Focused verification is warning-free green, and the named module refresh is
current because `PointedConvergence.lean` consumes the exported declaration.
The local instance/expression repairs used the reference metric only to bound
the fixed curve's speed and normalized real distance with `abs_sub_comm`.

`ConvOut.kinetic_convOn` is therefore 100% complete for its stated fixed-curve
compact-uniform role.  Full minimizer/reduced-distance convergence and
no-mass-loss remain separate producers.

`ConvOut.chartGram_convOn` and `ConvOut.chartKin_liminf` are both warning-free
focused green.  The latter uses the existing joint continuity of `gSeqExt`
chart Gram entries to discharge strong measurability, and then applies
`timeQuad_weak_unif`.  This closes the fixed-chart, explicitly confined kinetic
lower-semicontinuity producer.  Converting it to the intrinsic pointed
L-kinetic term remains a separate consumer-layer adapter.
