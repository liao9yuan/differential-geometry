# Pointwise tensor-curvature first-order bound

## 2026-08-05: supplied-cap rank-two, order-zero endpoint

The native target is `ptCurv_zero_of`. It takes a squared tangent-curvature cap `C0²`, a
nonnegative pointwise `∇R` cap `C1`, and proves

```text
‖pointwiseTensorCurv g 2 S‖ ≤
  ptCurvZeroC (finrank ℝ E) C0 C1 * (‖S‖ + ‖covGrad g 0 2 S‖).
```

The coefficient is explicit and uses no compactness-chosen constant. The two squared arms are
assembled with coefficients

- `P = d * (16 * Kpure + 2 * Cc)`, where `Kpure = d² * 2² * C0²` and
  `Cc = d³ * C0²`;
- `Q = d * (4 * Cd)`, where `Cd = 2² * d² * C1²`.

Thus `ptCurvZeroC` is `max (sqrt P) (sqrt Q)`. The public lemma
`ptCurvZeroC_nonneg` exposes its nonnegativity without unfolding this formula. The endpoint does
not require `0 ≤ C0`, because `C0` occurs only through its square. It keeps `0 ≤ C1`, which is
needed when summing the supplied unsquared `∇R` norm cap.

The only additional public structural leaf is `genuineTrace_le_of` in
`MovingFrameGenuineFieldFiberEnergy.lean`. The tangent-to-tensor curvature estimate, the
frame-contracted `∇R` estimate, and the two arm estimates remain private implementation details in
this file.

The first focused check failed before reaching the endpoint. The exact local failures were redundant
goal closers, an unqualified `Tensor0SNabla` declaration, an attempted use of a private smooth-section
helper, an invalid generic inner-product nonnegativity call for `g.inner`, two unstable rewrites, and
heartbeat exhaustion in `frameNablaCap_of` and `frameCurvDir_le_of`. The static repair now uses the
public `smoothExtensionFiber` API, a local metric nonnegativity fact, explicit rewrite witnesses, and
two smaller algebraic helpers (`frameSum_sq_le` and `covDeriv_dir_le`) so the expensive declarations no
longer elaborate all norm and monotonicity machinery inline. No missing project API or mathematical
gap was exposed.

The second focused check also failed before the endpoint. It confirmed that the original namespace,
privacy, metric-nonnegativity, and `frameNablaCap_of` timeout failures were gone. The remaining exact
failures were an unavailable imported `baseSlotCurv_eq_riemannOp` bridge, a beta-redex
blocking the differentiated-curvature rewrite, an already-closed frame-sum goal, a mis-indented `calc`
step, and heartbeat exhaustion in `frameCurvDir_le_of`. The current static repair uses the already
imported lower public bridge `riemannSec_eq_riemannOp_smooth`, normalizes the beta-redex with `change`,
removes the redundant closers, and splits the remaining expensive declaration across the
curvature-free helpers `rfns_finSum_le` and `covDeriv_sum_le` plus the small moving-frame specialization
`frameCurvVec_le`.

The next focused check stopped before elaboration because the temporary high-level
`GradientSlotCurvatureSplit` import had no built object file. That import has been removed; using its
lower public producer directly avoids both a dependency refresh and a duplicate wrapper.

The final focused one-thread check passed after the timeout split and local linter cleanup. The five
remaining unused-section-variable warnings predate this supplied-cap endpoint and were left untouched.
Thus `ptCurv_zero_of` is confirmed complete (100%), and its dedicated native supplied-cap machinery is
also 100% implemented and focused-check verified. The targeted module refresh passed, so the exported
declarations are available to downstream imports. The downstream HCG package is tracked separately.
The `(N)` uniform-existence theorem itself remains 0% proved; this is one producer brick and does not
by itself change the whole-campaign percentage.

The downstream adapter should live in
`HCGCompactness/UnifCurvActionZero.lean`, import `UnifCurvatureJetOne` plus this native module, and
package the endpoint under a short HCG-facing name such as `unifPtCurvZero`.
