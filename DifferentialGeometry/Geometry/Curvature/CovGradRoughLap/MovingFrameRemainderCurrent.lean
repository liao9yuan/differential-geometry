import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDiffCurvTraceSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The moving-frame remainder current of the curvature line's terminal quantitative leaf

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the navigation
hub of the **frame-summed remainder current** program that discharges the curvature line's terminal
quantitative leaf `genuineCurvFields_residue_eq_weitzenbockValue`
(`MovingFrameDiffCurvTraceSection`) — the rank-generic integrated tensor Bochner–Weitzenböck identity
for the order-`2` rough-Laplacian / covariant-gradient commutator defect
`Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`).

The genuinely-new structural content — the frame-summed pointwise integrand of the curvature
cross-pairing, the per-direction genuine/bracket split of the frame summand, and the pure-Riemann
genuine-sum identification — lives in the upstream-safe bridge `MovingFrameRemainderFrameSumBridge`
(it needs only the pure-Riemann genuine trace `GcurvSection`, frame-free and tensorial). The
differentiated-curvature genuine-sum identification with integrated bracket nullity, the assembled
genuine curvature-fields value `(★)`, and the leaf discharge live in the leaf file
`MovingFrameDiffCurvTraceSection` (they reference its concrete differentiated-curvature section
`genuineDiffCurvSection`). This file imports both, so the full discharge is visible to consumers of the
moving-frame remainder current.

## Map of the discharge

* `MovingFrameRemainderFrameSumBridge` — `remDiffFib` (the per-summand third-order difference field),
  `pointwiseTensorCurvPairing_eq_frameSum` / `tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_
  integral` (the integrand frame-sum), `remDiffGenuineFib` / `remDiffBracketFib` /
  `remDiffFib_eq_genuine_add_bracket` (the per-direction genuine/bracket split), and
  `remDiffFib_genuineFrameSum_pairing_eq_genuineFields` (the pure-Riemann genuine-sum identification).
* `MovingFrameDiffCurvTraceSection` — `integral_frameSum_remDiffBracket_pairing_eq_zero` (the
  differentiated-curvature genuine-sum identification with integrated bracket nullity),
  `genuineCurvFields_crossPairing_value` (the assembled value `(★)`), and the discharged leaf
  `genuineCurvFields_residue_eq_weitzenbockValue`.
-/
