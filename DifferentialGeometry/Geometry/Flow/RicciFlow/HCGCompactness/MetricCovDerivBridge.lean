import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields

/-!
# The metric-jet ↔ iterated-covariant-gradient norm bridge (`normBridge`)

Item-6 brick 2a, discharger D2.  This file is the ratified home (planner,
2026-07-24) of the reusable norm bridge that lets `UnifCurvatureJetBound.lean`'s
order-`≤2` jet envelope consume `MetricCovDerivOrderBoundOn` (which is phrased in
`normSq0S`/`metricCovDeriv` currency):

`‖(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x‖`
  `= √(normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))`.

## Status — GATED on a missing upstream framework agreement (see `MetricCovDerivBridge.md`)

`normBridge`'s two sides live in two different covariant-derivative formalisms:

* the envelope side (`iteratedCovGrad`/`covGrad`) is the **abstract** bundled
  `tensor0SCovariantDerivative` / `tensorRSCovariantDerivative`;
* the `metricCovDeriv` side is the **chart / model** `nabla0SFun` / `totalNabla0S`
  (`metricCovDeriv` and all its eval lemmas are `nabla0SFun`-based).

The crossing `nabla0SFun ↔ tensor0SCovariantDerivative` for `(0, s)` tensors is a
repeatedly-flagged MISSING agreement (`Evolution/NablaRiemannT1Bound.lean:75`,
`Evolution/IteratedNablaRmTower.md:729,748,777,868`; the proven chart↔abstract
agreement in `Connection/ChartTensorNabla/Agreement/` is for the *different*
`chartTensor0SCovariantDerivative`, with no stated `nabla0SFun` link).  Closing
`normBridge`'s inductive step therefore requires that upstream agreement first:

`nabla0SFun_eq_tensor0SCovariantDerivative (r = 0, all s), directional` — proposed
home `Connection/ChartTensorNabla/Agreement/`.  The remaining `normBridge` assembly
(base case, `(b)` norm reconciliation via `norm_toSection_eq_sqrt_riemannianFiberNormSq`
+ `tensorInnerPointwise_0s` + `normSq0S_eq_inner`, and the `2+j = j+2` cast) is fully
mapped in `MetricCovDerivBridge.md`.

The `normBridge` statement below is pinned and typechecked; its proof carries a
single `sorry` at exactly the missing agreement.  It is intentionally NOT
axiom-clean this session — it is the honest, precisely-stated frontier.
-/

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in
/-- **The metric-jet ↔ iterated-covariant-gradient norm bridge.**

For a background metric `gBase`, a metric `h`, an order `j`, and a base point `x`,
the `gBase`-Riemannian fibre norm of the `j`-th iterated covariant gradient of the
realized `(0,2)` metric tensor `metricCcTensor gBase h` equals the square root of the
`normSq0S`-norm of the `j`-th background covariant derivative `metricCovDeriv h gBase j`.

This is the reusable bridge that converts the `iteratedCovGrad` (abstract-connection)
jet-envelope currency into the `metricCovDeriv`/`normSq0S` (chart-connection) currency
of `MetricCovDerivOrderBoundOn`.

GATED: the inductive step requires the missing upstream agreement
`nabla0SFun ↔ tensor0SCovariantDerivative` (`(0, s)`); see the module docstring and
`MetricCovDerivBridge.md`.  Proof carries one `sorry` at that frontier. -/
theorem normBridge (h gBase : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + j)
    ‖((iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h)).toSection x :
        TensorRSSpace 0 (2 + j) I x)‖ =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (j + 2)
        (metricCovDeriv (I := I) h gBase j x)) := by
  sorry

end RicciFlow
end PDE
end DifferentialGeometry
