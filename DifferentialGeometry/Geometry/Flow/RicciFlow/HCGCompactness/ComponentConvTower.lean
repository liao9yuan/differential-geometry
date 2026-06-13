import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceDeriv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Covariant-tower component convergence (P3 Gap B, `componentConv_covDeriv_of_chartCInf`)

The `a ≥ 1` covariant tower of the metric component convergence.  The induction
runs on the bump-extended chart representative of the level-`p` tower scalar
`s_p^V(w) = (∇^p_gRef A0) w (V·w)` (`A0 = metricTensorField g`), using the existing
A2 machinery:

* `MetricPreconv.fderiv_chartRep_eq_towerStep` — the chart `fderiv` of `s_p^V`
  along a chart-constant direction `v` is the chart rep of `towerStep` (the
  level-`(p+1)` scalar plus the `gRef`-Christoffel corrections), as a germ.
* `MapCInfConvOnCompacts.fderivApply` (B2) — directional-derivative closure.
* `MapCInfConvOnCompacts.mulLeft`/`.sum`/`.add` (producer 3) — convergence algebra.
* `MapCInfConvOnCompacts.congr` — locality, to transfer convergence across the
  germ identity / where the global sections equal the chart-constant frame.

This file currently provides the foundational `ContDiff` and the directional-step
plumbing; the full induction is assembled on top.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The chart representative of a level-`p` tower scalar `s_p^V` is `ContDiffOn`
the extended-chart target. -/
theorem chartRep_towerScalar_contDiffOn
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)))
      (extChartAt I x₀).target := by
  intro z hz
  have hy : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hz
  have hzeq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hcd := contDiffAt_chartRep (I := I)
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w))
    (covDerivOfField_eval_contMDiff (I := I) gRef A0 p V) x₀ hy
  rw [hzeq] at hcd
  exact hcd.contDiffWithinAt

/-- **Bump-extended level-`p` tower scalar is globally `ContDiff`.**  Multiplying
the chart representative of `s_p^V` by a smooth bump supported in the chart target
gives a globally smooth function on the model space — the form `MapCInfConvOnCompacts`
and its derivative/algebra closures (`fderivApply`, `mulLeft`, `sum`) consume. -/
theorem bumpTowerScalar_contDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) z) :=
  bumpMul_contDiff (isOpen_extChartAt_target (I := I) x₀) hχ htsupp
    (chartRep_towerScalar_contDiffOn (I := I) gRef A0 p V x₀)

end HCGCompactness
end DifferentialGeometry
