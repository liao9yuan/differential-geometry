import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import RicciFlower.VectorBundle.LocalFrameRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Gradient regularity for realized scalar operators

This file proves the smooth-section regularity of the realized pointwise
gradient `gradientFun` from smoothness of the scalar function.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open Coordinates
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradientFun_coeff_eq_sum
    (g : SmoothRiemannianMetric I M) (f : M -> Real)
    {x₀ y : M} (hy : y ∈ coordinateFrameSet (I := I) x₀)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff k y
        (gradientFun (I := I) g f y) =
      ∑ l : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
            (extChartAt I x₀ y) *
          extDerivFun (I := I) f y (coordinateFrameAt (I := I) x₀ l y) := by
  classical
  let basis : Module.Basis (CoordinateIdx (𝕜 := Real) E) Real (TangentSpace I y) :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hy
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ a b
        (extChartAt I x₀ y)
  have hbasis :
      basis = coordinateFrameAt_basis (I := I) x₀ hy := by
    rfl
  have hinv : MetricInverseInBasis (I := I) g y basis gInv := by
    simpa [basis, hbasis, gInv] using
      gInvBasisAt (I := I) g x₀ (x := y) hy
  rw [(coordinateFrameAt_isLocalFrame (I := I) x₀).coeff_apply_of_mem
    hy (fun z : M => gradientFun (I := I) g f z) k]
  rw [coord_eq_invInner (I := I) g y basis gInv hinv k
    (gradientFun (I := I) g f y)]
  apply Finset.sum_congr rfl
  intro l _
  have hbasis_l : basis l = coordinateFrameAt (I := I) x₀ l y := by
    simpa [basis] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt_coe hy l
  calc
    gInv k l * g.inner y (basis l) (gradientFun (I := I) g f y)
        = gInv k l * g.inner y (gradientFun (I := I) g f y) (basis l) := by
          rw [g.symm y (basis l) (gradientFun (I := I) g f y)]
    _ = gInv k l * mfderiv I 𝓘(Real, Real) f y (basis l) := by
          rw [inner_gradientFun]
    _ = gInv k l * extDerivFun (I := I) f y (basis l) := by
          rw [RicciFlower.extDerivFun_real_eq_mfderiv (I := I) f y (basis l)]
    _ =
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
            (extChartAt I x₀ y) *
          extDerivFun (I := I) f y (coordinateFrameAt (I := I) x₀ l y) := by
          rw [hbasis_l]
          rfl

private theorem gradientFun_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (T% fun y : M => gradientFun (I := I) g f y) x₀ := by
  classical
  let frame := coordinateFrameAt_isLocalFrame (I := I) x₀
  refine frame.contMDiffAt_of_coeff_aux ?_ (coordinateFrameSet_open (I := I) x₀)
    (coordinateFrameAt_mem (I := I) x₀)
  intro k
  let rhs : M -> Real := fun y =>
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y) *
        extDerivFun (I := I) f y (coordinateFrameAt (I := I) x₀ l y)
  have hrhs : ContMDiffAt I 𝓘(Real, Real) ∞ rhs x₀ := by
    refine ContMDiffAt.sum fun l _ => ?_
    have hginv :
        ContMDiffAt I 𝓘(Real, Real) ∞
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) g x₀ k l
              (extChartAt I x₀ y)) x₀ :=
      gInvComp_contMDiffAt (I := I) g x₀ k l
    have hframe :
        ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
          (fun y : M =>
            (⟨y, coordinateFrameAt (I := I) x₀ l y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀)
        (coordinateFrameAt_mem (I := I) x₀) l
    have hderiv :
        ContMDiffAt I 𝓘(Real, Real) ∞
          (fun y : M =>
            extDerivFun (I := I) f y (coordinateFrameAt (I := I) x₀ l y)) x₀ :=
      extDerivFun_apply_contMDiffAt_of_section (I := I)
        (f := f) (X := coordinateFrameAt (I := I) x₀ l)
        hf.contMDiffAt hframe
    exact hginv.mul hderiv
  refine hrhs.congr_of_eventuallyEq ?_
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  exact gradientFun_coeff_eq_sum (I := I) g f hy k

/-- A smooth scalar has a smooth realized gradient as a tangent-bundle
section. -/
theorem gradientFun_smooth
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (T% fun y : M => gradientFun (I := I) g f y) := by
  intro x₀
  exact gradientFun_contMDiffAt (I := I) g hf x₀

/-- Pointwise differentiability of the realized gradient of a smooth scalar. -/
theorem gradientFun_mdiffAt
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x :=
  (gradientFun_smooth (I := I) g hf).contMDiffAt.mdifferentiableAt (by simp)

end Realized
end RicciFlower
