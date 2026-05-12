import RicciFlower.Operators.HessianTrace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Laplacian at a Spatial Minimum

This file contains the single-metric geometric input used by the scalar weak
maximum principle: at a spatial local minimum, the Laplacian is nonnegative.

The first lemma below is connection-independent and fully algebraic: at a point
where a vector-field section vanishes, the divergence of that section does not
depend on the chosen connection.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

/-! ## First-order minimum facts -/

/-- First-order Fermat rule for a scalar function on a boundaryless realized
manifold.

The boundaryless assumption makes the model-with-corners range locally equal
to the whole model space, so `fderivWithin` becomes `fderiv`. -/
theorem mfderiv_eq_zero_at_spatial_min
    [I.Boundaryless]
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mfderiv I 𝓘(Real, Real) f x = 0 := by
  have hmin_chart :
      IsLocalMin (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) := by
    have hmin' :
        IsLocalMin f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmin
    simpa only [Function.comp_apply] using
      hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hderiv_chart :
      fderiv Real (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) = 0 :=
    hmin_chart.fderiv_eq_zero
  have hrange : Set.range I ∈ nhds ((extChartAt I x) x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    mfderiv I 𝓘(Real, Real) f x =
        fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) ((extChartAt I x) x) := by
      exact hf.mfderiv
    _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          ((extChartAt I x) x) := by
      exact fderivWithin_of_mem_nhds hrange
    _ = 0 := by
      simpa [writtenInExtChartAt] using hderiv_chart

/-- At a spatial local minimum, the realized gradient vanishes. -/
theorem gradientFun_eq_zero_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  exact gradientFun_eq_zero_of_mfderiv_eq_zero (I := I) g f
    (mfderiv_eq_zero_at_spatial_min (I := I) hmin hf)

/-! ## Laplacian minimum input -/

/-- The single-metric second-order local input needed for maximum principles. -/
def LaplacianNonnegativeAtSpatialMin
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall {f : M -> Real} {x : M},
    IsLocalMin f x ->
      MDifferentiableAt I 𝓘(Real, Real) f x ->
        MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x ->
          0 <= laplacian (I := I) cov g f x

/-- If a vector-field section vanishes at `x`, its divergence at `x` is
independent of the chosen connection. -/
theorem divergence_eq_of_section_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hzero : X x = 0) :
    divergence (I := I) cov X x = divergence (I := I) cov' X x := by
  have hd :
      (CovariantDerivative.difference cov cov' x) (X x) =
        cov X x - cov' X x := by
    exact IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv)
      (hcov' := cov'.isCovariantDerivativeOnUniv)
      (σ := X) (x := x) (hx := by trivial) hX
  have hcov_eq : cov X x = cov' X x := by
    have hsub : cov X x - cov' X x = 0 := by
      rw [← hd, hzero]
      simp
    exact sub_eq_zero.mp hsub
  simp [divergence, hcov_eq]

/-- At a critical point of `f`, the Laplacian is independent of the chosen
connection. -/
theorem laplacian_eq_laplacian_of_gradient_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hgradSec : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgrad : gradientFun (I := I) g f x = 0) :
    laplacian (I := I) cov g f x = laplacian (I := I) cov' g f x := by
  exact divergence_eq_of_section_eq_zero (I := I) cov cov' hgradSec hgrad

/-- At a spatial local minimum, the Laplacian is nonnegative.

The remaining proof is the normal-coordinate/Hessian trace calculation: in a
normal orthonormal frame at the minimum, `df_x = 0`, the connection-dependent
terms vanish, and the Laplacian is the trace of the positive-semidefinite
Hessian of the chart representative. -/
theorem laplacian_nonneg_at_spatial_min
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    0 <= laplacian (I := I) cov g f x := by
  -- The first-order part is already available and is the reason the final
  -- normal-coordinate proof is connection-independent at the minimum.
  have hcritical :
      gradientFun (I := I) g f x = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g hmin hf
  -- The operator identity `Delta f = tr_g (nabla df)` is isolated in
  -- `scalarLaplacianRealizesTraceAt_of_nablaDu`.  The remaining local work is
  -- to produce the Hessian realization in a normal inverse basis and prove that
  -- the metric trace of a positive-semidefinite Hessian is nonnegative.
  sorry

/-- The producer form of `LaplacianNonnegativeAtSpatialMin`. -/
theorem laplacianNonnegativeAtSpatialMin_of_connection
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) :
    LaplacianNonnegativeAtSpatialMin (I := I) cov g := by
  intro f x hmin hf hgrad
  exact laplacian_nonneg_at_spatial_min (I := I) cov g hmin hf hgrad

end

end Realized
end RicciFlower
