import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.DuhamelMap

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHeatEquation

def tensorHeatMildSolutionHs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHs (I := I) (M := M) g r s σ :=
  duhamel (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ F t

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T₀ +
        ∫ τ in (0 : ℝ)..t,
          tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ) (F τ) :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHs_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F 0 = T₀ :=
  duhamel_zero
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ F

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ} (hF : Continuous F)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ) (F τ))
      MeasureTheory.volume 0 t :=
  duhamel_integrable
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) hF ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ} (hF : Continuous F) :
    ContinuousOn
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ici 0) :=
  duhamel_continuousOn
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ hF

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_zero_forcing
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ t : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ (fun _ => 0) t =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T₀ := by
  rw [tensorHeatMildSolutionHs_apply]
  have hzero : (fun τ : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ)
        ((fun _ => 0) τ)) =
      (fun _ => (0 : tensorHs (I := I) (M := M) g r s σ)) := by
    funext τ
    exact (tensorHeatSemigroupHsExt (I := I) (M := M)
      g r s σ (t - τ)).map_zero
  rw [hzero, intervalIntegral.integral_zero, add_zero]

end TensorHeatEquation

end Parabolic
end Analysis
end DifferentialGeometry

end
