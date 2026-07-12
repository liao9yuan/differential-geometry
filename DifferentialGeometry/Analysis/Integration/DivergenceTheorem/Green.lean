import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Analysis.Integration.Measure.Properties


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
theorem green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hh with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hh hh_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hf X x]
    change g.inner x (X x) ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g (I := I) g X x = f x * Δ_g (I := I) g hh x := by
    intro x
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

set_option linter.unusedSectionVars false in
private theorem integral_inner_grad_eq_neg_integral_smul_laplacian'
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hf hf_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hh X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hh X x]
  have hRHS_eq : ∀ x : M,
      h x * divergence_g (I := I) g X x = h x * Δ_g (I := I) g hf x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

set_option linter.unusedSectionVars false in
theorem green_second_integral_smul_laplacian_sub_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∫ x, (f x * Δ_g (I := I) g hh x - h x * Δ_g (I := I) g hf x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  have h1 := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hh hh_cs
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian' (I := I) g hf hh hf_cs
  have h_eq : ∫ x, f x * Δ_g (I := I) g hh x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have : -∫ x, f x * Δ_g (I := I) g hh x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g (I := I) g hf x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔh_cont : Continuous (Δ_g (I := I) g hh) :=
    (Δ_g_contMDiff (I := I) g hh).continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) :=
    (Δ_g_contMDiff (I := I) g hf).continuous
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g (I := I) g hh x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g (I := I) g hh x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g (I := I) g hf x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g (I := I) g hf x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

end DivergenceTheorem
end Integral
end DifferentialGeometry
