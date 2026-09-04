import DifferentialGeometry.Geometry.Comparison.BusemannEikonal
import DifferentialGeometry.Geometry.Comparison.BusemannLineHarmonic
import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry

open Geometry.Connection
open Geometry.Curvature
open Geometry.Operator
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The gradient of the forward Busemann function of a minimizing line is
parallel when the Ricci curvature is nonnegative. -/
theorem busemann_grad_par
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    (LeviCivita (I := I) g).toFun
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) x = 0 := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hnorm :
      normGradSqFun (I := I) g b = fun _ : M ↦ (1 : ℝ) := by
    funext y
    simpa only [b, normGradSqFun_def, gradient_eq_gradFun] using
      (busemann_grad_sq (I := I) g hEnorm hγ.pos_ray y
        (hb.contMDiffAt.mdifferentiableAt (by simp)))
  have hlap :
      Δ_g (I := I) g ⟨b, hb⟩ = fun _ : M ↦ (0 : ℝ) := by
    funext y
    simpa only [b] using
      (busemann_lap_zero (I := I) g hEnorm hγ hd hRic y)
  have hone : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : M ↦ (1 : ℝ)) :=
    contMDiff_const
  have hlhs :
      Δ_g (I := I) g
          ⟨normGradSqFun (I := I) g b,
            normGradSqFun_contMDiff (I := I) g hb⟩ x = 0 := by
    calc
      Δ_g (I := I) g
            ⟨normGradSqFun (I := I) g b,
              normGradSqFun_contMDiff (I := I) g hb⟩ x =
          Δ_g (I := I) g ⟨fun _ : M ↦ (1 : ℝ), hone⟩ x :=
        Δ_g_congr_of_eventuallyEq (I := I) g
          (normGradSqFun_contMDiff (I := I) g hb) hone
          (Filter.Eventually.of_forall fun y ↦ congrFun hnorm y)
      _ = 0 := Δ_g_const (I := I) g 1 x
  have hgradlap :
      gradFun (I := I) g (Δ_g (I := I) g ⟨b, hb⟩) x = 0 := by
    rw [hlap]
    exact Geometry.Operator.gradFun_const (I := I) g 0 x
  have hric :
      0 ≤ ricciTensor (I := I) g x
        (gradFun (I := I) g b x) (gradFun (I := I) g b x) := by
    simpa only [zero_mul] using hRic x (gradFun (I := I) g b x)
  have hhess_nonneg :
      0 ≤ chartHessFrobeniusSq (I := I) g b x :=
    chartHessFrobeniusSq_nonneg (I := I) g hb x
  have hbochner :=
    bochner_pointwise_concrete_metric_unconditional (I := I) g hb x
  rw [hlhs, hgradlap] at hbochner
  have hinner_zero :
      g.inner x (gradFun (I := I) g b x) (0 : TangentSpace I x) = 0 :=
    map_zero (g.inner x (gradFun (I := I) g b x))
  rw [hinner_zero, mul_zero, add_zero] at hbochner
  have hhess : chartHessFrobeniusSq (I := I) g b x = 0 := by
    linarith
  have hfrob :
      frobeniusSq_grad_vector (I := I) g
          (fun y : M ↦ gradFun (I := I) g b y) x = 0 := by
    rw [frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hb x]
    exact hhess
  have hcov := cov_zero_of_frob (I := I) g
    (fun y : M ↦ gradFun (I := I) g b y) x hfrob
  simpa only [b] using hcov

end DifferentialGeometry
