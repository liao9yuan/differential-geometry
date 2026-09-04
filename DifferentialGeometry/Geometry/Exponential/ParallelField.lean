import DifferentialGeometry.Geometry.Connection.ParallelTransport.PullbackNaturality
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Geodesic.ChartRegularity

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection
open Geodesic
open Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option backward.isDefEq.respectTransparency false in
/-- The complete geodesic launched in a smooth parallel vector field is an
integral curve of that field. -/
theorem intrinsic_intCurve
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (X : ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hX : ∀ y : M,
      (LeviCivita (I := I) g).toFun (fun z : M ↦ X z) y = 0)
    (x : M) :
    IsMIntegralCurve (I := I)
      (intrinsicGeodesic (I := I) g hEnorm x (X x))
      (fun y : M ↦ X y) := by
  classical
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x (X x)
  let V : ∀ t : ℝ, TangentSpace I (γ t) := fun t ↦ X (γ t)
  let W : ∀ t : ℝ, TangentSpace I (γ t) := fun t ↦
    (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ := by
    apply contMDiffOn_univ.mp
    refine isGeodesicOn_contMDiffOn_infty (I := I) g isOpen_univ ?_ ?_
    · simpa only [γ] using
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x (X x)).isGeodesicOn
          univ
    · simpa only [γ] using
        (intrinsicGeodesic_continuous (I := I) g hEnorm x (X x)).continuousOn
  have hγ_two : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ :=
    hγ_smooth.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hVdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
    have hbase : γ t ∈
        (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
    have hXcoord : MDifferentiableAt I 𝓘(ℝ, E)
        (Connection.chartE_section_repr (I := I) (γ t) (fun y : M ↦ X y))
        (γ t) :=
      (Connection.mdifferentiableAt_section_iff_chartE I (γ t)
        (fun y : M ↦ X y) hbase).mp X.mdifferentiableAt
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (Connection.chartE_section_repr (I := I) (γ t) (fun y : M ↦ X y) ∘ γ) t :=
      hXcoord.comp t (hγ_smooth.mdifferentiableAt (by simp))
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    simpa only [V, chartRepAt, Connection.chartE_section_repr,
      Function.comp_apply] using hcomp
  have hWdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t := by
    simpa only [W, chartRepAt] using
      MFDerivAlongCurve.velocity_coord_diff (I := I) γ t
        hγ_two.contMDiffAt
  have hVpar (t : ℝ) : covDerivAlong (I := I) g γ V t = 0 := by
    rw [covAlong_sec (I := I) g γ X t
      (hγ_smooth.mdifferentiableAt (by simp))]
    change (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) (γ t) _ = 0
    rw [hX (γ t)]
    rfl
  have hWpar (t : ℝ) : covDerivAlong (I := I) g γ W t = 0 := by
    simpa only [W, γ] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x (X x)) t
        hγ_two.contMDiffAt
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x (X x) t)
  have hinit : V 0 = W 0 := by
    have hγ0 : γ 0 = x := by
      simp only [γ, intrinsicGeodesic_zero]
    change X (γ 0) = (mfderiv 𝓘(ℝ, ℝ) I γ 0) 1
    rw [hγ0]
    simpa only [γ] using
      (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x (X x)).symm
  intro t
  have ht : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (-|t|) |t| :=
    ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hVW : V t = W t :=
    parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ_two V W
      (fun s _ ↦ hVdiff s) (fun s _ ↦ hWdiff s)
      (fun s _ ↦ hVpar s) (fun s _ ↦ hWpar s)
      (t₀ := 0) hzero hinit t ht
  have hvel :
      (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1 =
        X (γ t) := by
    simpa only [V, W] using hVW.symm
  have hmfderiv : mfderiv 𝓘(ℝ, ℝ) I γ t =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)) := by
    apply ContinuousLinearMap.ext
    intro (r : ℝ)
    calc
      (mfderiv 𝓘(ℝ, ℝ) I γ t) r =
          r • (mfderiv 𝓘(ℝ, ℝ) I γ t) 1 := by
        have hmap := ContinuousLinearMap.map_smul
          (mfderiv 𝓘(ℝ, ℝ) I γ t) r (1 : ℝ)
        have hr : r • (1 : ℝ) = r := by simp
        rw [hr] at hmap
        exact hmap
      _ = r • X (γ t) := by rw [hvel]
      _ = ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) r := by simp
  have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    (hγ_smooth.mdifferentiableAt (by simp)).hasMFDerivAt
  simpa only [γ] using hγ_at.congr_mfderiv hmfderiv

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
