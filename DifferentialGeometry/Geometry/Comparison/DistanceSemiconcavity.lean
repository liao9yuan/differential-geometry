import DifferentialGeometry.Analysis.Calculus.UpperSupport
import DifferentialGeometry.Geometry.Comparison.DistanceCalabi

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem dist_geo_semiconcave
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {O : M} {γ : ℝ → M} {D : Set ℝ} {δ S : ℝ}
    (hD : Convex ℝ D)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : ∀ t ∈ interior D,
      Geodesic.HasGeodesicEquationAt (I := I) g γ t)
    (hfin : ∀ t ∈ D,
      riemannianEDist I O (γ t) ≠ (⊤ : ENNReal))
    (hδ : 0 < δ)
    (hsep : ∀ t ∈ interior D,
      δ ≤ (riemannianEDist I O (γ t)).toReal)
    (hS : ∀ t ∈ interior D,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) ≤ S)
    (hsec : NonnegSecMetric (I := I) (M := M) g) :
    ConcaveOn ℝ D (fun t =>
      (riemannianEDist I O (γ t)).toReal - (S / δ) * t ^ 2) := by
  let f : ℝ → ℝ := fun t => (riemannianEDist I O (γ t)).toReal
  have hdist : Continuous (fun x : M => riemannianEDist I O x) := by
    simpa only [riemannianEDist_comm] using
      (continuous_riemannianEDist_to (I := I) O)
  have hdistγ : Continuous (fun t : ℝ => riemannianEDist I O (γ t)) :=
    hdist.comp hγ.continuous
  have hf : ContinuousOn f D := by
    refine ENNReal.continuousOn_toReal.comp' hdistγ.continuousOn ?_
    intro t ht
    exact hfin t ht
  have hconc := Analysis.concaveOn_sub_sq hD hf (C := 2 * S / δ) (by
    intro t ht
    have htD : t ∈ D := interior_subset ht
    have hr : 0 < (riemannianEDist I O (γ t)).toReal :=
      hδ.trans_le (hsep t ht)
    have hO : O ≠ γ t := by
      intro hEq
      rw [← hEq, riemannianEDist_self] at hr
      simp at hr
    obtain ⟨φ, hφdiff, hφeq, hφupper, hφ2⟩ :=
      calabi_geo_upper (I := I) g hEnorm hO (hfin t htD) hγ
        (hgeo t ht) hsec
    have h2top : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
      (inferInstance : ENat.LEInfty (2 : WithTop ℕ∞)).out
    refine ⟨φ, hφdiff.of_le h2top, hφeq, hφupper, ?_⟩
    let v : TangentSpace I (γ t) :=
      (mfderiv 𝓘(ℝ, ℝ) I γ t :
        ℝ →L[ℝ] TangentSpace I (γ t)) 1
    have hv : 0 ≤ g.inner (γ t) v v :=
      gInner_self_nonneg (I := I) g (γ t) v
    have hS0 : 0 ≤ S := hv.trans (hS t ht)
    have hfrac :
        2 * g.inner (γ t) v v /
            (riemannianEDist I O (γ t)).toReal ≤
          2 * S / δ := by
      exact div_le_div₀ (mul_nonneg (by norm_num) hS0)
        (mul_le_mul_of_nonneg_left (hS t ht) (by norm_num)) hδ (hsep t ht)
    exact hφ2.trans hfrac)
  have hcoeff : (2 * S / δ) / 2 = S / δ := by ring
  simpa only [f, hcoeff] using hconc

end DifferentialGeometry
