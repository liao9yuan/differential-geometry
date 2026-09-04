import DifferentialGeometry.Geometry.Comparison.HopfRinow
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond

open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A tangent vector shorter than a compact metric radius generates a geodesic
through time one without requiring completeness of the ambient manifold. -/
theorem exists_geo_one_cpt
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) {r : ℝ}
    (hv : Real.sqrt (g.inner x v v) < r)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal r))) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ IsPreconnected J ∧
      (0 : ℝ) ∈ J ∧ (1 : ℝ) ∈ J ∧
      IsGeodesicOn (I := I) g γ J ∧ ContinuousOn γ J ∧
      γ 0 = x ∧ (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) := by
  set c : ℝ := Real.sqrt (g.inner x v v) with hc_def
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hinner_nonneg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv_zero
    · simp
    · exact (g.pos x v hv_zero).le
  have hrc : 0 < r - c := sub_pos.mpr hv
  have hden : 0 < c + 1 := by linarith
  set B : ℝ := 1 + (r - c) / (c + 1) with hB_def
  have hB_one : 1 < B := by
    rw [hB_def]
    exact lt_add_of_pos_right _ (div_pos hrc hden)
  have hc_frac_lt : c * ((r - c) / (c + 1)) < r - c := by
    rw [show c * ((r - c) / (c + 1)) = c * (r - c) / (c + 1) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hcB_lt : c * B < r := by
    rw [hB_def]
    calc
      c * (1 + (r - c) / (c + 1)) = c + c * ((r - c) / (c + 1)) := by ring
      _ < c + (r - c) := by linarith
      _ = r := by ring
  obtain ⟨η, δ, hδ, hη_zero, _hη_cont_zero, hη_deriv, hη_mdiff,
      _hη_src, hη_geo⟩ := exists_isGeodesicOn_Ioo_at_velocity (I := I) g x v
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) := fun t ht ↦
    (hη_mdiff t ht).continuousAt.continuousWithinAt
  have hη_deriv_tangent :
      mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) = v := by
    change (mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) : E) = (v : E)
    exact hη_deriv
  have hη_speed :
      (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
          (mfderiv 𝓘(ℝ, ℝ) I η 0 1) ≤ c ^ 2 := by
    have hc_sq : c ^ 2 = (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
      rw [hc_def, Real.sq_sqrt hinner_nonneg]
      subst x
      exact (congrArg (fun w : TangentSpace I (η 0) ↦ g.inner (η 0) w w)
        hη_deriv_tangent).symm
    exact hc_sq.symm.le
  have hendpoint : ∀ (γ : ℝ → M) (b : ℝ), 0 < b → b < B →
      IsGeodesicOn (I := I) g γ (Set.Ioo (-δ) b) →
      ContinuousOn γ (Set.Ioo (-δ) b) →
      (∀ t < δ, t < b → γ t = η t) →
      HasEndpointContinuation (I := I) g γ b := by
    intro γ b hb hbB hγ hγ_cont hagree
    have hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo (-δ) b) :=
      isGeodesicOn_contMDiffOn_one (I := I) g isOpen_Ioo hγ hγ_cont
    have hγ_eq_η : γ =ᶠ[𝓝 0] η := by
      filter_upwards [Iio_mem_nhds hδ, Iio_mem_nhds hb] with t htδ htb
      exact hagree t htδ htb
    have hγ_zero : γ 0 = x := hγ_eq_η.eq_of_nhds.trans hη_zero
    have hγ_zero_seed : γ 0 = η 0 := hγ_eq_η.eq_of_nhds
    have hγ_deriv_seed : mfderiv 𝓘(ℝ, ℝ) I γ 0 = mfderiv 𝓘(ℝ, ℝ) I η 0 :=
      hγ_eq_η.mfderiv_eq
    have hSpeedSq : ∀ s ∈ Set.Ioo (-δ) b,
        (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
            (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2 := by
      intro s hs
      have hIcc : Set.Icc (min 0 s) (max 0 s) ⊆ Set.Ioo (-δ) b := by
        intro t ht
        exact ⟨lt_of_lt_of_le (lt_min (by linarith) hs.1) ht.1,
          lt_of_le_of_lt ht.2 (max_lt hb hs.2)⟩
      have hconst := isGeodesicOn_speedSq_const (I := I) g isOpen_Ioo hγ hγ_smooth hIcc
      rw [← hconst, hγ_zero_seed, hγ_deriv_seed]
      exact hη_speed
    have hSpeedBound : ∀ s ∈ Set.Ioo (-δ) b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c := by
      intro s hs
      rw [hEnorm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc
        Real.sqrt ((g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
            (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) ≤ Real.sqrt (c ^ 2) :=
          Real.sqrt_le_sqrt (hSpeedSq s hs)
        _ = c := by rw [Real.sqrt_sq hc_nonneg]
    have hγ_cpt : ∀ᶠ t in 𝓝[<] b,
        γ t ∈ Metric.closedEBall x (ENNReal.ofReal r) := by
      filter_upwards [Ioo_mem_nhdsLT hb] with t ht
      rw [Metric.mem_closedEBall']
      have hIcc : Set.Icc 0 t ⊆ Set.Ioo (-δ) b := by
        intro s hs
        exact ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 ht.2⟩
      have hdist := curve_edist_le_speed_mul_time (I := I) hc_nonneg ht.1.le
        (hγ_smooth.mono hIcc) (fun s hs ↦ hSpeedBound s (hIcc hs))
      have hed : edist x (γ t) ≤ ENNReal.ofReal (c * t) := by
        rw [IsRiemannianManifold.out (I := I) x (γ t), ← hγ_zero]
        simpa only [hγ_zero, sub_zero] using hdist
      exact hed.trans (ENNReal.ofReal_le_ofReal (by
        exact (lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (le_trans ht.2.le hbB.le) hc_nonneg) hcB_lt).le))
    exact endpointCont_compact (I := I) g (by linarith) hc_nonneg hγ_smooth
      hSpeedBound hSpeedSq hγ hcpt hγ_cpt
  obtain ⟨γ, hγ_geo, hγ_cont, hagree⟩ := geo_Ioo_extend_to (I := I) g
    (a₀ := -δ) (b₀ := δ) (B := B) (by linarith) hδ hη_geo hη_cont hendpoint
  have hB_pos : 0 < B := lt_trans zero_lt_one hB_one
  have hγ_eq_η : γ =ᶠ[𝓝 0] η := by
    filter_upwards [Iio_mem_nhds hδ, Iio_mem_nhds hB_pos] with t htδ htB
    exact hagree t htδ htB
  refine ⟨γ, Set.Ioo (-δ) B, isOpen_Ioo, isPreconnected_Ioo,
    ⟨by linarith, hB_pos⟩, ⟨by linarith, hB_one⟩, hγ_geo, hγ_cont, ?_, ?_⟩
  · exact (hagree 0 hδ hB_pos).trans hη_zero
  · rw [hγ_eq_η.mfderiv_eq]
    exact hη_deriv

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
