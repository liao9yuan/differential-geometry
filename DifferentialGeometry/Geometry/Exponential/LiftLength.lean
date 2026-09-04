import DifferentialGeometry.Geometry.Exponential.RadialSeminormFencing
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function MeasureTheory
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N]

private theorem radialDist_deriv
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hBsym : ∀ u v : V, B u v = B v u)
    (η : ℝ → V) (η' : V) {t : ℝ}
    (hη : HasDerivAt η η' t) (hpos : 0 < B (η t) (η t)) :
    HasDerivAt (fun s => Real.sqrt (B (η s) (η s)))
      (B (η t) η' / Real.sqrt (B (η t) (η t))) t := by
  have hf : HasDerivAt (fun s => B (η s) (η s))
      (B η' (η t) + B (η t) η') t :=
    (B.hasFDerivAt.comp_hasDerivAt t hη).clm_apply hη
  have hsqrt := hf.sqrt (ne_of_gt hpos)
  have hcoef :
      (B η' (η t) + B (η t) η') / (2 * Real.sqrt (B (η t) (η t))) =
        B (η t) η' / Real.sqrt (B (η t) (η t)) := by
    rw [hBsym η' (η t),
      show B (η t) η' + B (η t) η' = 2 * B (η t) η' by ring,
      mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rwa [hcoef] at hsqrt

/-- A map whose differential preserves the radial norm at zero and satisfies a
radial Cauchy bound along a lifted path cannot shorten its endpoint norm. -/
theorem lift_norm_le
    [(x : N) → NormedAddCommGroup (TangentSpace J x)]
    [(x : N) → NormedSpace ℝ (TangentSpace J x)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (F : V → N) {η : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) (hηa : η a = 0)
    (hη : ContDiffOn ℝ 1 η (Set.Icc a b))
    (hF : ∀ x ∈ Set.Icc a b,
      ContMDiffAt 𝓘(ℝ, V) J 1 F (η x))
    (hzero : ∀ v : V,
      Real.sqrt
          (g.inner (F 0)
            (mfderiv 𝓘(ℝ, V) J F 0 v)
            (mfderiv 𝓘(ℝ, V) J F 0 v)) =
        ‖v‖)
    (hrad : ∀ x ∈ Set.Icc a b, ∀ v : V,
      |Inner.inner ℝ (η x) v| ≤
        ‖η x‖ * Real.sqrt
          (g.inner (F (η x))
            (mfderiv 𝓘(ℝ, V) J F (η x) v)
            (mfderiv 𝓘(ℝ, V) J F (η x) v))) :
    ENNReal.ofReal ‖η b‖ ≤
      Manifold.pathELength J (F ∘ η) a b := by
  classical
  let γ : ℝ → N := F ∘ η
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  let ρ : ℝ → ℝ := fun t => Real.sqrt (B (η t) (η t))
  let φ : ℝ → ℝ := fun t =>
    Real.sqrt
      (g.inner (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) J γ (Set.Icc a b) t 1)
        (mfderivWithin 𝓘(ℝ, ℝ) J γ (Set.Icc a b) t 1))
  have hBsym : ∀ x y : V, B x y = B y x := by
    intro x y
    change Inner.inner ℝ x y = Inner.inner ℝ y x
    exact real_inner_comm y x
  have hBnn : ∀ x : V, 0 ≤ B x x := by
    intro x
    change 0 ≤ Inner.inner ℝ x x
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hηm :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η (Set.Icc a b) :=
    hη.contMDiffOn
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) J 1 γ (Set.Icc a b) := by
    intro x hx
    exact (hF x hx).comp_contMDiffWithinAt x (hηm x hx)
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    (psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn
      hη.continuousOn
  have hρa : ρ a ≤ 0 := by
    simp only [ρ, hηa, map_zero, Real.sqrt_zero, le_refl]
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [hηa, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : MapsTo
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) :=
    fun t ht => by simpa using ht
  have hVel : ContinuousOn
      (fun t : ℝ =>
        TotalSpace.mk' E (E := (TangentSpace J : N → Type _)) (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) J γ (Set.Icc a b) t 1))
      (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun _ _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    simp only [φ]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := J) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t :=
    fun _ _ => Real.sqrt_nonneg _
  have hφint : IntegrableOn φ (Set.Icc a b) volume :=
    hφc.integrableOn_compact isCompact_Icc
  have hφcont :
      ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz
      exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq : ∀ t ∈ Set.Ioo a b,
      φ t = Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) J γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) J γ t 1)) := by
    intro t ht
    simp only [φ]
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hchain : ∀ x ∈ Set.Icc a b,
      mfderivWithin 𝓘(ℝ, ℝ) J γ (Set.Icc a b) x 1 =
        mfderiv 𝓘(ℝ, V) J F (η x)
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, V)
            η (Set.Icc a b) x 1) := by
    intro x hx
    have hηdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, V)
        η (Set.Icc a b) x :=
      (hηm.mdifferentiableOn one_ne_zero) x hx
    have hFdiff : MDifferentiableWithinAt 𝓘(ℝ, V) J F Set.univ (η x) :=
      ((hF x hx).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
    have hc := mfderivWithin_comp
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V)) (I'' := J)
      (f := η) (g := F) (s := Set.Icc a b) (u := Set.univ)
      x hFdiff hηdiff (fun _ _ => Set.mem_univ _) (hUnique x hx)
    have happ := congrArg
      (fun D : ℝ →L[ℝ] TangentSpace J (γ x) => D 1) hc
    simpa only [γ, Function.comp_apply, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] using happ
  have hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    let cv : V :=
      mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η (Set.Icc a b) x 1
    have hηderiv : HasDerivWithinAt η cv (Set.Ici x) x := by
      have hηdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, V)
          η (Set.Icc a b) x :=
        (hηm.mdifferentiableOn one_ne_zero) x hxIcc
      have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, V)
          η (Set.Icc a b) x
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η (Set.Icc a b) x) :=
        hηdiff.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hderiv : HasDerivWithinAt η cv (Set.Icc a b) x :=
        hmf.hasDerivWithinAt
      refine hderiv.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz
        exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hηx : η x = 0
    · have htend : Tendsto (fun z => slope ρ x z)
          (nhdsWithin x (Set.Ioi x)) (nhds ‖cv‖) := by
        have hquot : Tendsto (fun z => (z - x)⁻¹ • η z)
            (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hηderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z
            simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (tendsto_congr' ?_).mp h0
          filter_upwards with z
          rw [slope_def_module, hηx, sub_zero]
        have htend' := continuous_norm.tendsto cv |>.comp hquot
        refine (tendsto_congr' ?_).mp htend'
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        simp only [Function.comp_apply, ρ, slope_def_module, hηx,
          map_zero, Real.sqrt_zero, sub_zero]
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzx),
          B, smul_eq_mul]
        change (z - x)⁻¹ * ‖η z‖ =
          (z - x)⁻¹ * Real.sqrt (Inner.inner ℝ (η z) (η z))
        rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      have hφx : φ x = ‖cv‖ := by
        simp only [φ]
        rw [hchain x hxIcc, hηx]
        have hγx : γ x = F 0 := by
          simp only [γ, Function.comp_apply, hηx]
        rw [hγx]
        change Real.sqrt
            (g.inner (F 0)
              (mfderiv 𝓘(ℝ, V) J F 0 cv)
              (mfderiv 𝓘(ℝ, V) J F 0 cv)) = ‖cv‖
        exact hzero cv
      rw [hφx] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa
        apply hηx
        rw [← hxa, hηa]
      have hmem : Set.Icc a b ∈ nhds x :=
        Icc_mem_nhds hxIoo.1 hxIoo.2
      have hηdiff : DifferentiableAt ℝ η x :=
        ((hη.differentiableOn one_ne_zero) x hxIcc).differentiableAt hmem
      have hηHDA : HasDerivAt η
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η x 1) x := by
        rw [mfderiv_eq_fderiv]
        exact hηdiff.hasDerivAt
      have hcv : cv = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η x 1 := by
        simp only [cv]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hpos : 0 < B (η x) (η x) := by
        simp only [B]
        change 0 < Inner.inner ℝ (η x) (η x)
        rw [real_inner_self_eq_norm_sq]
        positivity
      have hρderiv : HasDerivAt ρ
          (B (η x) cv / Real.sqrt (B (η x) (η x))) x := by
        rw [hcv]
        exact radialDist_deriv B hBsym η
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η x 1) hηHDA hpos
      let ρ' : ℝ := B (η x) cv / Real.sqrt (B (η x) (η x))
      have hφx : φ x = Real.sqrt
          (g.inner (F (η x))
            (mfderiv 𝓘(ℝ, V) J F (η x) cv)
            (mfderiv 𝓘(ℝ, V) J F (η x) cv)) := by
        simp only [φ]
        rw [hchain x hxIcc]
        rfl
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx]
        have hnorm : Real.sqrt (B (η x) (η x)) = ‖η x‖ := by
          simp only [B]
          change Real.sqrt (Inner.inner ℝ (η x) (η x)) = ‖η x‖
          rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
        simp only [ρ', hnorm]
        have hn : 0 < ‖η x‖ := norm_pos_iff.mpr hηx
        apply (div_le_iff₀ hn).2
        calc
          B (η x) cv ≤ |B (η x) cv| := le_abs_self _
          _ ≤ ‖η x‖ * Real.sqrt
              (g.inner (F (η x))
                (mfderiv 𝓘(ℝ, V) J F (η x) cv)
                (mfderiv 𝓘(ℝ, V) J F (η x) cv)) := by
            simpa only [B] using hrad x hxIcc cv
          _ = Real.sqrt
              (g.inner (F (η x))
                (mfderiv 𝓘(ℝ, V) J F (η x) cv)
                (mfderiv 𝓘(ℝ, V) J F (η x) cv)) * ‖η x‖ :=
            mul_comm _ _
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  have hftc : ρ b ≤ ∫ t in a..b, φ t :=
    image_radialDist_le_intervalIntegral_of_slope_le
      hab hρc hρa hφint hφcont hslope
  have hpath : ENNReal.ofReal (∫ t in a..b, φ t) ≤
      Manifold.pathELength J γ a b := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
          exact hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo
    filter_upwards with t ht
    rw [hφ_eq t ht]
    exact le_of_eq
      (hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) J γ t 1)).symm
  have hρb : ρ b = ‖η b‖ := by
    simp only [ρ, B]
    change Real.sqrt (Inner.inner ℝ (η b) (η b)) = ‖η b‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hρb]
  exact (ENNReal.ofReal_le_ofReal hftc).trans hpath

end Riemannian
end Geometry
end DifferentialGeometry
