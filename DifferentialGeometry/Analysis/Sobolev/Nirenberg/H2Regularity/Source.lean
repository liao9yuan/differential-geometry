import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Homogeneous
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SourceMaster

noncomputable section

open MeasureTheory Metric Set Filter
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem source_stdTest_eq
    {K : Set E} {eta u U : E → ℝ}
    (hU_eq : ∀ x ∈ K, U x = u x)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ K) :
    standardNirenbergTest k h eta U = standardNirenbergTest k h eta u := by
  unfold standardNirenbergTest
  apply congrArg (diffQuot k (-h))
  funext x
  by_cases hx : x ∈ tsupport eta
  · have hxK : x ∈ K :=
      hroom ((Metric.self_subset_cthickening (tsupport eta)) hx)
    have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈ K := by
      apply hroom
      refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport eta) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp
    rw [diffQuot_apply_of_ne (d := d) k hh,
      diffQuot_apply_of_ne (d := d) k hh,
      hU_eq x hxK, hU_eq _ hx_shiftK]
  · have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hetax]

omit [NeZero d] in
private theorem source_one_tsupp
    {V : Set E} {eta : E → ℝ}
    (heta_one : ∀ x ∈ closure V, eta x = 1) :
    closure V ⊆ tsupport eta := by
  intro x hx
  apply subset_tsupport eta
  intro hzero
  have hone := heta_one x hx
  rw [hzero] at hone
  norm_num at hone

omit [NeZero d] in
private theorem source_dq_grad_eq
    {eta : E → ℝ} {R₀ h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    {V : Set E} (hV_tsupp : V ⊆ tsupport eta)
    {g G : E → ℝ}
    (hgrad_eq : ∀ x ∈ Metric.cthickening R₀ (tsupport eta), G x = g x)
    (k : Fin d) :
    ∀ x ∈ V, diffQuot k h G x = diffQuot k h g x := by
  intro x hxV
  have hx_tsupp : x ∈ tsupport eta := hV_tsupp hxV
  have hxK : x ∈ Metric.cthickening R₀ (tsupport eta) :=
    (Metric.self_subset_cthickening (tsupport eta)) hx_tsupp
  have hx_shiftK : x + h • EuclideanSpace.single k 1 ∈
      Metric.cthickening R₀ (tsupport eta) := by
    refine Metric.mem_cthickening_of_dist_le _ x R₀ (tsupport eta) hx_tsupp ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simpa using hh_le
  rw [diffQuot_apply_of_ne (d := d) k hh,
    diffQuot_apply_of_ne (d := d) k hh,
    hgrad_eq _ hx_shiftK, hgrad_eq x hxK]

/-- A local scalar-source weak solution has a uniform local `L²` bound for
every difference quotient of each displayed weak-gradient component. -/
theorem srcSol_dq_bound
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0)
    {V : Set E} (hV_open : IsOpen V)
    (hV_compact : IsCompact (closure V))
    (heta_one : ∀ x ∈ closure V, eta x = 1)
    {N : ℝ} (hderiv : ∀ x : E, ‖fderiv ℝ eta x‖ ≤ N)
    (i k : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ, h ≠ 0 → |h| ≤ R₀ →
      eLpNorm (diffQuot k h (fun x => hu.weakGrad x i)) 2
        ((volume : Measure E).restrict V) ≤ ENNReal.ofReal M := by
  classical
  have hN : 0 ≤ N :=
    (norm_nonneg (fderiv ℝ eta (0 : E))).trans (hderiv 0)
  have hV_meas : MeasurableSet V := by
    have h_eq : V ∩ closure V = V := inter_eq_left.mpr subset_closure
    rw [← h_eq]
    exact hV_open.measurableSet.inter hV_compact.measurableSet
  obtain ⟨U, hU, hU_eq, hgrad_eq, hmaster⟩ :=
    src_master_nonsmooth (d := d) hOmega hu hweak B hrho heta heta_cpt
      heta_range hR₀ hK_Omega hcoeff hc k
  let g : Fin d → E → ℝ := fun j x => hU.weakGrad x j
  have hU_l2 : MemLp U 2 (volume : Measure E) := by
    simpa only [Measure.restrict_univ] using hU.memLp
  have hg_l2 : ∀ j : Fin d, MemLp (g j) 2 (volume : Measure E) := by
    intro j
    simpa only [g, Measure.restrict_univ] using hU.weakGrad_component_memLp j
  let fGlobal : E → ℝ := Omega.indicator (fun x => rho⁻¹ * f x)
  have hfGlobal : MemLp fGlobal 2 (volume : Measure E) := by
    change MemLp (Omega.indicator (fun x => rho⁻¹ * f x)) 2 (volume : Measure E)
    rw [MeasureTheory.memLp_indicator_iff_restrict hOmega.measurableSet]
    simpa only [smul_eq_mul] using hf.const_mul (rho⁻¹)
  have hfGlobal_loc : ∀ {W : Set E}, IsCompact (closure W) →
      MemLp fGlobal 2 ((volume : Measure E).restrict W) := by
    intro W _
    exact hfGlobal.restrict W
  let Omega' : Set E := Metric.thickening (R₀ + 1) (tsupport eta)
  have hOmega'_open : IsOpen Omega' := Metric.isOpen_thickening
  have hOmega'_compact : IsCompact (closure Omega') := by
    have hsub : closure Omega' ⊆
        Metric.cthickening (R₀ + 1) (tsupport eta) :=
      Metric.closure_thickening_subset_cthickening _ _
    exact heta_cpt.cthickening.of_isClosed_subset isClosed_closure hsub
  have heta_in_Omega' : tsupport eta ⊆ Omega' :=
    Metric.self_subset_thickening (by linarith) _
  have hroom_Omega' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport eta) ⊆ Omega' := by
    intro h hh_le
    exact Metric.cthickening_subset_thickening' (by linarith) (by linarith) _
  have hFK : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport eta, (diffQuot k h U x) ^ 2
          ∂(volume : Measure E) ≤
        ∫ x in Omega', ∑ j : Fin d, (g j x) ^ 2
          ∂(volume : Measure E) := by
    intro h hh hh_le
    have htsupp_compact : IsCompact (closure (tsupport eta)) := by
      simpa only [(isClosed_tsupport eta).closure_eq] using heta_cpt.isCompact
    have hthick : Metric.cthickening R₀ (closure (tsupport eta)) ⊆ Omega' := by
      simpa only [(isClosed_tsupport eta).closure_eq] using
        (Metric.cthickening_subset_thickening' (by linarith : 0 < R₀ + 1)
          (by linarith : R₀ < R₀ + 1) (tsupport eta))
    have hsingle :=
      integral_sq_diffQuot_le_integral_sq_weakPartial_meas
        (d := d) hU_l2 (hg_l2 k) k (hU.isWeakGrad k)
        hOmega'_open.measurableSet (isClosed_tsupport eta).measurableSet
        htsupp_compact hR₀ hthick hh hh_le
    have hk_int : Integrable (fun x => (g k x) ^ 2)
        ((volume : Measure E).restrict Omega') :=
      ((hg_l2 k).mono_measure Measure.restrict_le_self).integrable_sq
    have hsum_int : Integrable (fun x => ∑ j : Fin d, (g j x) ^ 2)
        ((volume : Measure E).restrict Omega') :=
      integrable_finset_sum Finset.univ fun j _ =>
        ((hg_l2 j).mono_measure Measure.restrict_le_self).integrable_sq
    exact hsingle.trans (integral_mono hk_int hsum_int fun x =>
      Finset.single_le_sum (fun j _ => sq_nonneg (g j x)) (Finset.mem_univ k))
  have htest : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (nirenbergTestFunction k h eta U x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport eta, (diffQuot k h U x) ^ 2
            ∂(volume : Measure E) +
        2 * ∫ x, eta x ^ 2 * (diffQuot k h (g k) x) ^ 2
          ∂(volume : Measure E) := by
    intro h hh _
    exact stdTest_sq_bound hU_l2 (hg_l2 k) k (hU.isWeakGrad k)
      heta heta_cpt heta_range hderiv hh
  have hsource_eq {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀) :
      ∫ x in (Set.univ : Set E),
          fGlobal x * nirenbergTestFunction k h eta U x
            ∂(volume : Measure E) =
        rho⁻¹ * ∫ x in Omega,
          f x * standardNirenbergTest k h eta u x
            ∂(volume : Measure E) := by
    have hroom : Metric.cthickening |h| (tsupport eta) ⊆
        Metric.cthickening R₀ (tsupport eta) :=
      Metric.cthickening_mono hh_le _
    have htest_eq : standardNirenbergTest k h eta U =
        standardNirenbergTest k h eta u :=
      source_stdTest_eq (d := d) hU_eq k hh hroom
    rw [setIntegral_univ]
    calc
      _ = ∫ x, Omega.indicator (fun y =>
          rho⁻¹ * (f y * standardNirenbergTest k h eta u y)) x
            ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Omega
        · rw [show nirenbergTestFunction k h eta U x =
              standardNirenbergTest k h eta U x from rfl,
            congrFun htest_eq x]
          simp only [fGlobal, Set.indicator_of_mem hx]
          ring
        · simp only [fGlobal, Set.indicator_of_notMem hx, zero_mul]
      _ = ∫ x in Omega,
          rho⁻¹ * (f x * standardNirenbergTest k h eta u x)
            ∂(volume : Measure E) :=
        MeasureTheory.integral_indicator hOmega.measurableSet
      _ = _ := integral_const_mul _ _
  let C : ℝ := nirenbergMasterYoungConstant (d := d) B N hOmega'_compact k
  let energy : ℝ :=
    (∫ x in Omega', ∑ j : Fin d, (g j x) ^ 2 ∂(volume : Measure E)) +
      ∫ x in Omega', U x ^ 2 ∂(volume : Measure E) +
      ∫ x in Omega', fGlobal x ^ 2 ∂(volume : Measure E)
  let S : ℝ := C * energy / (B.lam / 2)
  have hC : 0 ≤ C :=
    nirenbergMasterYoungConstant_nonneg (d := d) B hN hOmega'_compact k
  have henergy : 0 ≤ energy := by
    apply add_nonneg
    · apply add_nonneg
      · exact integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg (g j x)
      · exact integral_nonneg fun x => sq_nonneg (U x)
    · exact integral_nonneg fun x => sq_nonneg (fGlobal x)
  have hlam_half : 0 < B.lam / 2 := half_pos B.hlam_pos
  have hS : 0 ≤ S := div_nonneg (mul_nonneg hC henergy) hlam_half.le
  refine ⟨Real.sqrt S, Real.sqrt_nonneg S, ?_⟩
  intro h hh hh_le
  have hquant_h :=
    nirenberg_diffQuot_g_localL2_bound_quantitative
      (d := d) (Ω := Set.univ) (u := U) (f := fGlobal) (g := g)
      B hU_l2 hfGlobal_loc hg_l2 (fun j => hU.isWeakGrad j)
      heta heta_cpt heta_range hN hderiv hOmega'_open (subset_univ _)
      hOmega'_compact heta_in_Omega' hroom_Omega'
      (fun x hx => heta_one x (subset_closure hx)) hV_meas k
      hFK htest (fun {h} hh hh_le => by
        rw [hsource_eq hh hh_le]
        simpa [g, hc] using hmaster hh hh_le) hh hh_le
  have hsum_le :
      ∫ x in V, ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
          ∂(volume : Measure E) ≤ S := by
    apply (le_div_iff₀ hlam_half).2
    calc
      (∫ x in V, ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
          ∂(volume : Measure E)) * (B.lam / 2) =
          (B.lam / 2) * ∫ x in V,
            ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
              ∂(volume : Measure E) := mul_comm _ _
      _ ≤ C * energy := by
        simpa [C, energy] using hquant_h
  have hU_bound := dq_norm_of_sum hg_l2 hV_meas hS i k h hsum_le
  have hV_tsupp : V ⊆ tsupport eta :=
    subset_closure.trans (source_one_tsupp heta_one)
  have hdq_eq : diffQuot k h (g i) =ᵐ[(volume : Measure E).restrict V]
      diffQuot k h (fun x => hu.weakGrad x i) := by
    filter_upwards [ae_restrict_mem hV_meas] with x hx
    exact source_dq_grad_eq (d := d) hh hh_le hV_tsupp
      (fun y hy => hgrad_eq y hy i) k x hx
  rw [← eLpNorm_congr_ae hdq_eq]
  exact hU_bound

/-- Every displayed weak-gradient component of a scalar-source solution has
each second weak partial derivative locally in `L²`. -/
theorem srcSol_second
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0)
    {V : Set E} (hV_open : IsOpen V)
    (hV_compact : IsCompact (closure V))
    (heta_one : ∀ x ∈ closure V, eta x = 1)
    {N : ℝ} (hderiv : ∀ x : E, ‖fderiv ℝ eta x‖ ≤ N)
    (i k : Fin d) :
    ∃ G : E → ℝ,
      MemLp G 2 ((volume : Measure E).restrict V) ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k G
        (fun x => hu.weakGrad x i) V := by
  obtain ⟨M, hM, hbound⟩ := srcSol_dq_bound (d := d) hOmega hu hf hweak B hrho
    heta heta_cpt heta_range hR₀ hK_Omega hcoeff hc hV_open hV_compact
    heta_one hderiv i k
  have hV_tsupp : closure V ⊆ tsupport eta := source_one_tsupp heta_one
  have htsupp_K : tsupport eta ⊆ Metric.cthickening R₀ (tsupport eta) :=
    Metric.self_subset_cthickening (tsupport eta)
  have hV_Omega : closure V ⊆ Omega :=
    (hV_tsupp.trans htsupp_K).trans hK_Omega
  have hroom : Metric.cthickening R₀ (closure V) ⊆ Omega :=
    (Metric.cthickening_subset_of_subset R₀ hV_tsupp).trans hK_Omega
  obtain ⟨G, hG_l2, hG_weak, _hG_norm⟩ :=
    hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
      (d := d) hOmega hV_open hV_compact hV_Omega hR₀ hroom
      (hu.weakGrad_component_memLp i) k hM
      (fun h hpos hle => hbound h (abs_pos.mp hpos) hle)
  exact ⟨G, hG_l2, hG_weak⟩

/-- A local scalar-source weak solution with `L²` source belongs to `W^{2,2}`
on every inner open set on which the cutoff equals one. -/
theorem srcSol_memW2
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0)
    {V : Set E} (hV_open : IsOpen V)
    (hV_compact : IsCompact (closure V))
    (heta_one : ∀ x ∈ closure V, eta x = 1)
    {N : ℝ} (hderiv : ∀ x : E, ‖fderiv ℝ eta x‖ ≤ N) :
    MemWkp (d := d) 2 2 u V := by
  have hV_tsupp : closure V ⊆ tsupport eta := source_one_tsupp heta_one
  have htsupp_K : tsupport eta ⊆ Metric.cthickening R₀ (tsupport eta) :=
    Metric.self_subset_cthickening (tsupport eta)
  have hV_Omega : V ⊆ Omega :=
    ((subset_closure.trans hV_tsupp).trans htsupp_K).trans hK_Omega
  let huV : DeGiorgi.MemW1pWitness 2 u V := hu.restrict hV_open hV_Omega
  apply MemWkp.two_of_wit hV_open huV
  intro i
  refine ⟨huV.weakGrad_component_memLp i, ?_⟩
  intro k
  obtain ⟨G, hG_l2, hG_weak⟩ :=
    srcSol_second (d := d) hOmega hu hf hweak B hrho heta heta_cpt heta_range
      hR₀ hK_Omega hcoeff hc hV_open hV_compact heta_one hderiv i k
  refine ⟨G, hG_l2, ?_⟩
  simpa only [huV, DeGiorgi.MemW1pWitness.restrict] using hG_weak

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
