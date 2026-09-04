import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SourceWeakSolution
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.HomogeneousMaster

noncomputable section

open MeasureTheory Metric Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem stdTest_eq_on
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
private theorem stdTest_tsupport_on
    {K : Set E} {eta u : E → ℝ} (heta_cpt : HasCompactSupport eta)
    (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ K) :
    tsupport (standardNirenbergTest k h eta u) ⊆ K := by
  intro x hx
  rcases standardNirenbergTest_tsupport_subset (d := d) k h heta_cpt u hx with
    hx_eta | hx_shift
  · exact hroom ((Metric.self_subset_cthickening (tsupport eta)) hx_eta)
  · apply hroom
    refine Metric.mem_cthickening_of_dist_le x
      (x + (-h) • EuclideanSpace.single k 1) |h| (tsupport eta) hx_shift ?_
    rw [dist_eq_norm]
    have heq : x - (x + (-h) • EuclideanSpace.single k 1) =
        h • EuclideanSpace.single k 1 := by
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
    rw [heq, norm_smul]
    simp

/-- A local scalar-source weak equation whose principal coefficient agrees near
the cutoff with a positive multiple of a smooth global coefficient admits a
whole-space Sobolev representative satisfying the raw Nirenberg master bound. -/
theorem src_master_nonsmooth
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
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
    (k : Fin d) :
    ∃ (U : E → ℝ) (hU : DeGiorgi.MemW1pWitness 2 U Set.univ),
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), U x = u x) ∧
      (∀ x ∈ Metric.cthickening R₀ (tsupport eta), ∀ i : Fin d,
        hU.weakGrad x i = hu.weakGrad x i) ∧
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        B.lam * ∫ x, eta x ^ 2 * ∑ i : Fin d,
            diffQuot k h (fun y => hU.weakGrad y i) x ^ 2
          ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * translate k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
              hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
            2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
              (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
              hU.weakGrad x i * diffQuot k h U x
            ∂(volume : Measure E)| +
        |rho⁻¹ * ∫ x in Omega,
            f x * standardNirenbergTest k h eta u x ∂(volume : Measure E)| := by
  classical
  let K : Set E := Metric.cthickening R₀ (tsupport eta)
  have hK_compact : IsCompact K := heta_cpt.cthickening
  obtain ⟨U, hU, hU_eq, hgrad_eq⟩ :=
    DeGiorgi.exists_global_wit (d := d) hOmega hu hK_compact hK_Omega
  refine ⟨U, hU, hU_eq, hgrad_eq, ?_⟩
  let fGlobal : E → ℝ := fun x => -(rho⁻¹) * f x
  let Omega' : Set E := Metric.thickening (R₀ + 1) (tsupport eta)
  have hOmega'_open : IsOpen Omega' := Metric.isOpen_thickening
  have hOmega'_compact : IsCompact (closure Omega') := by
    have hsub : closure Omega' ⊆
        Metric.cthickening (R₀ + 1) (tsupport eta) :=
      Metric.closure_thickening_subset_cthickening _ _
    exact heta_cpt.cthickening.of_isClosed_subset isClosed_closure hsub
  have hroom_Omega' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport eta) ⊆ Omega' := by
    intro h hh_le
    exact Metric.cthickening_subset_thickening' (by linarith) (by linarith) _
  have hsource_eq : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, fGlobal x * standardNirenbergTest k h eta U x
          ∂(volume : Measure E) =
        -(rho⁻¹ * ∫ x in Omega,
          f x * standardNirenbergTest k h eta u x ∂(volume : Measure E)) := by
    intro h hh hh_le
    have hroom_K : Metric.cthickening |h| (tsupport eta) ⊆ K :=
      Metric.cthickening_mono hh_le _
    have htest_eq : standardNirenbergTest k h eta U =
        standardNirenbergTest k h eta u :=
      stdTest_eq_on (d := d) hU_eq k hh hroom_K
    have htest_supp : tsupport (standardNirenbergTest k h eta U) ⊆ Omega :=
      (stdTest_tsupport_on (d := d) heta_cpt k h hroom_K).trans hK_Omega
    have hzero : ∀ x ∉ Omega,
        fGlobal x * standardNirenbergTest k h eta U x = 0 := by
      intro x hx
      have htest_zero : standardNirenbergTest k h eta U x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxt => hx (htest_supp hxt))
      rw [htest_zero, mul_zero]
    calc
      _ = ∫ x in Omega, fGlobal x * standardNirenbergTest k h eta U x
          ∂(volume : Measure E) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ x in Omega, (-(rho⁻¹)) *
          (f x * standardNirenbergTest k h eta u x)
          ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show fGlobal x = -(rho⁻¹) * f x from rfl, congrFun htest_eq x]
        ring
      _ = -(rho⁻¹) * ∫ x in Omega,
          f x * standardNirenbergTest k h eta u x ∂(volume : Measure E) := by
        exact integral_const_mul _ _
      _ = _ := by ring
  have hsubst : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport eta) ⊆ (Set.univ : Set E) →
      ∫ x, (∑ i : Fin d, ∑ j : Fin d,
          translate k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            diffQuot k h (fun y => hU.weakGrad y i) x *
            diffQuot k h (fun y => hU.weakGrad y j) x)
        ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * translate k h (fun y : E => B.a y i j) x * eta x *
            (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
            diffQuot k h (fun y => hU.weakGrad y i) x * diffQuot k h U x
        ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          diffQuot k h (fun y : E => B.a y i j) x * eta x ^ 2 *
            hU.weakGrad x i * diffQuot k h (fun y => hU.weakGrad y j) x
        ∂(volume : Measure E) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * diffQuot k h (fun y : E => B.a y i j) x * eta x *
            (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
            hU.weakGrad x i * diffQuot k h U x
        ∂(volume : Measure E) +
      ∫ x, B.c x * U x * standardNirenbergTest k h eta U x
        ∂(volume : Measure E) =
      ∫ x, fGlobal x * standardNirenbergTest k h eta U x
        ∂(volume : Measure E) := by
    intro h hh hh_le _
    have hroom_K : Metric.cthickening |h| (tsupport eta) ⊆ K :=
      Metric.cthickening_mono hh_le _
    have hlocal := srcSol_substOn (d := d) hOmega hu hweak heta heta_cpt k h
      (hroom_K.trans hK_Omega)
    have hfour := subst_expand_on (d := d) hOmega hu hU hK_compact
      hK_Omega hU_eq hgrad_eq B hrho hcoeff heta heta_cpt k hh hroom_K hlocal
    have hexact := hfour.trans (hsource_eq hh hh_le).symm
    simpa [hc] using hexact
  have hU_l2 : MemLp U 2 (volume : Measure E) := by
    simpa only [Measure.restrict_univ] using hU.memLp
  have hg_l2 : ∀ i : Fin d,
      MemLp (fun x => hU.weakGrad x i) 2 (volume : Measure E) := by
    intro i
    simpa only [Measure.restrict_univ] using hU.weakGrad_component_memLp i
  intro h hh hh_le
  have hraw := (NirenbergSubstitutionNonSmooth.master_raw_nonsmooth
    (d := d) (Ω := Set.univ) (u := U) (f := fGlobal)
    (g := fun i x => hU.weakGrad x i) B hU_l2 hg_l2
    (fun i => hU.isWeakGrad i)
    heta heta_cpt heta_range hOmega'_open hOmega'_compact (subset_univ _)
    hroom_Omega' k hsubst) hh hh_le
  have hsource_raw : ∫ x in (Set.univ : Set E),
      fGlobal x * NirenbergTestFunction.nirenbergTestFunction k h eta U x
        ∂(volume : Measure E) =
      -(rho⁻¹ * ∫ x in Omega,
        f x * standardNirenbergTest k h eta u x ∂(volume : Measure E)) := by
    simpa only [setIntegral_univ, NirenbergTestFunction.nirenbergTestFunction,
      standardNirenbergTest] using hsource_eq hh hh_le
  rw [hsource_raw] at hraw
  simpa [hc, abs_neg] using hraw

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
