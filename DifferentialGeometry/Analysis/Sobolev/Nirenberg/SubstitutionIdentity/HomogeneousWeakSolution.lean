import DifferentialGeometry.Analysis.Sobolev.Nirenberg.MasterInequality.MasterInequalityNonSmooth
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.StandardNirenbergTest
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.External.DeGiorgi.Localization

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem memLp_mul_compact
    {f g : E → ℝ} (hf : Continuous f) (hf_cpt : HasCompactSupport f)
    (hg : MemLp g 2 (volume : Measure E)) :
    MemLp (fun x => f x * g x) 2 (volume : Measure E) := by
  obtain ⟨C, hC, hCf⟩ := exists_bound_of_continuous_compactSupport hf hf_cpt
  exact memLp_bounded_mul hf.aestronglyMeasurable hC hCf hg

private noncomputable def standardTestWitness
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Set.univ)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ) :
    DeGiorgi.MemW1pWitness 2 (standardNirenbergTest k h eta u) Set.univ := by
  classical
  let grad : Fin d → E → ℝ := fun j =>
    diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun x => hu.weakGrad x j) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
  let G : E → E := fun x => WithLp.toLp 2 fun j => grad j x
  have hu_l2 : MemLp u 2 (volume : Measure E) := by
    simpa using hu.memLp
  have hgrad_l2 : ∀ j : Fin d,
      MemLp (fun x => hu.weakGrad x j) 2 (volume : Measure E) := by
    intro j
    simpa using hu.weakGrad_component_memLp j
  have hdq_u : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h hu_l2
  have heta_sq_cont : Continuous (fun x : E => (eta x) ^ 2) :=
    heta.continuous.pow 2
  have heta_sq_cpt : HasCompactSupport (fun x : E => (eta x) ^ 2) := by
    simpa [pow_two] using heta_cpt.mul_right
  have hF_l2 : MemLp (fun x => (eta x) ^ 2 * diffQuot k h u x) 2
      (volume : Measure E) :=
    memLp_mul_compact heta_sq_cont heta_sq_cpt hdq_u
  have htest_l2 : MemLp (standardNirenbergTest k h eta u) 2
      (volume : Measure E) := by
    change MemLp (diffQuot k (-h) (fun x => (eta x) ^ 2 * diffQuot k h u x)) 2
      (volume : Measure E)
    exact memLp_diffQuot_two k (-h) hF_l2
  have hgrad_component_l2 : ∀ j : Fin d,
      MemLp (grad j) 2 (volume : Measure E) := by
    intro j
    have hdq_g : MemLp (diffQuot k h (fun x => hu.weakGrad x j)) 2
        (volume : Measure E) :=
      memLp_diffQuot_two k h (hgrad_l2 j)
    have hterm1 : MemLp
        (fun x => (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x) 2
        (volume : Measure E) :=
      memLp_mul_compact heta_sq_cont heta_sq_cpt hdq_g
    let coeff : E → ℝ := fun x =>
      2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single j 1)
    have hcoeff_cont : Continuous coeff := by
      exact (continuous_const.mul heta.continuous).mul
        ((heta.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hcoeff_cpt : HasCompactSupport coeff := by
      apply HasCompactSupport.intro'
        (K := tsupport eta) heta_cpt.isCompact (isClosed_tsupport eta)
      intro x hx
      have hetax : eta x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [coeff, hetax]
    have hterm2 : MemLp
        (fun x => coeff x * diffQuot k h u x) 2 (volume : Measure E) :=
      memLp_mul_compact hcoeff_cont hcoeff_cpt hdq_u
    have hsum : MemLp
        (fun x =>
          (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x +
            coeff x * diffQuot k h u x) 2 (volume : Measure E) :=
      hterm1.add hterm2
    change MemLp (diffQuot k (-h) (fun x =>
      (eta x) ^ 2 * diffQuot k h (fun y => hu.weakGrad y j) x +
        2 * eta x * (fderiv ℝ eta x) (EuclideanSpace.single j 1) *
          diffQuot k h u x)) 2 (volume : Measure E)
    simpa [coeff, mul_assoc] using memLp_diffQuot_two k (-h) hsum
  refine
    { memLp := by simpa using htest_l2
      weakGrad := G
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · intro j
    simpa [G, PiLp.toLp_apply] using hgrad_component_l2 j
  · intro j
    simpa [G, grad, PiLp.toLp_apply] using
      (hasWeakPartialDeriv_standardNirenbergTest (d := d) k j h heta
        (by simpa using hu_l2.locallyIntegrable (by norm_num))
        (by simpa using (hgrad_l2 j).locallyIntegrable (by norm_num))
        (hu.isWeakGrad j))

private theorem standardTest_memH01
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Set.univ)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ) :
    DeGiorgi.MemH01 (standardNirenbergTest k h eta u) Set.univ := by
  have hw := standardTestWitness (d := d) hu heta heta_cpt k h
  have hw' : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ))
      (standardNirenbergTest k h eta u) Set.univ := by
    simpa using hw.memW1p
  simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
    (d := d) isOpen_univ (p := (2 : ℝ)) (by norm_num) hw'
    (standardNirenbergTest_hasCompactSupport k h heta_cpt u) (subset_univ _)

omit [NeZero d] in
private theorem fderiv_cutoff_zero
    {K : Set E} {delta : ℝ} (hdelta : 0 < delta)
    {chi : E → ℝ}
    (hchi_one : ∀ x ∈ Metric.cthickening delta K, chi x = 1)
    {x : E} (hx : x ∈ K) (i : Fin d) :
    (fderiv ℝ chi x) (EuclideanSpace.single i 1) = 0 := by
  have hchi_eq : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds x (by linarith : 0 < delta / 2)) ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy_closed : y ∈ Metric.closedBall x (delta / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hy
    have hy_thick_half : y ∈ Metric.cthickening (delta / 2) K :=
      Metric.closedBall_subset_cthickening hx (delta / 2) hy_closed
    exact hchi_one y
      (Metric.cthickening_mono (by linarith : delta / 2 ≤ delta) K hy_thick_half)
  rw [Filter.EventuallyEq.fderiv_eq hchi_eq]
  simp

/-- Localize a Sobolev witness across the translation room needed by the
standard Nirenberg test. -/
noncomputable def stdTestWitnessOn
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    DeGiorgi.MemW1pWitness 2 (standardNirenbergTest k h eta u) Omega := by
  classical
  let K : Set E := Metric.cthickening |h| (tsupport eta)
  have hK_cpt : IsCompact K := heta_cpt.isCompact.cthickening
  have hdelta_exists := hK_cpt.exists_cthickening_subset_open hOmega hroom
  let delta : ℝ := Classical.choose hdelta_exists
  have hdelta_spec := Classical.choose_spec hdelta_exists
  have hdelta : 0 < delta := hdelta_spec.1
  have hdelta_sub : Metric.cthickening delta K ⊆ Omega := hdelta_spec.2
  let K' : Set E := Metric.cthickening (delta / 2) K
  have hK'_cpt : IsCompact K' := hK_cpt.cthickening
  have hK'_sub : K' ⊆ Omega := by
    exact (Metric.cthickening_mono (by linarith : delta / 2 ≤ delta) K).trans hdelta_sub
  have hchi_exists := DeGiorgi.exists_smooth_cutoff (d := d) hK'_cpt hOmega hK'_sub
  let chi : E → ℝ := Classical.choose hchi_exists
  have hchi_spec := Classical.choose_spec hchi_exists
  have hchi : ContDiff ℝ (⊤ : ℕ∞) chi := hchi_spec.1
  have hchi_cpt : HasCompactSupport chi := hchi_spec.2.1
  have hchi_range : Set.range chi ⊆ Set.Icc (0 : ℝ) 1 := hchi_spec.2.2.1
  have hchi_one : ∀ x ∈ K', chi x = 1 := hchi_spec.2.2.2.1
  have hchi_sub : tsupport chi ⊆ Omega := hchi_spec.2.2.2.2
  have hchi_bound : ∀ x, |chi x| ≤ 1 := by
    intro x
    rcases hchi_range ⟨x, rfl⟩ with ⟨hx0, hx1⟩
    simpa [abs_of_nonneg hx0] using hx1
  have hchi_deriv_cpt : HasCompactSupport (fderiv ℝ chi) :=
    hchi_cpt.fderiv (𝕜 := ℝ)
  have hC_exists := hchi_deriv_cpt.isCompact.exists_bound_of_continuousOn
    ((hchi.continuous_fderiv (by simp)).continuousOn)
  let C : ℝ := Classical.choose hC_exists
  have hC := Classical.choose_spec hC_exists
  let C1 : ℝ := max C 0
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hchi_deriv_bound : ∀ x, ‖fderiv ℝ chi x‖ ≤ C1 := by
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ chi)
    · exact (hC x hx).trans (le_max_left _ _)
    · have hz : fderiv ℝ chi x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [C1, hz]
  let huv : DeGiorgi.MemW1pWitness 2 (fun x => chi x * u x) Omega :=
    hu.mul_smooth_bounded_p (d := d) (by norm_num) hOmega hchi
      zero_le_one hC1 hchi_bound hchi_deriv_bound
  have hv_cpt : HasCompactSupport (fun x => chi x * u x) := hchi_cpt.mul_right
  have hv_sub : tsupport (fun x => chi x * u x) ⊆ Omega :=
    (tsupport_smul_subset_left chi u).trans hchi_sub
  have hv0 : DeGiorgi.MemW01p (ENNReal.ofReal (2 : ℝ))
      (fun x => chi x * u x) Omega := by
    have hvW : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ))
        (fun x => chi x * u x) Omega := by
      simpa [huv] using huv.memW1p
    exact DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
      (d := d) hOmega (p := (2 : ℝ)) (by norm_num) hvW hv_cpt hv_sub
  let huv_real : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (fun x => chi x * u x) Omega :=
    { memLp := by simpa using huv.memLp
      weakGrad := huv.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using huv.weakGrad_component_memLp i
      isWeakGrad := huv.isWeakGrad }
  let huvExtRaw : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ))
      (Omega.indicator (fun x => chi x * u x)) Set.univ :=
    DeGiorgi.zeroExtend_memW1pWitness_p (d := d) hOmega
      (p := 2) (by norm_num) hv0 huv_real
  have hindicator : Omega.indicator (fun x => chi x * u x) =
      (fun x => chi x * u x) := by
    funext x
    by_cases hx : x ∈ Omega
    · simp [hx]
    · have hchix : chi x = 0 := by
        apply DeGiorgi.zero_outside_of_tsupport_subset hchi_sub hx
      simp [hx, hchix]
  let huvExtRaw2 : DeGiorgi.MemW1pWitness 2
      (Omega.indicator (fun x => chi x * u x)) Set.univ :=
    { memLp := by simpa using huvExtRaw.memLp
      weakGrad := huvExtRaw.weakGrad
      weakGrad_component_memLp := by
        intro i
        simpa using huvExtRaw.weakGrad_component_memLp i
      isWeakGrad := huvExtRaw.isWeakGrad }
  let huvExt : DeGiorgi.MemW1pWitness 2
      (fun x => chi x * u x) Set.univ :=
    DeGiorgi.MemW1pWitness.of_ae_eq
      (Filter.Eventually.of_forall fun x => congrFun hindicator x) huvExtRaw2
  let hwExt := standardTestWitness (d := d) huvExt heta heta_cpt k h
  have hchi_one_K : ∀ x ∈ K, chi x = 1 := by
    intro x hx
    exact hchi_one x (Metric.self_subset_cthickening K hx)
  have hinner : (fun y => (eta y) ^ 2 *
        diffQuot k h (fun x => chi x * u x) y) =
      (fun y => (eta y) ^ 2 * diffQuot k h u y) := by
    funext y
    by_cases hy : y ∈ tsupport eta
    · have hyK : y ∈ K := Metric.self_subset_cthickening (tsupport eta) hy
      have hyhK : y + h • EuclideanSpace.single k 1 ∈ K := by
        refine Metric.mem_cthickening_of_dist_le _ y |h| (tsupport eta) hy ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp
      have hchiy : chi y = 1 := hchi_one_K y hyK
      have hchiyh : chi (y + h • EuclideanSpace.single k 1) = 1 :=
        hchi_one_K _ hyhK
      by_cases hh : h = 0
      · subst hh
        simp
      · rw [diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh]
        simp [hchiy, hchiyh]
    · have hetay : eta y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hetay]
  have hgrad_K : ∀ x ∈ K, ∀ i : Fin d,
      huvExt.weakGrad x i = hu.weakGrad x i := by
    intro x hx i
    have hxOmega : x ∈ Omega := hroom hx
    have hchi_x : chi x = 1 := hchi_one_K x hx
    have hfd_x : (fderiv ℝ chi x) (EuclideanSpace.single i 1) = 0 := by
      exact fderiv_cutoff_zero (K := K) (delta := delta / 2) (by linarith)
        (chi := chi) (hchi_one := fun y hy => hchi_one y (by simpa [K'] using hy)) hx i
    simp [huvExt, huvExtRaw2, huvExtRaw, huv_real, huv,
      DeGiorgi.MemW1pWitness.of_ae_eq,
      DeGiorgi.zeroExtend_memW1pWitness_p,
      DeGiorgi.MemW1pWitness.mul_smooth_bounded_p,
      PiLp.toLp_apply, hxOmega, hchi_x, hfd_x]
  have hinner_grad : ∀ i : Fin d,
      (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun x => huvExt.weakGrad x i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h (fun x => chi x * u x) y) =
      (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun x => hu.weakGrad x i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) := by
    intro i
    funext y
    by_cases hy : y ∈ tsupport eta
    · have hyK : y ∈ K := Metric.self_subset_cthickening (tsupport eta) hy
      have hyhK : y + h • EuclideanSpace.single k 1 ∈ K := by
        refine Metric.mem_cthickening_of_dist_le _ y |h| (tsupport eta) hy ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp
      have hgrad_y := hgrad_K y hyK i
      have hgrad_yh := hgrad_K _ hyhK i
      have hchi_y : chi y = 1 := hchi_one_K y hyK
      have hchi_yh : chi (y + h • EuclideanSpace.single k 1) = 1 :=
        hchi_one_K _ hyhK
      by_cases hh : h = 0
      · subst hh
        simp
      · rw [diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh,
          diffQuot_apply_of_ne (d := d) k hh]
        simp [hgrad_y, hgrad_yh, hchi_y, hchi_yh]
    · have heta_y : eta y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [heta_y]
  have htest_eq : standardNirenbergTest k h eta (fun x => chi x * u x) =
      standardNirenbergTest k h eta u := by
    unfold standardNirenbergTest
    rw [hinner]
  let htestRestrict := hwExt.restrict hOmega (subset_univ Omega)
  let hwRaw := DeGiorgi.MemW1pWitness.of_ae_eq
    (Filter.Eventually.of_forall fun x => congrFun htest_eq x) htestRestrict
  let explicitGrad : E → E := fun x => WithLp.toLp 2 fun i =>
    diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
          diffQuot k h u y) x
  have hraw_grad : ∀ x i, hwRaw.weakGrad x i = explicitGrad x i := by
    intro x i
    change diffQuot k (-h) (fun y =>
      (eta y) ^ 2 * diffQuot k h (fun z => huvExt.weakGrad z i) y +
        2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
          diffQuot k h (fun z => chi z * u z) y) x = _
    rw [hinner_grad i]
  refine
    { memLp := hwRaw.memLp
      weakGrad := explicitGrad
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · intro i
    have heq : (fun x => explicitGrad x i) = (fun x => hwRaw.weakGrad x i) := by
      funext x
      exact (hraw_grad x i).symm
    rw [heq]
    exact hwRaw.weakGrad_component_memLp i
  · intro i
    have heq : (fun x => explicitGrad x i) = (fun x => hwRaw.weakGrad x i) := by
      funext x
      exact (hraw_grad x i).symm
    rw [heq]
    exact hwRaw.isWeakGrad i

/-- The localized standard test witness carries the original witness's explicit
difference-quotient weak gradient. -/
theorem stdTest_grad
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega)
    (x : E) (i : Fin d) :
    (stdTestWitnessOn (d := d) hOmega hu heta heta_cpt k h hroom).weakGrad x i =
      diffQuot k (-h) (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x := by
  rfl

/-- The localized standard Nirenberg test belongs to `H₀¹` on the original
open domain. -/
theorem stdTest_memH01On
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    DeGiorgi.MemH01 (standardNirenbergTest k h eta u) Omega := by
  have hw := stdTestWitnessOn (d := d) hOmega hu heta heta_cpt k h hroom
  have htest_sub : tsupport (standardNirenbergTest k h eta u) ⊆ Omega := by
    refine (standardNirenbergTest_tsupport_subset (d := d) k h heta_cpt u).trans ?_
    intro x hx
    apply hroom
    rcases hx with hx | hx
    · exact Metric.self_subset_cthickening (tsupport eta) hx
    · have hdist : dist x (x + (-h) • EuclideanSpace.single k 1) ≤ |h| := by
        rw [dist_eq_norm]
        have heq : x - (x + (-h) • EuclideanSpace.single k 1) =
            h • EuclideanSpace.single k 1 := by
          rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
        rw [heq, norm_smul]
        simp
      exact Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport eta) hx hdist
  have hw' : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ))
      (standardNirenbergTest k h eta u) Omega := by
    simpa using hw.memW1p
  simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
    (d := d) hOmega (p := (2 : ℝ)) (by norm_num) hw'
    (standardNirenbergTest_hasCompactSupport k h heta_cpt u) htest_sub

/-- A local homogeneous weak solution may be tested against the standard
Nirenberg difference-quotient test using the original explicit weak gradient. -/
theorem homSol_substOn
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    ∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(volume : Measure E) = 0 := by
  let htest := stdTestWitnessOn (d := d) hOmega hu heta heta_cpt k h hroom
  have hzero := (hsol.to_homogeneous hOmega).2 hu
    (standardNirenbergTest k h eta u)
    (stdTest_memH01On (d := d) hOmega hu heta heta_cpt k h hroom)
    htest
  rw [DeGiorgi.bilinFormOfCoeff] at hzero
  have htest_grad : ∀ x i, htest.weakGrad x i =
      diffQuot k (-h) (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x := by
    intro x i
    exact stdTest_grad (d := d) hOmega hu heta heta_cpt k h hroom x i
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  simpa [DeGiorgi.bilinFormIntegrandOfCoeff, PiLp.inner_apply,
    DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, hscalar, htest_grad]
    using hzero

/-- A whole-space homogeneous weak solution may be tested against the standard
Nirenberg difference-quotient test, using only its explicit weak-gradient
witness. -/
theorem homSol_subst
    {A : DeGiorgi.EllipticCoeff d (Set.univ : Set E)} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (hu : DeGiorgi.MemW1pWitness 2 u Set.univ)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ) :
    ∫ x, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(volume : Measure E) = 0 := by
  let htest := standardTestWitness (d := d) hu heta heta_cpt k h
  have hzero := (hsol.to_homogeneous isOpen_univ).2 hu
    (standardNirenbergTest k h eta u)
    (standardTest_memH01 (d := d) hu heta heta_cpt k h) htest
  rw [DeGiorgi.bilinFormOfCoeff, setIntegral_univ] at hzero
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  simpa [htest, standardTestWitness, DeGiorgi.bilinFormIntegrandOfCoeff,
    PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct,
    hscalar] using hzero

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
