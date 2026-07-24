import DifferentialGeometry.Analysis.ODE.IndexFormUniqueness

set_option autoImplicit false

/-!
# Negative directions for the abstract index form

This module develops the continuation lemmas used to turn an interior zero of
a nontrivial Jacobi solution into a negative direction for the index form.
It is independent of the geometric realization by a parallel frame.
-/

open Set
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The polynomial test field used in the interior conjugate-point argument. -/
def indexTestField (q : F) (t : ℝ) : F :=
  (t * (1 - t)) • q

/-- The derivative of `indexTestField`. -/
def indexTestDeriv (q : F) (t : ℝ) : F :=
  (1 - 2 * t) • q

/-- Derivative formula for the polynomial index-form test field. -/
theorem indexTestField_deriv (q : F) (t : ℝ) :
    HasDerivAt (indexTestField q) (indexTestDeriv q t) t := by
  have hscalar :
      HasDerivAt (fun s : ℝ => s * (1 - s)) (1 - 2 * t) t := by
    convert (hasDerivAt_id t).mul
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) using 1
    simp
    ring
  simpa only [indexTestField, indexTestDeriv] using hscalar.smul_const q

/-- The polynomial index-form test field is continuous. -/
theorem indexTestField_cont (q : F) : Continuous (indexTestField q) := by
  unfold indexTestField
  fun_prop

/-- The derivative field of the polynomial test field is continuous. -/
theorem indexTestDeriv_cont (q : F) : Continuous (indexTestDeriv q) := by
  unfold indexTestDeriv
  fun_prop

/-- A polynomial index-form test field is smooth. -/
theorem testField_smooth (q : F) :
    ContDiff ℝ ∞ (indexTestField q) := by
  unfold indexTestField
  fun_prop

/-- On an open time set, a Jacobi ODE solution is as smooth as its smooth
coefficient. -/
theorem contDiffOn_jacobi
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J)
    (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t)
    (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n v J := by
  have hdy : DifferentiableOn ℝ y J :=
    fun t ht => (hy t ht).differentiableAt.differentiableWithinAt
  have hdv : DifferentiableOn ℝ v J :=
    fun t ht => (hv t ht).differentiableAt.differentiableWithinAt
  have hddy : ∀ t ∈ J, deriv y t = v t :=
    fun t ht => (hy t ht).deriv
  have hddv : ∀ t ∈ J, deriv v t = -(R t) (y t) :=
    fun t ht => (hv t ht).deriv
  induction n with
  | zero =>
      exact
        ⟨contDiffOn_zero.mpr hdy.continuousOn,
          contDiffOn_zero.mpr hdv.continuousOn⟩
  | succ n ih =>
      obtain ⟨hyn, hvn⟩ := ih
      have hRn : ContDiffOn ℝ n R J := contDiffOn_infty.mp hR n
      have hderiv_y : ContDiffOn ℝ n (deriv y) J :=
        hvn.congr hddy
      have hderiv_v : ContDiffOn ℝ n (deriv v) J :=
        ((hRn.clm_apply hyn).neg).congr hddv
      exact
        ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr
            ⟨hdy, by simp, hderiv_y⟩,
          (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr
            ⟨hdv, by simp, hderiv_v⟩⟩

/-- A Jacobi ODE pair with smooth coefficient and two-sided derivatives is
smooth on its open time domain. -/
theorem jacobi_pair_contDiff
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J)
    (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t) :
    ContDiffOn ℝ ∞ y J ∧ ContDiffOn ℝ ∞ v J :=
  ⟨contDiffOn_infty.mpr fun n => (contDiffOn_jacobi hJ hR hy hv n).1,
    contDiffOn_infty.mpr fun n => (contDiffOn_jacobi hJ hR hy hv n).2⟩

private theorem exists_quad_neg {κ Q : ℝ} (hκ : 0 < κ) :
    ∃ s : ℝ, 2 * s * κ + s ^ 2 * Q < 0 := by
  have hden : 0 < |Q| + 1 := by positivity
  let s : ℝ := -κ / (|Q| + 1)
  have hsneg : s < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hκ) hden
  have hsQ : |s * Q| < κ := by
    simp only [s]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hκ, abs_of_pos hden,
      div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg Q]
  have hsum : 0 < 2 * κ + s * Q := by
    linarith [(abs_lt.mp hsQ).1]
  refine ⟨s, ?_⟩
  calc
    2 * s * κ + s ^ 2 * Q = s * (2 * κ + s * Q) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hsneg hsum

namespace IsJacobiSolOn

/-- A Jacobi solution restricts to every smaller closed subinterval. -/
theorem mono
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {a b a' b' : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsJacobiSolOn R a' b' y v := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact
    { deriv_fst := fun t ht => (hsol.deriv_fst t (hsub ht)).mono hsub
      deriv_snd := fun t ht => (hsol.deriv_snd t (hsub ht)).mono hsub }

/-- A nontrivial Jacobi solution that vanishes at an interior time has
nonzero velocity there. -/
theorem snd_ne_zero
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {a b c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v)
    (hc : c ∈ Ioo a b)
    (hR : ContinuousOn R (Icc a b))
    (hyc : y c = 0)
    (hne : ∃ t ∈ Icc a b, y t ≠ 0) :
    v c ≠ 0 := by
  have hnorm : ContinuousOn (fun t : ℝ => ‖R t‖) (Icc a b) :=
    continuous_norm.comp_continuousOn hR
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hRbound : ∀ t ∈ Icc a b, ‖R t‖ ≤ max C 0 := by
    intro t ht
    exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  intro hvc
  have hzero := hsol.eq_zero_of_interior hc hC0 hRbound hyc hvc
  obtain ⟨t, ht, hyt⟩ := hne
  exact hyt (hzero t ht).1

/-- The cross term of a Jacobi solution with the polynomial test field is its
right-end velocity norm squared times `c(1-c)`. -/
theorem indexForm_test
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 c y v)
    (hc : 0 ≤ c)
    (hR : ContinuousOn R (Icc 0 c)) :
    indexForm R 0 c y v (indexTestField (v c)) (indexTestDeriv (v c))
      = c * (1 - c) * ‖v c‖ ^ 2 := by
  rw [hsol.indexForm_eq_sub hc hR
    (fun t _ => (indexTestField_deriv (v c) t).hasDerivWithinAt)
    (by
      unfold indexTestDeriv
      fun_prop)]
  simp [indexTestField, real_inner_smul_right]

/-- At an interior time of `[0,1]`, a nonzero Jacobi velocity makes the
polynomial-test-field cross term strictly positive. -/
theorem indexForm_test_pos
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 c y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Icc 0 c))
    (hvc : v c ≠ 0) :
    0 < indexForm R 0 c y v
      (indexTestField (v c)) (indexTestDeriv (v c)) := by
  rw [hsol.indexForm_test hc.1.le hR]
  have hnorm : 0 < ‖v c‖ := norm_pos_iff.mpr hvc
  exact mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (sq_pos_of_pos hnorm)

/-- An interior zero of a nontrivial Jacobi solution produces a negative
split index direction.  The two fields are smooth on their respective
subintervals and agree in value at the splitting time. -/
theorem exists_split_neg
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R 0 1 y v)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContinuousOn R (Icc 0 1))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ s : ℝ,
      indexForm R 0 c
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
        + indexForm R c 1
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c)) < 0 := by
  have hsol0c : IsJacobiSolOn R 0 c y v :=
    hsol.mono le_rfl hc.2.le
  have hR0c : ContinuousOn R (Icc 0 c) :=
    hR.mono (Icc_subset_Icc le_rfl hc.2.le)
  have hRc1 : ContinuousOn R (Icc c 1) :=
    hR.mono (Icc_subset_Icc hc.1.le le_rfl)
  have hvc : v c ≠ 0 :=
    hsol.snd_ne_zero hc hR hyc hne
  have hcross : 0 < indexForm R 0 c y v
      (indexTestField (v c)) (indexTestDeriv (v c)) :=
    hsol0c.indexForm_test_pos hc hR0c hvc
  have hself : indexForm R 0 c y v y v = 0 :=
    hsol0c.indexForm_self_zero hc.1.le hR0c hy0 hyc
  have hyy : IntervalIntegrable
      (indexIntegrand R y v y v) MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.1.le] using hR0c)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
  have hyz : IntervalIntegrable
      (indexIntegrand R y v
        (indexTestField (v c)) (indexTestDeriv (v c)))
      MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.1.le] using hR0c)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_fst)
      (by simpa only [uIcc_of_le hc.1.le] using hsol0c.contOn_snd)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
  have hzz0c : IntervalIntegrable
      (indexIntegrand R
        (indexTestField (v c)) (indexTestDeriv (v c))
        (indexTestField (v c)) (indexTestDeriv (v c)))
      MeasureTheory.volume 0 c :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.1.le] using hR0c)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.1.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
  have hzzc1 : IntervalIntegrable
      (indexIntegrand R
        (indexTestField (v c)) (indexTestDeriv (v c))
        (indexTestField (v c)) (indexTestDeriv (v c)))
      MeasureTheory.volume c 1 :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.2.le] using hRc1)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
  have hzero_cont : Continuous (fun _ : ℝ => (0 : F)) := continuous_const
  have h00 : IntervalIntegrable
      (indexIntegrand R (fun _ => 0) (fun _ => 0)
        (fun _ => 0) (fun _ => 0))
      MeasureTheory.volume c 1 :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.2.le] using hRc1)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
  have h0z : IntervalIntegrable
      (indexIntegrand R (fun _ => 0) (fun _ => 0)
        (indexTestField (v c)) (indexTestDeriv (v c)))
      MeasureTheory.volume c 1 :=
    intInt_indexIntegrand
      (by simpa only [uIcc_of_le hc.2.le] using hRc1)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by simpa only [uIcc_of_le hc.2.le] using hzero_cont.continuousOn)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestField_cont (v c)).continuousOn)
      (by
        simpa only [uIcc_of_le hc.2.le] using
          (indexTestDeriv_cont (v c)).continuousOn)
  have hleft (s : ℝ) :
      indexForm R 0 c
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
        = indexForm R 0 c y v y v
          + 2 * s * indexForm R 0 c y v
            (indexTestField (v c)) (indexTestDeriv (v c))
          + s ^ 2 * indexForm R 0 c
            (indexTestField (v c)) (indexTestDeriv (v c))
            (indexTestField (v c)) (indexTestDeriv (v c)) :=
    indexForm_add_smul hSym hyy hyz hzz0c s
  have hright (s : ℝ) :
      indexForm R c 1
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
        = s ^ 2 * indexForm R c 1
            (indexTestField (v c)) (indexTestDeriv (v c))
            (indexTestField (v c)) (indexTestDeriv (v c)) := by
    have h := indexForm_add_smul
      (R := R) (a := c) (b := 1)
      (y := fun _ => (0 : F)) (v := fun _ => (0 : F))
      (z := indexTestField (v c)) (w := indexTestDeriv (v c))
      hSym h00 h0z hzzc1 s
    simpa [indexForm, indexIntegrand] using h
  let κ : ℝ := indexForm R 0 c y v
    (indexTestField (v c)) (indexTestDeriv (v c))
  let Q : ℝ :=
    indexForm R 0 c
        (indexTestField (v c)) (indexTestDeriv (v c))
        (indexTestField (v c)) (indexTestDeriv (v c))
      + indexForm R c 1
        (indexTestField (v c)) (indexTestDeriv (v c))
        (indexTestField (v c)) (indexTestDeriv (v c))
  have hκ : 0 < κ := by simpa only [κ] using hcross
  obtain ⟨s, hs⟩ := exists_quad_neg hκ (Q := Q)
  refine ⟨s, ?_⟩
  calc
    indexForm R 0 c
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
          (y + s • indexTestField (v c))
          (v + s • indexTestDeriv (v c))
        + indexForm R c 1
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
          (s • indexTestField (v c))
          (s • indexTestDeriv (v c))
        = 2 * s * κ + s ^ 2 * Q := by
          rw [hleft s, hright s, hself]
          simp only [zero_add]
          dsimp only [κ, Q]
          ring
    _ < 0 := hs

/-- A Jacobi solution on an open interval containing `[0,1]` produces two
smooth, value-matching half-fields whose index forms have negative sum. -/
theorem exists_smooth_split
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {A B c : ℝ} {y v : ℝ → F}
    (hA : A < 0) (hB : 1 < B)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hR : ContDiffOn ℝ ∞ R (Ioo A B))
    (hSym : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : ∀ t ∈ Ioo A B, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Ioo A B, HasDerivAt v (-(R t) (y t)) t)
    (hy0 : y 0 = 0) (hyc : y c = 0)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, y t ≠ 0) :
    ∃ W₀ W₁ : ℝ → F,
      ContDiffOn ℝ ∞ W₀ (Ioo A B)
        ∧ ContDiff ℝ ∞ W₁
        ∧ W₀ 0 = 0
        ∧ W₁ 1 = 0
        ∧ W₀ c = W₁ c
        ∧ indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀)
          + indexForm R c 1 W₁ (deriv W₁) W₁ (deriv W₁) < 0 := by
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo A B := by
    intro t ht
    exact ⟨hA.trans_le ht.1, ht.2.trans_lt hB⟩
  have hR01 : ContinuousOn R (Icc (0 : ℝ) 1) :=
    hR.continuousOn.mono h01
  have hsol : IsJacobiSolOn R 0 1 y v :=
    { deriv_fst := fun t ht => (hy t (h01 ht)).hasDerivWithinAt
      deriv_snd := fun t ht => (hv t (h01 ht)).hasDerivWithinAt }
  obtain ⟨s, hs⟩ :=
    hsol.exists_split_neg hc hR01 hSym hy0 hyc hne
  let Z : ℝ → F := indexTestField (v c)
  let DZ : ℝ → F := indexTestDeriv (v c)
  have hZd : ∀ t, HasDerivAt Z (DZ t) t := by
    intro t
    exact indexTestField_deriv (v c) t
  have hW₀d : ∀ t ∈ Ioo A B,
      HasDerivAt (y + s • Z) (v t + s • DZ t) t := by
    intro t ht
    exact (hy t ht).add ((hZd t).const_smul s)
  have hdW₀ : ∀ t ∈ Ioo A B,
      deriv (y + s • Z) t = (v + s • DZ) t := by
    intro t ht
    simpa only [Pi.add_apply, Pi.smul_apply] using (hW₀d t ht).deriv
  have hdW₁ : ∀ t,
      deriv (s • Z) t = (s • DZ) t := by
    intro t
    simpa only [Pi.smul_apply] using ((hZd t).const_smul s).deriv
  have hySmooth : ContDiffOn ℝ ∞ y (Ioo A B) :=
    (jacobi_pair_contDiff isOpen_Ioo hR hy hv).1
  have hZSmooth : ContDiff ℝ ∞ Z := by
    exact testField_smooth (v c)
  have hW₀Smooth : ContDiffOn ℝ ∞ (y + s • Z) (Ioo A B) :=
    hySmooth.add (hZSmooth.const_smul s).contDiffOn
  have hW₁Smooth : ContDiff ℝ ∞ (s • Z) :=
    hZSmooth.const_smul s
  have h0c : Icc (0 : ℝ) c ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc le_rfl hc.2.le
  have hsub0c : Icc (0 : ℝ) c ⊆ Ioo A B :=
    h0c.trans h01
  have e₀ :
      indexForm R 0 c (y + s • Z) (deriv (y + s • Z))
          (y + s • Z) (deriv (y + s • Z))
        = indexForm R 0 c (y + s • Z) (v + s • DZ)
          (y + s • Z) (v + s • DZ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.1.le] at ht
    simp only [indexIntegrand]
    rw [hdW₀ t (hsub0c ht)]
  have e₁ :
      indexForm R c 1 (s • Z) (deriv (s • Z))
          (s • Z) (deriv (s • Z))
        = indexForm R c 1 (s • Z) (s • DZ)
          (s • Z) (s • DZ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [indexIntegrand]
    rw [hdW₁ t]
  refine ⟨y + s • Z, s • Z, hW₀Smooth, hW₁Smooth, ?_, ?_, ?_, ?_⟩
  · simp [Z, indexTestField, hy0]
  · simp [Z, indexTestField]
  · simp [hyc]
  · rw [e₀, e₁]
    exact hs

end IsJacobiSolOn

end DifferentialGeometry.Analysis.ODE
