import DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

/-!
# The interior-regularity test function `D_{-h}^k(η² · D_h^k u)`

This module isolates the algebraic primitives associated with the interior
test function

  `v_test(x) := D_{-h}^k(η² · D_h^k u)(x)`

used to extract second-order regularity for weak solutions of uniformly
elliptic divergence-form equations. The L²-norm bounds and the substitution
into the bilinear form are not addressed here: they are downstream of these
primitives.

## Main definitions

* `nirenbergTestFunction k h η u`: the test function
  `D_{-h}^k(η² · D_h^k u)`.

## Main results

* `contDiff_diffQuot_of_contDiff`, `contDiff_nirenbergTestFunction`: smoothness
  of the difference quotient and of the test function for `h ≠ 0`.
* `hasCompactSupport_translate_of_hasCompactSupport`,
  `hasCompactSupport_diffQuot_of_hasCompactSupport`,
  `hasCompactSupport_nirenbergTestFunction`: compact support is preserved.
* `tsupport_nirenbergTestFunction_subset`: the support of `v_test` lies in
  the closed `|h|`-thickening of `tsupport η`.
* `fderiv_diffQuot_apply_eq_diffQuot_partial`: the directional derivative
  of `D_h^k g` factors as the difference quotient of the directional
  derivative of `g`, when `g` is smooth.
* `fderiv_eta_sq_times_diffQuot_apply`: pointwise product-rule expansion
  of the directional derivative of `η² · D_h^k u`.
* `fderiv_nirenbergTestFunction_apply`: pointwise expansion of the
  directional derivative of `v_test`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Smoothness of difference quotients of smooth functions -/

omit [NeZero d] in
/-- For `h ≠ 0` the forward difference quotient `D_h^k v` of a smooth
function `v` is itself smooth: it equals
`h⁻¹ • ((v ∘ τ_h) - v)` for the smooth translation `τ_h x := x + h • e_k`. -/
theorem contDiff_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) := by
  -- Translation map `y ↦ y + h • e_k` is smooth.
  have h_translate :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => y + h • EuclideanSpace.single k 1) :=
    contDiff_id.add contDiff_const
  -- Composition `y ↦ v(y + h • e_k)` is smooth.
  have h_comp :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => v (y + h • EuclideanSpace.single k 1)) :=
    hv.comp h_translate
  -- Difference is smooth.
  have h_sub :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => v (y + h • EuclideanSpace.single k 1) - v y) :=
    h_comp.sub hv
  -- Division by the constant `h` is smooth.
  have h_div :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) := by
    have heq :
        (fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h) =
          fun y : E =>
            h⁻¹ • (v (y + h • EuclideanSpace.single k 1) - v y) := by
      funext y
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    exact h_sub.const_smul h⁻¹
  -- Identify `diffQuot k h v` with the smooth representative.
  have heq_fun :
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) =
        fun y : E => (v (y + h • EuclideanSpace.single k 1) - v y) / h := by
    funext y
    exact DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh v y
  rw [heq_fun]
  exact h_div

omit [NeZero d] in
/-- The interior-regularity test function `v_test = D_{-h}^k(η² · D_h^k u)`
is smooth whenever `η, u ∈ C^∞(E)` and `h ≠ 0`. -/
theorem contDiff_nirenbergTestFunction_aux
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h)
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y)) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  -- `η y ^ 2` is smooth.
  have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
  -- `D_h^k u` is smooth.
  have h_diffQuot_u :
      ContDiff ℝ (⊤ : ℕ∞)
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  -- Their product is smooth.
  have h_prod :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) :=
    h_eta_sq.mul h_diffQuot_u
  -- Apply `D_{-h}^k` once more.
  exact contDiff_diffQuot_of_contDiff (d := d) h_prod k hnh

/-! ## Compact-support preservation under translation and difference
quotients -/

omit [NeZero d] in
/-- If `v : E → ℝ` has compact support, then so does the translated function
`τ_h v(x) = v(x + h • e_k)`. -/
theorem hasCompactSupport_translate_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.translate k h v) := by
  -- The translation `x ↦ x + h • e_k` is a self-homeomorphism of `E`.
  let φ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  -- `translate k h v = v ∘ φ`.
  have heq :
      DifferentialGeometry.Analysis.Sobolev.translate k h v = v ∘ φ := by
    funext x
    rfl
  rw [heq]
  exact hv.comp_homeomorph φ

omit [NeZero d] in
/-- The forward difference quotient inherits compact support from the
underlying function. -/
theorem hasCompactSupport_diffQuot_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h]
    exact HasCompactSupport.zero
  · -- Rewrite `diffQuot` as `h⁻¹ • (translate − v)`.
    have heq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h v =
          (h⁻¹ : ℝ) •
            (DifferentialGeometry.Analysis.Sobolev.translate k h v - v) := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hh v x]
      change (v (x + h • EuclideanSpace.single k 1) - v x) / h =
        h⁻¹ • (v (x + h • EuclideanSpace.single k 1) - v x)
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    -- Compact support of the difference, then scaled by a constant.
    have h_translate :
        HasCompactSupport
          (DifferentialGeometry.Analysis.Sobolev.translate k h v) :=
      hasCompactSupport_translate_of_hasCompactSupport (d := d) hv k h
    have h_diff :
        HasCompactSupport
          (DifferentialGeometry.Analysis.Sobolev.translate k h v - v) :=
      h_translate.sub hv
    exact h_diff.smul_left

/-! ## The interior-regularity test function -/

/-- The Nirenberg interior-regularity test function:
`v_test(x) := D_{-h}^k(η² · D_h^k u)(x)`. -/
noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : E → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h)
    (fun y : E => η y ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y)

omit [NeZero d] in
/-- Smoothness of the test function for `h ≠ 0`. -/
theorem contDiff_nirenbergTestFunction
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  exact contDiff_nirenbergTestFunction_aux (d := d) hη hu k hh

omit [NeZero d] in
/-- The test function inherits compact support from `η`. -/
theorem hasCompactSupport_nirenbergTestFunction
    {η u : E → ℝ} (hη_supp : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  -- Step 1: `η^2` has compact support.
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y
      ring
    rw [heq]
    exact hη_supp.mul_right
  -- Step 2: the product `η² · D_h^k u` has compact support (left factor).
  have h_prod_supp :
      HasCompactSupport
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) :=
    h_eta_sq_supp.mul_right
  -- Step 3: applying another difference quotient preserves compact support.
  exact hasCompactSupport_diffQuot_of_hasCompactSupport
    (d := d) h_prod_supp k (-h)

/-! ## Localisation of the test function: thickening of `tsupport η` -/

omit [NeZero d] in
/-- Auxiliary: support of the squared cutoff is contained in the support of
the cutoff itself. -/
private lemma support_eta_sq_subset
    (η : E → ℝ) :
    Function.support (fun y : E => η y ^ 2) ⊆ Function.support η := by
  intro y hy
  by_contra hyη
  rw [Function.notMem_support] at hyη
  apply hy
  change η y ^ 2 = 0
  rw [hyη]
  simp

omit [NeZero d] in
/-- Auxiliary: support of `η² · D_h^k u` is contained in `support η`. -/
private lemma support_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    Function.support
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) ⊆
      Function.support η := by
  intro y hy
  -- If the product is nonzero, both factors are nonzero.
  have hsq_ne : η y ^ 2 ≠ 0 := by
    intro hsq
    apply hy
    change η y ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y = 0
    rw [hsq, zero_mul]
  -- So `η y ≠ 0`, i.e. `y ∈ support η`.
  intro hyη
  apply hsq_ne
  rw [hyη]
  simp

omit [NeZero d] in
/-- Auxiliary: `tsupport (η² · D_h^k u) ⊆ tsupport η`. -/
private lemma tsupport_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) ⊆
      tsupport η := by
  exact closure_mono (support_eta_sq_diffQuot_subset (d := d) η u k h)

omit [NeZero d] in
/-- The test function `v_test = D_{-h}^k(η² · D_h^k u)` has support contained
in the closed `|h|`-thickening of `tsupport η`. -/
theorem tsupport_nirenbergTestFunction_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      Metric.cthickening |h| (tsupport η) := by
  unfold nirenbergTestFunction
  -- Notation.
  set g : E → ℝ := fun y : E => η y ^ 2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y with hg_def
  -- We show: `support (D_{-h}^k g) ⊆ cthickening |h| (tsupport η)`.
  -- Then take closures (the thickening is already closed).
  have h_thick_closed : IsClosed (Metric.cthickening |h| (tsupport η)) :=
    isClosed_cthickening
  -- The thickening contains `tsupport η` itself.
  have h_self_subset_thick : tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    self_subset_cthickening _
  -- Distance bound for the shifted point.
  -- For any `y₀ ∈ tsupport η`, the point `y₀ - (-h) • e_k = y₀ + h • e_k`
  -- lies within distance `|h|` of `y₀`.
  have h_shift_in_thick :
      ∀ y₀ ∈ tsupport η,
        y₀ - (-h) • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
    intro y₀ hy₀
    -- Distance from `y₀ + h • e_k` to `tsupport η` is `≤ |h|` because `y₀`
    -- is in `tsupport η` and the displacement is `h • e_k` with norm `|h|`.
    refine Metric.mem_cthickening_of_dist_le _ y₀ |h| (tsupport η) hy₀ ?_
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have hdist_eq :
        dist (y₀ - (-h) • EuclideanSpace.single k 1) y₀ =
          ‖(-h) • EuclideanSpace.single k (1 : ℝ)‖ := by
      rw [dist_eq_norm]
      have :
          (y₀ - (-h) • EuclideanSpace.single k 1) - y₀ =
            -((-h) • EuclideanSpace.single k 1) := by
        rw [sub_right_comm, sub_self, zero_sub]
      rw [this, norm_neg]
    rw [hdist_eq]
    rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs, abs_neg]
  -- Now show: `support (D_{-h}^k g) ⊆ cthickening |h| (tsupport η)`.
  have h_supp_subset :
      Function.support
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) g) ⊆
        Metric.cthickening |h| (tsupport η) := by
    intro x hx
    -- `D_{-h}^k g (x) ≠ 0`.
    have hx_ne : DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) g x ≠ 0 :=
      hx
    by_cases hh : h = 0
    · -- If `h = 0`, the diffQuot is zero everywhere.
      subst hh
      exfalso
      apply hx_ne
      change DifferentialGeometry.Analysis.Sobolev.diffQuot k (-(0 : ℝ)) g x = 0
      have hzeroNeg : (-(0 : ℝ)) = 0 := neg_zero
      rw [hzeroNeg]
      change DifferentialGeometry.Analysis.Sobolev.diffQuot k 0 g x = 0
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h]
      rfl
    · have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
      -- Unpack the diffQuot at `x`.
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hnh g x] at hx_ne
      -- So `(g (x + (-h) • e_k) - g x) / (-h) ≠ 0`.
      -- Hence `g (x + (-h) • e_k) - g x ≠ 0`.
      have hnum_ne : g (x + (-h) • EuclideanSpace.single k 1) - g x ≠ 0 := by
        intro hnum
        apply hx_ne
        rw [hnum, zero_div]
      -- So at least one of the two values is nonzero.
      have h_or :
          g (x + (-h) • EuclideanSpace.single k 1) ≠ 0 ∨ g x ≠ 0 := by
        by_contra hboth
        rw [not_or] at hboth
        obtain ⟨hb1, hb2⟩ := hboth
        have hb1' : g (x + (-h) • EuclideanSpace.single k 1) = 0 :=
          not_not.mp hb1
        have hb2' : g x = 0 := not_not.mp hb2
        apply hnum_ne
        rw [hb1', hb2', sub_zero]
      cases h_or with
      | inl h1 =>
        -- The shifted point is in `support g ⊆ support η ⊆ tsupport η`.
        have h_in_supp_g :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support g :=
          h1
        have h_in_supp_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_supp_g
        have h_in_tsupp_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
          subset_closure h_in_supp_η
        -- Then `x = (x + (-h) e_k) + h e_k = (x + (-h) e_k) - (-h) e_k`.
        -- The shifted point `y₀ := x + (-h) e_k` lies in `tsupport η`.
        -- Apply `h_shift_in_thick` to `y₀ := x + (-h) e_k`:
        --   `y₀ - (-h) • e_k = x ∈ cthickening |h| (tsupport η)`.
        have h_x_eq :
            x =
              (x + (-h) • EuclideanSpace.single k 1) -
                (-h) • EuclideanSpace.single k 1 := by
          rw [add_sub_cancel_right]
        rw [h_x_eq]
        exact h_shift_in_thick _ h_in_tsupp_η
      | inr h2 =>
        -- `x ∈ support g ⊆ support η ⊆ tsupport η`, so in `cthickening`.
        have h_in_supp_g : x ∈ Function.support g := h2
        have h_in_supp_η : x ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_supp_g
        have h_in_tsupp_η : x ∈ tsupport η := subset_closure h_in_supp_η
        exact h_self_subset_thick h_in_tsupp_η
  -- The thickening is closed, so `tsupport ⊆ thickening` from `support ⊆ thickening`.
  exact (closure_minimal h_supp_subset h_thick_closed)

/-! ## Pointwise fderiv expansion -/

omit [NeZero d] in
/-- Translation `y ↦ y + h • e_k` has Fréchet derivative the identity at every
point. -/
private lemma hasFDerivAt_translate (k : Fin d) (h : ℝ) (x : E) :
    HasFDerivAt
      (fun y : E => y + h • EuclideanSpace.single k 1)
      (ContinuousLinearMap.id ℝ E) x := by
  exact (hasFDerivAt_id x).add_const _

omit [NeZero d] in
/-- For smooth `g`, the directional derivative of `D_h^k g` is the difference
quotient of the directional derivative of `g`, when `h ≠ 0`. -/
theorem fderiv_diffQuot_apply_eq_diffQuot_partial
    {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h g) x)
      (EuclideanSpace.single j 1) =
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x := by
  -- Differentiability of `g`.
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  -- `g` has Fréchet derivative `fderiv ℝ g _` at every point.
  have hg_at : ∀ y : E, HasFDerivAt g (fderiv ℝ g y) y :=
    fun y => (hg_diff y).hasFDerivAt
  -- Translation map `τ_h : y ↦ y + h • e_k` has fderiv = id at every `y`.
  have h_translate_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => z + h • EuclideanSpace.single k 1)
        (ContinuousLinearMap.id ℝ E) y :=
    fun y => hasFDerivAt_translate (d := d) k h y
  -- Composition: `y ↦ g(y + h • e_k)` has fderiv `fderiv ℝ g (y + h • e_k)`.
  have h_comp_at : ∀ y : E,
      HasFDerivAt (fun z : E => g (z + h • EuclideanSpace.single k 1))
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1)) y := by
    intro y
    have hcomp :=
      (hg_at (y + h • EuclideanSpace.single k 1)).comp y (h_translate_at y)
    -- `f.comp id = f` modulo defeq via composition of CLMs.
    have heq :
        ((fderiv ℝ g (y + h • EuclideanSpace.single k 1)).comp
          (ContinuousLinearMap.id ℝ E)) =
          fderiv ℝ g (y + h • EuclideanSpace.single k 1) := by
      ext z
      rfl
    rw [heq] at hcomp
    -- `g ∘ τ_h y = g (τ_h y) = g (y + h • e_k)`, defeq.
    exact hcomp
  -- Difference of two FDerivs: `(g ∘ τ_h) - g`.
  have h_diff_at : ∀ y : E,
      HasFDerivAt
        (fun z : E => g (z + h • EuclideanSpace.single k 1) - g z)
        (fderiv ℝ g (y + h • EuclideanSpace.single k 1) - fderiv ℝ g y) y := by
    intro y
    exact (h_comp_at y).sub (hg_at y)
  -- Multiply by the constant `h⁻¹`.
  have h_div_at : ∀ y : E,
      HasFDerivAt
        (fun z : E =>
          (g (z + h • EuclideanSpace.single k 1) - g z) / h)
        (h⁻¹ • (fderiv ℝ g (y + h • EuclideanSpace.single k 1) -
          fderiv ℝ g y)) y := by
    intro y
    have hcs := (h_diff_at y).const_smul h⁻¹
    -- The function in `hcs` is `h⁻¹ • fun z => g(...) - g z`, which equals
    -- `fun z => h⁻¹ • (g(...) - g z) = fun z => (g(...) - g z) / h`.
    have heq_fun :
        (h⁻¹ • fun z : E => g (z + h • EuclideanSpace.single k 1) - g z) =
          fun z : E =>
            (g (z + h • EuclideanSpace.single k 1) - g z) / h := by
      funext z
      change h⁻¹ • (g (z + h • EuclideanSpace.single k 1) - g z) =
        (g (z + h • EuclideanSpace.single k 1) - g z) / h
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq_fun] at hcs
    exact hcs
  -- Identify `diffQuot k h g` with this representative.
  have heq_diffQuot :
      (DifferentialGeometry.Analysis.Sobolev.diffQuot k h g) =
        fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h := by
    funext y
    exact DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := d) k hh g y
  rw [heq_diffQuot]
  -- The fderiv of `(g ∘ τ_h - g)/h` at `x` is the explicit one.
  have h_at : HasFDerivAt
      (fun y : E => (g (y + h • EuclideanSpace.single k 1) - g y) / h)
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
        fderiv ℝ g x)) x := h_div_at x
  rw [h_at.fderiv]
  -- Apply to `EuclideanSpace.single j 1`.
  -- `(h⁻¹ • (A - B)) v = h⁻¹ • ((A - B) v) = h⁻¹ * ((A v) - (B v))`.
  set ej : E := EuclideanSpace.single j 1 with hej
  have h_apply :
      (h⁻¹ • (fderiv ℝ g (x + h • EuclideanSpace.single k 1) -
          fderiv ℝ g x)) ej =
        h⁻¹ • ((fderiv ℝ g (x + h • EuclideanSpace.single k 1)) ej -
          (fderiv ℝ g x) ej) := by
    rw [ContinuousLinearMap.smul_apply]
    rw [ContinuousLinearMap.sub_apply]
  rw [h_apply]
  -- And expressing diffQuot of the partial derivative:
  rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
    (d := d) k hh _ x]
  rw [div_eq_inv_mul, smul_eq_mul]

omit [NeZero d] in
/-- Pointwise expansion of the directional derivative of
`y ↦ η(y)² · D_h^k u(y)`:
`∂_j (η² · D_h^k u) = 2η · ∂_j η · D_h^k u + η² · D_h^k(∂_j u)`. -/
theorem fderiv_eta_sq_times_diffQuot_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
      (EuclideanSpace.single j 1) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x +
      η x ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x := by
  -- Differentiability of relevant pieces.
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hη_sq_diff : Differentiable ℝ (fun y : E => η y ^ 2) :=
    (hη.pow 2).differentiable (by simp)
  have h_diffQuot_u_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  have h_diffQuot_u_diff :
      Differentiable ℝ
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    h_diffQuot_u_smooth.differentiable (by simp)
  -- Goal: expand the fderiv of the product.
  set ej : E := EuclideanSpace.single j 1 with hej
  -- Use the product rule: `fderiv (η^2 · q) x = (η x)^2 • fderiv q x +
  --   q x • fderiv (η^2) x` (where we use `c • d` form which for ℝ-valued
  --   pointwise is `(η x)^2 * fderiv q x + q x * fderiv (η^2) x` after applying).
  have h_prod :
      fderiv ℝ
          (fun y : E => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x =
        η x ^ 2 •
          fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) x +
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x •
            fderiv ℝ (fun y : E => η y ^ 2) x := by
    exact fderiv_fun_mul (hη_sq_diff x) (h_diffQuot_u_diff x)
  -- Apply both sides to `ej`.
  -- LHS unchanged after rewriting; RHS becomes a sum.
  rw [h_prod]
  -- Apply CLMs to ej.
  rw [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
  -- The fderiv of `η^2`:
  -- `fderiv (η^2) x = (2 • η x ^ (2-1)) • fderiv η x = 2 (η x) • fderiv η x`.
  have hη_pow_fd :
      fderiv ℝ (fun y : E => η y ^ 2) x =
        ((2 : ℕ) • (η x) ^ ((2 : ℕ) - 1)) • fderiv ℝ η x :=
    fderiv_fun_pow 2 (hη_diff x)
  rw [hη_pow_fd]
  -- Compute `(2 • η x ^ 1) • fderiv η x` applied to `ej`:
  -- `((2 : ℕ) • (η x) ^ 1) • fderiv η x ej = (2 * η x) • fderiv η x ej`.
  rw [ContinuousLinearMap.smul_apply]
  -- Convert `(2 : ℕ) • r` to `2 * r` and `r ^ ((2 : ℕ) - 1)` to `r`.
  have hpow1 : (η x) ^ ((2 : ℕ) - 1) = η x := by
    norm_num
  rw [hpow1]
  -- We now have, on the RHS:
  --   η x ^ 2 • fderiv (D_h^k u) x ej +
  --   D_h^k u x • ((2 : ℕ) • η x) • fderiv η x ej
  -- Convert to multiplications and rearrange to match the goal.
  -- Use the helper that fderiv (D_h^k u) x ej = D_h^k (∂_j u) x.
  have h_fderiv_diffQuot :
      (fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) x) ej =
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x :=
    fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hu k j hh x
  rw [h_fderiv_diffQuot]
  -- Now combine everything.
  -- The goal becomes (after smul_eq_mul, etc.):
  --   η x ^ 2 * D_h^k(∂_j u) x +
  --   D_h^k u x * (2 * η x * fderiv η x ej) =
  --   2 η x * fderiv η x ej * D_h^k u x + η x ^ 2 * D_h^k(∂_j u) x
  -- which is just commutativity / associativity.
  -- Convert smul to mul.
  have h_two_smul : ((2 : ℕ) • η x) = 2 * η x := by
    change 2 • η x = 2 * η x
    rw [two_smul]
    ring
  rw [h_two_smul]
  -- Convert all `•` to `*` and rearrange.
  change η x ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x *
        (2 * η x * (fderiv ℝ η x) ej) =
      2 * η x * (fderiv ℝ η x) ej *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x +
      η x ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x
  ring

omit [NeZero d] in
/-- Pointwise directional-derivative expansion of the test function. -/
theorem fderiv_nirenbergTestFunction_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ (nirenbergTestFunction k h η u) x)
        (EuclideanSpace.single j 1) =
      DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h)
        (fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y +
          η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y)
        x := by
  unfold nirenbergTestFunction
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  -- Define `g := y ↦ η y ^ 2 * D_h^k u y`. It is smooth.
  have hg_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) := by
    have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h_diffQuot_u :
        ContDiff ℝ (⊤ : ℕ∞)
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact h_eta_sq.mul h_diffQuot_u
  -- Apply `fderiv_diffQuot_apply_eq_diffQuot_partial` to `g` with step `-h`.
  rw [fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hg_smooth k j hnh x]
  -- Inside the diffQuot: rewrite the integrand pointwise via the product rule.
  -- The integrand of the diffQuot at point `y` is
  -- `(fderiv ℝ g y) (single j 1)`, which we expand as the sum from
  -- `fderiv_eta_sq_times_diffQuot_apply`.
  have h_pointwise :
      (fun y : E =>
          (fderiv ℝ
              (fun z : E => η z ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot k h u z) y)
            (EuclideanSpace.single j 1)) =
        fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y +
          η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y := by
    funext y
    exact fderiv_eta_sq_times_diffQuot_apply (d := d) hη hu k j hh y
  rw [h_pointwise]

/-! ## Sanity examples -/

example {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k 1 η u) :=
  contDiff_nirenbergTestFunction hη hu k one_ne_zero

example {η : E → ℝ} (hη_supp : HasCompactSupport η) (u : E → ℝ)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) :=
  hasCompactSupport_nirenbergTestFunction hη_supp k h

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
