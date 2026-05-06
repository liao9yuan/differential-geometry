import DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution

/-!
# Coercivity expansion of the substitution identity

Starting from the substitution identity

  `-∑ i j ∫ D_h^k (a^{ij} ∂_i u) · ∂_j (η² · D_h^k u) + ∫_Ω c · u · v_test
    = ∫_Ω f · v_test`

(produced in `NirenbergSubstitution.nirenberg_substitution_identity`), we
expand the principal term using the discrete product rule for difference
quotients

  `D_h^k (a^{ij} ∂_i u)(x) =
    (τ_h a^{ij})(x) · D_h^k(∂_i u)(x) + (D_h^k a^{ij})(x) · ∂_i u(x)`

and the partial-derivative formula for `η² · D_h^k u`

  `∂_j (η² · D_h^k u)(x) =
    2 η(x) · ∂_j η(x) · D_h^k u(x) + η(x)² · D_h^k(∂_j u)(x)`.

Multiplying these two expansions yields four explicit terms per `(i, j)`
pair. The principal term, with coefficient `(τ_h a^{ij})(x) · η²(x)`, is
controlled below by ellipticity at the shifted point. The remaining three
"cross" terms are bounded by absolute values, ready for downstream
estimation.

## Main outputs

* `principalIntegrand_at_translate_self_ge`: pointwise ellipticity at the
  shifted point `x + h e_k`, applied to the difference-quotient gradient
  `D_h^k ∇u(x)`.
* `nirenberg_principal_decomposition`: identity expressing the principal
  LHS of the substitution identity as `PRINCIPAL_term - CROSS_1 - CROSS_2 -
  CROSS_3`.
* `principal_term_ge_lambda_norm_sq`: integral lower bound
  `λ ∫ η² ‖D_h^k ∇u‖² ≤ PRINCIPAL_term`.
* `nirenberg_master_inequality`: the headline bound
  `λ ∫ η² ‖D_h^k ∇u‖² ≤ |Cross_1| + |Cross_2| + |Cross_3| +
    |∫ f · v_test| + |∫ c u · v_test|`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitution
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergCoercivity

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Section 1: Pointwise ellipticity at the shifted point -/

/-- The "shifted-coefficient principal integrand" at `x`: the quadratic form
`∑ i j a^{ij}(x + h e_k) · ξ_i · ξ_j`, evaluated with
`ξ_i := D_h^k(∂_i u)(x)`. This is the integrand of `PRINCIPAL_term` modulo
the factor `η(x)²`. -/
private def shiftedPrincipal
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    DifferentialGeometry.Analysis.Sobolev.translate k h
      (fun y : E => B.a y i j) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x

/-- The Euclidean vector `D_h^k ∇u(x) ∈ E`: the difference quotient applied
componentwise to the gradient of `u`. -/
private def diffQuotGradient
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i : Fin d =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)

omit [NeZero d] in
/-- The Euclidean norm squared of the difference-quotient gradient equals
the sum of squares of its components. -/
private lemma diffQuotGradient_norm_sq
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) :
    ‖diffQuotGradient u k h x‖ ^ 2 =
      ∑ i : Fin d,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 := by
  unfold diffQuotGradient
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ‖DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

/-- Pointwise ellipticity at the shifted point: when the shifted point
`x + h e_k` lies in `Ω`, the quadratic form

  `∑ i j a^{ij}(x + h e_k) · D_h^k(∂_i u)(x) · D_h^k(∂_j u)(x)`

is bounded below by `λ · ‖D_h^k ∇u(x)‖²`. -/
private theorem shiftedPrincipal_ge
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (k : Fin d) (h : ℝ) {x : E}
    (hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω) :
    B.lam * ‖diffQuotGradient u k h x‖ ^ 2 ≤
      shiftedPrincipal B u k h x := by
  classical
  -- Set abbreviation for the shifted point.
  set y : E := x + h • EuclideanSpace.single k 1 with hy_def
  -- Abbreviate the gradient vector at `x`.
  set ξ : E := diffQuotGradient u k h x with hξ_def
  -- The components of ξ.
  set V : Fin d → ℝ := fun i =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x with hV_def
  -- ξ.ofLp = V (by `gradientVec` definition style).
  have hξofLp : ξ.ofLp = V := by simp [hξ_def, hV_def, diffQuotGradient]
  -- Coercivity of `B.a y` against ξ.
  have hcoer : B.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ :=
    B.coercive y hx_translate ξ
  -- The inner product expands to `(B.a y).mulVec V ⬝ᵥ V`.
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ =
        ∑ i : Fin d, ∑ j : Fin d,
          B.a y i j * V i * V j := by
    -- Standard identification, mirroring `principalIntegrand_self_eq_inner`.
    have hmatofLp : (DeGiorgi.matMulE (B.a y) ξ).ofLp = (B.a y).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξofLp]
    change (DeGiorgi.matMulE (B.a y) ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [hmatofLp, hξofLp]
    -- Over ℝ, star V = V.
    have hstarV : (star V : Fin d → ℝ) = V := by
      funext i; simp
    rw [hstarV]
    -- Now expand `mulVec V ⬝ᵥ V` to a double sum, with summation order
    -- matching the goal statement.
    -- (mulVec V) i = ∑ j, B.a y i j * V j; then dotProduct sums over i.
    change ∑ i : Fin d, (B.a y).mulVec V i * V i = _
    refine Finset.sum_congr rfl ?_
    intro i _
    change (∑ j : Fin d, B.a y i j * V j) * V i = ∑ j : Fin d, B.a y i j * V i * V j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  -- Convert the abbreviated `shiftedPrincipal` to the matched double sum.
  have h_target :
      shiftedPrincipal B u k h x =
        ∑ i : Fin d, ∑ j : Fin d, B.a y i j * V i * V j := by
    unfold shiftedPrincipal
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    -- `translate k h (fun y => B.a y i j) x = B.a (x + h • e_k) i j = B.a y i j`.
    change DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun z : E => B.a z i j) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) x =
          B.a y i j * V i * V j
    rfl
  rw [h_target]
  rw [h_inner] at hcoer
  exact hcoer

/-! ## Section 2: Pointwise expansion of the principal integrand -/

/-- Pointwise expansion of `D_h^k(a^{ij} ∂_i u) · ∂_j(η² · D_h^k u)` as a
sum of four explicit terms. -/
private theorem principal_integrand_pointwise_decomposition
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1)) =
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
      2 * DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
      2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x := by
  -- Step 1. Expand the LHS first factor via `diffQuot_coeff_apply`.
  have h_first : DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x =
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x +
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    diffQuot_coeff_apply (d := d) k h
      (fun y : E => B.a y i j)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x
  -- Step 2. Expand the LHS second factor via `fderiv_eta_sq_times_diffQuot_apply`.
  have h_second :
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1)) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x +
      η x ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x :=
    fderiv_eta_sq_times_diffQuot_apply (d := d) hη hu k j hh x
  -- Now apply both rewrites and expand by `ring`.
  rw [h_first, h_second]
  ring

/-! ## Section 3: Pointwise integrability of each cross term -/

omit [NeZero d] in
/-- `D_h^k v` of a smooth `v` is itself continuous (a special case of
`contDiff_diffQuot_of_contDiff` and `ContDiff.continuous`). -/
private lemma continuous_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) (h : ℝ) :
    Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h]
    exact continuous_const
  · exact (contDiff_diffQuot_of_contDiff (d := d) hv k hh).continuous

omit [NeZero d] in
/-- The translation `τ_h v` is continuous when `v` is. -/
private lemma continuous_translate_of_continuous
    {v : E → ℝ} (hv : Continuous v) (k : Fin d) (h : ℝ) :
    Continuous (DifferentialGeometry.Analysis.Sobolev.translate k h v) := by
  unfold DifferentialGeometry.Analysis.Sobolev.translate
  have h_translate_map :
      Continuous (fun y : E => y + h • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  exact hv.comp h_translate_map

/-! ## Section 4: The principal LHS decomposition (integral form) -/

/-- The principal LHS of the substitution identity decomposes into a sum of
four explicit integrals. Specifically:

`-∑ i j ∫ D_h^k(a^{ij} ∂_i u) · ∂_j(η² D_h^k u)
  = -PRINCIPAL_term - CROSS_1 - CROSS_2 - CROSS_3`,

where each piece is an explicit double sum of integrals. -/
theorem nirenberg_principal_decomposition
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j *
              ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ
              (fun y : E => η y ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)) := by
  classical
  -- Continuity / compact-support facts.
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  -- η² compact support.
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]
    exact hη_supp.mul_right
  -- For the integrability of each cross integrand, we exhibit a compact
  -- support coming from η (or from a factor thereof).
  -- Step 1 — pointwise: each (i, j) integrand decomposes into 4 terms.
  -- Step 2 — sum of 4 integrals: linearity of integration on each (i, j).
  -- Step 3 — exchange ∑_{i, j} with ∫: routine, given integrability.
  -- We organise via a per-pair lemma.
  have h_pair : ∀ i j : Fin d, ∀ x : E,
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j *
              ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ
              (fun y : E => η y ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
            (EuclideanSpace.single j 1)) =
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
        2 * DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x +
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x := by
    intro i j x
    exact principal_integrand_pointwise_decomposition (d := d) B hu hη i j k hh x
  -- Define the four pointwise "cross" integrand functions, per (i, j).
  let T1 : Fin d → Fin d → E → ℝ := fun i j x =>
    DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : E => B.a y i j) x * (η x)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
  let T2 : Fin d → Fin d → E → ℝ := fun i j x =>
    2 * DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : E => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
  let T3 : Fin d → Fin d → E → ℝ := fun i j x =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
  let T4 : Fin d → Fin d → E → ℝ := fun i j x =>
    2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
  -- LHS integrand:
  let LHSint : Fin d → Fin d → E → ℝ := fun i j x =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1))
  -- Pointwise decomposition.
  have h_LHS_eq : ∀ i j : Fin d, ∀ x : E,
      LHSint i j x = T1 i j x + T2 i j x + T3 i j x + T4 i j x := h_pair
  -- Continuity facts for each Tk.
  -- (a) `B.a y i j` is smooth, hence continuous; `translate k h` of it is continuous.
  -- (b) `fderiv u y (e_i)`, `fderiv η y (e_j)` are continuous.
  -- (c) `diffQuot k h v` for smooth v is continuous.
  -- All four T_k are products of these.
  have h_a_cont : ∀ i j : Fin d, Continuous (fun y : E => B.a y i j) :=
    fun i j => B.continuous_a i j
  have h_translate_a_cont : ∀ i j : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_translate_of_continuous (d := d)
      (h_a_cont i j) k h
  have h_partial_u_cont : ∀ i : Fin d,
      Continuous (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    fun i => (hu_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_partial_η_cont : ∀ j : Fin d,
      Continuous (fun y : E => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    fun j => (hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_diffQuot_partial_u_cont : ∀ i : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    intro i
    have h_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_of_contDiff (d := d) h_smooth k h
  have h_diffQuot_a_cont : ∀ i j : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_diffQuot_of_contDiff (d := d) (B.contDiff_a i j) k h
  have h_diffQuot_u_cont :
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u) :=
    continuous_diffQuot_of_contDiff (d := d) hu k h
  -- Continuity of each T.
  have hT1_cont : ∀ i j : Fin d, Continuous (T1 i j) := by
    intro i j
    refine ((((h_translate_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_diffQuot_partial_u_cont i)).mul
      (h_diffQuot_partial_u_cont j))
  have hT2_cont : ∀ i j : Fin d, Continuous (T2 i j) := by
    intro i j
    refine (((((continuous_const : Continuous (fun _ : E => (2 : ℝ))).mul
      (h_translate_a_cont i j)).mul hη.continuous).mul
      (h_partial_η_cont j)).mul (h_diffQuot_partial_u_cont i)).mul
      h_diffQuot_u_cont
  have hT3_cont : ∀ i j : Fin d, Continuous (T3 i j) := by
    intro i j
    refine ((((h_diffQuot_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_partial_u_cont i)).mul (h_diffQuot_partial_u_cont j))
  have hT4_cont : ∀ i j : Fin d, Continuous (T4 i j) := by
    intro i j
    refine (((((continuous_const : Continuous (fun _ : E => (2 : ℝ))).mul
      (h_diffQuot_a_cont i j)).mul hη.continuous).mul
      (h_partial_η_cont j)).mul (h_partial_u_cont i)).mul h_diffQuot_u_cont
  -- LHSint is continuous (as sum of T1..T4 by pointwise equality).
  have hLHS_cont_via_eq : ∀ i j : Fin d, Continuous (LHSint i j) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    exact (((hT1_cont i j).add (hT2_cont i j)).add (hT3_cont i j)).add
      (hT4_cont i j)
  -- Compact support via η for T1, T3 (containing η²), T2, T4 (containing η).
  -- T1, T3 have factor (η x)^2; T2, T4 have factor (η x).
  have hT1_supp : ∀ i j : Fin d, HasCompactSupport (T1 i j) := by
    intro i j
    -- T1 i j x = A * (η x)^2 * B * C, so T1 i j = ((A * η^2) * B) * C
    -- η^2 has compact support, hence (·) * η^2 has compact support, ...
    have h_factor_supp : HasCompactSupport (fun x : E => (η x)^2) := h_eta_sq_supp
    -- (η^2) is the second factor in the product chain.
    -- The full T1 i j x is `(translate a) * η² * dq(∂u_i) * dq(∂u_j)`.
    -- Since the multiplication is left-associative in our chain,
    --   T1 = (((translate a) * η²) * dq(∂u_i)) * dq(∂u_j).
    -- But we just need the support to be compact, and it suffices to find a
    -- factor with compact support. Use a `unfold`-friendly form.
    change HasCompactSupport (fun x : E =>
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    -- Build up factor-wise. Treat the full product as a chain.
    -- (translate * η²) has compact support (η² compact, translate continuous, mul_left).
    have h_step1 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_supp.mul_left
    -- Multiplying further on the right doesn't disturb compact support if the
    -- existing support is compact (use `mul_right`).
    have h_step2 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT2_supp : ∀ i j : Fin d, HasCompactSupport (T2 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      2 * DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)
    -- ((2 * τa) * η) has compact support since η has compact support.
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)) := hη_supp.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
    have h_step3 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step2.mul_right
    exact h_step3.mul_right
  have hT3_supp : ∀ i j : Fin d, HasCompactSupport (T3 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    have h_step1 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_supp.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT4_supp : ∀ i j : Fin d, HasCompactSupport (T4 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)) := hη_supp.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
    have h_step3 : HasCompactSupport (fun x : E =>
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
      h_step2.mul_right
    exact h_step3.mul_right
  -- LHSint compact support: from pointwise equality with T1+T2+T3+T4.
  have hLHS_supp : ∀ i j : Fin d, HasCompactSupport (LHSint i j) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    exact (((hT1_supp i j).add (hT2_supp i j)).add (hT3_supp i j)).add
      (hT4_supp i j)
  -- Integrability.
  have hT1_int : ∀ i j : Fin d, Integrable (T1 i j) volume := fun i j =>
    (hT1_cont i j).integrable_of_hasCompactSupport (hT1_supp i j)
  have hT2_int : ∀ i j : Fin d, Integrable (T2 i j) volume := fun i j =>
    (hT2_cont i j).integrable_of_hasCompactSupport (hT2_supp i j)
  have hT3_int : ∀ i j : Fin d, Integrable (T3 i j) volume := fun i j =>
    (hT3_cont i j).integrable_of_hasCompactSupport (hT3_supp i j)
  have hT4_int : ∀ i j : Fin d, Integrable (T4 i j) volume := fun i j =>
    (hT4_cont i j).integrable_of_hasCompactSupport (hT4_supp i j)
  -- Per-pair integral identity.
  have h_pair_int : ∀ i j : Fin d,
      ∫ x, LHSint i j x ∂(volume : Measure E) =
        ∫ x, T1 i j x ∂(volume : Measure E) +
        ∫ x, T2 i j x ∂(volume : Measure E) +
        ∫ x, T3 i j x ∂(volume : Measure E) +
        ∫ x, T4 i j x ∂(volume : Measure E) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    -- Use `integral_add` step by step, identifying each step.
    have h_step1 :
        ∫ x, T1 i j x + T2 i j x + T3 i j x + T4 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x + T2 i j x + T3 i j x ∂(volume : Measure E)) +
          ∫ x, T4 i j x ∂(volume : Measure E) :=
      integral_add ((hT1_int i j).add (hT2_int i j) |>.add (hT3_int i j))
        (hT4_int i j)
    have h_step2 :
        ∫ x, T1 i j x + T2 i j x + T3 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x + T2 i j x ∂(volume : Measure E)) +
          ∫ x, T3 i j x ∂(volume : Measure E) :=
      integral_add ((hT1_int i j).add (hT2_int i j)) (hT3_int i j)
    have h_step3 :
        ∫ x, T1 i j x + T2 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x ∂(volume : Measure E)) +
          ∫ x, T2 i j x ∂(volume : Measure E) :=
      integral_add (hT1_int i j) (hT2_int i j)
    rw [h_step1, h_step2, h_step3]
  -- Convert to the statement form.
  -- We sum the per-pair identity over (i, j).
  rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x, LHSint i j x ∂(volume : Measure E)) =
      ∑ i : Fin d, ∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
        ∫ x, T2 i j x ∂(volume : Measure E) +
        ∫ x, T3 i j x ∂(volume : Measure E) +
        ∫ x, T4 i j x ∂(volume : Measure E)) from ?_]
  · -- Now distribute the sum.
    -- ∑ i ∑ j (a_ij + b_ij + c_ij + d_ij) = ∑∑ a + ∑∑ b + ∑∑ c + ∑∑ d.
    have h_split : ∀ i : Fin d,
        (∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
            ∫ x, T2 i j x ∂(volume : Measure E) +
            ∫ x, T3 i j x ∂(volume : Measure E) +
            ∫ x, T4 i j x ∂(volume : Measure E))) =
          (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E)) := by
      intro i
      rw [show (fun j : Fin d => ∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E) +
              ∫ x, T4 i j x ∂(volume : Measure E)) =
          (fun j : Fin d => (∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E)) +
              ∫ x, T4 i j x ∂(volume : Measure E)) from rfl]
      rw [Finset.sum_add_distrib]
      rw [show (fun j : Fin d => ∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E)) =
          (fun j : Fin d => (∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E)) +
              ∫ x, T3 i j x ∂(volume : Measure E)) from rfl]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
    -- Now handle outer sum.
    rw [show (fun i : Fin d => ∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
            ∫ x, T2 i j x ∂(volume : Measure E) +
            ∫ x, T3 i j x ∂(volume : Measure E) +
            ∫ x, T4 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E)))) from
        funext (fun i => h_split i)]
    -- Distribute outer sum.
    rw [show (fun i : Fin d => (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E))) from rfl]
    rw [Finset.sum_add_distrib]
    rw [show (fun i : Fin d => (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E))) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) from rfl]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_pair_int i j

/-! ## Section 5: Coercivity lower bound on the principal term -/

/-- Pointwise lower bound on the integrand of the principal term: at every
`x ∈ tsupport η` and every `h` with `Metric.cthickening |h| (tsupport η) ⊆
Ω`,

  `λ · η²(x) · ‖D_h^k ∇u(x)‖² ≤ η²(x) · ∑ i j (τ_h a^{ij})(x) ·
                                       D_h^k(∂_i u)(x) · D_h^k(∂_j u)(x)`.

Outside `tsupport η`, both sides are zero. -/
private theorem principal_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ)
    {η : E → ℝ}
    (k : Fin d) {h : ℝ}
    (hh_supp : Metric.cthickening |h| (tsupport η) ⊆ Ω) (x : E) :
    B.lam * (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 ≤
      (η x)^2 * shiftedPrincipal B u k h x := by
  by_cases hx : x ∈ tsupport η
  · -- Inside tsupport η: apply ellipticity at the shifted point.
    have hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω := by
      apply hh_supp
      -- Show x + h • e_k ∈ cthickening |h| (tsupport η).
      refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport η) hx ?_
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hdist_eq :
          dist (x + h • EuclideanSpace.single k 1) x =
            ‖h • EuclideanSpace.single k (1 : ℝ)‖ := by
        rw [dist_eq_norm]
        have hsub :
            (x + h • EuclideanSpace.single k 1) - x =
              h • EuclideanSpace.single k (1 : ℝ) := by
          rw [add_sub_cancel_left]
        rw [hsub]
      rw [hdist_eq]
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    -- Apply the shifted-coefficient bound.
    have h_bound :=
      shiftedPrincipal_ge (d := d) B u k h hx_translate
    -- Multiply both sides by `(η x)^2 ≥ 0`.
    have h_eta_nn : 0 ≤ (η x)^2 := sq_nonneg _
    -- Convert the RHS of the bound to use diffQuotGradient.
    have h_grad_norm_sq :
        ‖diffQuotGradient u k h x‖ ^ 2 =
          ∑ i : Fin d,
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 :=
      diffQuotGradient_norm_sq (d := d) u k h x
    rw [← h_grad_norm_sq]
    have h_mul := mul_le_mul_of_nonneg_left h_bound h_eta_nn
    -- h_mul : (η x)^2 * (B.lam * ‖dgrad‖²) ≤ (η x)^2 * shiftedPrincipal
    -- Goal: B.lam * (η x)^2 * ‖dgrad‖² ≤ (η x)^2 * shiftedPrincipal
    have h_lhs_eq :
        B.lam * (η x)^2 * ‖diffQuotGradient u k h x‖ ^ 2 =
          (η x)^2 * (B.lam * ‖diffQuotGradient u k h x‖ ^ 2) := by
      ring
    rw [h_lhs_eq]
    exact h_mul
  · -- Outside tsupport η: η x = 0 (since x ∉ closure(support η)), so both
    -- sides vanish.
    have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hη_zero]
    simp

set_option linter.unusedVariables false in
/-- The integral lower bound: for every `h ≠ 0` with `cthickening |h|
(tsupport η) ⊆ Ω`,

  `λ · ∫ η² · ‖D_h^k ∇u‖² ≤ PRINCIPAL_term`,

where `PRINCIPAL_term` is the `(τ_h a) · η² · D_h^k(∂u) · D_h^k(∂u)` term
of the four-term decomposition. -/
theorem principal_term_ge_lambda_norm_sq
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hh_supp : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
      ∂(volume : Measure E) ≤
    ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E) := by
  classical
  -- We prove the integral inequality via a pointwise bound and integration.
  -- Step 1. Continuity / compact-support facts for the LHS integrand.
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  -- η² compact support.
  have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]
    exact hη_supp.mul_right
  -- Continuity of `D_h^k(∂_i u)`.
  have h_diffQuot_partial_u_cont : ∀ i : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    intro i
    have h_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_of_contDiff (d := d) h_smooth k h
  have h_a_cont : ∀ i j : Fin d, Continuous (fun y : E => B.a y i j) :=
    fun i j => B.continuous_a i j
  have h_translate_a_cont : ∀ i j : Fin d,
      Continuous (DifferentialGeometry.Analysis.Sobolev.translate k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_translate_of_continuous (d := d)
      (h_a_cont i j) k h
  -- The LHS integrand is `(η x)^2 * ∑_i (D_h^k(∂_i u) x)^2`.
  -- It's continuous (η^2 cont, sum of squares cont).
  have h_LHS_cont : Continuous (fun x : E =>
      (η x)^2 * ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) := by
    refine (hη.continuous.pow 2).mul ?_
    exact continuous_finset_sum _ (fun i _ => (h_diffQuot_partial_u_cont i).pow 2)
  -- Compact support of LHS integrand: η² has compact support, so the product
  -- has compact support.
  have h_LHS_supp : HasCompactSupport (fun x : E =>
      (η x)^2 * ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) :=
    h_eta_sq_supp.mul_right
  have h_LHS_int : Integrable (fun x : E =>
      (η x)^2 * ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
        volume :=
    h_LHS_cont.integrable_of_hasCompactSupport h_LHS_supp
  -- The principal-term integrand (PRINCIPAL_term integrand) is continuous and
  -- compactly supported.
  -- T1 i j is the (i, j) summand; we already produced its compact support,
  -- continuity, integrability above.
  have hT1_cont : ∀ i j : Fin d, Continuous (fun x : E =>
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    intro i j
    refine ((((h_translate_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_diffQuot_partial_u_cont i)).mul (h_diffQuot_partial_u_cont j))
  have hT1_supp : ∀ i j : Fin d, HasCompactSupport (fun x : E =>
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    intro i j
    have h_step1 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_supp.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT1_int : ∀ i j : Fin d, Integrable (fun x : E =>
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
        volume := fun i j =>
    (hT1_cont i j).integrable_of_hasCompactSupport (hT1_supp i j)
  -- Continuity & integrability of (η x)² · shiftedPrincipal:
  have h_shiftedPrincipal_cont :
      Continuous (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) := by
    refine (hη.continuous.pow 2).mul ?_
    unfold shiftedPrincipal
    refine continuous_finset_sum _ ?_
    intro i _
    refine continuous_finset_sum _ ?_
    intro j _
    refine ((h_translate_a_cont i j).mul (h_diffQuot_partial_u_cont i)).mul
      (h_diffQuot_partial_u_cont j)
  have h_shiftedPrincipal_supp :
      HasCompactSupport (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) :=
    h_eta_sq_supp.mul_right
  have h_shiftedPrincipal_int :
      Integrable (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) volume :=
    h_shiftedPrincipal_cont.integrable_of_hasCompactSupport
      h_shiftedPrincipal_supp
  -- Step 2. Pointwise inequality.
  have h_pointwise_ineq : ∀ x : E,
      B.lam * ((η x)^2 * (∑ i : Fin d,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)) ≤
        (η x)^2 * shiftedPrincipal B u k h x := by
    intro x
    have hpw := principal_pointwise_bound (d := d) B u (η := η) k hh_supp x
    -- hpw : B.lam * (η x)^2 * (...) ≤ (η x)^2 * shiftedPrincipal
    -- Goal: B.lam * ((η x)^2 * (...)) ≤ (η x)^2 * shiftedPrincipal
    have h_lhs_eq :
        B.lam * ((η x)^2 * (∑ i : Fin d,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)) =
          B.lam * (η x)^2 * (∑ i : Fin d,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) := by
      ring
    rw [h_lhs_eq]
    exact hpw
  -- Step 3. Integrate the pointwise inequality.
  -- LHS = B.lam · ∫ (η²) · (∑ (D_h^k ∂u)²)
  --     = ∫ B.lam · (η²) · (∑ ...)        [pull constant inside]
  -- RHS = ∫ η² · shiftedPrincipal
  -- Sum-integral commutation matches RHS to the explicit double-sum form.
  have h_lhs_factor :
      B.lam * ∫ x, (η x)^2 *
          (∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
        ∂(volume : Measure E) =
      ∫ x, B.lam * ((η x)^2 *
          (∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2))
        ∂(volume : Measure E) := by
    rw [integral_const_mul]
  rw [h_lhs_factor]
  -- Apply integral_mono (between the constant-multiplied LHS integrand and
  -- (η²) * shiftedPrincipal).
  have h_LHS_int_mul :
      Integrable (fun x : E => B.lam * ((η x)^2 *
          (∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)))
        volume := h_LHS_int.const_mul B.lam
  have h_int_le :
      ∫ x, B.lam * ((η x)^2 *
          (∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2))
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 * shiftedPrincipal B u k h x ∂(volume : Measure E) :=
    integral_mono h_LHS_int_mul h_shiftedPrincipal_int h_pointwise_ineq
  refine h_int_le.trans ?_
  -- Convert ∫ (η²) · shiftedPrincipal to the explicit double-sum form.
  -- shiftedPrincipal x = ∑ i j (τ a) x · D_h^k(∂_i u) x · D_h^k(∂_j u) x.
  -- (η²) · shiftedPrincipal = ∑ i j (τ a) · η² · D_h^k(∂_i u) · D_h^k(∂_j u).
  -- Then sum-integral commutation.
  have h_pointwise_eq : ∀ x : E,
      (η x)^2 * shiftedPrincipal B u k h x =
        ∑ i : Fin d, ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x := by
    intro x
    unfold shiftedPrincipal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_eq_fun :
      (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) =
        (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    funext x
    exact h_pointwise_eq x
  rw [h_eq_fun]
  -- Apply sum-integral commutation: ∫ ∑_{i, j} F = ∑_{i, j} ∫ F.
  have h_inner_int : ∀ i : Fin d,
      Integrable (fun x : E => ∑ j : Fin d,
        DifferentialGeometry.Analysis.Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
    fun i => integrable_finset_sum _ (fun j _ => hT1_int i j)
  rw [show (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) =
      (fun x : E => ∑ i : Fin d, (fun y : E => ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun z : E => B.a z i j) y * (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) y) x)
      from rfl]
  rw [integral_finset_sum _ (fun i _ => h_inner_int i)]
  refine le_of_eq ?_
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (fun y : E => ∑ j : Fin d,
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun z : E => B.a z i j) y * (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) y) =
      (fun y : E => ∑ j : Fin d, (fun z : E =>
          DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun w : E => B.a w i j) z * (η z)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun w : E => (fderiv ℝ u w) (EuclideanSpace.single i 1)) z *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun w : E => (fderiv ℝ u w) (EuclideanSpace.single j 1)) z) y)
      from rfl]
  rw [integral_finset_sum _ (fun j _ => hT1_int i j)]

/-! ## Section 6: The headline master inequality -/

/-- The master inequality: the sum of three "cross" terms plus the data
terms `f · v_test` and `c · u · v_test` dominates `λ ∫ η² ‖D_h^k ∇u‖²`.

This is the rearranged form of the substitution identity, after expanding
the principal LHS via the discrete product rule and using ellipticity at
the shifted point. It is the immediate input to the difference-quotient
estimate that controls all `D_h^k ∂_i u` simultaneously by the data and
lower-order pieces.

The "cross" terms are:

* `Cross_1` = `∑ i j ∫ 2 (τ_h a^{ij}) η · ∂_j η · D_h^k(∂_i u) · D_h^k u`,
* `Cross_2` = `∑ i j ∫ (D_h^k a^{ij}) η² · ∂_i u · D_h^k(∂_j u)`,
* `Cross_3` = `∑ i j ∫ 2 (D_h^k a^{ij}) η · ∂_j η · ∂_i u · D_h^k u`.

The inequality reads:

  `λ · ∫ η² · ‖D_h^k ∇u‖² ≤
    |Cross_1| + |Cross_2| + |Cross_3| + |∫ f · v_test| + |∫ c u · v_test|`.

It is stated below using `‖D_h^k ∇u‖² = ∑ i, (D_h^k ∂_i u)²`. -/
theorem nirenberg_master_inequality
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (h_weak : B.IsSmoothWeakSolution u f)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hh_supp : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
      ∂(volume : Measure E) ≤
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| +
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)| +
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| +
      |∫ x in Ω, f x * nirenbergTestFunction k h η u x| +
      |∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x| := by
  classical
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  -- Step 1. Substitution identity.
  have h_sub :=
    nirenberg_substitution_identity (d := d) B h_weak hη hη_supp k hh hh_supp
  -- Rearrange the substitution identity: name the principal LHS sum as `S`.
  -- S := ∑_{i, j} ∫ D_h^k(a^{ij} ∂_i u) · ∂_j(η² D_h^k u) dx.
  -- The substitution identity gives: -S + ∫_Ω c · u · v_test = ∫_Ω f · v_test.
  -- So S = ∫_Ω c · u · v_test - ∫_Ω f · v_test.
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j *
            ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
        ((fderiv ℝ
            (fun y : E => η y ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) x)
          (EuclideanSpace.single j 1))
      ∂(volume : Measure E) with hS_def
  set Q : ℝ := ∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x
    with hQ_def
  set R : ℝ := ∫ x in Ω, f x * nirenbergTestFunction k h η u x
    with hR_def
  -- h_sub: -S + Q = R.
  have h_sub_S : -S + Q = R := h_sub
  -- Step 2. Decompose S into 4 explicit parts.
  set P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
    ∂(volume : Measure E) with hP_def
  set C1 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * DifferentialGeometry.Analysis.Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
    ∂(volume : Measure E) with hC1_def
  set C2 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
    ∂(volume : Measure E) with hC2_def
  set C3 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
    ∂(volume : Measure E) with hC3_def
  have h_decomp : S = P + C1 + C2 + C3 :=
    nirenberg_principal_decomposition (d := d) B hu hη hη_supp k hh
  -- Step 3. Coercivity.
  set L : ℝ := B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
    ∂(volume : Measure E) with hL_def
  have h_coerc : L ≤ P :=
    principal_term_ge_lambda_norm_sq (d := d) B hu hη hη_supp k hh hh_supp
  -- Step 4. Combine. From h_sub_S: -S + Q = R, so S = Q - R.
  -- From h_decomp: S = P + C1 + C2 + C3, so P = S - C1 - C2 - C3.
  -- Hence L ≤ P = (Q - R) - C1 - C2 - C3
  --            = -C1 - C2 - C3 - R + Q
  --            ≤ |C1| + |C2| + |C3| + |R| + |Q|.
  have h_S_eq : S = Q - R := by
    have := h_sub_S
    linarith
  have h_P_eq : P = S - C1 - C2 - C3 := by
    have := h_decomp
    linarith
  have h_chain : L ≤ -C1 - C2 - C3 - R + Q := by
    have hP : P = -C1 - C2 - C3 - R + Q := by
      rw [h_P_eq, h_S_eq]; ring
    rw [hP] at h_coerc
    exact h_coerc
  -- Triangle inequality.
  have h_abs : -C1 - C2 - C3 - R + Q ≤
      |C1| + |C2| + |C3| + |R| + |Q| := by
    have h1 : -C1 ≤ |C1| := by
      have h := neg_abs_le C1
      linarith [abs_nonneg C1]
    have h2 : -C2 ≤ |C2| := by
      have h := neg_abs_le C2
      linarith [abs_nonneg C2]
    have h3 : -C3 ≤ |C3| := by
      have h := neg_abs_le C3
      linarith [abs_nonneg C3]
    have h4 : -R ≤ |R| := by
      have h := neg_abs_le R
      linarith [abs_nonneg R]
    have h5 : Q ≤ |Q| := le_abs_self Q
    linarith
  exact h_chain.trans h_abs

end DifferentialGeometry.Analysis.Sobolev.NirenbergCoercivity
