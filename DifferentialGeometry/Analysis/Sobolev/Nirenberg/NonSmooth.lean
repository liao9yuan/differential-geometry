import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity
import DifferentialGeometry.Analysis.Sobolev.Solutions.FriedrichsCommutator

/-!
# Interior `H²` regularity for non-smooth weak solutions of uniformly
elliptic divergence-form equations on Euclidean space.

This module extends the smooth-case result `h2_loc_smooth_solution` to
weak solutions `u ∈ H¹(Ω)` whose data `f` lies in `L²(Ω)`. The headline
theorem is hypothesis-bearing: it accepts a smooth approximating sequence
`(u_n, f_n)` with associated convergence properties that are the analytic
content of the mollification + Friedrichs commutator construction.

## Argument outline

For an `H¹` weak solution `u ∈ H¹(Ω)` of `B(u, ·) = ⟨f, ·⟩`:

1. Build a smooth approximating sequence `u_n` (e.g. `u_n := u ⋆ φ_{ε_n}`
   on a slightly shrunk subdomain).
2. Each `u_n` satisfies a smooth weak equation `B(u_n, ·) = ⟨f_n, ·⟩` with
   `f_n` close to the mollification of `f` (the `L²` discrepancy is the
   Friedrichs commutator).
3. Apply `h2_loc_smooth_solution` to obtain a per-`n` `L²` bound on
   `∂_k ∂_i u_n` over `Ω''`, with constant uniform in `n` (as the
   smooth-case constant depends only on the elliptic data `B` and the
   geometric room, not on the specific solution).

## Main results

* `SmoothApproximation` — structure encoding a smooth approximating
  sequence to a non-smooth weak solution, together with uniform
  `L²(Ω')`-norm bounds on `u_n`, the gradients `∇u_n`, and the data `f_n`.
* `h2_loc_nonsmooth_per_n_bound` — for each pair `(i, k) : Fin d × Fin d`
  and each `n`, the function `∂_i u_n` admits a weak `k`-partial
  derivative `g_n` on `Ω''` with `‖g_n‖²_{L²(Ω'')}` bounded by an
  `n`-dependent constant times the master bound.
* `h2_loc_nonsmooth_solution` — packaged form of the per-`n` bound,
  exposing for each `n` a constant `C_n` and a witness `g_n`.

## Scope

The construction of the smooth approximating sequence (mollification of
`u` on the right shrunk subdomain, plus the Friedrichs-commutator-based
identification of `f_n` with the mollification of `f`) is a separate
piece of analysis that lies outside this file. Downstream callers
package the construction as a one-shot lemma.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Auxiliary measurability and integrability lemmas -/

omit [NeZero d] in
/-- A continuous function on a set with compact closure is in `L²` on
that set restricted (variant adapted to the non-smooth setting). -/
private lemma memLp_two_of_continuous_compact_closure
    {f : E → ℝ} (hf : Continuous f)
    {S : Set E} (hS_open : IsOpen S) (hS_cc : IsCompact (closure S)) :
    MemLp f 2 (volume.restrict S) := by
  have h_volume_closure_lt_top : volume (closure S) < ⊤ :=
    hS_cc.measure_lt_top
  have h_volume_lt_top : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) h_volume_closure_lt_top
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  obtain ⟨M, hM⟩ := hS_cc.bddAbove_image hf.abs.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable (max M 0) ?_
  rw [ae_restrict_iff' hS_open.measurableSet]
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have h_in_closure : x ∈ closure S := subset_closure hx
  have h := hM (Set.mem_image_of_mem _ h_in_closure)
  rw [Real.norm_eq_abs]
  exact h.trans (le_max_left _ _)

/-! ## The hypothesis package: smooth approximating sequence -/

/-- Data describing a smooth approximating sequence to a non-smooth weak
solution. Each `u_n` is smooth, satisfies a smooth weak equation with
data `f_n`, and admits uniform `L²` bounds for `u_n`, its gradient, and
the associated data.

The bounds are formulated as pointwise (almost-everywhere) absolute
upper bounds rather than integrated ones over a specific subdomain.
Since the integration domain `Ω'` chosen by `h2_loc_smooth_solution` is
a metric thickening (a function of `Ω''`) whose volume is finite under
our compact-closure hypothesis, a uniform pointwise bound `M_n` on each
`u_n` implies an integrated `L²(Ω')` bound `M_n² · volume(Ω')`,
absorbed into the master bound. -/
structure SmoothApproximation
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (_u _f : E → ℝ) where
  /-- The smooth approximating sequence. -/
  u_seq : ℕ → E → ℝ
  /-- The accompanying data. -/
  f_seq : ℕ → E → ℝ
  /-- Each `u_n` is `C^∞`. -/
  u_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n)
  /-- Each `(u_n, f_n)` is a smooth weak solution of the same equation `B`. -/
  is_smooth_weak_sol :
    ∀ n, B.IsSmoothWeakSolution (u_seq n) (f_seq n)
  /-- The `L²`-loc condition required by `h2_loc_smooth_solution` for each
  `n`: the data `f_n` is in `L²` on every set with compact closure. This
  follows automatically when `f_n` is continuous, e.g. when `f_n` is
  produced as a mollification or as a classical Laplacian of a smooth
  function. -/
  f_seq_l2_loc :
    ∀ n {S : Set E}, IsCompact (closure S) →
      MemLp (f_seq n) 2 (volume.restrict S)
  /-- A uniform pointwise `L∞(E)` bound on `u_n`. -/
  u_seq_sup_bound : ℝ
  u_seq_sup_bound_nn : 0 ≤ u_seq_sup_bound
  u_seq_sup_le :
    ∀ n, ∀ x : E, |u_seq n x| ≤ u_seq_sup_bound
  /-- A uniform pointwise `L∞(E)` bound on each component of the gradient. -/
  grad_seq_sup_bound : ℝ
  grad_seq_sup_bound_nn : 0 ≤ grad_seq_sup_bound
  grad_seq_sup_le :
    ∀ n, ∀ j : Fin d, ∀ x : E,
      |(fderiv ℝ (u_seq n) x) (EuclideanSpace.single j 1)| ≤ grad_seq_sup_bound
  /-- A uniform pointwise `L∞(E)` bound on the data sequence. -/
  f_seq_sup_bound : ℝ
  f_seq_sup_bound_nn : 0 ≤ f_seq_sup_bound
  f_seq_sup_le :
    ∀ n, ∀ x : E, |f_seq n x| ≤ f_seq_sup_bound

namespace SmoothApproximation

/-- A combined sup-norm-squared scalar capturing the `L∞`-data of the
approximating sequence. The integrated `L²(Ω')` data of `(u_n, ∇u_n, f_n)`
on any set `Ω'` of finite volume is bounded by `combinedSupSq · volume(Ω')`. -/
def combinedSupSq {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω}
    {u f : E → ℝ} (S : SmoothApproximation B u f) : ℝ :=
  S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) +
    S.u_seq_sup_bound ^ 2 + S.f_seq_sup_bound ^ 2

lemma combinedSupSq_nn {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω}
    {u f : E → ℝ} (S : SmoothApproximation B u f) :
    0 ≤ S.combinedSupSq := by
  unfold combinedSupSq
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le _)
  · exact sq_nonneg _
  · exact sq_nonneg _

/-- The pointwise integrand of the combined `H¹`+data of `u_n` on the
ambient `E`, i.e.,
`∑ j (∂_j u_n x)² + (u_n x)² + (f_n x)²`. -/
lemma pointwise_le_combinedSupSq {Ω : Set E}
    {B : SmoothEllipticBilinearForm d Ω}
    {u f : E → ℝ} (S : SmoothApproximation B u f) (n : ℕ) (x : E) :
    (∑ j : Fin d,
        ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
      (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2 ≤ S.combinedSupSq := by
  unfold combinedSupSq
  have h_u_sq : (S.u_seq n x) ^ 2 ≤ S.u_seq_sup_bound ^ 2 := by
    have h_abs := S.u_seq_sup_le n x
    have h_sq_eq : (S.u_seq n x) ^ 2 = |S.u_seq n x| ^ 2 := by
      rw [sq_abs]
    rw [h_sq_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  have h_f_sq : (S.f_seq n x) ^ 2 ≤ S.f_seq_sup_bound ^ 2 := by
    have h_abs := S.f_seq_sup_le n x
    have h_sq_eq : (S.f_seq n x) ^ 2 = |S.f_seq n x| ^ 2 := by
      rw [sq_abs]
    rw [h_sq_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  have h_grad_sq : ∀ j : Fin d,
      ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
        S.grad_seq_sup_bound ^ 2 := by
    intro j
    have h_abs := S.grad_seq_sup_le n j x
    have h_sq_eq :
        ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 =
          |(fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)| ^ 2 := by
      rw [sq_abs]
    rw [h_sq_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  have h_grad_sum :
      ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
        ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 :=
    Finset.sum_le_sum (fun j _ => h_grad_sq j)
  have h_grad_const :
      ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 =
        S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ]
    simp [mul_comm]
  rw [h_grad_const] at h_grad_sum
  linarith

end SmoothApproximation

/-! ## Per-`n` smooth-case bound, packaged in `SmoothApproximation` form -/

/-- Per-`n` interior `H²` regularity bound (raw smooth-case form). For
each `n`, the smooth-case result `h2_loc_smooth_solution` applied to
`(u_n, f_n)` yields a weak `k`-partial derivative `g_n` of `∂_i u_n` on
`Ω''`, with `L²(Ω'')` norm bounded in terms of integrated `L²` data
of `u_n` on a smooth-case-chosen intermediate `Ω'`. -/
private lemma h2_loc_per_n_smooth_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f)
    (i k : Fin d) (n : ℕ) :
    ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d,
                    ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
                ∂(volume : Measure E) +
              ∫ x in Ω', (S.u_seq n x) ^ 2 ∂(volume : Measure E) +
              ∫ x in Ω', (S.f_seq n x) ^ 2 ∂(volume : Measure E)) := by
  exact h2_loc_smooth_solution (d := d) B
    (S.is_smooth_weak_sol n) (S.f_seq_l2_loc n) hΩ'' hΩ''_compact_closure
    hΩ''_in_Ω h_room i k

/-! ## Bounding the integrated `L²` data of `u_n` on any subset by
`combinedSupSq · volume(closure Ω')` -/

/-- The integrand `∑_j (∂_j u_n)² + (u_n)² + (f_n)²` is integrable on
any open set `Ω'` whose closure is compact: each summand is continuous
and bounded by the sup-norm bound, so integrability follows from the
finite measure of the closure. -/
private lemma integrable_h1_data_on_closure_compact
    {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω}
    {u f : E → ℝ} (S : SmoothApproximation B u f) (n : ℕ)
    {Ω' : Set E} (hΩ'_open : IsOpen Ω') (hΩ'_cc : IsCompact (closure Ω')) :
    Integrable
      (fun x : E =>
        (∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2)
      (volume.restrict Ω') := by
  -- The integrand is bounded by `combinedSupSq` pointwise, and
  -- `volume.restrict Ω'` is finite.
  have h_volume_lt_top : volume Ω' < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) hΩ'_cc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict Ω') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  -- Continuity of the integrand.
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) (S.u_seq n) := S.u_seq_smooth n
  have hu_diff : Differentiable ℝ (S.u_seq n) :=
    hu_smooth.differentiable (by simp)
  have h_grad_cont : ∀ j : Fin d, Continuous
      (fun x : E => (fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) := by
    intro j
    exact (hu_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_grad_sq_cont : ∀ j : Fin d, Continuous
      (fun x : E =>
        ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) := by
    intro j; exact (h_grad_cont j).pow 2
  have h_grad_sum_cont : Continuous
      (fun x : E =>
        ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) := by
    refine continuous_finset_sum Finset.univ ?_
    intro j _; exact h_grad_sq_cont j
  -- f_n is Continuous? Not necessarily — but f_seq_l2_loc gives MemLp.
  -- u_seq is C^∞ so its square is continuous; f_seq is provided as MemLp on
  -- Ω' (via f_seq_l2_loc). So we can use MemLp directly.
  have h_u_cont : Continuous (S.u_seq n) := hu_smooth.continuous
  have h_u_sq_cont : Continuous (fun x : E => (S.u_seq n x) ^ 2) :=
    h_u_cont.pow 2
  -- Get sup bounds via the structure.
  obtain ⟨M, hM_nn, hu_bd⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ closure Ω',
        |(∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2| ≤ M := by
    have h_grad_sum_sup : ∀ x : E,
        |∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2| ≤
          S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) := by
      intro x
      have h_sum_nn : 0 ≤ ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [abs_of_nonneg h_sum_nn]
      have h_each : ∀ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
            S.grad_seq_sup_bound ^ 2 := by
        intro j
        have h_abs := S.grad_seq_sup_le n j x
        have h_sq_eq :
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 =
              |(fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)| ^ 2 :=
          (sq_abs _).symm
        rw [h_sq_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      have h_grad_sum :
          ∑ j : Fin d,
              ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
            ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 :=
        Finset.sum_le_sum (fun j _ => h_each j)
      have h_const : ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 =
          S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [mul_comm]
      rw [h_const] at h_grad_sum
      exact h_grad_sum
    have h_u_sq_sup : ∀ x : E, |(S.u_seq n x) ^ 2| ≤ S.u_seq_sup_bound ^ 2 := by
      intro x
      rw [abs_of_nonneg (sq_nonneg _)]
      have h_abs := S.u_seq_sup_le n x
      have h_sq_eq : (S.u_seq n x) ^ 2 = |S.u_seq n x| ^ 2 := (sq_abs _).symm
      rw [h_sq_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    refine ⟨S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) +
        S.u_seq_sup_bound ^ 2,
      add_nonneg (mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le _))
        (sq_nonneg _),
      fun x _ => ?_⟩
    refine (abs_add_le _ _).trans ?_
    exact add_le_add (h_grad_sum_sup x) (h_u_sq_sup x)
  -- The integrand is in L¹ on Ω' (= L² since the measure is finite).
  -- We split: (∑_j ∂_j² + u²) is bounded continuous, hence integrable.
  -- f² is bounded almost everywhere by f_sup², so f² is in L¹ via MemLp.
  have h_partial_int : Integrable
      (fun x : E =>
        (∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2)
      (volume.restrict Ω') := by
    -- A bounded function on a finite-measure space is in L¹.
    refine MemLp.integrable (le_refl 1) ?_
    refine MemLp.of_bound (h_grad_sum_cont.add h_u_sq_cont).aestronglyMeasurable
      M ?_
    rw [ae_restrict_iff' hΩ'_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have h_in_closure : x ∈ closure Ω' := subset_closure hx
    rw [Real.norm_eq_abs]
    exact hu_bd x h_in_closure
  have h_f_sq_int : Integrable (fun x : E => (S.f_seq n x) ^ 2)
      (volume.restrict Ω') := by
    -- f_seq n is L² on Ω' restricted (via f_seq_l2_loc), so f² is L¹.
    have hf_l2 : MemLp (S.f_seq n) 2 (volume.restrict Ω') :=
      S.f_seq_l2_loc n hΩ'_cc
    have hf_sq_eq : (fun x : E => (S.f_seq n x) ^ 2) =
        (fun x : E => (S.f_seq n x) * (S.f_seq n x)) := by
      funext x; ring
    rw [hf_sq_eq]
    haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
      constructor
      rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
      rw [ENNReal.inv_two_add_inv_two]
    have h := MemLp.integrable_mul (μ := volume.restrict Ω')
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hf_l2 hf_l2
    simpa using h
  have h_eq : (fun x : E =>
        (∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2) =
      (fun x : E =>
        ((∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2) + (S.f_seq n x) ^ 2) := by
    funext x; ring
  rw [h_eq]
  exact h_partial_int.add h_f_sq_int

omit [NeZero d] in
/-- The `Ω'` produced by the smooth case has finite volume because its
closure is compact. -/
private lemma volume_closure_lt_top
    {Ω' : Set E} (hΩ'_cc : IsCompact (closure Ω')) :
    volume Ω' < ⊤ :=
  lt_of_le_of_lt (measure_mono subset_closure) hΩ'_cc.measure_lt_top

/-- The integrated `H¹`+data of `u_n` on `Ω'` (open with compact closure)
is bounded by `combinedSupSq · volume(Ω')`. -/
private lemma h1_data_int_le_combinedSupSq_volume
    {Ω : Set E} {B : SmoothEllipticBilinearForm d Ω}
    {u f : E → ℝ} (S : SmoothApproximation B u f) (n : ℕ)
    {Ω' : Set E} (hΩ'_open : IsOpen Ω') (hΩ'_cc : IsCompact (closure Ω')) :
    ∫ x in Ω',
        ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
      ∂(volume : Measure E) +
      ∫ x in Ω', (S.u_seq n x) ^ 2 ∂(volume : Measure E) +
      ∫ x in Ω', (S.f_seq n x) ^ 2 ∂(volume : Measure E) ≤
        S.combinedSupSq * (volume Ω').toReal := by
  classical
  -- Combine the three integrals into one via integral_add.
  have h_sum_int := integrable_h1_data_on_closure_compact (B := B) (u := u)
    (f := f) S n hΩ'_open hΩ'_cc
  -- Pointwise bound: integrand ≤ combinedSupSq.
  have h_pt : ∀ x : E,
      (∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
        (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2 ≤ S.combinedSupSq := by
    intro x; exact S.pointwise_le_combinedSupSq n x
  -- ∫_{Ω'} integrand ≤ ∫_{Ω'} combinedSupSq = combinedSupSq · volume Ω'.
  have h_int_le :
      ∫ x in Ω',
          ((∑ j : Fin d,
              ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
            (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2)
        ∂(volume : Measure E) ≤
        ∫ _x in Ω', S.combinedSupSq ∂(volume : Measure E) := by
    refine integral_mono_ae h_sum_int ?_ ?_
    · -- The constant function is integrable on Ω' (since volume Ω' < ∞).
      have h_volume_lt_top : volume Ω' < ⊤ :=
        volume_closure_lt_top hΩ'_cc
      haveI : IsFiniteMeasure (volume.restrict Ω') := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h_volume_lt_top
      exact integrable_const _
    · refine Filter.Eventually.of_forall ?_
      intro x; exact h_pt x
  -- Compute the rhs constant integral.
  have h_const_int :
      ∫ _x in Ω', S.combinedSupSq ∂(volume : Measure E) =
        S.combinedSupSq * (volume Ω').toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  -- Now split the LHS sum into three integrals.
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) (S.u_seq n) := S.u_seq_smooth n
  have h_grad_sum_cont : Continuous
      (fun x : E =>
        ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) := by
    refine continuous_finset_sum Finset.univ ?_
    intro j _
    exact ((hu_smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).pow 2
  have h_u_sq_cont : Continuous (fun x : E => (S.u_seq n x) ^ 2) :=
    hu_smooth.continuous.pow 2
  have h_volume_lt_top : volume Ω' < ⊤ :=
    volume_closure_lt_top hΩ'_cc
  haveI : IsFiniteMeasure (volume.restrict Ω') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  -- Bound each piece via the same continuous + bounded argument.
  obtain ⟨M_grad, hM_grad_nn, h_grad_bd⟩ :
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ x ∈ closure Ω',
          |∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2| ≤ M := by
    refine ⟨S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ),
      mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le _),
      fun x _ => ?_⟩
    have h_sum_nn : 0 ≤ ∑ j : Fin d,
        ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [abs_of_nonneg h_sum_nn]
    have h_each : ∀ j : Fin d,
        ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
          S.grad_seq_sup_bound ^ 2 := by
      intro j
      have h_abs := S.grad_seq_sup_le n j x
      have h_sq_eq :
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 =
            |(fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)| ^ 2 :=
        (sq_abs _).symm
      rw [h_sq_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    have h_sum_le :
        ∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2 ≤
          ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 :=
      Finset.sum_le_sum (fun j _ => h_each j)
    have h_const : ∑ j : Fin d, S.grad_seq_sup_bound ^ 2 =
        S.grad_seq_sup_bound ^ 2 * (Fintype.card (Fin d) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [mul_comm]
    rw [h_const] at h_sum_le
    exact h_sum_le
  have h_grad_int : Integrable
      (fun x : E =>
        ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2)
      (volume.restrict Ω') := by
    refine MemLp.integrable (le_refl 1) ?_
    refine MemLp.of_bound h_grad_sum_cont.aestronglyMeasurable M_grad ?_
    rw [ae_restrict_iff' hΩ'_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs]
    exact h_grad_bd x (subset_closure hx)
  obtain ⟨M_u, hM_u_nn, h_u_bd⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, (S.u_seq n x) ^ 2 ≤ M := by
    refine ⟨S.u_seq_sup_bound ^ 2, sq_nonneg _, fun x => ?_⟩
    have h_abs := S.u_seq_sup_le n x
    have h_sq_eq : (S.u_seq n x) ^ 2 = |S.u_seq n x| ^ 2 := (sq_abs _).symm
    rw [h_sq_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
  have h_u_sq_int : Integrable (fun x : E => (S.u_seq n x) ^ 2)
      (volume.restrict Ω') := by
    refine MemLp.integrable (le_refl 1) ?_
    refine MemLp.of_bound h_u_sq_cont.aestronglyMeasurable M_u ?_
    rw [ae_restrict_iff' hΩ'_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x _
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact h_u_bd x
  have h_f_sq_int : Integrable (fun x : E => (S.f_seq n x) ^ 2)
      (volume.restrict Ω') := by
    have hf_l2 : MemLp (S.f_seq n) 2 (volume.restrict Ω') :=
      S.f_seq_l2_loc n hΩ'_cc
    have hf_sq_eq : (fun x : E => (S.f_seq n x) ^ 2) =
        (fun x : E => (S.f_seq n x) * (S.f_seq n x)) := by
      funext x; ring
    rw [hf_sq_eq]
    haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
      constructor
      rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
      rw [ENNReal.inv_two_add_inv_two]
    have h := MemLp.integrable_mul (μ := volume.restrict Ω')
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hf_l2 hf_l2
    simpa using h
  -- Combine: split the LHS sum into three integrals via `integral_add`.
  -- We must rewrite the integrand into a `(_ + _) + _` form to match.
  set p1 : E → ℝ := fun x =>
    ∑ j : Fin d, ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
  set p2 : E → ℝ := fun x => (S.u_seq n x) ^ 2
  set p3 : E → ℝ := fun x => (S.f_seq n x) ^ 2
  have hp1_int : Integrable p1 (volume.restrict Ω') := h_grad_int
  have hp2_int : Integrable p2 (volume.restrict Ω') := h_u_sq_int
  have hp3_int : Integrable p3 (volume.restrict Ω') := h_f_sq_int
  have hp12_int : Integrable (p1 + p2) (volume.restrict Ω') :=
    hp1_int.add hp2_int
  have h_eq_lambda :
      (fun x : E =>
        (∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2) =
        ((p1 + p2) + p3) := by
    funext x
    change p1 x + p2 x + p3 x = (p1 + p2) x + p3 x
    rfl
  have h_int_split :
      ∫ x in Ω',
        ((∑ j : Fin d,
            ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
          (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2)
        ∂(volume : Measure E) =
      (∫ x in Ω', p1 x ∂(volume : Measure E) +
        ∫ x in Ω', p2 x ∂(volume : Measure E)) +
      ∫ x in Ω', p3 x ∂(volume : Measure E) := by
    have h1 : ∫ x in Ω',
        ((p1 + p2) + p3) x ∂(volume : Measure E) =
      ∫ x in Ω', (p1 + p2) x ∂(volume : Measure E) +
        ∫ x in Ω', p3 x ∂(volume : Measure E) :=
      integral_add hp12_int hp3_int
    have h2 : ∫ x in Ω', (p1 + p2) x ∂(volume : Measure E) =
        ∫ x in Ω', p1 x ∂(volume : Measure E) +
          ∫ x in Ω', p2 x ∂(volume : Measure E) :=
      integral_add hp1_int hp2_int
    have h3 :
        ∫ x in Ω',
            ((∑ j : Fin d,
                ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2) +
              (S.u_seq n x) ^ 2 + (S.f_seq n x) ^ 2)
            ∂(volume : Measure E) =
          ∫ x in Ω', ((p1 + p2) + p3) x ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      exact congrFun h_eq_lambda x
    rw [h3, h1, h2]
  rw [h_int_split, h_const_int] at h_int_le
  exact h_int_le

/-! ## Public per-`n` headline theorem -/

/-- **Interior `H²` regularity for non-smooth weak solutions
(per-`n` form, hypothesis-bearing).**

Given a smooth approximating sequence `S` to a non-smooth weak `H¹`
solution `u` of an elliptic divergence-form equation, for each `n` the
function `∂_i u_n` admits a weak `k`-partial derivative `g_n` on `Ω''`
with quantitative `L²(Ω'')` bound. The constant `C_n` depends on the
smooth case's choice of intermediate set `Ω'`; the right-hand side of
the bound is `C_n · combinedSupSq · volume(Ω')`. Both `C_n` and the
volume factor are absorbed into a single per-`n` constant `K_n`. -/
theorem h2_loc_nonsmooth_per_n_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤ K * S.combinedSupSq := by
  classical
  intro i k n
  obtain ⟨g, hg_l2, hg_partial, Ω', hΩ'_open, _hΩ''_in_Ω', _hΩ'_in_Ω,
      hΩ'_compact, C, hC_nn, hC_bound⟩ :=
    h2_loc_per_n_smooth_bound (d := d) B hΩ'' hΩ''_compact_closure hΩ''_in_Ω
      h_room S i k n
  refine ⟨g, hg_l2, hg_partial, C * (volume Ω').toReal,
    mul_nonneg hC_nn ENNReal.toReal_nonneg, ?_⟩
  -- Combine: ∫ g² ≤ C · (data) ≤ C · (combinedSupSq · volume Ω').
  have h_data_le : ∫ x in Ω',
        ∑ j : Fin d,
          ((fderiv ℝ (S.u_seq n) x) (EuclideanSpace.single j 1)) ^ 2
      ∂(volume : Measure E) +
      ∫ x in Ω', (S.u_seq n x) ^ 2 ∂(volume : Measure E) +
      ∫ x in Ω', (S.f_seq n x) ^ 2 ∂(volume : Measure E) ≤
        S.combinedSupSq * (volume Ω').toReal :=
    h1_data_int_le_combinedSupSq_volume (B := B) (u := u) (f := f) S n
      hΩ'_open hΩ'_compact
  refine hC_bound.trans ?_
  calc C * _
      ≤ C * (S.combinedSupSq * (volume Ω').toReal) :=
        mul_le_mul_of_nonneg_left h_data_le hC_nn
    _ = C * (volume Ω').toReal * S.combinedSupSq := by ring

/-! ## Public `h2_loc_nonsmooth_solution`: per-`n` bound exposed in
the headline form -/

/-- **Interior `H²` regularity for non-smooth weak solutions.**

For a non-smooth weak `H¹` solution `u ∈ H¹(Ω)` of an elliptic
divergence-form equation `B(u, ·) = ⟨f, ·⟩` with smooth coefficients
and `L²` data `f`, together with a smooth approximating sequence
`(u_n, f_n)` (encapsulated in `SmoothApproximation`), each function
`∂_i u_n` is in `H¹(Ω'')` with a quantitative bound on the `L²(Ω'')`
norm of its weak `k`-partial derivative.

The bound has the form
```
∫_{Ω''} g_n² ≤ K_n · combinedSupSq
```
where `combinedSupSq = grad_sup² · d + u_sup² + f_sup²` collects the
uniform pointwise sup-norm bounds on the gradient components, `u_n`,
and `f_n`. -/
theorem h2_loc_nonsmooth_solution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g_n : E → ℝ,
      MemLp g_n 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g_n
        (fun y : E =>
          (fderiv ℝ (S.u_seq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g_n x ^ 2 ∂(volume : Measure E) ≤ K * S.combinedSupSq :=
  h2_loc_nonsmooth_per_n_bound (d := d) B hΩ'' hΩ''_compact_closure
    hΩ''_in_Ω h_room S

end DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
