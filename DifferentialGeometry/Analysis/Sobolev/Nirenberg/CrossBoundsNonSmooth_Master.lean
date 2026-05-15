import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_Cross2
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_Cross3
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_CTerm
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_FTerm

/-!
# Non-smooth analogue of `nirenberg_master_inequality_after_young`

This module establishes the non-smooth analogue of the headline
absorbing inequality
`NirenbergCrossBounds.nirenberg_master_inequality_after_young`.

In the smooth case, the headline inequality combines the master
inequality
`λ · ∫ η² ‖D_h^k ∇u‖² ≤ |Cross_1| + |Cross_2| + |Cross_3| +
  |∫_Ω f · v_test| + |∫_Ω c · u · v_test|`
with the five Young absorbing bounds (`cross_1_bound`, `cross_2_bound`,
`cross_3_bound`, `c_term_bound`, `f_term_bound`) at parameter
`ε := λ/8`. This yields the absorbing inequality
`λ · ∫ η² ‖D_h^k ∇u‖² ≤ (λ/2) · ∫ η² ‖D_h^k ∇u‖² +
   C · (G + U + F)`,
where `G = ‖∇u‖²_{L²(Ω')}`, `U = ‖u‖²_{L²(Ω')}`, `F = ‖f‖²_{L²(Ω')}`.

In the non-smooth case the partial derivatives `∂_i u` are replaced by
explicit weak partials `g i : E → ℝ` (with `g i ∈ L²` and
`DeGiorgi.HasWeakPartialDeriv i (g i) u Set.univ`). The five Young
bounds carry over verbatim — they are
`cross_1_bound_nonsmooth`, `cross_2_bound_nonsmooth`,
`cross_3_bound_nonsmooth`, `c_term_bound_nonsmooth`,
`f_term_bound_nonsmooth` — once the appropriate Fréchet–Kolmogorov bounds
on `D_h^k u`, `D_h^k g_j`, and the L² bound on the standard Nirenberg
test function are supplied.

The master inequality itself is *not* derivable from non-smooth data:
its proof in `Coercivity.lean` uses pointwise smoothness of `u` to
expand `D_h^k(a^{ij} ∂_i u)` via the Leibniz rule and to invoke
`nirenberg_principal_decomposition`. We therefore expose the non-smooth
master inequality as a hypothesis `h_master_nonsmooth`. Downstream
callers in possession of mollification + the substitution identity for
weak solutions supply the bound by approximation.

## Inputs

* `h_master_nonsmooth` — the non-smooth master inequality.
* `h_FK_diffQuot_u_bound` — `∫_{tsupport η}(D_h^k u)² ≤ ∫_{Ω'} ∑_i g_i²`.
* `h_v_test_sq_bound` — the L² bound on the standard Nirenberg test
  function `D_{-h}^k(η² · D_h^k u)`.

The per-component Fréchet–Kolmogorov bound
`∫_{tsupport η}(D_h^k g_j)² ≤ ∫_{Ω'} ∑_i g_i²` is **not** needed: the
non-smooth Cross_2 bound (`cross_2_bound_nonsmooth`) reuses only the
pointwise / algebraic ingredient of its smooth counterpart, which does
not consume any FK bound on the partials.

## Main result

* `nirenberg_master_inequality_after_young_nonsmooth` — the headline
  absorbing inequality transcribed for the non-smooth case.

## Strategy

Mechanical mimic of `nirenberg_master_inequality_after_young`. We choose
`ε := λ/8` in the four absorbing-term bounds (`cross_1`, `cross_2`,
`c_term`, `f_term`); `cross_3` does not have an absorbing piece. Sum:
`λ · I ≤ |C1| + |C2| + |C3| + |R| + |Q|`
`     ≤ (ε I + C1' G) + (ε I + C2' G) + C3' G +
        (ε I + Cc' (G + U)) + (ε I + Cf' (G + F))`
`     = 4ε · I + (C1' + C2' + C3' + Cc' + Cf') · G + Cc' · U + Cf' · F`.
With `ε = λ/8` we have `4ε = λ/2`, and bounding each remaining constant
by `C := max(C1' + C2' + C3' + Cc' + Cf', max Cc' Cf')` gives the
absorbing form.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

set_option linter.unusedVariables false in
/-- **Non-smooth analogue of `nirenberg_master_inequality_after_young`.**

For a non-smooth `u : E → ℝ` with `u ∈ L²` and explicit weak partials
`g i : E → ℝ` (with `g i ∈ L²` and
`DeGiorgi.HasWeakPartialDeriv i (g i) u Set.univ`), assuming:

* the non-smooth master inequality (`h_master_nonsmooth`)
  `λ · ∫ η² ∑_i (D_h^k g_i)² ≤ |C1_sum| + |C2_sum| + |C3_sum| +
      |∫_Ω f · v_test| + |∫_Ω c · u · v_test|`,
  with the cross-sums having the same shape as in the smooth case but
  with `g i` in place of `∂_i u`;
* the Fréchet–Kolmogorov bound on `D_h^k u`
  (`h_FK_diffQuot_u_bound`);
* the L² bound on the standard Nirenberg test function
  (`h_v_test_sq_bound`),

we obtain the absorbing master inequality
`λ · ∫ η² ∑_i (D_h^k g_i)² ≤ (λ/2) · ∫ η² ∑_i (D_h^k g_i)² +
   C · (G + U + F)`,
with `G = ∫_{Ω'} ∑_i g_i²`, `U = ∫_{Ω'} u²`, `F = ∫_{Ω'} f²`, and `C`
independent of `h` (for `|h| ≤ 1`).

Apart from the non-smooth ingredients above, the proof is a mechanical
combination of `cross_1_bound_nonsmooth`, `cross_2_bound_nonsmooth`,
`cross_3_bound_nonsmooth`, `c_term_bound_nonsmooth`, and
`f_term_bound_nonsmooth`. -/
theorem nirenberg_master_inequality_after_young_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_loc : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    (h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        (B.lam / 2) * ∫ x, (η x)^2 *
            ∑ i : Fin d,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  -- Strategy: choose ε := λ/8 in the four absorbing-term bounds
  -- (cross_1, cross_2, c_term, f_term). cross_3 doesn't have an
  -- absorbing piece. Sum:
  -- λ · I ≤ |C1| + |C2| + |C3| + |R| + |Q|
  --       ≤ (ε I + C1' G) + (ε I + C2' G) + C3' G +
  --         (ε I + Cc' (G + U)) + (ε I + Cf' (G + F))
  --       = 4ε · I + (C1' + C2' + C3' + Cc' + Cf') · G + Cc' · U + Cf' · F
  -- With ε = λ/8: 4ε = λ/2.
  -- Set C := max(C1' + C2' + C3' + Cc' + Cf', max Cc' Cf').
  set ε_eff : ℝ := B.lam / 8 with hε_eff_def
  have hε_eff_pos : 0 < ε_eff := by
    rw [hε_eff_def]; exact div_pos B.hlam_pos (by norm_num)
  -- Apply the five non-smooth bounds.
  obtain ⟨C1, hC1_nn, hC1⟩ := cross_1_bound_nonsmooth (d := d) B hu_l2 hg_l2
    h_weakPartial hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
    hh_supp_in_Ω' k h_FK_diffQuot_u_bound ε_eff hε_eff_pos
  obtain ⟨C2, hC2_nn, hC2⟩ := cross_2_bound_nonsmooth (d := d) B hu_l2 hg_l2
    h_weakPartial hη hη_supp hη_range hΩ' hΩ'_closure hΩ'_compact
    hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨C3, hC3_nn, hC3⟩ := cross_3_bound_nonsmooth (d := d) B hu_l2 hg_l2
    h_weakPartial hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
    hh_supp_in_Ω' k h_FK_diffQuot_u_bound
  obtain ⟨Cc, hCc_nn, hCc⟩ := c_term_bound_nonsmooth (d := d) B hu_l2 hg_l2
    h_weakPartial hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
    hη_in_Ω' hh_supp_in_Ω' k ε_eff hε_eff_pos h_v_test_sq_bound h_FK_diffQuot_u_bound
  -- Derive the sum-form `v_test²` bound (needed by `f_term_bound_nonsmooth`)
  -- from the single-index form (`h_v_test_sq_bound`). The sum form has the
  -- weaker upper bound since `(D_h^k g_k)² ≤ ∑_i (D_h^k g_i)²`, so the
  -- single-index hypothesis trivially implies the sum-form hypothesis.
  have h_v_test_sq_bound_sum : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            ∑ i : Fin d,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
          ∂(volume : Measure E) := by
    intro h hh hh_le
    have h_single := h_v_test_sq_bound hh hh_le
    have h_pointwise : ∀ x : E,
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2 ≤
          (η x)^2 * ∑ i : Fin d,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2 := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have h_kmem : k ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k
      have h_term_le_sum :
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2 ≤
            ∑ i : Fin d,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2 :=
        Finset.single_le_sum
          (f := fun i => (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
          (fun i _ => sq_nonneg _) h_kmem
      exact h_term_le_sum
    have h_integrable_single : Integrable (fun x : E =>
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2)
        (volume : Measure E) := by
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_supp
        k k h 1
      have h_eq : (fun x : E => (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2) =
          (fun x : E => 1 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_integrable_sum : Integrable (fun x : E =>
        (η x)^2 * ∑ i : Fin d,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure E) := by
      have h_per_i : ∀ i : Fin d, Integrable (fun x : E =>
          (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        intro i
        have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_supp
          i k h 1
        have h_eq : (fun x : E => (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) =
            (fun x : E => 1 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
          funext x; ring
        rw [h_eq]
        exact hint
      have h_sum_int := integrable_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => h_per_i i)
      have h_eq : (fun x : E =>
          (η x)^2 * ∑ i : Fin d,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : E => ∑ i : Fin d,
            (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
        funext x
        rw [Finset.mul_sum]
      rw [h_eq]
      exact h_sum_int
    have h_int_le :
        ∫ x, (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
            ∂(volume : Measure E) ≤
          ∫ x, (η x)^2 * ∑ i : Fin d,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
            ∂(volume : Measure E) :=
      integral_mono h_integrable_single h_integrable_sum h_pointwise
    -- Multiply by 2 and combine.
    have h_two_int_le :
        2 * ∫ x, (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
            ∂(volume : Measure E) ≤
          2 * ∫ x, (η x)^2 * ∑ i : Fin d,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2
            ∂(volume : Measure E) :=
      mul_le_mul_of_nonneg_left h_int_le (by linarith)
    linarith
  obtain ⟨Cf, hCf_nn, hCf⟩ := f_term_bound_nonsmooth (d := d) hf_l2_loc hu_l2 hg_l2
    h_weakPartial hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
    hη_in_Ω' hh_supp_in_Ω' k h_FK_diffQuot_u_bound h_v_test_sq_bound_sum ε_eff hε_eff_pos
  -- The final constant.
  set C : ℝ := max (C1 + C2 + C3 + Cc + Cf) (max Cc Cf) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg hC1_nn hC2_nn) hC3_nn) hCc_nn) hCf_nn
  refine ⟨C, hC_nn, ?_⟩
  intro h hh hh_le
  -- Set up notation for the integrals.
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
    ∂(volume : Measure E) with hI_def
  set G : ℝ := ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
    ∂(volume : Measure E) with hG_def
  set U : ℝ := ∫ x in Ω', (u x)^2 ∂(volume : Measure E) with hU_def
  set F : ℝ := ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hF_def
  have hI_nn : 0 ≤ I := by
    refine integral_nonneg ?_
    intro x
    refine mul_nonneg (sq_nonneg _) ?_
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG_nn : 0 ≤ G := integral_nonneg
    (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hU_nn : 0 ≤ U := integral_nonneg (fun x => sq_nonneg _)
  have hF_nn : 0 ≤ F := integral_nonneg (fun x => sq_nonneg _)
  -- Apply the non-smooth master inequality.
  have h_master := h_master_nonsmooth hh hh_le
  -- h_master: B.lam * I ≤ |C1_sum| + |C2_sum| + |C3_sum| + |R| + |Q|.
  -- Substitute the specific bounds.
  have hC1_h := hC1 hh hh_le
  have hC2_h := hC2 hh hh_le
  have hC3_h := hC3 hh hh_le
  have hCc_h := hCc hh hh_le
  have hCf_h := hCf hh hh_le
  -- Combine: λ · I ≤ |C1| + |C2| + |C3| + |R| + |Q|
  --              ≤ (ε_eff · I + C1 · G) + (ε_eff · I + C2 · G) + (C3 · G) +
  --                (ε_eff · I + Cc · (G + U)) + (ε_eff · I + Cf · (G + F))
  --              = 4 ε_eff · I + (C1 + C2 + C3 + Cc + Cf) · G + Cc · U + Cf · F
  --              = (λ/2) · I + (...) · G + Cc · U + Cf · F
  --              ≤ (λ/2) · I + C · (G + U + F).
  have h_4ε_eq : 4 * ε_eff = B.lam / 2 := by
    rw [hε_eff_def]; ring
  have h_combine : B.lam * I ≤
      4 * ε_eff * I + (C1 + C2 + C3 + Cc + Cf) * G + Cc * U + Cf * F := by
    -- Sum up the cross-term and data-term bounds.
    -- |R| (f-term, from master) is the C_f bound; |Q| (c-term) is the C_c bound.
    -- Specifically, from the master inequality:
    -- λ I ≤ |C1_sum| + |C2_sum| + |C3_sum| + |R| + |Q|
    -- where R = ∫_Ω f · v_test and Q = ∫_Ω c u v_test.
    -- The bounds give:
    -- |C1_sum| ≤ ε_eff · I + C1 · G
    -- |C2_sum| ≤ ε_eff · I + C2 · G
    -- |C3_sum| ≤ C3 · G
    -- |Q| ≤ ε_eff · I + Cc · (G + U)
    -- |R| ≤ ε_eff · I + Cf · (G + F)
    -- Sum: ≤ 4 ε_eff · I + (C1 + C2 + C3 + Cc + Cf) · G + Cc · U + Cf · F.
    have h_sum_bound :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∫ x in Ω, f x *
              DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| +
          |∫ x in Ω, B.c x * u x *
              DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x ∂(volume : Measure E)| ≤
        (ε_eff * I + C1 * G) + (ε_eff * I + C2 * G) + (C3 * G) +
          (ε_eff * I + Cf * (G + F)) + (ε_eff * I + Cc * (G + U)) := by
      have h1 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := hC1_h
      have h1' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := by
        rw [← abs_neg]; exact h1
      have h2 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := hC2_h
      have h2' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := by
        rw [← abs_neg]; exact h2
      have h3 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := hC3_h
      have h3' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := by
        rw [← abs_neg]; exact h3
      linarith
    -- λ I ≤ sum bound.
    refine h_master.trans (h_sum_bound.trans ?_)
    -- Sum bound = 4 ε_eff I + (C1+C2+C3+Cc+Cf) G + Cc U + Cf F.
    have hCc_distrib : Cc * (G + U) = Cc * G + Cc * U := by ring
    have hCf_distrib : Cf * (G + F) = Cf * G + Cf * F := by ring
    linarith [hCc_distrib, hCf_distrib]
  -- 4 ε_eff = λ/2; combine with bounds.
  rw [show (4 * ε_eff * I) = (B.lam / 2) * I from by rw [h_4ε_eq]] at h_combine
  -- Now combine: (λ/2) I + (C1+...+Cf) G + Cc U + Cf F ≤ (λ/2) I + C (G + U + F).
  have hC_grad_le : C1 + C2 + C3 + Cc + Cf ≤ C := le_max_left _ _
  have hC_Cc_le : Cc ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_Cf_le : Cf ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have h_step1 : (C1 + C2 + C3 + Cc + Cf) * G ≤ C * G :=
    mul_le_mul_of_nonneg_right hC_grad_le hG_nn
  have h_step2 : Cc * U ≤ C * U :=
    mul_le_mul_of_nonneg_right hC_Cc_le hU_nn
  have h_step3 : Cf * F ≤ C * F :=
    mul_le_mul_of_nonneg_right hC_Cf_le hF_nn
  have h_C_dist : C * (G + U + F) = C * G + C * U + C * F := by ring
  linarith

/-! ## Absorbed corollary: explicit `(λ/2) · I ≤ C · (G + U + F)` -/

set_option linter.unusedVariables false in
/-- **Absorbed form of `nirenberg_master_inequality_after_young_nonsmooth`.**

After moving the `(λ/2) · I` term from RHS to LHS in the headline
`nirenberg_master_inequality_after_young_nonsmooth`, we obtain
  `(λ/2) · ∫ η² ∑_i (D_h^k g_i)² ≤ C · (G + U + F)`,
which is the cleaner uniform-in-`h` L² bound on the difference quotient
of the weak gradient, weighted by `η²`. -/
theorem nirenberg_master_inequality_absorbed_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_loc : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    (h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := nirenberg_master_inequality_after_young_nonsmooth
    (d := d) B hu_l2 hf_l2_loc hg_l2 h_weakPartial hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hη_in_Ω' hh_supp_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound
    h_master_nonsmooth
  refine ⟨C, hC_nn, ?_⟩
  intro h hh hh_le
  have h_main := hC hh hh_le
  -- h_main: λ · I ≤ (λ/2) · I + C · (G + U + F).
  -- Subtracting (λ/2) · I gives: (λ/2) · I ≤ C · (G + U + F).
  -- (Note: we use λ - λ/2 = λ/2, valid since the inequality is on ℝ.)
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
    ∂(volume : Measure E) with hI_def
  have h_lam_split : B.lam * I - (B.lam / 2) * I = (B.lam / 2) * I := by ring
  linarith [h_main]

/-! ## Localised corollary: bound on `D_h^k g_i` over `{η = 1}` -/

set_option linter.unusedVariables false in
/-- **Localised non-smooth absorbing inequality.**

A direct consequence of `nirenberg_master_inequality_absorbed_nonsmooth`:
since `η x = 1` whenever `x ∈ Ω''` (here `Ω''` is any set on which
`η ≡ 1`, e.g. an inner concentric ball), the weighted integral
`∫ η² · ∑_i (D_h^k g_i)²` is at least `∫_{Ω''} ∑_i (D_h^k g_i)²`. We
therefore obtain the uniform-in-`h` bound
  `(λ/2) · ∫_{Ω''} ∑_i (D_h^k g_i)² ≤ C · (G + U + F)`,
which is the standard local L² estimate on the difference quotient of
the weak gradient. -/
theorem nirenberg_diffQuot_g_localL2_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_loc : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    (h_weakPartial : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := d) i (g i) u Set.univ)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * ∫ x in Ω'',
          ∑ i : Fin d, DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := nirenberg_master_inequality_absorbed_nonsmooth
    (d := d) B hu_l2 hf_l2_loc hg_l2 h_weakPartial hη hη_supp hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hη_in_Ω' hh_supp_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound
    h_master_nonsmooth
  refine ⟨C, hC_nn, ?_⟩
  intro h hh hh_le
  have h_main := hC hh hh_le
  -- The key observation: ∫_{Ω''} ∑_i (D_h^k g_i)² ≤ ∫ η² · ∑_i (D_h^k g_i)²
  -- because η = 1 on Ω''.
  set sumSq : E → ℝ := fun x : E => ∑ i : Fin d,
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x ^ 2
    with hsumSq_def
  have h_sumSq_nn : ∀ x : E, 0 ≤ sumSq x := by
    intro x; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- ∫_{Ω''} sumSq = ∫ Ω''.indicator sumSq.
  -- Pointwise: Ω''.indicator sumSq x ≤ η² x · sumSq x.
  --   On Ω'': indicator = sumSq, η² · sumSq = 1 · sumSq = sumSq. So equal.
  --   Off Ω'': indicator = 0, η² · sumSq ≥ 0. So 0 ≤ η² · sumSq.
  have h_pointwise : ∀ x : E,
      Ω''.indicator sumSq x ≤ (η x)^2 * sumSq x := by
    intro x
    by_cases hx : x ∈ Ω''
    · rw [Set.indicator_of_mem hx]
      rw [hη_one_on_Ω'' x hx, one_pow, one_mul]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (sq_nonneg _) (h_sumSq_nn x)
  -- Integrability infrastructure for indicator and η²·sumSq.
  have h_eta_sq_sumSq_int : Integrable (fun x : E => (η x)^2 * sumSq x)
      (volume : Measure E) := by
    have h_per_i : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure E) := by
      intro i
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_supp
        i k h 1
      have h_eq : (fun x : E => (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : E => 1 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_sum_int := integrable_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => h_per_i i)
    have h_eq : (fun x : E => (η x)^2 * sumSq x) =
        (fun x : E => ∑ i : Fin d,
          (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
      funext x
      simp only [hsumSq_def, Finset.mul_sum]
    rw [h_eq]
    exact h_sum_int
  have h_indicator_int : Integrable (fun x : E => Ω''.indicator sumSq x)
      (volume : Measure E) := by
    refine h_eta_sq_sumSq_int.mono' ?_ ?_
    · refine AEStronglyMeasurable.indicator ?_ hΩ''_meas
      -- sumSq is AE strongly measurable since each diffQuot k h (g i) is.
      have h_per_i_aesm : ∀ i : Fin d, AEStronglyMeasurable
          (fun x : E => (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        intro i
        exact (aestronglyMeasurable_diffQuot (d := d) k h
          (hg_l2 i).aestronglyMeasurable).pow 2
      have h_sum_aesm : AEStronglyMeasurable
          (fun x : E => ∑ i : Fin d,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        have h_aux := Finset.aestronglyMeasurable_sum
          (Finset.univ : Finset (Fin d)) (fun i _ => h_per_i_aesm i)
        have h_eq : (∑ i ∈ (Finset.univ : Finset (Fin d)),
              fun x : E => (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) =
            (fun x : E => ∑ i : Fin d,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g i) x)^2) := by
          funext x
          rw [Finset.sum_apply]
        rw [h_eq] at h_aux
        exact h_aux
      exact h_sum_aesm
    · refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs]
      have h_indicator_nn : 0 ≤ Ω''.indicator sumSq x :=
        Set.indicator_nonneg (fun y _ => h_sumSq_nn y) x
      rw [abs_of_nonneg h_indicator_nn]
      exact h_pointwise x
  -- Compare integrals.
  have h_int_le : ∫ x, Ω''.indicator sumSq x ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 * sumSq x ∂(volume : Measure E) :=
    integral_mono h_indicator_int h_eta_sq_sumSq_int h_pointwise
  -- Convert indicator integral to set integral.
  have h_indicator_eq : ∫ x, Ω''.indicator sumSq x ∂(volume : Measure E) =
      ∫ x in Ω'', sumSq x ∂(volume : Measure E) :=
    MeasureTheory.integral_indicator hΩ''_meas
  rw [h_indicator_eq] at h_int_le
  -- Now: (λ/2) · ∫_{Ω''} sumSq ≤ (λ/2) · ∫ η² · sumSq ≤ C · (G + U + F).
  have h_lam_half_nn : 0 ≤ B.lam / 2 := by linarith [B.hlam_pos]
  have h_step1 : (B.lam / 2) * ∫ x in Ω'', sumSq x ∂(volume : Measure E) ≤
      (B.lam / 2) * ∫ x, (η x)^2 * sumSq x ∂(volume : Measure E) :=
    mul_le_mul_of_nonneg_left h_int_le h_lam_half_nn
  exact h_step1.trans h_main

end DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
