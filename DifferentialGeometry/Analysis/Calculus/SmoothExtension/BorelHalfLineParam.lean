import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Parametrized Borel half-line extension

This is the parameter-uniform generalization of `borel_halfLine_extend`. Given a family
`g : ℝ → E → F` that is jointly `C^∞` on the closed-half-line slab `Set.Ici 0 ×ˢ K` (with `K`
compact and `z₀` in its interior), we build a single function `gext : ℝ → E → F` that is jointly
`C^∞` at every point `(t₀, z₀)` and agrees with `g` for all `t ≥ 0` near `z₀`.

## Construction

Write `cₙ z := iteratedDerivWithin n (g · z) (Set.Ici 0) 0` for the one-sided `t`-jet of `g(·, z)`.
The first non-trivial fact (`param_jet_contDiffOn`) is that `cₙ` is `C^∞` in the parameter `z`,
obtained by inducting `ContDiffWithinAt.fderivWithin_apply` over the joint slice
`(z, t) ↦ iteratedDerivWithin n (g · z) (Set.Ici 0) t`.

We then run the Borel series jointly on `ℝ × E`: the `n`-th term is
`fₙ(t, z) = ((λₙ)⁻ⁿ · borelBumpMono n (λₙ t)) • (ρ z • cₙ z)`, where `ρ` is a smooth cutoff equal
to `1` at `z₀` and supported in `interior K` (this is where finite-dimensionality of `E` enters —
it is needed for a smooth compactly-supported bump), and `λₙ ≥ 1` is a rapidly increasing scale.
The scale is chosen (`paramScale`) to dominate `4ⁿ · Gₙ · (1 + Aₙ)`, where `Gₙ` bounds the
bump-monomial derivatives and `Aₙ` bounds all `z`-derivatives of `ρ · cₙ` (finite by compact
support). The key joint estimate `paramTerm_iteratedFDeriv_bound` then gives
`‖iteratedFDeriv ℝ k fₙ (t, z)‖ ≤ 2⁻ⁿ` for all `k < n`, uniformly in `(t, z)`, by expanding the
product via `norm_iteratedFDeriv_smul_le` and pre-composition with the coordinate projections.
Summability of these bounds feeds `contDiff_tsum`, so the series is globally `C^∞` on `ℝ × E`.

Away from the seam `t = 0` the extension `gext t z := if 0 ≤ t then g t z else ∑' n, fₙ(t, z)` is
`C^∞` because it locally agrees with either `g` (on the open upper half) or the smooth series (on
the open lower half).

## Deferred input

The seam case `t₀ = 0` is the *joint* analogue of `contDiff_if_le_of_jet_match` across the
hyperplane `{0} × E`: it requires that the globally-smooth series and `g` share their full joint
Taylor jet at `(0, z₀)`. The series matches `g`'s one-sided `t`-jet `cₙ` for every parameter `z`
near `z₀` by construction, so the mixed `t`/`z` Taylor coefficients agree by Clairaut symmetry, but
formalising this bivariate-Taylor decomposition of `iteratedFDeriv` on a product, together with the
joint hyperplane glue, is a self-contained deep result and is left here as the file's single
deferred `sorry` (so `borel_halfLine_extend_param` transitively depends on `sorryAx`).
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

section Bridge

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness of the partial `t`-jet of a jointly-smooth family. If `uncurry g` is `C∞`
on `Ici 0 ×ˢ U`, then `(z, t) ↦ iteratedDerivWithin n (g · z) (Ici 0) t` is `C∞`
on `U ×ˢ Ici 0`, for every order `n`. -/
private theorem param_iteratedDerivWithin_contDiffOn
    (g : ℝ → E → F) (U : Set E)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U)) :
    ∀ n : ℕ, ContDiffOn ℝ ∞
      (fun p : E × ℝ => iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) p.2)
      (U ×ˢ (Set.Ici (0:ℝ))) := by
  have hgswap : ContDiffOn ℝ ∞ (fun p : E × ℝ => g p.2 p.1) (U ×ˢ Set.Ici 0) := by
    have hswap : ContDiffOn ℝ ∞ (fun p : E × ℝ => (p.2, p.1)) (U ×ˢ Set.Ici 0) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    have hmaps : Set.MapsTo (fun p : E × ℝ => (p.2, p.1)) (U ×ˢ Set.Ici 0) (Set.Ici 0 ×ˢ U) := by
      intro p hp; exact ⟨hp.2, hp.1⟩
    exact hg.comp hswap hmaps
  intro n
  induction n with
  | zero =>
    simp only [iteratedDerivWithin_zero]
    exact hgswap
  | succ n IH =>
    have hUDt : UniqueDiffOn ℝ (Set.Ici (0:ℝ)) := uniqueDiffOn_Ici 0
    have hrw : ∀ p : E × ℝ, p ∈ U ×ˢ Set.Ici (0:ℝ) →
        iteratedDerivWithin (n+1) (fun s => g s p.1) (Set.Ici 0) p.2 =
          fderivWithin ℝ (fun s => iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) s)
            (Set.Ici 0) p.2 (1:ℝ) := by
      intro p _
      rw [iteratedDerivWithin_succ, derivWithin]
    refine ContDiffOn.congr ?_ hrw
    intro q hq
    have hf : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (p : E × ℝ) (s : ℝ) =>
          iteratedDerivWithin n (fun s => g s p.1) (Set.Ici 0) s))
        ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (q, q.2) := by
      have hproj : ContDiffWithinAt ℝ ∞ (fun r : (E × ℝ) × ℝ => (r.1.1, r.2))
          ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (q, q.2) :=
        ((contDiff_fst.fst).prodMk contDiff_snd).contDiffWithinAt
      have hmaps : Set.MapsTo (fun r : (E × ℝ) × ℝ => (r.1.1, r.2))
          ((U ×ˢ Set.Ici (0:ℝ)) ×ˢ Set.Ici 0) (U ×ˢ Set.Ici 0) := by
        intro r hr; exact ⟨hr.1.1, hr.2⟩
      exact (IH.contDiffWithinAt ⟨hq.1, hq.2⟩).comp (q, q.2) hproj hmaps
    have hgsec : ContDiffWithinAt ℝ ∞ (fun p : E × ℝ => p.2) (U ×ˢ Set.Ici (0:ℝ)) q :=
      contDiff_snd.contDiffWithinAt
    have hksec : ContDiffWithinAt ℝ ∞ (fun _ : E × ℝ => (1:ℝ)) (U ×ˢ Set.Ici (0:ℝ)) q :=
      contDiffWithinAt_const
    have hst : (U ×ˢ Set.Ici (0:ℝ)) ⊆ (fun p : E × ℝ => p.2) ⁻¹' Set.Ici 0 := fun p hp => hp.2
    have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    exact ContDiffWithinAt.fderivWithin_apply hf hgsec hksec hUDt hmn hq hst

/-- The `t = 0` slice: `z ↦ iteratedDerivWithin n (g · z) (Ici 0) 0` is `C∞` on `U`. -/
private theorem param_jet_contDiffOn
    (g : ℝ → E → F) (U : Set E)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z : E => iteratedDerivWithin n (fun s => g s z) (Set.Ici 0) 0) U := by
  have hsec : ContDiffOn ℝ ∞ (fun z : E => (z, (0:ℝ))) U :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun z : E => (z, (0:ℝ))) U (U ×ˢ Set.Ici 0) :=
    fun z hz => ⟨hz, Set.self_mem_Ici⟩
  exact (param_iteratedDerivWithin_contDiffOn g U hg n).comp hsec hmaps

end Bridge

section Engine

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform-over-`j ≤ n` global bound on the iterated Fréchet derivatives of a compactly
supported `C∞` coefficient `a : E → F`. -/
private theorem param_coeff_deriv_bound (a : E → F) (ha : ContDiff ℝ ∞ a)
    (hsupp : HasCompactSupport a) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ n, ∀ z : E, ‖iteratedFDeriv ℝ j a z‖ ≤ A := by
  have hbnd : ∀ j, ∃ C : ℝ, ∀ z : E, ‖iteratedFDeriv ℝ j a z‖ ≤ C := by
    intro j
    have hcs : HasCompactSupport (iteratedFDeriv ℝ j a) := hsupp.iteratedFDeriv j
    have hcont : Continuous (iteratedFDeriv ℝ j a) :=
      ha.continuous_iteratedFDeriv (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤ ∞)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨C, hC⟩
  choose C hC using hbnd
  refine ⟨(Finset.range (n + 1)).sup' (by simp) (fun j => max (C j) 0), ?_, ?_⟩
  · exact le_trans (le_max_right _ _)
      (Finset.le_sup' (fun j => max (C j) 0) (by simp : (0 : ℕ) ∈ Finset.range (n + 1)))
  · intro j hj z
    refine le_trans (hC j z) ?_
    refine le_trans (le_max_left (C j) 0) ?_
    exact Finset.le_sup' (fun j => max (C j) 0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

variable (a : ℕ → E → F)
    (ha : ∀ n, ContDiff ℝ ∞ (a n)) (hsupp : ∀ n, HasCompactSupport (a n))

/-- The scale `λₙ ≥ 1` for the `n`-th parametrized term: large enough that the joint
`k`-th derivative (`k < n`) of the term is `≤ 2⁻ⁿ`. It dominates `4ⁿ · Gₙ · (1 + Aₙ)`, where
`Gₙ` bounds the bump-monomial derivatives and `Aₙ` bounds the `z`-derivatives of `a n`. -/
private def paramScale (n : ℕ) : ℝ :=
  max 1 ((4:ℝ) ^ n * Classical.choose (borelBumpMono_deriv_bound n) *
    (1 + Classical.choose (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n)))

private theorem one_le_paramScale (n : ℕ) : 1 ≤ paramScale a ha hsupp n :=
  le_max_left _ _

private theorem paramScale_pos (n : ℕ) : 0 < paramScale a ha hsupp n :=
  lt_of_lt_of_le one_pos (one_le_paramScale a ha hsupp n)

/-- The `n`-th parametrized Borel term on `ℝ × E`:
`fₙ(t,z) = ((λₙ)⁻ⁿ · borelBumpMono n (λₙ t)) • a n z`. The `t`-scalar is exactly the fixed-case
scalar; the constant vector is replaced by the smooth coefficient `a n z`. -/
private def paramTerm (n : ℕ) (p : ℝ × E) : F :=
  ((paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * p.1)) • a n p.2

private theorem paramTerm_contDiff (n : ℕ) : ContDiff ℝ ∞ (paramTerm a ha hsupp n) := by
  have hb : ContDiff ℝ ∞ (fun p : ℝ × E =>
      (paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * p.1)) :=
    contDiff_const.mul ((borelBumpMono_comp_smul_contDiff n (paramScale a ha hsupp n)).comp
      contDiff_fst)
  have ha' : ContDiff ℝ ∞ (fun p : ℝ × E => a n p.2) := (ha n).comp contDiff_snd
  exact hb.smul ha'

/-- The `t`-scalar of the `n`-th parametrized term:
`sₙ(t) = (λₙ)⁻ⁿ · borelBumpMono n (λₙ t)`. -/
private def paramScalar (n : ℕ) (t : ℝ) : ℝ :=
  (paramScale a ha hsupp n)⁻¹ ^ n * borelBumpMono n (paramScale a ha hsupp n * t)

private theorem paramScalar_contDiff (n : ℕ) : ContDiff ℝ ∞ (paramScalar a ha hsupp n) :=
  contDiff_const.mul (borelBumpMono_comp_smul_contDiff n (paramScale a ha hsupp n))

private theorem paramScalar_hasCompactSupport (n : ℕ) :
    HasCompactSupport (paramScalar a ha hsupp n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(2 / paramScale a ha hsupp n)) (2 / paramScale a ha hsupp n)) isCompact_Icc
  intro t ht
  by_contra hmem
  apply ht
  have hL0 : 0 < paramScale a ha hsupp n := paramScale_pos a ha hsupp n
  have h2 : 2 ≤ (paramScale a ha hsupp n * t) ^ 2 := by
    rcases not_and_or.1 hmem with h | h
    · have ht' : t < -(2 / paramScale a ha hsupp n) := lt_of_not_ge h
      have hlt : paramScale a ha hsupp n * t <
          paramScale a ha hsupp n * (-(2 / paramScale a ha hsupp n)) :=
        mul_lt_mul_of_pos_left ht' hL0
      rw [mul_neg, mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
    · have ht' : 2 / paramScale a ha hsupp n < t := lt_of_not_ge h
      have hlt : paramScale a ha hsupp n * (2 / paramScale a ha hsupp n) <
          paramScale a ha hsupp n * t := mul_lt_mul_of_pos_left ht' hL0
      rw [mul_div_cancel₀ _ hL0.ne'] at hlt
      nlinarith
  simp only [paramScalar, borelBumpMono, borelCutoff_eq_zero h2, zero_mul, zero_div, mul_zero]

/-- Pointwise iterated derivative of the `t`-scalar. -/
private theorem paramScalar_iteratedDeriv (n i : ℕ) (t : ℝ) :
    iteratedDeriv i (paramScalar a ha hsupp n) t =
      (paramScale a ha hsupp n)⁻¹ ^ n * (paramScale a ha hsupp n) ^ i *
        iteratedDeriv i (borelBumpMono n) (paramScale a ha hsupp n * t) := by
  set L : ℝ := paramScale a ha hsupp n with hLdef
  have hcd : ContDiffAt ℝ i (fun s => borelBumpMono n (L * s)) t :=
    (borelBumpMono_comp_smul_contDiff (N := (i : ℕ∞)) n L).contDiffAt
  have hconst : iteratedDeriv i (paramScalar a ha hsupp n) t =
      L⁻¹ ^ n • iteratedDeriv i (fun s => borelBumpMono n (L * s)) t := by
    have := iteratedDeriv_const_smul (𝕜 := ℝ) (R := ℝ) (n := i) (x := t)
      (f := fun s => borelBumpMono n (L * s)) hcd (L⁻¹ ^ n)
    simpa only [paramScalar, hLdef, Pi.smul_apply, smul_eq_mul] using this
  rw [hconst]
  have hcomp : iteratedDeriv i (fun s => borelBumpMono n (L * s)) t =
      L ^ i • iteratedDeriv i (borelBumpMono n) (L * t) := by
    have h := iteratedDeriv_comp_const_smul (n := i) (f := borelBumpMono n)
      (borelBumpMono_contDiff (N := (i : ℕ∞)) n) L
    exact congrFun h t
  rw [hcomp]; simp only [smul_eq_mul]; ring

/-- For `i < n`, the `i`-th derivative of the `t`-scalar is bounded by `Gₙ / λₙ`, where `Gₙ` is
the bump-monomial derivative bound. -/
private theorem paramScalar_iteratedDeriv_bound {n i : ℕ} (hin : i < n) (t : ℝ) :
    ‖iteratedDeriv i (paramScalar a ha hsupp n) t‖ ≤
      Classical.choose (borelBumpMono_deriv_bound n) / paramScale a ha hsupp n := by
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  have hGspec := Classical.choose_spec (borelBumpMono_deriv_bound n)
  rw [← hGdef] at hGspec
  obtain ⟨hGnn, hGbound⟩ := hGspec
  set L : ℝ := paramScale a ha hsupp n with hLdef
  have hL1 : 1 ≤ L := one_le_paramScale a ha hsupp n
  have hL0 : 0 < L := paramScale_pos a ha hsupp n
  rw [paramScalar_iteratedDeriv]
  have hD : ‖iteratedDeriv i (borelBumpMono n) (L * t)‖ ≤ G := hGbound i (le_of_lt hin) (L * t)
  have hpow : L⁻¹ ^ n * L ^ i ≤ L⁻¹ := by
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    have hrw : L ^ n * L⁻¹ = L ^ (n - 1) := by
      have : L ^ n = L ^ (n - 1) * L := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [this, mul_assoc, mul_inv_cancel₀ hL0.ne', mul_one]
    rw [hrw]; exact pow_le_pow_right₀ hL1 (by omega)
  have hcoeff_nn : (0:ℝ) ≤ L⁻¹ ^ n * L ^ i := by positivity
  rw [show L⁻¹ ^ n * L ^ i * iteratedDeriv i (borelBumpMono n) (L * t)
      = (L⁻¹ ^ n * L ^ i) • iteratedDeriv i (borelBumpMono n) (L * t) from by
        rw [smul_eq_mul], norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff_nn]
  calc (L⁻¹ ^ n * L ^ i) * ‖iteratedDeriv i (borelBumpMono n) (L * t)‖
      ≤ L⁻¹ * G := mul_le_mul hpow hD (norm_nonneg _) (by positivity)
    _ = G / L := by rw [inv_mul_eq_div]

/-- Pre-composing with the first projection does not increase the iterated-derivative norm. -/
private theorem norm_iteratedFDeriv_comp_fst_le {b : ℝ → F} (hb : ContDiff ℝ ∞ b) (i : ℕ)
    (p : ℝ × E) : ‖iteratedFDeriv ℝ i (fun q : ℝ × E => b q.1) p‖ ≤ ‖iteratedFDeriv ℝ i b p.1‖ := by
  have hcomp : (fun q : ℝ × E => b q.1) = b ∘ (ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [hcomp, (ContinuousLinearMap.fst ℝ ℝ E).iteratedFDeriv_comp_right hb p
    (by exact_mod_cast le_top : (i : WithTop ℕ∞) ≤ ∞)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ E
  have hprod : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 := by
    calc ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ ∏ _j : Fin i, (1:ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hfst)
      _ = 1 := by simp
  have hpval : (ContinuousLinearMap.fst ℝ ℝ E) p = p.1 := rfl
  rw [hpval]
  calc ‖iteratedFDeriv ℝ i b p.1‖ * ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ ℝ E‖
      ≤ ‖iteratedFDeriv ℝ i b p.1‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i b p.1‖ := mul_one _

/-- Pre-composing with the second projection does not increase the iterated-derivative norm. -/
private theorem norm_iteratedFDeriv_comp_snd_le {b : E → F} (hb : ContDiff ℝ ∞ b) (j : ℕ)
    (p : ℝ × E) : ‖iteratedFDeriv ℝ j (fun q : ℝ × E => b q.2) p‖ ≤ ‖iteratedFDeriv ℝ j b p.2‖ := by
  have hcomp : (fun q : ℝ × E => b q.2) = b ∘ (ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rw [hcomp, (ContinuousLinearMap.snd ℝ ℝ E).iteratedFDeriv_comp_right hb p
    (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤ ∞)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ E
  have hprod : ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ 1 := by
    calc ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ ∏ _j : Fin j, (1:ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hsnd)
      _ = 1 := by simp
  have hpval : (ContinuousLinearMap.snd ℝ ℝ E) p = p.2 := rfl
  rw [hpval]
  calc ‖iteratedFDeriv ℝ j b p.2‖ * ∏ _j : Fin j, ‖ContinuousLinearMap.snd ℝ ℝ E‖
      ≤ ‖iteratedFDeriv ℝ j b p.2‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j b p.2‖ := mul_one _

/-- **The joint Borel decay estimate.** By the scale choice, the joint `k`-th Fréchet derivative
of the `n`-th parametrized term on `ℝ × E` is bounded by `2⁻ⁿ` whenever `k < n`, uniformly in
`(t, z)`. -/
private theorem paramTerm_iteratedFDeriv_bound {n k : ℕ} (hkn : k < n) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ (2 : ℝ)⁻¹ ^ n := by
  set L : ℝ := paramScale a ha hsupp n with hLdef
  set G : ℝ := Classical.choose (borelBumpMono_deriv_bound n) with hGdef
  set A : ℝ := Classical.choose (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n) with hAdef
  have hGnn : 0 ≤ G := (Classical.choose_spec (borelBumpMono_deriv_bound n)).1
  have hAspec := Classical.choose_spec (param_coeff_deriv_bound (a n) (ha n) (hsupp n) n)
  rw [← hAdef] at hAspec
  obtain ⟨hAnn, hAbound⟩ := hAspec
  have hL0 : 0 < L := paramScale_pos a ha hsupp n
  have hLmax : (4:ℝ) ^ n * G * (1 + A) ≤ L := le_max_right _ _
  -- paramTerm n = (paramScalar∘fst) • (a∘snd)
  have hterm_eq : paramTerm a ha hsupp n =
      fun q : ℝ × E => (fun r : ℝ × E => paramScalar a ha hsupp n r.1) q •
        (fun r : ℝ × E => a n r.2) q := by
    funext q; rfl
  rw [hterm_eq]
  have hsmul := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun r : ℝ × E => paramScalar a ha hsupp n r.1)
    (g := fun r : ℝ × E => a n r.2)
    ((paramScalar_contDiff a ha hsupp n).comp contDiff_fst)
    ((ha n).comp contDiff_snd) p (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)
  refine le_trans hsmul ?_
  -- Bound each summand by C(k,i) * (G/L) * A.
  have hsummand : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun r : ℝ × E => paramScalar a ha hsupp n r.1) p‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun r : ℝ × E => a n r.2) p‖
      ≤ (k.choose i : ℝ) * (G / L) * A := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
    have hilt : i < n := lt_of_le_of_lt hik hkn
    have hib : ‖iteratedFDeriv ℝ i (fun r : ℝ × E => paramScalar a ha hsupp n r.1) p‖ ≤ G / L := by
      refine le_trans (norm_iteratedFDeriv_comp_fst_le (paramScalar_contDiff a ha hsupp n) i p) ?_
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have hb := paramScalar_iteratedDeriv_bound a ha hsupp hilt p.1
      rwa [← hLdef, ← hGdef] at hb
    have hjb : ‖iteratedFDeriv ℝ (k - i) (fun r : ℝ × E => a n r.2) p‖ ≤ A := by
      refine le_trans (norm_iteratedFDeriv_comp_snd_le (ha n) (k - i) p) ?_
      exact hAbound (k - i) (by omega) p.2
    gcongr
  refine le_trans (Finset.sum_le_sum hsummand) ?_
  -- ∑ C(k,i) * (G/L) * A = 2^k * (G/L) * A
  have hsum_eq : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (G / L) * A
      = (2:ℝ) ^ k * (G / L) * A := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 2
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast; ring
  rw [hsum_eq]
  -- Now finish: 2^k * (G/L) * A ≤ 2⁻ⁿ.
  rcases eq_or_lt_of_le hGnn with hG0 | hGpos
  · rw [← hG0]; simp
  · have h1A : (0:ℝ) < 1 + A := by positivity
    have h2n : (0:ℝ) < (2:ℝ) ^ n := by positivity
    -- Step 1: G / L ≤ 1 / (4^n * (1 + A)).
    have hGL : G / L ≤ 1 / ((4:ℝ) ^ n * (1 + A)) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]
      have hrw : G * ((4:ℝ) ^ n * (1 + A)) = (4:ℝ) ^ n * G * (1 + A) := by ring
      rw [hrw, one_mul]; exact hLmax
    have h2kn : (2:ℝ) ^ k ≤ (2:ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4n : (4:ℝ) ^ n = (2:ℝ) ^ n * (2:ℝ) ^ n := by rw [← mul_pow]; norm_num
    -- Reduce `2⁻ⁿ` to `1 / 2^n` and clear denominators.
    rw [inv_pow, inv_eq_one_div, le_div_iff₀ h2n]
    have hstep1 : (2:ℝ) ^ k * (G / L) * A * (2:ℝ) ^ n
        ≤ (2:ℝ) ^ n * (1 / ((4:ℝ) ^ n * (1 + A))) * A * (2:ℝ) ^ n := by
      have hAnn' : (0:ℝ) ≤ A := hAnn
      gcongr
    refine le_trans hstep1 ?_
    have hsimp : (2:ℝ) ^ n * (1 / ((4:ℝ) ^ n * (1 + A))) * A * (2:ℝ) ^ n = A / (1 + A) := by
      rw [h4n]; field_simp
    rw [hsimp, div_le_one h1A]; linarith

/-- For every derivative order `k`, the `k`-th joint Fréchet derivative of the `n`-th term is
globally bounded (compact support + continuity). -/
private theorem paramTerm_hasCompactSupport (n : ℕ) :
    HasCompactSupport (paramTerm a ha hsupp n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := tsupport (paramScalar a ha hsupp n) ×ˢ tsupport (a n))
    ((paramScalar_hasCompactSupport a ha hsupp n).prod (hsupp n))
  intro p hp
  rw [Function.mem_support] at hp
  have hterm_eq : paramTerm a ha hsupp n p = paramScalar a ha hsupp n p.1 • a n p.2 := rfl
  refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
  · intro hz
    apply hp
    rw [hterm_eq, hz, zero_smul]
  · intro hz
    apply hp
    rw [hterm_eq, hz, smul_zero]

private theorem paramTerm_iteratedFDeriv_global_bound (n k : ℕ) :
    ∃ B : ℝ, ∀ p : ℝ × E, ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ B := by
  have hcs : HasCompactSupport (iteratedFDeriv ℝ k (paramTerm a ha hsupp n)) :=
    (paramTerm_hasCompactSupport a ha hsupp n).iteratedFDeriv k
  have hcont : Continuous (iteratedFDeriv ℝ k (paramTerm a ha hsupp n)) :=
    (paramTerm_contDiff a ha hsupp n).continuous_iteratedFDeriv
      (by exact_mod_cast le_top : (k : WithTop ℕ∞) ≤ ∞)
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨B, hB⟩

/-- Summable dominating function for the parametrized Borel series: `2⁻ⁿ` for `k < n`, and a
global bound otherwise. -/
private def paramDomBound (k n : ℕ) : ℝ :=
  if k < n then (2 : ℝ)⁻¹ ^ n
  else Classical.choose (paramTerm_iteratedFDeriv_global_bound a ha hsupp n k)

private theorem paramDomBound_summable (k : ℕ) : Summable (paramDomBound a ha hsupp k) := by
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) := by
    simpa only [one_div] using summable_geometric_two
  refine Summable.congr_cofinite hgeom ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop k] with n hn
  rw [paramDomBound, if_pos hn]

private theorem paramDomBound_bound (k n : ℕ) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ k (paramTerm a ha hsupp n) p‖ ≤ paramDomBound a ha hsupp k n := by
  rw [paramDomBound]
  by_cases hkn : k < n
  · rw [if_pos hkn]; exact paramTerm_iteratedFDeriv_bound a ha hsupp hkn p
  · rw [if_neg hkn]
    exact Classical.choose_spec (paramTerm_iteratedFDeriv_global_bound a ha hsupp n k) p

/-- The parametrized Borel series `(t,z) ↦ ∑' n, fₙ(t,z)` is globally `C∞` on `ℝ × E`. -/
private theorem paramSeries_contDiff [CompleteSpace F] :
    ContDiff ℝ ∞ (fun p : ℝ × E => ∑' n, paramTerm a ha hsupp n p) :=
  contDiff_tsum (N := (⊤ : ℕ∞)) (v := paramDomBound a ha hsupp)
    (fun n => paramTerm_contDiff a ha hsupp n)
    (fun k _ => paramDomBound_summable a ha hsupp k)
    (fun k n p _ => paramDomBound_bound a ha hsupp k n p)

end Engine

section Setup

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplying a function smooth on an open set by a smooth cutoff supported inside that set
produces a globally smooth function. -/
private theorem contDiff_cutoff_smul {ρ : E → ℝ} {c : E → F} {U : Set E} (hU : IsOpen U)
    (hρ : ContDiff ℝ ∞ ρ) (htsupp : tsupport ρ ⊆ U) (hc : ContDiffOn ℝ ∞ c U) :
    ContDiff ℝ ∞ (fun z => ρ z • c z) := by
  rw [← contDiffOn_univ]
  intro z _
  by_cases hz : z ∈ tsupport ρ
  · have hzU : z ∈ U := htsupp hz
    have h1 : ContDiffWithinAt ℝ ∞ ρ Set.univ z := hρ.contDiffAt.contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ ∞ c Set.univ z :=
      (hc.contDiffAt (hU.mem_nhds hzU)).contDiffWithinAt
    exact h1.smul h2
  · -- z ∉ tsupport ρ: ρ ≡ 0 on the open complement, so the product is ≡ 0 near z.
    have hopen : (tsupport ρ)ᶜ ∈ 𝓝 z := (isClosed_tsupport ρ).isOpen_compl.mem_nhds hz
    have heq : (fun z => ρ z • c z) =ᶠ[𝓝 z] (fun _ => (0:F)) := by
      filter_upwards [hopen] with y hy
      have : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [this, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- **Parametrized Borel half-line extension.** Let `g : ℝ → E → F` be jointly `C∞` on
`Ici 0 ×ˢ K` for a compact `K` with `z₀` in its interior. Then there is a function `gext` that is
jointly `C∞` at every `(t₀, z₀)` and agrees with `g` for all `t ≥ 0` near `z₀`.

This is the `z`-uniform generalization of `borel_halfLine_extend`: the fixed-parameter jet
coefficients are promoted to smooth functions of the parameter `z`, multiplied by a smooth cutoff
near `z₀`, and the Borel series is run jointly on `ℝ × E`. The model space `E` is finite-dimensional
(as in every intended application, where `E` is a chart/tangent model `ℝ^d`); this is required to
build the smooth cutoff `ρ`. -/
theorem borel_halfLine_extend_param [FiniteDimensional ℝ E] [CompleteSpace F]
    (g : ℝ → E → F) (K : Set E) (hK : IsCompact K) (z₀ : E) (hz₀ : z₀ ∈ interior K)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ K)) :
    ∃ gext : ℝ → E → F,
      (∀ t₀ : ℝ, ContDiffAt ℝ ∞ (Function.uncurry gext) (t₀, z₀)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ᶠ z in nhds z₀, gext t z = g t z) := by
  classical
  -- A smooth cutoff `ρ ≡ 1` at `z₀`, supported in the open set `interior K`.
  obtain ⟨ρ, hρ_tsupp, hρ_cs, hρ_smooth0, _hρ_range, hρ_one⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (x := z₀) (isOpen_interior.mem_nhds hz₀)
  have hρ_smooth : ContDiff ℝ ∞ ρ := by
    rw [show (∞ : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]; exact hρ_smooth0
  set U : Set E := interior K with hU_def
  have hUopen : IsOpen U := isOpen_interior
  -- The jet coefficients are smooth on `U`.
  have hg' : ContDiffOn ℝ ∞ (Function.uncurry g) ((Set.Ici (0:ℝ)) ×ˢ U) :=
    hg.mono (Set.prod_mono_right interior_subset)
  -- The parametrized coefficient family `a n z = ρ z • cₙ z`.
  set a : ℕ → E → F :=
    fun n z => ρ z • iteratedDerivWithin n (fun s => g s z) (Set.Ici 0) 0 with ha_def
  have ha : ∀ n, ContDiff ℝ ∞ (a n) := fun n =>
    contDiff_cutoff_smul hUopen hρ_smooth hρ_tsupp (param_jet_contDiffOn g U hg' n)
  have hsupp : ∀ n, HasCompactSupport (a n) := fun n => hρ_cs.smul_right
  -- The extension.
  set gext : ℝ → E → F :=
    fun t z => if 0 ≤ t then g t z else ∑' n, paramTerm a ha hsupp n (t, z) with hgext_def
  refine ⟨gext, ?_, ?_⟩
  · -- Joint `C∞` at every `(t₀, z₀)`.
    intro t₀
    rcases lt_trichotomy t₀ 0 with ht | ht | ht
    · -- `t₀ < 0`: agrees with the globally smooth series near `(t₀, z₀)`.
      have hseries : ContDiff ℝ ∞ (fun p : ℝ × E => ∑' n, paramTerm a ha hsupp n p) :=
        paramSeries_contDiff a ha hsupp
      have heq : (Function.uncurry gext) =ᶠ[𝓝 (t₀, z₀)]
          (fun p : ℝ × E => ∑' n, paramTerm a ha hsupp n p) := by
        have hmem : Set.Iio (0:ℝ) ×ˢ (Set.univ : Set E) ∈ 𝓝 (t₀, z₀) :=
          prod_mem_nhds (Iio_mem_nhds ht) univ_mem
        filter_upwards [hmem] with p hp
        simp only [Function.uncurry, hgext_def, if_neg (not_le.mpr (Set.mem_Iio.mp hp.1))]
      exact hseries.contDiffAt.congr_of_eventuallyEq heq
    · -- `t₀ = 0`: the seam across the hyperplane `{0} × E`.
      -- Here `uncurry gext` is the piecewise glue of the globally-smooth Borel series `G`
      -- (lower side `t ≤ 0`) and `uncurry g` (upper side `t ≥ 0`). Smoothness at `(0, z₀)` is the
      -- *joint* analogue of `contDiff_if_le_of_jet_match`: it requires that the two pieces share
      -- their full joint Taylor jet at `(0, z₀)`, i.e.
      --   `iteratedFDerivWithin ℝ k (uncurry g) (Ici 0 ×ˢ U) (0, z₀)`
      --     `= iteratedFDeriv ℝ k (fun p => ∑' n, paramTerm a ha hsupp n p) (0, z₀)`  for all `k`.
      -- The series matches `g`'s *one-sided t-jet* (`cₙ z = ∂ₜⁿ g(·,z)|₀`) for every `z` near `z₀`
      -- by construction; the *mixed* `t`/`z` coefficients then agree by Clairaut symmetry, so the
      -- joint jets coincide. Formalising this bivariate-Taylor / mixed-partial decomposition of
      -- `iteratedFDeriv` on the product `ℝ × E`, together with the joint hyperplane glue
      -- (`HasFTaylorSeriesUpToOn` on a neighbourhood with the seam derivative produced by
      -- `HasFDerivWithinAt.union` over `(Iic 0 ×ˢ U) ∪ (Ici 0 ×ˢ U)`), is a self-contained deep
      -- result of its own — the joint/parametrized `contDiff_if_le_of_jet_match` — and is left as
      -- the single deferred input of this file.
      subst ht
      sorry
    · -- `t₀ > 0`: agrees with `g` near `(t₀, z₀)`.
      have hgU : ContDiffOn ℝ ∞ (Function.uncurry g) (Set.Ioi (0:ℝ) ×ˢ U) :=
        hg'.mono (Set.prod_mono_left Ioi_subset_Ici_self)
      have hopen : IsOpen (Set.Ioi (0:ℝ) ×ˢ U) := isOpen_Ioi.prod hUopen
      have hmem₀ : (t₀, z₀) ∈ Set.Ioi (0:ℝ) ×ˢ U := ⟨ht, hz₀⟩
      have hgAt : ContDiffAt ℝ ∞ (Function.uncurry g) (t₀, z₀) :=
        hgU.contDiffAt (hopen.mem_nhds hmem₀)
      have heq : (Function.uncurry gext) =ᶠ[𝓝 (t₀, z₀)] (Function.uncurry g) := by
        have hmem : Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set E) ∈ 𝓝 (t₀, z₀) :=
          prod_mem_nhds (Ioi_mem_nhds ht) univ_mem
        filter_upwards [hmem] with p hp
        simp only [Function.uncurry, hgext_def, if_pos (le_of_lt (Set.mem_Ioi.mp hp.1))]
      exact hgAt.congr_of_eventuallyEq heq
  · -- EqOn for `t ≥ 0`.
    intro t ht
    filter_upwards with z
    simp only [hgext_def, if_pos ht]

end Setup

end Analysis
end DifferentialGeometry
