import DifferentialGeometry.Analysis.ODE.FlowVariationalLinearMap

/-!
# Parametric linear ODE solution operator

For a continuous family of bounded linear operators `A : F → ℝ → (G →L[ℝ] G)`
on a Banach space `G`, parametric in `x ∈ F`, this file builds the solution
operator of the linear ODE

`Z'(t) = A(x, t) Z(t),  Z(h₀) = Z₀(x)`

on an open interval `Ioo a b` around `h₀`, together with the initial-condition
and ODE clauses.

## Main definitions

* `HasLinearODESolution A a b h₀ Z₀ x` — per-parameter existence predicate
  on the open interval `Ioo a b`:  there is a curve `Z : ℝ → G` satisfying
  `Z h₀ = Z₀ x` and the ODE pointwise on `Ioo a b`.
* `linearODESolution A a b h₀ Z₀ : F → ℝ → G` — the parametric solution
  on the open interval `Ioo a b`.  Defined unconditionally via
  `Classical.choose`: returns *the* solution on `Ioo a b` when
  `HasLinearODESolution` holds, and the constant fallback `fun _ => Z₀ x`
  otherwise.

## Main results

* `exists_linearODE_solution_of_short` — short-interval existence on
  `Icc (h₀ - T) (h₀ + T)` via Mathlib `IsPicardLindelof`, assuming `M · T < 1`
  for the operator-norm bound `M` on this interval.
* `linearODE_unique_on_Ioo` — uniqueness on `Ioo a b` via Mathlib
  `ODE_solution_unique_of_mem_Ioo`.
* `linearODESolution_init` — unconditional: `linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x`.
* `linearODESolution_hasDerivAt_of_hasSolution` — ODE clause under the
  `HasLinearODESolution` hypothesis.
* `hasLinearODESolution_of_continuousOn` — discharges the per-parameter
  existence predicate from joint continuity of `A` on `U ×ˢ Ioo a b` and
  `x ∈ U`.  The construction iterates `exists_linearODE_solution_of_short`
  finitely many times to cover each closed sub-interval `Icc α β ⊂ Ioo a b`,
  then exhausts `Ioo a b` by a countable family of such sub-intervals.
* `linearODESolution_hasDerivAt` — wrapped ODE clause: combines
  `hasLinearODESolution_of_continuousOn` and
  `linearODESolution_hasDerivAt_of_hasSolution`.

All results are formulated on generic Banach spaces `F` and `G`; the parameter
space `F` carries no completeness assumption.  `[CompleteSpace G]` is required
for Picard–Lindelöf to apply to the state space.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

/-! ## Short-interval Picard for a linear ODE

For a fixed parameter `x` and a continuous, operator-norm-bounded coefficient
`A` on `Icc (h₀ - T) (h₀ + T)` with `M · T < 1`, the linear ODE
`Z'(t) = A(t) Z(t),  Z(h₀) = Z₀` has a solution on `Icc (h₀ - T) (h₀ + T)`.
-/

section ShortIntervalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/--
**Short-interval existence** for the linear ODE `Z'(t) = A(t) Z(t)` on
`Icc (h₀ - T) (h₀ + T)`, assuming `‖A t‖ ≤ M` on this interval and `M · T < 1`.
The solution exists for **every** initial value `Z₀ ∈ G`.

This is the elementary Picard step on which the global existence theory
(forthcoming in the follow-up substep) is built.
-/
theorem exists_linearODE_solution_of_short
    {A : ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + T), ‖A t‖ ≤ M)
    (Z₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Z₀ ∧
      ∀ t ∈ Icc (h₀ - T) (h₀ + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (h₀ - T) (h₀ + T)) t := by
  set v : ℝ → G → G := fun t y => A t y with hv_def
  set r₀ : ℝ := ‖Z₀‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMT_pos : 0 < 1 - M * T := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * T) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMT_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaT_le : M * a₀ * T ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * T) = r₀ + 1 := by
      rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * T = r₀ + 1 := by
      have : a₀ - M * a₀ * T = a₀ * (1 - M * T) := by ring
      rw [this, hkey]
    linarith
  let tmin : ℝ := h₀ - T
  let tmax : ℝ := h₀ + T
  have htmin_le_t₀ : tmin ≤ h₀ := by change h₀ - T ≤ h₀; linarith
  have ht₀_le_tmax : h₀ ≤ tmax := by change h₀ ≤ h₀ + T; linarith
  let t₀Icc : Icc tmin tmax := ⟨h₀, ⟨htmin_le_t₀, ht₀_le_tmax⟩⟩
  let aN : ℝ≥0 := ⟨a₀, ha₀_nn⟩
  let rN : ℝ≥0 := ⟨r₀, hr₀_nn⟩
  let LN : ℝ≥0 := ⟨M * a₀, mul_nonneg hM ha₀_nn⟩
  let KN : ℝ≥0 := ⟨M, hM⟩
  have hpl : IsPicardLindelof v t₀Icc (0 : G) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro t ht
      have hAτ_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le hAτ_bd
      exact hlip.lipschitzOnWith (s := closedBall (0 : G) aN)
    · intro y _
      have happly : Continuous (fun B : G →L[ℝ] G => B y) :=
        (ContinuousLinearMap.apply ℝ G y).continuous
      exact happly.comp_continuousOn hA_cont
    · intro t ht y hy
      have hAt_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hy_norm : ‖y‖ ≤ a₀ := by
        simpa [mem_closedBall_zero_iff] using hy
      change ‖v t y‖ ≤ (LN : ℝ)
      calc ‖v t y‖ = ‖A t y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul hAt_bd hy_norm (norm_nonneg _) hM
    · change (LN : ℝ) * max (tmax - h₀) (h₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - h₀) (h₀ - tmin) = T := by
        have h1 : tmax - h₀ = T := by change (h₀ + T) - h₀ = T; ring
        have h2 : h₀ - tmin = T := by change h₀ - (h₀ - T) = T; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      change M * a₀ * T ≤ a₀ - r₀
      exact hMaT_le
  have hZ₀_mem : Z₀ ∈ closedBall (0 : G) rN := by
    rw [mem_closedBall_zero_iff]; change ‖Z₀‖ ≤ r₀; rfl
  obtain ⟨Z, hZ_init, hZ_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hZ₀_mem
  exact ⟨Z, hZ_init, hZ_deriv⟩

end ShortIntervalExistence

/-! ## Uniqueness of solutions to a linear ODE on an open interval

For a fixed parameter `x`, two solutions of the linear ODE on `Ioo a b` sharing
the initial condition at `h₀ ∈ Ioo a b` agree on `Ioo a b`.  This follows from
`ODE_solution_unique_of_mem_Ioo` applied to the linear vector field
`v t y := A t y`, which is `‖A t‖`-Lipschitz with a uniform bound on each
compact sub-interval.
-/

section Uniqueness

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniqueness** of solutions to a linear ODE on an open interval `Ioo a b`. -/
theorem linearODE_unique_on_Ioo
    {A : ℝ → (G →L[ℝ] G)} {a b h₀ : ℝ}
    (ht₀ : h₀ ∈ Ioo a b)
    (hA_cont : ContinuousOn A (Ioo a b))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Ioo a b, HasDerivAt Z₁ (A t (Z₁ t)) t)
    (hZ₂ : ∀ t ∈ Ioo a b, HasDerivAt Z₂ (A t (Z₂ t)) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    EqOn Z₁ Z₂ (Ioo a b) := by
  intro t ht
  let v : ℝ → G → G := fun t y => A t y
  -- Pick a closed sub-interval `[a', b']` of `Ioo a b` containing both `t` and `h₀`.
  set a' := (a + min t h₀) / 2 with ha'
  set b' := (b + max t h₀) / 2 with hb'
  have hmin_lt : a < min t h₀ := lt_min ht.1 ht₀.1
  have hmax_lt : max t h₀ < b := max_lt ht.2 ht₀.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have ha'_lt_min : a' < min t h₀ := by rw [ha']; linarith
  have ha_lt_a' : a < a' := by rw [ha']; linarith
  have hmax_lt_b' : max t h₀ < b' := by rw [hb']; linarith
  have hb'_lt_b : b' < b := by rw [hb']; linarith
  have hsub : Ioo a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_trans ha_lt_a' hs.1, lt_trans hs.2 hb'_lt_b⟩
  have ht_mem' : t ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t, lt_of_le_of_lt ht_le_max hmax_lt_b'⟩
  have ht₀_mem' : h₀ ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t₀, lt_of_le_of_lt ht₀_le_max hmax_lt_b'⟩
  -- Norm bound for `A` on `Icc a' b'`.
  have hab_le : a' ≤ b' := le_of_lt (lt_trans ha'_lt_min (lt_of_le_of_lt hmin_le_t
    (lt_of_lt_of_le ht_mem'.2 (le_refl _))))
  have hIcc_sub : Icc a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_a' hs.1, lt_of_le_of_lt hs.2 hb'_lt_b⟩
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc a' b', ‖A τ‖ ≤ M := by
    have hcont' : ContinuousOn A (Icc a' b') := hA_cont.mono hIcc_sub
    have hcont_norm : ContinuousOn (fun τ => ‖A τ‖) (Icc a' b') :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc a' b') := isCompact_Icc
    have hne : (Icc a' b').Nonempty := ⟨a', left_mem_Icc.mpr hab_le⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖A τ₁‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  obtain ⟨M, hM_nn, hMbd⟩ := hbd
  let K : ℝ≥0 := ⟨M, hM_nn⟩
  have hv_lip : ∀ τ ∈ Ioo a' b', LipschitzOnWith K (v τ) univ := by
    intro τ hτ
    have hlip : LipschitzWith K (A τ) :=
      (A τ).lipschitzWith_of_opNorm_le (hMbd τ (Ioo_subset_Icc_self hτ))
    exact (LipschitzWith.lipschitzOnWith (s := (univ : Set G)) hlip)
  exact (ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => univ) (K := K)
    hv_lip ht₀_mem'
    (fun τ hτ => ⟨hZ₁ τ (hsub hτ), mem_univ _⟩)
    (fun τ hτ => ⟨hZ₂ τ (hsub hτ), mem_univ _⟩)
    heq) ht_mem'

end Uniqueness

/-! ## The parametric solution operator

The parametric solution `linearODESolution A a b h₀ Z₀ : F → ℝ → G` is defined
unconditionally via `Classical.choose`.  For each `x : F`, the per-parameter
existence statement `HasLinearODESolution A a b h₀ Z₀ x` provides a curve
on `Ioo a b` when it holds; otherwise the definition falls back to the constant
function `fun _ => Z₀ x`.

The headline theorems `linearODESolution_init` and
`linearODESolution_hasDerivAt_of_hasSolution` extract the init clause and the
ODE clause; the init clause is unconditional, the ODE clause requires the
existence predicate `HasLinearODESolution`.

Discharging `HasLinearODESolution` from joint continuity of `A` on
`U ×ˢ Ioo a b` is provided by `hasLinearODESolution_of_continuousOn`, which
assembles `exists_linearODE_solution_of_short` over a finite cover of each
closed sub-interval `Icc α β ⊂ Ioo a b`, then exhausts `Ioo a b` by a
countable family of such sub-intervals.
-/

section SolutionOperator

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/--
**Per-parameter existence predicate.**  `HasLinearODESolution A a b h₀ Z₀ x`
asserts that for the fixed parameter `x : F`, there exists a curve `Z : ℝ → G`
with `Z h₀ = Z₀ x` and `HasDerivAt Z (A x t (Z t)) t` for every `t ∈ Ioo a b`.

This predicate is used internally by `linearODESolution` to decide whether to
return the chosen solution on `Ioo a b` or the constant fallback.
-/
def HasLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧ ∀ t ∈ Ioo a b, HasDerivAt Z (A x t (Z t)) t

/--
**Parametric solution of the linear ODE** `Z'(t) = A(x, t) Z(t)` with initial
condition `Z(x, h₀) = Z₀ x` on the open interval `Ioo a b`.

Defined unconditionally:

* If a solution on `Ioo a b` exists for the parameter `x` (predicate
  `HasLinearODESolution`), `linearODESolution A a b h₀ Z₀ x` is *the* chosen
  solution, via `Classical.choose`.
* Otherwise, it is the constant curve `fun _ => Z₀ x`.

The unconditional choice makes `linearODESolution` total; the headline
theorems `linearODESolution_init` and
`linearODESolution_hasDerivAt_of_hasSolution` extract the meaningful clauses
under the appropriate hypotheses.
-/
noncomputable def linearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) :
    F → ℝ → G := by
  classical
  exact fun x =>
    if h : HasLinearODESolution A a b h₀ Z₀ x then
      Classical.choose h
    else
      fun _ => Z₀ x

/--
**Initial condition** for `linearODESolution`.  At `t = h₀`, the parametric
solution equals the initial datum `Z₀ x`.

This identity is unconditional: it holds regardless of whether the
per-parameter existence predicate `HasLinearODESolution` holds.
-/
theorem linearODESolution_init
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) :
    linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x := by
  unfold linearODESolution
  by_cases h : HasLinearODESolution A a b h₀ Z₀ x
  · simp only [dif_pos h]
    exact (Classical.choose_spec h).1
  · simp only [dif_neg h]

/--
**ODE clause** for `linearODESolution` under the per-parameter existence
hypothesis.

When `HasLinearODESolution A a b h₀ Z₀ x` holds, the parametric solution at
`x` satisfies the linear ODE pointwise on `Ioo a b`.
-/
theorem linearODESolution_hasDerivAt_of_hasSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G)
    {x : F} (hx : HasLinearODESolution A a b h₀ Z₀ x) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t := by
  have hZ_eq : linearODESolution A a b h₀ Z₀ x = Classical.choose hx := by
    unfold linearODESolution
    simp only [dif_pos hx]
  rw [hZ_eq]
  exact (Classical.choose_spec hx).2 t ht

end SolutionOperator

/-! ## Discharging the existence predicate from joint continuity

The remaining task is to discharge `HasLinearODESolution A a b h₀ Z₀ x` from
the natural hypothesis "`A` is jointly continuous on `U ×ˢ Ioo a b`,
`x ∈ U`".

The strategy:

1. For a fixed `x ∈ U`, restrict joint continuity to obtain
   `ContinuousOn (A x) (Ioo a b)`.
2. For any closed sub-interval `Icc α β ⊂ Ioo a b` with `α ≤ h₀ ≤ β`,
   build a solution on `Icc α β` by iterating `exists_linearODE_solution_of_short`
   finitely many times.  The coefficient `A x` is bounded by some `M < ∞` on
   the slightly larger `Icc α' β'` (compactness + continuity), so Picard steps
   of size `T = 1 / (2(M+1))` succeed, and `⌈(β - α)/T⌉` of them cover
   `[α, β]`.
3. Exhaust `Ioo a b` by a countable family of nested `Icc αₙ βₙ`, take a
   pointwise union via uniqueness on overlaps.
4. Extend by the constant `Z₀ x` outside `Ioo a b` (the predicate places no
   requirement there).
-/

section GlobalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **One Picard step** at a non-centered base time `c`.  Given a continuous,
operator-norm-bounded coefficient `A` on a closed interval `[c - T, c + T]`
with `M · T < 1`, the linear ODE `Z'(t) = A(t) Z(t),  Z(c) = Y_c` has a
solution on `[c - T, c + T]`.

This is `exists_linearODE_solution_of_short` re-stated with the initial time
`c` named separately so it can be used in an inductive Picard-extension
argument. -/
theorem exists_linearODE_solution_of_short_at
    {A : ℝ → (G →L[ℝ] G)} {c T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (c - T) (c + T)))
    (hA_bd : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M)
    (Y_c : G) :
    ∃ Z : ℝ → G, Z c = Y_c ∧
      ∀ t ∈ Icc (c - T) (c + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (c - T) (c + T)) t :=
  exists_linearODE_solution_of_short (A := A) (h₀ := c) (T := T) (M := M)
    hT hM hMT hA_cont hA_bd Y_c

/-- **Glue two Picard-style segments** sharing the time `t₁` into a single
function defined on `Icc α β = Icc α t₁ ∪ Icc t₁ β` (when `α ≤ t₁ ≤ β`).

The hypothesis is that two functions `f, g` satisfy the ODE on their
respective closed intervals and agree at the shared endpoint `t₁`.  We use
`f` on `(-∞, t₁]` and `g` on `(t₁, ∞)`, patched via `if t ≤ t₁ then f t else g t`. -/
private theorem hasDerivWithinAt_glue_Icc_at_pt
    {f g : ℝ → G} {A : ℝ → (G →L[ℝ] G)} {α t₁ β : ℝ}
    (hα_le : α ≤ t₁) (hβ_ge : t₁ ≤ β)
    (hf : ∀ t ∈ Icc α t₁, HasDerivWithinAt f (A t (f t)) (Icc α t₁) t)
    (hg : ∀ t ∈ Icc t₁ β, HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t)
    (h_match : f t₁ = g t₁) :
    let Z : ℝ → G := fun t => if t ≤ t₁ then f t else g t
    Z t₁ = f t₁ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  intro Z
  have hZ_t1 : Z t₁ = f t₁ := by simp [Z]
  refine ⟨hZ_t1, ?_⟩
  -- Equalities of `Z` with `f` on `(-∞, t₁]` and with `g` on `(t₁, ∞)`.
  have hZ_eq_f : ∀ t, t ≤ t₁ → Z t = f t := by
    intro t ht; simp [Z, ht]
  have hZ_eq_g : ∀ t, t₁ ≤ t → Z t = g t := by
    intro t ht
    by_cases htle : t ≤ t₁
    · have : t = t₁ := le_antisymm htle ht
      simp [Z, this, h_match]
    · simp [Z, htle]
  intro t ht
  have hunion : Icc α t₁ ∪ Icc t₁ β = Icc α β :=
    Set.Icc_union_Icc_eq_Icc hα_le hβ_ge
  rcases le_total t t₁ with htle | htge
  · -- `t ∈ [α, t₁]`: derivative within `Icc α t₁`, extend to `Icc α β` via union.
    have ht_left : t ∈ Icc α t₁ := ⟨ht.1, htle⟩
    have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t₁) t := hf t ht_left
    -- `Z` agrees with `f` on `Icc α t₁`.
    have hZ_eq_set : EqOn Z f (Icc α t₁) := fun s hs => hZ_eq_f s hs.2
    have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t₁) t :=
      hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t htle)
    by_cases hteq : t = t₁
    · -- At the gluing point, also use right-piece via union.
      subst hteq
      have ht_right : t ∈ Icc t β := ⟨le_rfl, hβ_ge⟩
      have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t β) t := hg t ht_right
      have hZ_eq_set_r : EqOn Z g (Icc t β) := fun s hs => hZ_eq_g s hs.1
      have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t β) t :=
        hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · -- Strict interior: `t < t₁`. Derivative within `Icc α t₁` extends to within `Icc α β`.
      have htlt : t < t₁ := lt_of_le_of_ne htle hteq
      have h_AZ_eq : A t (Z t) = A t (f t) := by rw [hZ_eq_f t htle]
      have hZf_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc α t₁) t := by
        rw [h_AZ_eq]; exact hZf_deriv
      -- `Icc α t₁ ⊆ Icc α β` so we'd want `mono` … but `mono` goes the wrong way (we want from
      -- smaller set to larger set, which weakens the assertion). Use `nhdsWithin` filter monotonicity:
      -- `𝓝[Icc α t₁] t ≤ 𝓝[Icc α β] t` is FALSE in general. We need the other direction.
      -- However, since `t < t₁`, on a neighborhood `Ioo (t₁ - 1) t₁` (intersected with `Icc α β`)
      -- equals `Ioo (t₁ - 1) t₁ ∩ Icc α β` ⊆ Icc α t₁` because `s < t₁` ⇒ `s ≤ t₁`.
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc α t₁] t := by
        apply le_antisymm
        · -- 𝓝[Icc α β] t ≤ 𝓝[Icc α t₁] t : show Icc α t₁ ∈ 𝓝[Icc α β] t.
          rw [nhdsWithin_le_iff]
          -- We need `Icc α t₁ ∈ 𝓝[Icc α β] t`.
          -- Take open `s := Iio (t₁ + (t₁ - t)/2)` ∩ Icc α β` — hmm use `Iio` for simplicity.
          -- Actually simpler: `Icc α t₁ = Icc α β ∩ Iic t₁`. Use `inter_mem_nhdsWithin`.
          have h_Iic_nhd : Iic t₁ ∈ 𝓝 t := Iic_mem_nhds htlt
          have : Iic t₁ ∈ 𝓝[Icc α β] t := mem_nhdsWithin_of_mem_nhds h_Iic_nhd
          have h_inter : Icc α β ∩ Iic t₁ = Icc α t₁ := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h1.1, h2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hβ_ge⟩, h2⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Iic_nhd
          rw [h_inter] at this; exact this
        · -- 𝓝[Icc α t₁] t ≤ 𝓝[Icc α β] t : standard, since Icc α t₁ ⊆ Icc α β.
          exact nhdsWithin_mono _ (Icc_subset_Icc_right hβ_ge)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZf_at_t
      exact hZf_at_t
  · -- `t ∈ [t₁, β]`: symmetric.
    have ht_right : t ∈ Icc t₁ β := ⟨htge, ht.2⟩
    have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t := hg t ht_right
    have hZ_eq_set_r : EqOn Z g (Icc t₁ β) := fun s hs => hZ_eq_g s hs.1
    have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t₁ β) t :=
      hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t htge)
    by_cases hteq : t = t₁
    · -- Handled in `t ≤ t₁` branch already.
      subst hteq
      have ht_left : t ∈ Icc α t := ⟨hα_le, le_rfl⟩
      have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t) t := hf t ht_left
      have hZ_eq_set : EqOn Z f (Icc α t) := fun s hs => hZ_eq_f s hs.2
      have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t) t :=
        hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · have htgt : t₁ < t := lt_of_le_of_ne htge (Ne.symm hteq)
      have h_AZ_eq : A t (Z t) = A t (g t) := by rw [hZ_eq_g t htge]
      have hZg_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc t₁ β) t := by
        rw [h_AZ_eq]; exact hZg_deriv
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc t₁ β] t := by
        apply le_antisymm
        · rw [nhdsWithin_le_iff]
          have h_Ici_nhd : Ici t₁ ∈ 𝓝 t := Ici_mem_nhds htgt
          have h_inter : Icc α β ∩ Ici t₁ = Icc t₁ β := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h2, h1.2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨le_trans hα_le h1, h2⟩, h1⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Ici_nhd
          rw [h_inter] at this; exact this
        · exact nhdsWithin_mono _ (Icc_subset_Icc_left hα_le)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZg_at_t
      exact hZg_at_t

/-- **Right-extension** of a linear-ODE solution by iterated Picard.

Given a continuous, operator-norm-bounded coefficient `A` on `Icc h₀ (h₀ + B)`
with `‖A‖ ≤ M` there and `M · T < 1`, for any natural number `n` with
`h₀ + n · T ≤ h₀ + B` (equivalently `n · T ≤ B`), there exists a function
`Z : ℝ → G` with `Z h₀ = Y₀` and satisfying the ODE on `Icc h₀ (h₀ + n · T)`. -/
private theorem exists_linearODE_solution_right_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + B + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + B + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc h₀ (h₀ + (n : ℝ) * T),
          HasDerivWithinAt Z (A t (Z t)) (Icc h₀ (h₀ + (n : ℝ) * T)) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    -- `Icc h₀ h₀ = {h₀}`; `HasDerivWithinAt` on a singleton is trivial.
    simp only [Nat.cast_zero, zero_mul, add_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    -- Use the `HasFDerivWithinAt.of_finite` lemma and convert.
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    -- Previous step: solution on `Icc h₀ (h₀ + k·T)`.
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_init, hZ_k_deriv⟩ := ih hkT_prev
    -- New step: Picard at center `h₀ + (k+1)·T` with radius `T`.
    -- Covers `[h₀ + k·T, h₀ + (k+2)·T] ∩ [h₀ + k·T, h₀ + (k+1)·T] = [h₀ + k·T, h₀ + (k+1)·T]`,
    -- but for uniqueness we need the larger Picard interval.
    -- Actually we apply `exists_linearODE_solution_of_short` at center `c := h₀ + k·T + T`
    -- with radius `T`. It produces a solution on `[c - T, c + T] = [h₀ + k·T, h₀ + (k+2)·T]`.
    -- Then we glue at `t₁ := h₀ + k·T` using `Z_k` on the left and the Picard piece on the right
    -- restricted to `[h₀ + k·T, h₀ + (k+1)·T]`.
    set c : ℝ := h₀ + (k : ℝ) * T + T with hc_def
    -- A bound + continuity on the Picard interval `[c - T, c + T] = [h₀ + k·T, h₀ + (k+2)·T]`.
    have hsub_picard : Icc (c - T) (c + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ c - T := by
          rw [hc_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : c + T ≤ h₀ + B + T := by
          rw [hc_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T + T = ((k : ℝ) + 1) * T + T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard : ContinuousOn A (Icc (c - T) (c + T)) := hA_cont.mono hsub_picard
    have hA_bd_picard : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (hsub_picard ht)
    -- Apply Picard at center `c` with initial value `Z_k (h₀ + k·T)`.
    set Y_c : G := Z_k (h₀ + (k : ℝ) * T) with hY_c_def
    have h_t1_mem : h₀ + (k : ℝ) * T ∈ Icc (c - T) (c + T) := by
      rw [hc_def]; refine ⟨by linarith, by linarith [hT_pos]⟩
    -- We actually want Picard centered at `t₁` (so initial value at `t₁`), not at `c`.
    -- Re-center: use center `t₁ := h₀ + k·T` with radius `T`.
    set t₁ : ℝ := h₀ + (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ t₁ - T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + B + T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    obtain ⟨Z_pic, hZ_pic_init, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    -- `Z_pic` is defined on `[t₁ - T, t₁ + T] = [h₀ + (k-1)T, h₀ + (k+1)T]`,
    -- in particular on `[t₁, t₁ + T] = [h₀ + k·T, h₀ + (k+1)·T]`.
    have h_pic_right : ∀ t ∈ Icc t₁ (t₁ + T),
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc t₁ (t₁ + T)) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨by linarith [ht.1, hT_pos], ht.2⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      -- Restrict from `[t₁ - T, t₁ + T]` to `[t₁, t₁ + T]` via `mono`.
      exact hd.mono (Icc_subset_Icc_left (by linarith [hT_pos]))
    -- Glue `Z_k` (left, on `[h₀, t₁]`) and `Z_pic` (right, on `[t₁, t₁ + T]`).
    -- Match value: `Z_k t₁ = Y_c = Z_pic t₁` (Picard init).
    have h_match : Z_k t₁ = Z_pic t₁ := by
      rw [hZ_pic_init]
    -- The previous-step domain is `Icc h₀ (h₀ + k·T) = Icc h₀ t₁`.
    have h_prev_deriv : ∀ t ∈ Icc h₀ t₁,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc h₀ t₁) t := by
      intro t ht
      exact hZ_k_deriv t ht
    -- The right interval is `[t₁, t₁ + T] = [h₀ + k·T, h₀ + (k+1)·T]`.
    have h_ht1_le_top : t₁ ≤ t₁ + T := by linarith [hT_pos]
    have h_h0_le_t1 : h₀ ≤ t₁ := by
      change h₀ ≤ h₀ + (k : ℝ) * T
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_glued :=
      hasDerivWithinAt_glue_Icc_at_pt (f := Z_k) (g := Z_pic) (A := A)
        (α := h₀) (t₁ := t₁) (β := t₁ + T) h_h0_le_t1 h_ht1_le_top
        h_prev_deriv h_pic_right h_match
    -- Result: a function `Z := if t ≤ t₁ then Z_k t else Z_pic t` defined on `[h₀, t₁ + T]`.
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_k t else Z_pic t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    -- Init: at `t = h₀ ≤ t₁`, `Z h₀ = Z_k h₀ = Y₀`.
    have hZ_init : Z h₀ = Y₀ := by
      simp [Z, h_h0_le_t1, hZ_k_init]
    -- The required domain is `Icc h₀ (h₀ + (k+1)·T) = Icc h₀ (t₁ + T)`.
    have h_dom_eq : h₀ + ((k : ℝ) + 1) * T = t₁ + T := by
      rw [ht₁_def]; ring
    refine ⟨Z, hZ_init, fun t ht => ?_⟩
    have h_dom_eq' : h₀ + ((k : ℕ) + 1 : ℝ) * T = t₁ + T := by
      change h₀ + ((k : ℝ) + 1) * T = (h₀ + (k : ℝ) * T) + T; ring
    have h_dom_cast : h₀ + (↑(k + 1) : ℝ) * T = t₁ + T := by
      have : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
      rw [this]; exact h_dom_eq'
    have ht_cast : t ∈ Icc h₀ (t₁ + T) := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h_dom_cast] at h2; exact h2
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc h₀ (t₁ + T) = Icc h₀ (h₀ + (↑(k + 1) : ℝ) * T) := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

/-- **Left-extension** of a linear-ODE solution by iterated Picard (the
mirror of `exists_linearODE_solution_right_iterated`). -/
private theorem exists_linearODE_solution_left_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - B - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - B - T) (h₀ + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc (h₀ - (n : ℝ) * T) h₀,
          HasDerivWithinAt Z (A t (Z t)) (Icc (h₀ - (n : ℝ) * T) h₀) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul, sub_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_init, hZ_k_deriv⟩ := ih hkT_prev
    set t₁ : ℝ := h₀ - (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - B - T) (h₀ + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - B - T ≤ t₁ - T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    set Y_c : G := Z_k t₁ with hY_c_def
    obtain ⟨Z_pic, hZ_pic_init, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    -- `Z_pic` is defined on `[t₁ - T, t₁ + T]`; we need its restriction to `[t₁ - T, t₁]`.
    have h_pic_left : ∀ t ∈ Icc (t₁ - T) t₁,
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) t₁) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨ht.1, by linarith [ht.2, hT_pos]⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      exact hd.mono (Icc_subset_Icc_right (by linarith [hT_pos]))
    -- Glue: `Z_pic` on `[t₁ - T, t₁]` (left) and `Z_k` on `[t₁, h₀]` (right).
    have h_match : Z_pic t₁ = Z_k t₁ := hZ_pic_init
    have h_next_deriv : ∀ t ∈ Icc t₁ h₀,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc t₁ h₀) t := by
      intro t ht
      exact hZ_k_deriv t ht
    have h_t1_le_h0 : t₁ ≤ h₀ := by
      change h₀ - (k : ℝ) * T ≤ h₀
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_ht1m_le_t1 : t₁ - T ≤ t₁ := by linarith [hT_pos]
    have h_glued :=
      hasDerivWithinAt_glue_Icc_at_pt (f := Z_pic) (g := Z_k) (A := A)
        (α := t₁ - T) (t₁ := t₁) (β := h₀) h_ht1m_le_t1 h_t1_le_h0
        h_pic_left h_next_deriv h_match
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_pic t else Z_k t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    have hZ_init : Z h₀ = Y₀ := by
      by_cases h : h₀ ≤ t₁
      · -- Forces `h₀ = t₁`, so `(k : ℝ) * T = 0`, so `k = 0` (or `T = 0`, excluded), so init via `Z_pic`.
        have h_eq : h₀ = t₁ := le_antisymm h h_t1_le_h0
        have h_match' : Z_pic t₁ = Y₀ := by rw [hY_c_def] at hZ_pic_init
                                            rw [hZ_pic_init, ← h_eq, hZ_k_init]
        simp only [Z, h, ↓reduceIte]
        rw [h_eq]; exact h_match'
      · rw [not_le] at h
        simp only [Z, not_le.mpr h, ↓reduceIte, hZ_k_init]
    have h_dom_cast : h₀ - (↑(k + 1) : ℝ) * T = t₁ - T := by
      rw [ht₁_def]; push_cast; ring
    refine ⟨Z, hZ_init, fun t ht => ?_⟩
    have ht_cast : t ∈ Icc (t₁ - T) h₀ := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h_dom_cast] at h1; exact h1
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc (t₁ - T) h₀ = Icc (h₀ - (↑(k + 1) : ℝ) * T) h₀ := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

/-- **Solution on an arbitrary closed sub-interval** `Icc α β ⊂ Ioo a b`,
constructed by combining `exists_linearODE_solution_left_iterated` (leftward
from `h₀`) and `exists_linearODE_solution_right_iterated` (rightward from
`h₀`) and patching at `h₀`. -/
private theorem exists_linearODE_solution_on_Icc_subset
    {A : ℝ → (G →L[ℝ] G)} {a b α β h₀ : ℝ}
    (hα_lt : a < α) (hβ_lt : β < b)
    (hα_le : α ≤ h₀) (hβ_ge : h₀ ≤ β)
    (hA_cont : ContinuousOn A (Ioo a b))
    (Y₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  -- Buffer: slightly enlarge `[α, β]` to `[α'', β''] ⊂ Ioo a b`.
  set α'' : ℝ := (a + α) / 2 with hα''_def
  set β'' : ℝ := (β + b) / 2 with hβ''_def
  have hα''_lt : a < α'' := by rw [hα''_def]; linarith
  have hα''_le_α : α'' < α := by rw [hα''_def]; linarith
  have hβ''_lt : β'' < b := by rw [hβ''_def]; linarith
  have hβ''_ge_β : β < β'' := by rw [hβ''_def]; linarith
  -- Closed sub-interval `Icc α'' β'' ⊂ Ioo a b`.
  have h_subset : Icc α'' β'' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα''_lt hs.1, lt_of_le_of_lt hs.2 hβ''_lt⟩
  have hα''_le : α'' ≤ β'' := by linarith [hα_le.trans hβ_ge]
  have hα''_lt_β'' : α'' < β'' := by linarith [hα_le.trans hβ_ge]
  -- Bound `M = sup ‖A t‖` on `Icc α'' β''`.
  have hcont' : ContinuousOn A (Icc α'' β'') := hA_cont.mono h_subset
  have hcont_norm : ContinuousOn (fun t => ‖A t‖) (Icc α'' β'') :=
    continuous_norm.comp_continuousOn hcont'
  have hcpt : IsCompact (Icc α'' β'') := isCompact_Icc
  have hne : (Icc α'' β'').Nonempty := ⟨α'', left_mem_Icc.mpr hα''_le⟩
  rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ_max, _, hτ_max⟩
  set M : ℝ := ‖A τ_max‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd : ∀ t ∈ Icc α'' β'', ‖A t‖ ≤ M := fun t ht => hτ_max ht
  -- Pick step `T = 1 / (2 (M+1))`. Then `M * T = M / (2(M+1)) ≤ 1/2 < 1`.
  set T : ℝ := 1 / (2 * (M + 1)) with hT_def
  have hT_pos : 0 < T := by
    rw [hT_def]; positivity
  have hMT : M * T < 1 := by
    have h_denom_pos : 0 < 2 * (M + 1) := by positivity
    have hT_eq : T = 1 / (2 * (M + 1)) := hT_def
    rw [hT_eq]
    have : M * (1 / (2 * (M + 1))) = M / (2 * (M + 1)) := by ring
    rw [this, div_lt_one h_denom_pos]
    have h_M_le_M1 : M ≤ M + 1 := by linarith
    calc M = M * 1 := (mul_one _).symm
      _ ≤ (M + 1) * 1 := mul_le_mul_of_nonneg_right h_M_le_M1 zero_le_one
      _ < 2 * (M + 1) := by linarith
  -- Bound right-iteration count: need `n_R * T ≥ β - h₀` and `n_R * T ≤ β'' - h₀ - T`
  -- (so that `[h₀ - T, h₀ + n_R T + T] ⊆ [α'', β'']`, which requires
  -- `h₀ - T ≥ α''` and `h₀ + n_R T + T ≤ β''`).
  -- The first inequality `h₀ - T ≥ α''` needs `T ≤ h₀ - α''`, which we can arrange by shrinking `T`.
  -- The second `h₀ + (n_R + 1) T ≤ β''` needs `n_R T ≤ β'' - h₀ - T`.
  -- Let `B_R := β'' - h₀ - T`. We need `n_R T ≤ B_R` AND `h₀ + n_R T ≥ β`.
  -- Choose `n_R := ⌈(β - h₀) / T⌉`. Then `n_R T ≥ β - h₀`, and we need `n_R T ≤ B_R`.
  -- Worst case `n_R T < β - h₀ + T` (by ceiling property). So we need
  -- `β - h₀ + T ≤ B_R = β'' - h₀ - T`, i.e., `β + 2T ≤ β''`, i.e., `T ≤ (β'' - β) / 2`.
  -- Similarly for left: `T ≤ (α - α'') / 2`.
  -- Replace `T` with `min(T, (β'' - β) / 2, (α - α'') / 2)`. Re-derive `M*T < 1` (still holds since smaller).
  set δ_R : ℝ := (β'' - β) / 2 with hδ_R_def
  set δ_L : ℝ := (α - α'') / 2 with hδ_L_def
  have hδ_R_pos : 0 < δ_R := by rw [hδ_R_def]; linarith
  have hδ_L_pos : 0 < δ_L := by rw [hδ_L_def]; linarith
  set T' : ℝ := min T (min δ_R δ_L) with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]; exact lt_min hT_pos (lt_min hδ_R_pos hδ_L_pos)
  have hT'_le_T : T' ≤ T := by rw [hT'_def]; exact min_le_left _ _
  have hT'_le_δ_R : T' ≤ δ_R := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hT'_le_δ_L : T' ≤ δ_L := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hMT' : M * T' < 1 := by
    have : M * T' ≤ M * T := mul_le_mul_of_nonneg_left hT'_le_T hM_nn
    linarith
  -- Now pick natural number step counts.
  set B_R : ℝ := β - h₀ with hB_R_def
  set B_L : ℝ := h₀ - α with hB_L_def
  have hB_R_nn : 0 ≤ B_R := by rw [hB_R_def]; linarith
  have hB_L_nn : 0 ≤ B_L := by rw [hB_L_def]; linarith
  -- Right step count.
  set n_R : ℕ := ⌈B_R / T'⌉₊ with hn_R_def
  have hn_R_bound : B_R ≤ (n_R : ℝ) * T' := by
    rw [hn_R_def]
    have := Nat.le_ceil (B_R / T')
    have h_div : B_R / T' * T' = B_R := by
      field_simp
    calc B_R = B_R / T' * T' := h_div.symm
      _ ≤ (⌈B_R / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_R_step_bound : (n_R : ℝ) * T' ≤ B_R + T' := by
    rw [hn_R_def]
    have hceil := Nat.ceil_lt_add_one (a := B_R / T') (div_nonneg hB_R_nn hT'_pos.le)
    have : (⌈B_R / T'⌉₊ : ℝ) ≤ B_R / T' + 1 := le_of_lt hceil
    calc (⌈B_R / T'⌉₊ : ℝ) * T' ≤ (B_R / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_R / T' * T' + T' := by ring
      _ = B_R + T' := by field_simp
  -- Left step count.
  set n_L : ℕ := ⌈B_L / T'⌉₊ with hn_L_def
  have hn_L_bound : B_L ≤ (n_L : ℝ) * T' := by
    rw [hn_L_def]
    have := Nat.le_ceil (B_L / T')
    have h_div : B_L / T' * T' = B_L := by field_simp
    calc B_L = B_L / T' * T' := h_div.symm
      _ ≤ (⌈B_L / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_L_step_bound : (n_L : ℝ) * T' ≤ B_L + T' := by
    rw [hn_L_def]
    have hceil := Nat.ceil_lt_add_one (a := B_L / T') (div_nonneg hB_L_nn hT'_pos.le)
    have : (⌈B_L / T'⌉₊ : ℝ) ≤ B_L / T' + 1 := le_of_lt hceil
    calc (⌈B_L / T'⌉₊ : ℝ) * T' ≤ (B_L / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_L / T' * T' + T' := by ring
      _ = B_L + T' := by field_simp
  -- Set "effective B" for each direction: `(n_R : ℝ) * T'`.
  -- Need `[h₀ - T', h₀ + n_R * T' + T'] ⊆ [α'', β'']`. First the right end:
  -- `h₀ + n_R * T' + T' ≤ β''` iff `n_R * T' ≤ β'' - h₀ - T'`.
  -- We have `n_R * T' ≤ B_R + T' = β - h₀ + T'`. We need `β - h₀ + T' ≤ β'' - h₀ - T'`,
  -- i.e., `β + 2T' ≤ β''`, i.e., `T' ≤ (β'' - β) / 2 = δ_R`. We have `T' ≤ δ_R`. So OK.
  have h_right_end : h₀ + (n_R : ℝ) * T' + T' ≤ β'' := by
    have : (n_R : ℝ) * T' + T' ≤ B_R + 2 * T' := by linarith
    have h1 : h₀ + (B_R + 2 * T') = β + 2 * T' := by rw [hB_R_def]; ring
    have h2 : β + 2 * T' ≤ β + 2 * δ_R := by linarith
    have h3 : β + 2 * δ_R = β'' := by rw [hδ_R_def]; ring
    linarith
  -- Similarly the left end:
  have h_left_end : α'' ≤ h₀ - (n_L : ℝ) * T' - T' := by
    have h1 : (n_L : ℝ) * T' + T' ≤ B_L + 2 * T' := by linarith
    have h2 : h₀ - (B_L + 2 * T') = α - 2 * T' := by rw [hB_L_def]; ring
    have h3 : α - 2 * T' ≥ α - 2 * δ_L := by linarith
    have h4 : α - 2 * δ_L = α'' := by rw [hδ_L_def]; ring
    linarith
  -- Continuity / bound restricted to the right "Picard zone" [h₀ - T', h₀ + n_R T' + T'].
  have h_R_sub_α'β'' : Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have : α'' ≤ h₀ - T' := by
        have hL_step : h₀ - (n_L : ℝ) * T' - T' ≤ h₀ - T' := by
          have : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.1]
    · linarith [hs.2, h_right_end]
  have hA_cont_R : ContinuousOn A (Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T')) :=
    hcont'.mono h_R_sub_α'β''
  have hA_bd_R : ∀ t ∈ Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_R_sub_α'β'' ht)
  -- Build the right-iterated solution.
  obtain ⟨Z_R, hZ_R_init, hZ_R_deriv⟩ :=
    exists_linearODE_solution_right_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_R : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_R hA_bd_R Y₀ n_R le_rfl
  -- Similarly the left "Picard zone".
  have h_L_sub_α'β'' : Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · linarith [hs.1, h_left_end]
    · have : h₀ + T' ≤ β'' := by
        have hR_step : h₀ + T' ≤ h₀ + (n_R : ℝ) * T' + T' := by
          have : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.2]
  have hA_cont_L : ContinuousOn A (Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T')) :=
    hcont'.mono h_L_sub_α'β''
  have hA_bd_L : ∀ t ∈ Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_L_sub_α'β'' ht)
  -- Build the left-iterated solution.
  -- The hypothesis for `left_iterated` is `Icc (h₀ - B - T) (h₀ + T)`. With `B := n_L * T'`,
  -- this is `Icc (h₀ - n_L * T' - T') (h₀ + T')`.
  obtain ⟨Z_L, hZ_L_init, hZ_L_deriv⟩ :=
    exists_linearODE_solution_left_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_L : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_L hA_bd_L Y₀ n_L le_rfl
  -- Glue `Z_L` (on `[h₀ - n_L T', h₀]`) and `Z_R` (on `[h₀, h₀ + n_R T']`) at `h₀`.
  have h_match : Z_L h₀ = Z_R h₀ := by rw [hZ_L_init, hZ_R_init]
  have h_α_ge_L : h₀ - (n_L : ℝ) * T' ≤ h₀ := by
    have h : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
    linarith
  have h_R_ge_β : h₀ ≤ h₀ + (n_R : ℝ) * T' := by
    have h : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
    linarith
  have h_glued := hasDerivWithinAt_glue_Icc_at_pt
    (f := Z_L) (g := Z_R) (A := A)
    (α := h₀ - (n_L : ℝ) * T') (t₁ := h₀) (β := h₀ + (n_R : ℝ) * T')
    h_α_ge_L h_R_ge_β hZ_L_deriv hZ_R_deriv h_match
  set Z : ℝ → G := fun t => if t ≤ h₀ then Z_L t else Z_R t with hZ_def
  obtain ⟨hZ_h0, hZ_LR_deriv⟩ := h_glued
  -- `Z h₀ = Z_L h₀ = Y₀`.
  have hZ_init : Z h₀ = Y₀ := by
    simp only [Z, le_refl, ↓reduceIte, hZ_L_init]
  refine ⟨Z, hZ_init, ?_⟩
  -- Final: `Icc α β ⊆ Icc (h₀ - n_L T') (h₀ + n_R T')` via `hn_L_bound`, `hn_R_bound`.
  have h_α_lb : h₀ - (n_L : ℝ) * T' ≤ α := by
    have : (n_L : ℝ) * T' ≥ B_L := hn_L_bound
    have hα_eq : h₀ - B_L = α := by rw [hB_L_def]; ring
    linarith
  have h_β_ub : β ≤ h₀ + (n_R : ℝ) * T' := by
    have : (n_R : ℝ) * T' ≥ B_R := hn_R_bound
    have hβ_eq : h₀ + B_R = β := by rw [hB_R_def]; ring
    linarith
  have h_Icc_sub : Icc α β ⊆ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := fun s hs =>
    ⟨le_trans h_α_lb hs.1, le_trans hs.2 h_β_ub⟩
  intro t ht
  have ht' : t ∈ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := h_Icc_sub ht
  have hd := hZ_LR_deriv t ht'
  exact hd.mono h_Icc_sub

/-- **Monotonic sub-interval sequence** `αₙ ↘ a`, `βₙ ↗ b` strictly inside
`Ioo a b`, with `h₀ ∈ Ioo (αₙ n) (βₙ n)` for every `n`. -/
private def subIntervalSeq (a h₀ b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (a + (h₀ - a) / ((n : ℝ) + 2), b - (b - h₀) / ((n : ℝ) + 2))

/-- **Discharge of the per-parameter existence predicate** from joint
continuity of `A` on `U ×ˢ Ioo a b`.

For any `x` in the open parameter set `U` and any `h₀ ∈ Ioo a b`, the linear
ODE `Z'(t) = A(x, t) Z(t),  Z(h₀) = Z₀(x)` has a solution on `Ioo a b`. -/
theorem hasLinearODESolution_of_continuousOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (_hab_lt : a < b) (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (_hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) :
    HasLinearODESolution A a b h₀ Z₀ x := by
  classical
  -- Restrict joint continuity to `A x : ℝ → (G →L[ℝ] G)` on `Ioo a b`.
  have hA_x_cont : ContinuousOn (A x) (Ioo a b) :=
    ContinuousOn.uncurry_left (a := x) (sα := U) (sβ := Ioo a b) hx hA_cont
  have hh0a : a < h₀ := h₀_mem.1
  have hh0b : h₀ < b := h₀_mem.2
  -- Sub-interval sequence: `αₙ := a + (h₀-a)/(n+2)`, `βₙ := b - (b-h₀)/(n+2)`.
  let α : ℕ → ℝ := fun n => a + (h₀ - a) / ((n : ℝ) + 2)
  let β : ℕ → ℝ := fun n => b - (b - h₀) / ((n : ℝ) + 2)
  -- Boundary properties.
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hden_ge1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 2 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  have hα_lt_a : ∀ n, a < α n := fun n => by
    change a < a + (h₀ - a) / ((n : ℝ) + 2)
    have h : 0 < (h₀ - a) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hβ_lt_b : ∀ n, β n < b := fun n => by
    change b - (b - h₀) / ((n : ℝ) + 2) < b
    have h : 0 < (b - h₀) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hα_le_h0 : ∀ n, α n ≤ h₀ := fun n => by
    change a + (h₀ - a) / ((n : ℝ) + 2) ≤ h₀
    have h : (h₀ - a) / ((n : ℝ) + 2) ≤ h₀ - a := by
      rw [div_le_iff₀ (hden n)]
      calc h₀ - a = (h₀ - a) * 1 := (mul_one _).symm
        _ ≤ (h₀ - a) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  have hh0_le_β : ∀ n, h₀ ≤ β n := fun n => by
    change h₀ ≤ b - (b - h₀) / ((n : ℝ) + 2)
    have h : (b - h₀) / ((n : ℝ) + 2) ≤ b - h₀ := by
      rw [div_le_iff₀ (hden n)]
      calc b - h₀ = (b - h₀) * 1 := (mul_one _).symm
        _ ≤ (b - h₀) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  -- Per-`n` solution on `Icc (α n) (β n)`.
  have h_exists : ∀ n : ℕ, ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧
      ∀ t ∈ Icc (α n) (β n), HasDerivWithinAt Z (A x t (Z t)) (Icc (α n) (β n)) t :=
    fun n => exists_linearODE_solution_on_Icc_subset
      (hα_lt_a n) (hβ_lt_b n) (hα_le_h0 n) (hh0_le_β n) hA_x_cont (Z₀ x)
  choose Zn hZn_init hZn_deriv using h_exists
  -- Monotonicity of `α, β` in `n`.
  have hα_mono : ∀ k₁ k₂, k₁ ≤ k₂ → α k₂ ≤ α k₁ := by
    intro k₁ k₂ hk
    change a + (h₀ - a) / ((k₂ : ℝ) + 2) ≤ a + (h₀ - a) / ((k₁ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (h₀ - a) / ((k₂ : ℝ) + 2) ≤ (h₀ - a) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  have hβ_mono : ∀ k₁ k₂, k₁ ≤ k₂ → β k₁ ≤ β k₂ := by
    intro k₁ k₂ hk
    change b - (b - h₀) / ((k₁ : ℝ) + 2) ≤ b - (b - h₀) / ((k₂ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (b - h₀) / ((k₂ : ℝ) + 2) ≤ (b - h₀) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  -- Uniqueness across `n, m`: `Zn n` and `Zn m` agree on the intersection
  -- `Icc (α n) (β n) ∩ Icc (α m) (β m) = Icc (α (min n m)) (β (min n m))`,
  -- since `α` decreasing ⇒ `max (α n) (α m) = α (min n m)`, and
  -- `β` increasing ⇒ `min (β n) (β m) = β (min n m)`.
  have h_unique : ∀ n m : ℕ, ∀ s ∈ Ioo (α (min n m)) (β (min n m)),
      Zn n s = Zn m s := by
    intro n m s hs_min
    set N := min n m
    have hαn_le : α n ≤ α N := hα_mono N n (min_le_left _ _)
    have hαm_le : α m ≤ α N := hα_mono N m (min_le_right _ _)
    have hβn_ge : β N ≤ β n := hβ_mono N n (min_le_left _ _)
    have hβm_ge : β N ≤ β m := hβ_mono N m (min_le_right _ _)
    have h_subset_n : Ioo (α N) (β N) ⊆ Icc (α n) (β n) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαn_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβn_ge)⟩
    have h_subset_m : Ioo (α N) (β N) ⊆ Icc (α m) (β m) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαm_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβm_ge)⟩
    have h_h0_in_N : h₀ ∈ Ioo (α N) (β N) := by
      refine ⟨?_, ?_⟩
      · change a + (h₀ - a) / ((N : ℝ) + 2) < h₀
        have h_pos : 0 < (h₀ - a) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (h₀ - a) / ((N : ℝ) + 2) < h₀ - a := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_h0a_pos : 0 < h₀ - a := by linarith
          calc (h₀ - a) / ((N : ℝ) + 2)
              < (h₀ - a) / 1 := by
                apply div_lt_div_of_pos_left h_h0a_pos (by norm_num) h_den_gt1
            _ = h₀ - a := by norm_num
        linarith
      · change h₀ < b - (b - h₀) / ((N : ℝ) + 2)
        have h_pos : 0 < (b - h₀) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (b - h₀) / ((N : ℝ) + 2) < b - h₀ := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_bh0_pos : 0 < b - h₀ := by linarith
          calc (b - h₀) / ((N : ℝ) + 2)
              < (b - h₀) / 1 := by
                apply div_lt_div_of_pos_left h_bh0_pos (by norm_num) h_den_gt1
            _ = b - h₀ := by norm_num
        linarith
    have h_subN_to_Ioo : Ioo (α N) (β N) ⊆ Ioo a b := fun u hu =>
      ⟨lt_of_lt_of_le (hα_lt_a N) hu.1.le, lt_of_le_of_lt hu.2.le (hβ_lt_b N)⟩
    have hA_cont_N : ContinuousOn (A x) (Ioo (α N) (β N)) :=
      hA_x_cont.mono h_subN_to_Ioo
    have h_Zn_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn n) (A x u (Zn n u)) u := by
      intro u hu
      have hd := hZn_deriv n u (h_subset_n hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαn_le hu.1) (lt_of_lt_of_le hu.2 hβn_ge))
    have h_Zm_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn m) (A x u (Zn m u)) u := by
      intro u hu
      have hd := hZn_deriv m u (h_subset_m hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαm_le hu.1) (lt_of_lt_of_le hu.2 hβm_ge))
    have h_match : Zn n h₀ = Zn m h₀ := by rw [hZn_init, hZn_init]
    exact linearODE_unique_on_Ioo (A := A x) h_h0_in_N hA_cont_N
      h_Zn_deriv_open h_Zm_deriv_open h_match hs_min
  -- Exhaustion: each `t ∈ Ioo a b` is in some `Ioo (α n) (β n)`.
  have h_exhaust : ∀ t ∈ Ioo a b, ∃ n : ℕ, t ∈ Ioo (α n) (β n) := by
    intro t ht
    have hta : 0 < t - a := by linarith [ht.1]
    have htb : 0 < b - t := by linarith [ht.2]
    obtain ⟨N, hN⟩ :=
      exists_nat_gt (max ((h₀ - a) / (t - a)) ((b - h₀) / (b - t)))
    have hN1 : (h₀ - a) / (t - a) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hN2 : (b - h₀) / (b - t) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    refine ⟨N, ?_, ?_⟩
    · change a + (h₀ - a) / ((N : ℝ) + 2) < t
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (h₀ - a) / ((N : ℝ) + 2) < t - a := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (h₀ - a) = (h₀ - a) / (t - a) * (t - a) := by field_simp
        rw [h_eq]
        rw [mul_comm (t - a) ((N : ℝ) + 2)]
        calc (h₀ - a) / (t - a) * (t - a)
            < (N : ℝ) * (t - a) := mul_lt_mul_of_pos_right hN1 hta
          _ ≤ ((N : ℝ) + 2) * (t - a) :=
              mul_le_mul_of_nonneg_right (by linarith) hta.le
      linarith
    · change t < b - (b - h₀) / ((N : ℝ) + 2)
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (b - h₀) / ((N : ℝ) + 2) < b - t := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (b - h₀) = (b - h₀) / (b - t) * (b - t) := by field_simp
        rw [h_eq]
        rw [mul_comm (b - t) ((N : ℝ) + 2)]
        calc (b - h₀) / (b - t) * (b - t)
            < (N : ℝ) * (b - t) := mul_lt_mul_of_pos_right hN2 htb
          _ ≤ ((N : ℝ) + 2) * (b - t) :=
              mul_le_mul_of_nonneg_right (by linarith) htb.le
      linarith
  -- Global `Z`: pick smallest index for which `t` is in the open sub-interval.
  let Z : ℝ → G := fun t =>
    if h : ∃ n, t ∈ Ioo (α n) (β n) then Zn (Nat.find h) t else Z₀ x
  refine ⟨Z, ?_, ?_⟩
  · -- `Z h₀ = Z₀ x`.
    have h_h0_mem : ∃ n, h₀ ∈ Ioo (α n) (β n) := by
      refine ⟨0, ?_, ?_⟩
      · change a + (h₀ - a) / ((0 : ℕ) + 2 : ℝ) < h₀
        have : 0 < (h₀ - a) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
      · change h₀ < b - (b - h₀) / ((0 : ℕ) + 2 : ℝ)
        have : 0 < (b - h₀) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
    change (if h : ∃ n, h₀ ∈ Ioo (α n) (β n) then Zn (Nat.find h) h₀ else Z₀ x) = Z₀ x
    rw [dif_pos h_h0_mem]
    exact hZn_init _
  · -- ODE clause.
    intro t ht
    obtain ⟨N, hN⟩ := h_exhaust t ht
    have h_ex_t : ∃ n, t ∈ Ioo (α n) (β n) := ⟨N, hN⟩
    let N₀ := Nat.find h_ex_t
    have hN0_spec : t ∈ Ioo (α N₀) (β N₀) := Nat.find_spec h_ex_t
    -- `Zn N₀` has `HasDerivAt` at `t`.
    have h_in_Icc : t ∈ Icc (α N₀) (β N₀) := ⟨hN0_spec.1.le, hN0_spec.2.le⟩
    have h_nhd : Icc (α N₀) (β N₀) ∈ 𝓝 t := Icc_mem_nhds hN0_spec.1 hN0_spec.2
    have hd_within := hZn_deriv N₀ t h_in_Icc
    have hd : HasDerivAt (Zn N₀) (A x t (Zn N₀ t)) t := hd_within.hasDerivAt h_nhd
    -- `Z = Zn N₀` on a neighborhood of `t`.
    have h_Z_eq_eventually : Z =ᶠ[𝓝 t] Zn N₀ := by
      have h_nhd_open : Ioo (α N₀) (β N₀) ∈ 𝓝 t := Ioo_mem_nhds hN0_spec.1 hN0_spec.2
      filter_upwards [h_nhd_open] with s hs
      have h_ex_s : ∃ n, s ∈ Ioo (α n) (β n) := ⟨N₀, hs⟩
      change (if h : ∃ n, s ∈ Ioo (α n) (β n) then Zn (Nat.find h) s else Z₀ x) = Zn N₀ s
      rw [dif_pos h_ex_s]
      let M_s := Nat.find h_ex_s
      have hMs_spec : s ∈ Ioo (α M_s) (β M_s) := Nat.find_spec h_ex_s
      apply h_unique M_s N₀ s
      refine ⟨?_, ?_⟩
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.1
        · rw [min_eq_right h]; exact hs.1
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.2
        · rw [min_eq_right h]; exact hs.2
    have h_Z_t_eq : Z t = Zn N₀ t := h_Z_eq_eventually.eq_of_nhds
    rw [h_Z_t_eq]
    exact hd.congr_of_eventuallyEq h_Z_eq_eventually

/-- **Wrapped ODE clause** for `linearODESolution`.

Combines `hasLinearODESolution_of_continuousOn` (existence) and
`linearODESolution_hasDerivAt_of_hasSolution` (extraction of the ODE clause)
to give the ODE clause directly from joint continuity. -/
theorem linearODESolution_hasDerivAt
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (hab_lt : a < b) (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t :=
  linearODESolution_hasDerivAt_of_hasSolution A a b h₀ Z₀
    (hasLinearODESolution_of_continuousOn hab_lt h₀_mem hU hA_cont hx) ht

end GlobalExistence

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
