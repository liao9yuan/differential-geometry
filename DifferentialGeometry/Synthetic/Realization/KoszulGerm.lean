import DifferentialGeometry.Synthetic.Realization.LeviCivita

/-!
# Germ and 1-jet dependence of the concrete Koszul connection

The Synthetic `koszul_connection`, realized as `concreteKoszulConnection`, enjoys
the standard locality property of a Levi-Civita connection: the value of
`concreteKoszulConnection I M g X Y x₀` depends only on the germ of `Y` at `x₀`
(for fixed `X` and `x₀`).

Stronger than germ-dependence is **1-jet dependence**: the value depends only on
`Y x₀` and the `mfderiv` of the trivialization-read of `Y` at `x₀`. This is
Phase B Step B of the Ricci-flow realization programme.

## Main results (Phase B substep B.1 — germ-dependence)

* `koszul_connection_germ_dep` : if `Y` and `Y'` have the same germ at `x₀`,
  the Koszul values agree at `x₀`.

## Phase B Step B — 1-jet dependence (in progress)

This file also contains substantial partial infrastructure for proving 1-jet
dependence. The completed parts are:

* `trivReadAt I M (⇑Y) x₀` — the trivialization-read of `Y` in the
  trivialization at `x₀`, as a function `M → E`.
* `trivReadAt_self` : `trivReadAt I M (⇑Y) x₀ x₀ = Y x₀`.
* `trivReadAt_add_eventually`, `trivReadAt_sub_eventually` : additivity / subtraction
  hold on a neighborhood of `x₀` (the baseSet of the trivialization).
* `mpullbackWithin_extChartAt_symm_eq_trivReadAt` : the chart pullback equals
  the trivialization-read within the chart source. This compatibility lemma
  bridges the chart-based and trivialization-based identifications of
  `TangentSpace I y ≃ E`.
* `fderivWithin_mpullback_zero` : for a section `ΔY` with zero trivialization-read
  `mfderiv` at `x₀`, the chart pullback has zero `fderivWithin` at `extChartAt I x₀ x₀`.
* `mlieBracketSection_snd_of_zero_1jet`, `mlieBracketSection_fst_of_zero_1jet` :
  **Lie-bracket 1-jet lemma**. If `ΔY` has zero 1-jet at `x₀` (value 0 and zero
  trivialization-read mfderiv), then `[X, ΔY] x₀ = 0` and `[ΔY, X] x₀ = 0`.

The remaining pieces (scalar 1-jet vanishing for the inner-product scalar
function, and the main 1-jet theorem) require a longer chart-based computation
using `HasFDerivWithinAt.clm_apply` twice combined with smoothness of `gTriv`
(the trivialization-pushforward of the metric). See the Report at the top of
this development's Phase B work.

## Proof strategy (B.1)

The `koszul_connection` is defined via the Koszul formula:
```
2 * g(∇_X Y, Z) = koszul_rhs X Y Z
                = X(g(Y,Z)) + Y(g(Z,X)) - Z(g(X,Y))
                  - g(X, [Y,Z]) + g(Y, [Z,X]) + g(Z, [X,Y])
```
We prove that each of the six terms, *evaluated at `x₀`*, depends only on the
germ of `Y` at `x₀`. For the arguments inside `X(...)` and `Z(...)` this follows
from `Filter.EventuallyEq.mfderiv_eq`; for the Lie-bracket terms it follows from
`Filter.EventuallyEq.mlieBracket_vectorField_eq`; for the remaining terms the
value of `Y` and its germ at `x₀` coincide with those of `Y'` by
`Filter.EventuallyEq.self_of_nhds`.

We then use pointwise nondegeneracy of the Riemannian metric
(positive-definiteness of `g.inner x₀`) to transfer the scalar-level germ
identity into a tangent-vector-level identity, completing the proof.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle SyntheticTensor

namespace KoszulGerm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev V_k := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_k := C^∞⟮I, M; ℝ⟯

/-! ### Fiber-level nondegeneracy of the Riemannian metric

We re-derive the fiber-level injectivity of `g.inner x` here because the Mathlib-
adjacent `metric_flat_injective` in `Metric.lean` is declared `private`. -/

/-- Fiber-level nondegeneracy: two tangent vectors at `x₀` are equal iff their
inner products with every tangent vector at `x₀` agree. -/
private theorem fiber_eq_of_forall_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) (u v : TangentSpace I x₀)
    (h : ∀ w : TangentSpace I x₀, g.inner x₀ u w = g.inner x₀ v w) :
    u = v := by
  by_contra hne
  have h_diff : u - v ≠ 0 := sub_ne_zero.mpr hne
  -- g.inner x₀ (u - v) (u - v) = 0 from the hypothesis (applied at w = u - v)
  have h_zero : g.inner x₀ (u - v) (u - v) = 0 := by
    have hsub : g.inner x₀ (u - v) = g.inner x₀ u - g.inner x₀ v := map_sub _ _ _
    rw [hsub, ContinuousLinearMap.sub_apply, h (u - v), sub_self]
  exact absurd h_zero (ne_of_gt (g.pos x₀ (u - v) h_diff))

/-! ### Germ-dependence of scalar actions -/

/-- Germ-dependence of `extDerivFun` for scalar smooth functions: if two `M → ℝ`
functions agree on a neighborhood of `x₀`, they have the same directional
derivative at `x₀`. -/
private theorem extDerivFun_eq_of_germ_eq
    (f₁ f₂ : M → ℝ) (x₀ : M) (v : TangentSpace I x₀)
    (h : f₁ =ᶠ[nhds x₀] f₂) :
    extDerivFun (I := I) f₁ x₀ v = extDerivFun (I := I) f₂ x₀ v := by
  have h_pt : f₁ x₀ = f₂ x₀ := h.self_of_nhds
  have h_mfderiv : mfderiv I 𝓘(ℝ, ℝ) f₁ x₀ = mfderiv I 𝓘(ℝ, ℝ) f₂ x₀ :=
    h.mfderiv_eq
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [h_mfderiv, h_pt]

/-- If the smooth functions `met.g Y Z` and `met.g Y' Z` have the same germ
at `x₀` (as Pi-typed functions), then the embedded derivation acts identically
on them at `x₀`. -/
private theorem embed_eq_of_fn_germ_eq
    (X : V_k I M) (f₁ f₂ : R_k I M) (x₀ : M)
    (h : (f₁ : M → ℝ) =ᶠ[nhds x₀] (f₂ : M → ℝ)) :
    ((concreteDerivationEmbedding I M).embed X) f₁ x₀ =
    ((concreteDerivationEmbedding I M).embed X) f₂ x₀ := by
  -- Reduce through the definitional chain to `vectorFieldAction`.
  change vectorFieldAction I M X f₁ x₀ = vectorFieldAction I M X f₂ x₀
  simp only [vectorFieldAction]
  exact extDerivFun_eq_of_germ_eq I M (f₁ : M → ℝ) (f₂ : M → ℝ) x₀ (X x₀) h

/-! ### Germ equality of `met.g A B` as raw `M → ℝ` functions -/

/-- If two sections `Y, Y'` agree on a neighborhood of `x₀` as Pi-typed
functions, then `met.g Y Z` and `met.g Y' Z` agree on a neighborhood of `x₀` as
raw `M → ℝ` functions. -/
private theorem gMet_germ_eq_of_Y_germ_eq
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y Y' Z : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    (((concreteMetricDuality I M g).g Y Z : M → ℝ)) =ᶠ[nhds x₀]
      (((concreteMetricDuality I M g).g Y' Z : M → ℝ)) := by
  filter_upwards [hYY'] with y hy
  rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval]
  -- Y y = Y' y at each `y` where the germ holds, so the inner products agree.
  change g.inner y (Y y) (Z y) = g.inner y (Y' y) (Z y)
  rw [show (Y y : TangentSpace I y) = Y' y from hy]

/-- Symmetric version: if `Y =ᶠ Y'` near `x₀`, then `met.g Z Y` and `met.g Z Y'`
agree on a neighborhood of `x₀`. -/
private theorem gMet_germ_eq_of_Y_germ_eq_right
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Z Y Y' : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    (((concreteMetricDuality I M g).g Z Y : M → ℝ)) =ᶠ[nhds x₀]
      (((concreteMetricDuality I M g).g Z Y' : M → ℝ)) := by
  filter_upwards [hYY'] with y hy
  rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval]
  change g.inner y (Z y) (Y y) = g.inner y (Z y) (Y' y)
  rw [show (Y y : TangentSpace I y) = Y' y from hy]

/-! ### Germ-dependence of the bracket in the first argument -/

/-- The Synthetic bracket agrees with `VectorField.mlieBracket` pointwise, and
inherits germ-dependence from the latter. If `Y =ᶠ Y'` near `x₀`, then
`bracket emb Y Z x₀ = bracket emb Y' Z x₀`. -/
private theorem bracket_fst_germ_pointwise_eq
    (Y Y' Z : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    bracket (concreteDerivationEmbedding I M) Y Z x₀ =
    bracket (concreteDerivationEmbedding I M) Y' Z x₀ := by
  rw [bracket_eq_mlieBracketSection, bracket_eq_mlieBracketSection]
  change VectorField.mlieBracket I (⇑Y) (⇑Z) x₀ =
    VectorField.mlieBracket I (⇑Y') (⇑Z) x₀
  exact Filter.EventuallyEq.mlieBracket_vectorField_eq hYY' Filter.EventuallyEq.rfl

/-- The Synthetic bracket in the SECOND argument inherits germ-dependence from
`VectorField.mlieBracket`. If `Y =ᶠ Y'` near `x₀`, then
`bracket emb Z Y x₀ = bracket emb Z Y' x₀`. -/
private theorem bracket_snd_germ_pointwise_eq
    (Z Y Y' : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    bracket (concreteDerivationEmbedding I M) Z Y x₀ =
    bracket (concreteDerivationEmbedding I M) Z Y' x₀ := by
  rw [bracket_eq_mlieBracketSection, bracket_eq_mlieBracketSection]
  change VectorField.mlieBracket I (⇑Z) (⇑Y) x₀ =
    VectorField.mlieBracket I (⇑Z) (⇑Y') x₀
  exact Filter.EventuallyEq.mlieBracket_vectorField_eq Filter.EventuallyEq.rfl hYY'

/-! ### Scalar-level germ dependence of `koszul_rhs` at `x₀` -/

/-- **Main scalar lemma.** Given `Y =ᶠ Y'` near `x₀`, for every smooth `Z` the
Koszul RHS evaluates identically at `x₀` with `Y` or `Y'`. -/
private theorem koszul_rhs_germ_dep_Y
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Y' Z : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    (koszul_rhs (concreteDerivationEmbedding I M) (concreteMetricDuality I M g) X Y Z) x₀ =
    (koszul_rhs (concreteDerivationEmbedding I M) (concreteMetricDuality I M g) X Y' Z) x₀ := by
  set emb := concreteDerivationEmbedding I M
  set met := concreteMetricDuality I M g
  -- Expand both sides via the definition of `koszul_rhs`.
  -- Because `koszul_rhs` gives a smooth function (= `R_k I M` = `C^∞⟮I,M;ℝ⟯`)
  -- whose coercion `M → ℝ` is literally the pointwise difference / sum of the
  -- six scalar smooth functions, we can evaluate at `x₀` and check equality
  -- term by term.
  change (koszul_rhs emb met X Y Z : R_k I M) x₀ =
       (koszul_rhs emb met X Y' Z : R_k I M) x₀
  -- Unfold koszul_rhs, propagating ContMDiffMap arithmetic to Pi-applied form.
  simp only [koszul_rhs, ContMDiffMap.coe_add, ContMDiffMap.coe_sub, Pi.add_apply, Pi.sub_apply]
  -- Now we must show the six-term combination evaluates the same at x₀.
  -- Point equality Y x₀ = Y' x₀ from the germ hypothesis.
  have hYpt : (Y : Π x, TangentSpace I x) x₀ = (Y' : Π x, TangentSpace I x) x₀ :=
    hYY'.self_of_nhds
  -- T1: X(g(Y,Z)) x₀ = X(g(Y',Z)) x₀ — uses germ of the scalar function.
  have hT1 : (emb.embed X) (met.g Y Z) x₀ = (emb.embed X) (met.g Y' Z) x₀ :=
    embed_eq_of_fn_germ_eq I M X (met.g Y Z) (met.g Y' Z) x₀
      (gMet_germ_eq_of_Y_germ_eq I M g Y Y' Z x₀ hYY')
  -- T2: Y(g(Z,X)) x₀ = Y'(g(Z,X)) x₀. The function `met.g Z X` is the SAME;
  -- the change is in the vector `Y x₀ = Y' x₀`.
  have hT2 : (emb.embed Y) (met.g Z X) x₀ = (emb.embed Y') (met.g Z X) x₀ := by
    change vectorFieldAction I M Y (met.g Z X) x₀ =
      vectorFieldAction I M Y' (met.g Z X) x₀
    simp only [vectorFieldAction]
    rw [hYpt]
  -- T3: Z(g(X,Y)) x₀ = Z(g(X,Y')) x₀ — symmetric to T1 (germ of the scalar).
  have hT3 : (emb.embed Z) (met.g X Y) x₀ = (emb.embed Z) (met.g X Y') x₀ :=
    embed_eq_of_fn_germ_eq I M Z (met.g X Y) (met.g X Y') x₀
      (gMet_germ_eq_of_Y_germ_eq_right I M g X Y Y' x₀ hYY')
  -- T4: g(X, [Y,Z]) x₀ = g(X, [Y',Z]) x₀ — germ-dependence of [·,Z].
  have hT4 : (met.g X (bracket emb Y Z)) x₀ = (met.g X (bracket emb Y' Z)) x₀ := by
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval]
    rw [bracket_fst_germ_pointwise_eq I M Y Y' Z x₀ hYY']
  -- T5: g(Y, [Z,X]) x₀ = g(Y', [Z,X]) x₀ — Y x₀ = Y' x₀ and [Z,X] unchanged.
  have hT5 : (met.g Y (bracket emb Z X)) x₀ = (met.g Y' (bracket emb Z X)) x₀ := by
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval]
    rw [show (Y x₀ : TangentSpace I x₀) = Y' x₀ from hYpt]
  -- T6: g(Z, [X,Y]) x₀ = g(Z, [X,Y']) x₀ — germ-dependence of [X,·].
  have hT6 : (met.g Z (bracket emb X Y)) x₀ = (met.g Z (bracket emb X Y')) x₀ := by
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval]
    rw [bracket_snd_germ_pointwise_eq I M X Y Y' x₀ hYY']
  -- Also unfold the `met.g _ _` terms through `ContMDiffMap.coe_add` / `Pi.add_apply`
  -- so the simp has produced the pointwise RHS already. Conclude by rewriting with hT*.
  rw [hT1, hT2, hT3, hT4, hT5, hT6]

/-! ### Transfer to the vector level via fiber nondegeneracy -/

/-- **Vector-level companion lemma.** For every smooth section `Z`, the inner
product `g.inner x₀ (∇_X Y x₀) (Z x₀)` equals `g.inner x₀ (∇_X Y' x₀) (Z x₀)`
whenever `Y =ᶠ Y'` near `x₀`. -/
private theorem inner_koszul_Z_germ_eq
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Y' Z : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    g.inner x₀ (concreteKoszulConnection I M g X Y x₀) (Z x₀) =
    g.inner x₀ (concreteKoszulConnection I M g X Y' x₀) (Z x₀) := by
  set emb := concreteDerivationEmbedding I M
  set met := concreteMetricDuality I M g
  -- From `koszul_connection_spec`:
  --   2 * met.g (∇_X Y) Z = koszul_rhs X Y Z   (as smooth functions)
  -- Evaluate at x₀ and use fiber-level 2 * a = 2 * b ⇒ a = b in ℝ.
  have spec_Y := koszul_connection_spec emb met X Y Z
  have spec_Y' := koszul_connection_spec emb met X Y' Z
  -- Apply DFunLike.congr_fun at x₀ to extract the pointwise identity.
  have hY_eval := DFunLike.congr_fun spec_Y x₀
  have hY'_eval := DFunLike.congr_fun spec_Y' x₀
  -- Each side of `spec_*` evaluated at x₀.
  -- LHS evaluation: (2 * met.g ∇Y Z) x₀ = 2 * met.g ∇Y Z x₀ = 2 * g.inner x₀ ∇Y(x₀) Z(x₀)
  have hLHS_Y : (2 * met.g (concreteKoszulConnection I M g X Y) Z) x₀ =
      (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y x₀) (Z x₀) := by
    rw [show ((2 : R_k I M) * met.g (concreteKoszulConnection I M g X Y) Z : R_k I M) x₀ =
          (2 : R_k I M) x₀ * (met.g (concreteKoszulConnection I M g X Y) Z : R_k I M) x₀ from by
        simp [ContMDiffMap.coe_mul]]
    rw [concreteMetricDuality_g_eval]
    -- `(2 : R_k I M) x₀ = (2 : ℝ)` by two_smooth_eval.
    have h2 : ((2 : R_k I M) : M → ℝ) x₀ = (2 : ℝ) := by
      change (2 : R_k I M) x₀ = (2 : ℝ)
      have h_two_eq : (2 : R_k I M) = (1 : R_k I M) + (1 : R_k I M) := by norm_num
      rw [h_two_eq]
      simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply]
      norm_num
    rw [h2]
  have hLHS_Y' : (2 * met.g (concreteKoszulConnection I M g X Y') Z) x₀ =
      (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y' x₀) (Z x₀) := by
    rw [show ((2 : R_k I M) * met.g (concreteKoszulConnection I M g X Y') Z : R_k I M) x₀ =
          (2 : R_k I M) x₀ * (met.g (concreteKoszulConnection I M g X Y') Z : R_k I M) x₀ from by
        simp [ContMDiffMap.coe_mul]]
    rw [concreteMetricDuality_g_eval]
    have h2 : ((2 : R_k I M) : M → ℝ) x₀ = (2 : ℝ) := by
      change (2 : R_k I M) x₀ = (2 : ℝ)
      have h_two_eq : (2 : R_k I M) = (1 : R_k I M) + (1 : R_k I M) := by norm_num
      rw [h_two_eq]
      simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply]
      norm_num
    rw [h2]
  -- Combine: 2 * g.inner _ = (koszul_rhs ...) x₀ on each side.
  have hY_id : (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y x₀) (Z x₀) =
      (koszul_rhs emb met X Y Z) x₀ := by
    rw [← hLHS_Y]; exact hY_eval
  have hY'_id : (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y' x₀) (Z x₀) =
      (koszul_rhs emb met X Y' Z) x₀ := by
    rw [← hLHS_Y']; exact hY'_eval
  -- Koszul RHS at x₀ is germ-dependent only in Y.
  have hK := koszul_rhs_germ_dep_Y I M g X Y Y' Z x₀ hYY'
  -- Finish with cancellation of the nonzero scalar 2.
  have heq : (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y x₀) (Z x₀) =
      (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X Y' x₀) (Z x₀) := by
    rw [hY_id, hY'_id, hK]
  have h2_ne : (2 : ℝ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2_ne heq

/-! ### Main theorem: germ-dependence of `concreteKoszulConnection` in `Y` -/

/-- **Germ-dependence of the concrete Koszul connection in `Y`.**

If the smooth sections `Y` and `Y'` have the same germ at `x₀` (as Pi-typed
functions), then `concreteKoszulConnection I M g X Y` and
`concreteKoszulConnection I M g X Y'` have the same value at `x₀`. -/
theorem koszul_connection_germ_dep
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Y' : V_k I M) (x₀ : M)
    (hYY' : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[nhds x₀] ⇑Y') :
    concreteKoszulConnection I M g X Y x₀ =
    concreteKoszulConnection I M g X Y' x₀ := by
  -- Use the fiber-level Riesz / positive-definiteness nondegeneracy: two
  -- tangent vectors are equal iff every `g.inner x₀ · w` agrees. Then build
  -- smooth sections Z with Z x₀ = w via `ContMDiffSection.exists_eq_at`.
  apply fiber_eq_of_forall_inner_eq I M g x₀
  intro w
  -- Existence of a smooth section Z with Z x₀ = w.
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ w
  -- Specialize the vector-level companion lemma to this Z.
  have h := inner_koszul_Z_germ_eq I M g X Y Y' Z x₀ hYY'
  rw [hZ] at h
  exact h

/-! ## Phase B Step B — 1-jet dependence

We now strengthen `koszul_connection_germ_dep` to **1-jet dependence**: for smooth
sections `Y` and `Y'` that agree in *value* at `x₀` and whose
trivialization-reads at `x₀` have matching manifold derivatives at `x₀`, the
Koszul connection values agree.

### Strategy

1. Reduce to showing `concreteKoszulConnection X ΔY x₀ = 0` when `ΔY := Y - Y'`
   has zero 1-jet at `x₀`. This uses right-additivity `concreteKoszul_add_right`.
2. Via `koszul_connection_spec` and fiber nondegeneracy, reduce to
   `koszul_rhs X ΔY Z x₀ = 0` for all smooth sections `Z`.
3. Term-by-term in the six-term Koszul RHS:
   - Terms involving `ΔY` in the bracket slot (T1, T3, T4, T6) rely on the
     Lie-bracket-1-jet-vanishing lemma `mlieBracketSection_of_zero_1jet`.
   - Terms involving only the *value* `ΔY x₀ = 0` (T2, T5) reduce via linearity.
   - The scalar-action terms (T1, T3) use the 1-jet-vanishing mfderiv lemma
     `mfderiv_gInner_pair_of_zero_1jet`.

### Key technical lemma (chart view)

The **chart-level representation** of the 1-jet hypothesis: letting
`ψ = extChartAt I x₀`, the hypothesis that
`mfderiv (triv-read Y) x₀ = mfderiv (triv-read Y') x₀`
translates to
`fderivWithin (Y ∘ ψ.symm, in chart coordinates) (range I) (ψ x₀) =
 fderivWithin (Y' ∘ ψ.symm, in chart coordinates) (range I) (ψ x₀)`.
-/

/-! ### Chart-pullback helpers -/

/-- Abbreviation for the trivialization-read of a section `σ` at the fixed
base-point `x₀`. On a neighborhood of `x₀`, this is `C^∞` in `M → E`. -/
private def trivReadAt
    (σ : Π x : M, TangentSpace I x) (x₀ : M) : M → E :=
  fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2

/-- The trivialization-read of a smooth section is smooth on a nhd of `x₀`. -/
private theorem trivReadAt_smooth (Y : V_k I M) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (trivReadAt I M (⇑Y) x₀) x₀ := by
  have := Y.contMDiff x₀
  -- Use `contMDiffAt_section` to extract the fiber-component smoothness at `x₀`.
  rw [contMDiffAt_section x₀] at this
  exact this

/-- The trivialization-read of a smooth section is `MDifferentiableAt` at `x₀`. -/
private theorem trivReadAt_mdifferentiableAt (Y : V_k I M) (x₀ : M) :
    MDifferentiableAt I 𝓘(ℝ, E) (trivReadAt I M (⇑Y) x₀) x₀ :=
  (trivReadAt_smooth I M Y x₀).mdifferentiableAt (by simp)

/-- At the basepoint `x₀`, the trivialization-read of `Y` equals `Y x₀`. -/
private theorem trivReadAt_self
    (Y : V_k I M) (x₀ : M) :
    trivReadAt I M (⇑Y) x₀ x₀ = Y x₀ := by
  unfold trivReadAt
  -- `(trivializationAt _ _ x₀ ⟨x₀, Y x₀⟩).2 = (continuousLinearMapAt ℝ x₀) (Y x₀)`,
  -- and `continuousLinearMapAt ℝ x₀` at the basepoint is the identity.
  have hb : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  -- Rewrite the trivialization application via `continuousLinearMapAt`.
  change (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x₀, Y x₀⟩).2 = Y x₀
  rw [show (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x₀, Y x₀⟩).2 =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x₀ (Y x₀)
      from by
        rw [Trivialization.continuousLinearMapAt_apply,
          (trivializationAt E (TangentSpace I : M → Type _) x₀).coe_linearMapAt_of_mem hb]]
  -- `continuousLinearMapAt ℝ x₀ = mfderiv (extChartAt I x₀) x₀ = id`.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (mem_chart_source H x₀)]
  rw [mfderiv_extChartAt_self (I := I)]
  rfl

/-! ### Sum of smooth sections has trivialization-read equal to the sum of
trivialization-reads on the baseSet. -/

/-- Helper: on the baseSet, `(triv ⟨y, v⟩).2 = continuousLinearMapAt ℝ y v`.
This unifies the trivialization-read with the CLM. -/
private theorem trivReadAt_eq_continuousLinearMapAt
    (σ : Π x : M, TangentSpace I x) (x₀ y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    trivReadAt I M σ x₀ y =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ y (σ y) := by
  unfold trivReadAt
  rw [Trivialization.continuousLinearMapAt_apply,
    (trivializationAt E (TangentSpace I : M → Type _) x₀).coe_linearMapAt_of_mem hy]

/-- The baseSet of the trivialization-at-`x₀` is an open neighborhood of `x₀`. -/
private theorem trivializationAt_baseSet_mem_nhds
    (x₀ : M) :
    (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ nhds x₀ := by
  exact (trivializationAt E (TangentSpace I : M → Type _)
    x₀).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)

/-- The trivialization-read at `x₀` is additive in `Y` on the baseSet near `x₀`. -/
private theorem trivReadAt_add_eventually
    (Y Y' : V_k I M) (x₀ : M) :
    (trivReadAt I M (⇑(Y + Y')) x₀) =ᶠ[nhds x₀]
      (trivReadAt I M (⇑Y) x₀ + trivReadAt I M (⇑Y') x₀) := by
  filter_upwards [trivializationAt_baseSet_mem_nhds I M x₀] with y hy
  change trivReadAt I M (⇑(Y + Y')) x₀ y =
      trivReadAt I M (⇑Y) x₀ y + trivReadAt I M (⇑Y') x₀ y
  rw [trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
      trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
      trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy]
  have h_sum_ev : (Y + Y' : V_k I M) y = Y y + Y' y := rfl
  rw [h_sum_ev, map_add]

/-- The trivialization-read at `x₀` respects negation on the baseSet near `x₀`. -/
private theorem trivReadAt_neg_eventually
    (Y : V_k I M) (x₀ : M) :
    (trivReadAt I M (⇑(-Y)) x₀) =ᶠ[nhds x₀] (fun y => -trivReadAt I M (⇑Y) x₀ y) := by
  filter_upwards [trivializationAt_baseSet_mem_nhds I M x₀] with y hy
  show trivReadAt I M (⇑(-Y)) x₀ y = -trivReadAt I M (⇑Y) x₀ y
  rw [trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
      trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy]
  have h_neg_ev : (-Y : V_k I M) y = -(Y y) := rfl
  rw [h_neg_ev, map_neg]

/-- The trivialization-read at `x₀` respects subtraction on the baseSet near `x₀`. -/
private theorem trivReadAt_sub_eventually
    (Y Y' : V_k I M) (x₀ : M) :
    (trivReadAt I M (⇑(Y - Y')) x₀) =ᶠ[nhds x₀]
      (trivReadAt I M (⇑Y) x₀ - trivReadAt I M (⇑Y') x₀) := by
  filter_upwards [trivializationAt_baseSet_mem_nhds I M x₀] with y hy
  change trivReadAt I M (⇑(Y - Y')) x₀ y =
      trivReadAt I M (⇑Y) x₀ y - trivReadAt I M (⇑Y') x₀ y
  rw [trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
      trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
      trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy]
  have h_sub_ev : (Y - Y' : V_k I M) y = Y y - Y' y := rfl
  rw [h_sub_ev, map_sub]

/-! ### The zero-1-jet hypothesis propagates additively -/

/-- `ΔY := Y - Y'` has zero value at `x₀` when `Y x₀ = Y' x₀`. -/
private theorem sub_eq_zero_at_of_eq
    (Y Y' : V_k I M) (x₀ : M) (h : Y x₀ = Y' x₀) :
    (Y - Y' : V_k I M) x₀ = 0 := by
  simp [h]

/-- `mfderiv (triv-read of Y - Y') x₀ = 0` when `mfderiv (triv-read Y) x₀ =
mfderiv (triv-read Y') x₀`. -/
private theorem mfderiv_trivReadAt_sub_eq_zero
    (Y Y' : V_k I M) (x₀ : M)
    (h : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑Y) x₀) x₀
      = mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑Y') x₀) x₀) :
    mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑(Y - Y')) x₀) x₀ = 0 := by
  -- Use `EventuallyEq.mfderiv_eq` to transfer the mfderiv through the nbhd identity.
  have heq := trivReadAt_sub_eventually I M Y Y' x₀
  rw [heq.mfderiv_eq]
  rw [mfderiv_sub (trivReadAt_mdifferentiableAt I M Y x₀)
    (trivReadAt_mdifferentiableAt I M Y' x₀)]
  rw [h, sub_self]

/-! ### Lie-bracket 1-jet lemma

We prove that if `ΔY` has zero 1-jet at `x₀` (value zero and zero
trivialization-read derivative), then for any smooth section `X`,
`mlieBracketSection X ΔY x₀ = 0` and `mlieBracketSection ΔY X x₀ = 0`.

The proof works in chart coordinates: pulling back `ΔY` through `(extChartAt
I x₀).symm`, we get a local vector field on the model space `E`. Under the
hypotheses on `ΔY`'s 1-jet, this pullback vanishes at `y₀ := extChartAt I x₀ x₀`
and has zero fderivWithin `(range I)` at `y₀`. Then the model-space Lie
bracket `lieBracketWithin V W s y₀` vanishes: both terms `fderivWithin W s y₀
(V y₀) = 0` (since `V y₀ = 0`) and `fderivWithin V s y₀ (W y₀) = 0` (since
`fderivWithin V s y₀ = 0`).
-/

/-- For any `y` in `(extChartAt I x₀).source`, the chart-pullback
`mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x₀).symm (⇑ΔY) (range I) (extChartAt I x₀ y)`
equals the trivialization-read `trivReadAt (⇑ΔY) x₀ y`.

This is the compatibility between the two natural identifications
`TangentSpace I y → E`:
- the chart-based one via `(mfderivWithin (extChartAt I x₀).symm (range I)
  (extChartAt I x₀ y)).inverse`
- the trivialization-based one via `(triv x₀).continuousLinearMapAt ℝ y`. -/
private theorem mpullbackWithin_extChartAt_symm_eq_trivReadAt
    (ΔY : V_k I M) (x₀ : M) (y : M)
    (hy_src : y ∈ (extChartAt I x₀).source) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (⇑ΔY) (Set.range I)
      (extChartAt I x₀ y) =
    trivReadAt I M (⇑ΔY) x₀ y := by
  have hy_tgt : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy_src
  have hy_chart : y ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I)] at hy_src
  have hy_base : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := hy_chart
  -- Target reformulation via `continuousLinearMapAt`.
  rw [trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy_base]
  simp only [VectorField.mpullbackWithin_apply]
  -- The inverse of `mfderivWithin (extChartAt I x₀).symm (range I) (φ y)` equals
  -- `mfderiv (extChartAt I x₀) y` via `ContinuousLinearMap.inverse_eq`.
  have h_inv_eq :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I)
        (extChartAt I x₀ y)).inverse =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) ((extChartAt I x₀).symm (extChartAt I x₀ y)) :=
    ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy_tgt)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy_tgt)
  rw [h_inv_eq, (extChartAt I x₀).left_inv hy_src]
  -- `mfderiv (extChartAt I x₀) y = continuousLinearMapAt ℝ y`.
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hy_chart]
  rfl

/-! ### Fderiv-level zero 1-jet for the chart-pullback -/

/-- If `ΔY` has zero 1-jet at `x₀` (value 0 and zero trivialization-read mfderiv),
then the chart-pullback has `fderivWithin (range I) (extChartAt I x₀ x₀) = 0`. -/
private theorem fderivWithin_mpullback_zero
    (ΔY : V_k I M) (x₀ : M)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    fderivWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (⇑ΔY) (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀) = 0 := by
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  -- The chart pullback agrees with `(trivReadAt ΔY x₀) ∘ φ.symm` on a nbhd-within `s` of `y₀`.
  have h_eq_nbhd :
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (⇑ΔY) s) =ᶠ[𝓝[s] y₀]
        (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) := by
    have htgt_nw : (extChartAt I x₀).target ∈ 𝓝[Set.range I] (extChartAt I x₀ x₀) :=
      extChartAt_target_mem_nhdsWithin x₀
    filter_upwards [htgt_nw] with y hy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hh := mpullbackWithin_extChartAt_symm_eq_trivReadAt I M ΔY x₀ (φ.symm y) hy_src
    rw [φ.right_inv hy] at hh
    exact hh
  -- Rewrite fderivWithin via this EventuallyEq identity.
  rw [Filter.EventuallyEq.fderivWithin_eq h_eq_nbhd (h_eq_nbhd.self_of_nhdsWithin hy₀s)]
  -- Now compute fderivWithin (trivReadAt ΔY x₀ ∘ φ.symm) s y₀ via the chain rule.
  -- Strategy: mfderivWithin of g ∘ φ.symm = (mfderiv g (φ.symm y₀)) ∘ (mfderivWithin φ.symm s y₀).
  have hg_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ :=
    trivReadAt_mdifferentiableAt I M ΔY x₀
  have hφ_symm_y₀ : φ.symm y₀ = x₀ := by rw [hy₀]; exact φ.left_inv (mem_extChartAt_source x₀)
  have hy₀_tgt : y₀ ∈ φ.target := by
    rw [hy₀]; exact φ.map_source (mem_extChartAt_source x₀)
  have hφsymm_mdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm s y₀ := by
    have hsmooth : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (Set.range I) y₀ :=
      contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ hy₀_tgt
    exact hsmooth.mdifferentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hUniq : UniqueMDiffWithinAt 𝓘(ℝ, E) s y₀ :=
    I.uniqueMDiffOn _ hy₀s
  -- Use mfderivWithin_comp to compute the chain rule.
  have hg_within : MDifferentiableWithinAt I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) Set.univ
      (φ.symm y₀) := by
    rw [hφ_symm_y₀]
    exact hg_mdiff.mdifferentiableWithinAt
  have hφ_maps : s ⊆ φ.symm ⁻¹' (Set.univ : Set M) := fun _ _ => Set.mem_univ _
  have hcomp :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) s y₀ =
      (mfderivWithin I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) Set.univ (φ.symm y₀)).comp
        (mfderivWithin 𝓘(ℝ, E) I φ.symm s y₀) :=
    mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) y₀
      hg_within hφsymm_mdiff hφ_maps hUniq
  -- Simplify: `mfderivWithin _ _ _ univ _ = mfderiv _ _ _ _` and `φ.symm y₀ = x₀`.
  rw [hφ_symm_y₀, mfderivWithin_univ] at hcomp
  -- For model-space maps, mfderivWithin = fderivWithin.
  rw [show fderivWithin ℝ (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) s y₀ =
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) s y₀ from
    (mfderivWithin_eq_fderivWithin).symm]
  rw [hcomp, hΔY_mf]
  simp

/-! ### Lie-bracket 1-jet vanishing -/

/-- **Lie-bracket 1-jet lemma (ΔY in 2nd slot)**. If `ΔY` has zero 1-jet at `x₀`,
then `mlieBracketSection X ΔY x₀ = 0` for any smooth `X`. -/
private theorem mlieBracketSection_snd_of_zero_1jet
    (X ΔY : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    mlieBracketSection I M X ΔY x₀ = 0 := by
  -- Unfold the Lie bracket section.
  change VectorField.mlieBracket I (⇑X) (⇑ΔY) x₀ = 0
  rw [show VectorField.mlieBracket I (⇑X) (⇑ΔY) = VectorField.mlieBracketWithin I (⇑X) (⇑ΔY)
      Set.univ from by simp]
  rw [VectorField.mlieBracketWithin_apply]
  simp only [Set.preimage_univ, Set.univ_inter]
  -- Goal: (mfderiv (extChartAt I x₀) x₀).inverse
  --   (lieBracketWithin ℝ V W (range I) y₀) = 0
  -- Show that the inner lieBracketWithin is zero.
  have h_inner_zero : VectorField.lieBracketWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (⇑X) (Set.range I))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (⇑ΔY) (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀) = 0 := by
    simp only [VectorField.lieBracketWithin_eq]
    -- lieBracketWithin V W s x = fderivWithin W s x (V x) - fderivWithin V s x (W x)
    have hΔY_fderiv := fderivWithin_mpullback_zero I M ΔY x₀ hΔY_mf
    have hΔY_y₀ :
        VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (⇑ΔY)
          (Set.range I) (extChartAt I x₀ x₀) = 0 := by
      rw [mpullbackWithin_extChartAt_symm_eq_trivReadAt I M ΔY x₀ x₀
        (mem_extChartAt_source x₀)]
      rw [trivReadAt_self I M ΔY x₀, hΔY_val]
    rw [hΔY_fderiv, hΔY_y₀]
    simp
  rw [h_inner_zero]
  simp

/-- **Lie-bracket 1-jet lemma (ΔY in 1st slot)**. Symmetric version. -/
private theorem mlieBracketSection_fst_of_zero_1jet
    (X ΔY : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    mlieBracketSection I M ΔY X x₀ = 0 := by
  change VectorField.mlieBracket I (⇑ΔY) (⇑X) x₀ = 0
  rw [VectorField.mlieBracket_swap_apply, neg_eq_zero]
  exact mlieBracketSection_snd_of_zero_1jet I M X ΔY x₀ hΔY_val hΔY_mf

/-! ### Scalar 1-jet vanishing via chart pullback

We now prove that for a smooth section `ΔY` with zero 1-jet at `x₀`, the scalar
function `y ↦ g.inner y (ΔY y) (Z y)` has zero mfderiv at `x₀` (and also zero
value at `x₀`). This is the scalar analog of the Lie-bracket 1-jet lemma.

### Strategy

We pull back the scalar function through `extChartAt I x₀`. In chart coordinates,
the function becomes (near `y₀ := φ x₀` within `range I`):
```
F̃(z) = G(z) (Δ̂(z)) (Ẑ(z))
```
where:
- `G(z) : E →L[ℝ] E →L[ℝ] ℝ` is a smooth bilinear form on `E` (the
  trivialization-pushed-forward of `g.inner`).
- `Δ̂(z) := trivReadAt ΔY x₀ (φ.symm z)` is the chart-pushed-forward of the
  trivialization-read of ΔY.
- `Ẑ(z) := trivReadAt Z x₀ (φ.symm z)` similarly.

At `z₀`: `Δ̂(z₀) = ΔY x₀ = 0` and `fderivWithin Δ̂ (range I) z₀ = 0`
(both from the zero 1-jet of ΔY).

Applying `fderivWithin_clm_apply` twice (once for the inner, once for the outer
`clm_apply`), we conclude `fderivWithin F̃ (range I) z₀ = 0`.

Then `mfderiv F x₀ = fderivWithin F̃ (range I) z₀ ∘L mfderiv (extChartAt I x₀) x₀
= 0 ∘L id = 0`.
-/

/-- The inner product bilinear form pushed through the trivialization at `x₀`.

At a point `y` in the trivialization baseSet, this sends `(u, v) ∈ E × E` to
`g.inner y ((triv).symmL y u) ((triv).symmL y v)`. -/
private noncomputable def gTriv
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) (x₀ : M) :
    M → E →L[ℝ] E →L[ℝ] ℝ :=
  fun y =>
    (g.inner y).comp
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y) |>.flip.comp
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y) |>.flip

/-- The defining equation: on the baseSet, `gTriv` satisfies
`gTriv g x₀ y u v = g.inner y (symmL ℝ y u) (symmL ℝ y v)`. -/
private theorem gTriv_apply
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) (y : M) (u v : E) :
    gTriv I M g x₀ y u v = g.inner y
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u)
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y v) := by
  unfold gTriv
  rfl

/-- Compatibility between the original inner product and `gTriv` on the baseSet:
for `y` in the baseSet of the trivialization at `x₀`,
`g.inner y (ΔY y) (Z y) = gTriv g x₀ y (trivReadAt ΔY x₀ y) (trivReadAt Z x₀ y)`. -/
private theorem gInner_eq_gTriv_of_mem_baseSet
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (ΔY Z : V_k I M) (x₀ : M) (y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    g.inner y (ΔY y) (Z y) =
      gTriv I M g x₀ y (trivReadAt I M (⇑ΔY) x₀ y) (trivReadAt I M (⇑Z) x₀ y) := by
  rw [gTriv_apply, trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy,
    trivReadAt_eq_continuousLinearMapAt I M _ x₀ y hy]
  -- Now: g.inner y (ΔY y) (Z y) =
  --      g.inner y (symmL ℝ y (continuousLinearMapAt ℝ y (ΔY y)))
  --                (symmL ℝ y (continuousLinearMapAt ℝ y (Z y)))
  -- This follows from `symmL_continuousLinearMapAt`.
  rw [Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (e := trivializationAt E (TangentSpace I : M → Type _) x₀) hy (ΔY y),
    Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (e := trivializationAt E (TangentSpace I : M → Type _) x₀) hy (Z y)]

/-- The chart-pushed-forward trivialization-read of a smooth section `Y`:
`M → E` composed with `φ.symm : E → M` to get an `E → E` map. On `φ.target`,
this equals `trivReadAt Y x₀ ∘ φ.symm`. -/
private def trivReadAtChart
    (Y : V_k I M) (x₀ : M) : E → E :=
  trivReadAt I M (⇑Y) x₀ ∘ (extChartAt I x₀).symm

/-- `trivReadAtChart` is smooth within `range I` at `y₀ := extChartAt I x₀ x₀`. -/
private theorem trivReadAtChart_contMDiffWithinAt
    (Y : V_k I M) (x₀ : M) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (trivReadAtChart I M Y x₀) (Set.range I)
      (extChartAt I x₀ x₀) := by
  have hY_smooth := trivReadAt_smooth I M Y x₀
  -- trivReadAt Y x₀ is ContMDiffAt I 𝓘(ℝ, E) ∞ at x₀. Compose with φ.symm on the left:
  set φ := extChartAt I x₀
  set y₀ := φ x₀
  have hφsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (Set.range I) y₀ :=
    contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ (φ.map_source
      (mem_extChartAt_source x₀))
  have hφsymm_at_y₀ : φ.symm y₀ = x₀ := φ.left_inv (mem_extChartAt_source x₀)
  -- ContMDiffAt.comp_contMDiffWithinAt_of_eq
  exact hY_smooth.comp_contMDiffWithinAt_of_eq hφsymm hφsymm_at_y₀

/-- `trivReadAtChart` has value `Y x₀` at `y₀ = extChartAt I x₀ x₀`. -/
private theorem trivReadAtChart_self
    (Y : V_k I M) (x₀ : M) :
    trivReadAtChart I M Y x₀ (extChartAt I x₀ x₀) = Y x₀ := by
  unfold trivReadAtChart
  simp only [Function.comp_apply]
  rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
  exact trivReadAt_self I M Y x₀

/-- `trivReadAtChart` has zero value at `y₀` when `ΔY x₀ = 0`. -/
private theorem trivReadAtChart_eq_zero_of_val_zero
    (ΔY : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0) :
    trivReadAtChart I M ΔY x₀ (extChartAt I x₀ x₀) = 0 := by
  rw [trivReadAtChart_self, hΔY_val]

/-- `trivReadAtChart` has zero value and zero `fderivWithin` at `y₀` when the
section has zero 1-jet. -/
private theorem fderivWithin_trivReadAtChart_zero
    (ΔY : V_k I M) (x₀ : M)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    fderivWithin ℝ (trivReadAtChart I M ΔY x₀) (Set.range I) (extChartAt I x₀ x₀) = 0 := by
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  have hy₀_tgt : y₀ ∈ φ.target := by
    rw [hy₀]; exact φ.map_source (mem_extChartAt_source x₀)
  have hφ_symm_y₀ : φ.symm y₀ = x₀ := by
    rw [hy₀]; exact φ.left_inv (mem_extChartAt_source x₀)
  -- Use the chain rule for mfderivWithin.
  have hg_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ :=
    trivReadAt_mdifferentiableAt I M ΔY x₀
  have hφsymm_mdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm s y₀ := by
    have hsmooth : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (Set.range I) y₀ :=
      contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ hy₀_tgt
    exact hsmooth.mdifferentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hUniq : UniqueMDiffWithinAt 𝓘(ℝ, E) s y₀ :=
    I.uniqueMDiffOn _ hy₀s
  have hg_within : MDifferentiableWithinAt I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) Set.univ
      (φ.symm y₀) := by
    rw [hφ_symm_y₀]
    exact hg_mdiff.mdifferentiableWithinAt
  have hφ_maps : s ⊆ φ.symm ⁻¹' (Set.univ : Set M) := fun _ _ => Set.mem_univ _
  have hcomp :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) s y₀ =
      (mfderivWithin I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) Set.univ (φ.symm y₀)).comp
        (mfderivWithin 𝓘(ℝ, E) I φ.symm s y₀) :=
    mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) y₀
      hg_within hφsymm_mdiff hφ_maps hUniq
  rw [hφ_symm_y₀, mfderivWithin_univ] at hcomp
  rw [show fderivWithin ℝ (trivReadAtChart I M ΔY x₀) s y₀ =
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀ ∘ φ.symm) s y₀ from
    (mfderivWithin_eq_fderivWithin).symm]
  rw [hcomp, hΔY_mf]
  simp

/-! ### Smoothness of `gTriv` via the Hom-bundle trivialization

We establish that `gTriv I M g x₀ : M → E →L[ℝ] E →L[ℝ] ℝ` is `ContMDiffAt` at
`x₀`. The proof uses `contMDiffAt_section` applied to the smoothness of `g.inner`
as a section of the bilinear Hom-bundle, then identifies the trivialized
read with `gTriv` via `inCoordinates_apply_eq₂`. -/

/-- Smoothness of the auxiliary trivialized bilinear form `gTriv I M g x₀`
at the basepoint `x₀`. -/
private theorem gTriv_contMDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (gTriv I M g x₀) x₀ := by
  -- From `g.contMDiff`, the section `y ↦ ⟨y, g.inner y⟩` is smooth.
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => (⟨y, g.inner y⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
    g.contMDiff.of_le le_top
  have hg_at := hg.contMDiffAt (x := x₀)
  rw [contMDiffAt_section x₀] at hg_at
  -- hg_at : ContMDiffAt I ∞ (y ↦ trivialized g.inner y) x₀
  -- Transfer to gTriv via nbhd equality.
  apply hg_at.congr_of_eventuallyEq
  filter_upwards [trivializationAt_baseSet_mem_nhds I M x₀] with y hy
  -- Goal: gTriv I M g x₀ y = (trivializationAt (Hom bundle) x₀ ⟨y, g.inner y⟩).2
  rw [hom_trivializationAt_apply]
  ext u v
  -- Goal: gTriv I M g x₀ y u v = (inCoordinates E Tangent (E →L ℝ) Cotangent x₀ y x₀ y (g.inner y)) u v
  rw [gTriv_apply]
  -- Use inCoordinates_apply_eq₂, specialized to F₃ = ℝ, E₃ = Trivial M ℝ.
  -- inCoordinates F₁ E₁ (F₂ →L F₃) (E₂ →L E₃) x₀ y x₀ y ϕ u v =
  --   (triv_ℝ y).linearMapAt (ϕ (symmL_E y u) (symmL_E y v))
  -- For Trivial ℝ bundle, linearMapAt y = identity on ℝ (baseSet = univ).
  change g.inner y
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u)
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y v) =
      (ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _)
        (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀ y x₀ y
        (g.inner y)) u v
  -- Unfold the outer inCoordinates.
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Goal: g.inner y (symmL y u) (symmL y v) =
  --   ((triv_cot).continuousLinearMapAt ℝ y (g.inner y (symmL y u))) v
  -- For y in cotangent trivialization baseSet (which equals tangent baseSet since ℝ is trivial):
  have hcot_base :
      y ∈ (trivializationAt (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)
        x₀).baseSet := by
    -- The cotangent trivialization's baseSet is the intersection of the two factor baseSets.
    simp only [hom_trivializationAt_baseSet]
    refine ⟨hy, ?_⟩
    -- The Trivial ℝ bundle has baseSet = univ, so membership is trivial.
    change y ∈ (Set.univ : Set M)
    trivial
  rw [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hcot_base]
  -- Goal: g.inner y (symmL y u) (symmL y v) = (triv_cot ⟨y, g.inner y (symmL y u)⟩).2 v
  -- Identify triv_cot with the hom-bundle construction. By hom_trivializationAt + rfl,
  -- we can compute the trivialization application directly.
  -- Use hom_trivializationAt_apply which rewrites the total space form.
  change g.inner y
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u)
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y v) =
    ((trivializationAt (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀)
        ⟨y, g.inner y ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u)⟩).2 v
  rw [hom_trivializationAt_apply]
  -- Goal: g.inner y (symmL y u) (symmL y v) = ⟨y, inCoordinates E Tangent ℝ Trivial x₀ y x₀ y α⟩.2 v
  change g.inner y ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u)
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y v) =
    (ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _)
      ℝ (Bundle.Trivial M ℝ) x₀ y x₀ y
      (g.inner y ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ y u))) v
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Goal: g.inner y (symmL y u) (symmL y v) =
  --   (triv_ℝ).continuousLinearMapAt ℝ y
  --     (g.inner y (symmL y u) ((triv_tan).symmL ℝ y v))
  rw [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _
      (by change y ∈ (Set.univ : Set M); trivial :
        y ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).baseSet)]
  -- Goal: g.inner y (symmL y u) (symmL y v) = (triv_ℝ ⟨y, ...⟩).2
  rfl

/-- Smoothness of `gTriv I M g x₀` composed with the chart inverse, within
`range I` at `y₀ := extChartAt I x₀ x₀`. -/
private theorem gTriv_contMDiffWithinAt_chart
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (gTriv I M g x₀ ∘ (extChartAt I x₀).symm) (Set.range I)
      (extChartAt I x₀ x₀) := by
  set φ := extChartAt I x₀
  set y₀ := φ x₀
  have hφsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (Set.range I) y₀ :=
    contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀
      (φ.map_source (mem_extChartAt_source x₀))
  have hφsymm_at_y₀ : φ.symm y₀ = x₀ := φ.left_inv (mem_extChartAt_source x₀)
  exact (gTriv_contMDiffAt I M g x₀).comp_contMDiffWithinAt_of_eq hφsymm hφsymm_at_y₀

/-- `MDifferentiable` version of `gTriv_contMDiffWithinAt_chart`. -/
private theorem gTriv_mdifferentiableWithinAt_chart
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
      (gTriv I M g x₀ ∘ (extChartAt I x₀).symm) (Set.range I)
      (extChartAt I x₀ x₀) :=
  (gTriv_contMDiffWithinAt_chart I M g x₀).mdifferentiableWithinAt (by simp)

/-- `DifferentiableWithinAt ℝ` version: using `mdifferentiableWithinAt_iff_differentiableWithinAt`
on the model space. -/
private theorem gTriv_differentiableWithinAt_chart
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x₀ : M) :
    DifferentiableWithinAt ℝ
      (gTriv I M g x₀ ∘ (extChartAt I x₀).symm) (Set.range I)
      (extChartAt I x₀ x₀) :=
  (gTriv_mdifferentiableWithinAt_chart I M g x₀).differentiableWithinAt

/-- `DifferentiableWithinAt` of `trivReadAtChart` within `range I`. -/
private theorem trivReadAtChart_differentiableWithinAt
    (Y : V_k I M) (x₀ : M) :
    DifferentiableWithinAt ℝ
      (trivReadAtChart I M Y x₀) (Set.range I)
      (extChartAt I x₀ x₀) :=
  ((trivReadAtChart_contMDiffWithinAt I M Y x₀).mdifferentiableWithinAt
    (by simp)).differentiableWithinAt

/-! ### Scalar 1-jet vanishing

Using the smoothness of `gTriv`, we can now prove the scalar 1-jet lemma: if
`ΔY` has zero 1-jet at `x₀`, then the scalar function `F := g.inner · (ΔY ·) (Z ·)`
has zero mfderiv at `x₀`. The proof strategy is chart-based. -/

/-- The chart-pulled-back scalar function `F̃ := F ∘ φ.symm` agrees on a
neighborhood of `y₀` within the chart target with the clm-apply-twice form:
`gTriv x₀ (φ.symm z) (trivReadAtChart ΔY x₀ z) (trivReadAtChart Z x₀ z)`. -/
private theorem scalar_F_eq_clm_apply
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (ΔY Z : V_k I M) (x₀ : M) :
    (fun z => g.inner ((extChartAt I x₀).symm z)
        (ΔY ((extChartAt I x₀).symm z)) (Z ((extChartAt I x₀).symm z)))
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun z => (gTriv I M g x₀ ∘ (extChartAt I x₀).symm) z
        (trivReadAtChart I M ΔY x₀ z) (trivReadAtChart I M Z x₀ z)) := by
  -- We apply the nbhd filter upward within both:
  -- 1. `(extChartAt I x₀).target` (so `φ.symm` is defined and φ.right_inv holds),
  -- 2. `(trivializationAt _).baseSet` transported via `φ.symm`.
  have htgt_nw : (extChartAt I x₀).target ∈ 𝓝[Set.range I] (extChartAt I x₀ x₀) :=
    extChartAt_target_mem_nhdsWithin x₀
  -- The image of φ.symm near y₀ is contained in the chart source, hence in the baseSet.
  have h_source_nbhd : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
    extChartAt_source_mem_nhds x₀
  -- Pull back to a nhd of y₀ within s using the continuity of φ.symm.
  have h_basePullback : ((extChartAt I x₀).symm ⁻¹'
    (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) ∈
    𝓝[Set.range I] (extChartAt I x₀ x₀) := by
    have hcont : ContinuousWithinAt (extChartAt I x₀).symm (Set.range I)
        (extChartAt I x₀ x₀) := by
      have : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm (Set.range I)
          (extChartAt I x₀ x₀) :=
        contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀
          ((extChartAt I x₀).map_source (mem_extChartAt_source x₀))
      exact this.continuousWithinAt
    have hmap : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
      (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
    have hbase_nhds :
        (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
      trivializationAt_baseSet_mem_nhds I M x₀
    have := hcont.preimage_mem_nhdsWithin (by rw [hmap]; exact hbase_nhds)
    exact this
  filter_upwards [htgt_nw, h_basePullback] with z htgt hbase
  -- On this nbhd, `φ.symm z ∈ source` (from htgt via map_target) and `∈ baseSet`.
  simp only [Function.comp_apply]
  rw [gInner_eq_gTriv_of_mem_baseSet I M g ΔY Z x₀ ((extChartAt I x₀).symm z) hbase]
  rfl

/-- The scalar function `F := fun y ↦ g.inner y (ΔY y) (Z y)` on a nbhd of `x₀`
equals the composition via chart coordinates. -/
private theorem scalar_F_eq_chart_pullback
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (ΔY Z : V_k I M) (x₀ : M) :
    (fun y => g.inner y (ΔY y) (Z y))
      =ᶠ[𝓝 x₀]
    ((fun z => g.inner ((extChartAt I x₀).symm z)
        (ΔY ((extChartAt I x₀).symm z)) (Z ((extChartAt I x₀).symm z)))
      ∘ extChartAt I x₀) := by
  filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with y hy
  simp only [Function.comp_apply]
  rw [(extChartAt I x₀).left_inv hy]

/-- **Scalar 1-jet lemma: ΔY in the first inner-product slot.**
If `ΔY` has zero 1-jet at `x₀`, then the scalar function
`y ↦ g.inner y (ΔY y) (Z y)` has zero mfderiv at `x₀`. -/
private theorem mfderiv_gInner_fst_zero_1jet
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (ΔY Z : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => g.inner y (ΔY y) (Z y)) x₀ = 0 := by
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  -- Step 1: express the scalar function on a nbhd of x₀ via the chart-pullback.
  -- F(y) = F̃(φ y) near x₀ where F̃(z) = g.inner (φ.symm z) (ΔY (φ.symm z)) (Z (φ.symm z)).
  -- Thus `mfderiv F x₀ = mfderivWithin F̃ s y₀ ∘L mfderiv φ x₀`.
  -- Strategy: compute `fderivWithin F̃_clm s y₀ = 0` where `F̃_clm` is the
  -- clm-apply-twice form; this equals F̃ on a nbhd within s.
  -- Then conclude via the chain rule through φ.
  set F : M → ℝ := fun y => g.inner y (ΔY y) (Z y) with hF
  -- Smoothness of F from gFun_smooth.
  have hF_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ F :=
    fun x => by
      have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun x => (⟨x, g.inner x⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) :=
        g.contMDiff.of_le le_top
      have hgX : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
          (fun x => (⟨x, g.inner x (ΔY x)⟩ :
            TotalSpace (E →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] ℝ))) x :=
        ContMDiffAt.clm_bundle_apply hg.contMDiffAt ΔY.contMDiff.contMDiffAt
      have hgXY : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun x => (⟨x, g.inner x (ΔY x) (Z x)⟩ :
            TotalSpace ℝ (fun _ : M => ℝ))) x :=
        ContMDiffAt.clm_bundle_apply hgX Z.contMDiff.contMDiffAt
      simp only [contMDiffAt_totalSpace] at hgXY
      exact hgXY.2
  have hF_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) F x₀ :=
    (hF_smooth.contMDiffAt).mdifferentiableAt (by simp)
  -- Step 2: show mfderiv F x₀ = 0 via going through the chart.
  -- The strategy: mfderiv F x₀ = fderivWithin (F ∘ φ.symm) s y₀ ∘L (mfderiv φ x₀)
  -- and we show fderivWithin (F ∘ φ.symm) s y₀ = 0.
  have hφ_symm_y₀ : φ.symm y₀ = x₀ := by rw [hy₀]; exact φ.left_inv (mem_extChartAt_source x₀)
  have hy₀_tgt : y₀ ∈ φ.target := by
    rw [hy₀]; exact φ.map_source (mem_extChartAt_source x₀)
  have hUniq : UniqueMDiffWithinAt 𝓘(ℝ, E) s y₀ := I.uniqueMDiffOn _ hy₀s
  have hUniqDiff : UniqueDiffWithinAt ℝ s y₀ := hUniq.uniqueDiffWithinAt
  have hφsymm_mdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm s y₀ := by
    have hsmooth : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm s y₀ :=
      contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ hy₀_tgt
    exact hsmooth.mdifferentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  -- Step 3: the chart-pullback of F equals the clm-apply-twice form on a nbhd.
  -- This comes from scalar_F_eq_clm_apply.
  have h_local_eq := scalar_F_eq_clm_apply I M g ΔY Z x₀
  -- Work in chart coordinates: define F̃ (F with chart pullback) and its
  -- alternate form G̃ (via gTriv).
  set Fchart : E → ℝ := fun z => g.inner (φ.symm z)
      (ΔY (φ.symm z)) (Z (φ.symm z)) with hFchart
  set Gchart : E → ℝ := fun z => (gTriv I M g x₀ ∘ φ.symm) z
      (trivReadAtChart I M ΔY x₀ z) (trivReadAtChart I M Z x₀ z) with hGchart
  -- Fchart =ᶠ[𝓝[s] y₀] Gchart (this is what scalar_F_eq_clm_apply gives).
  have h_chart_local_eq : Fchart =ᶠ[𝓝[s] y₀] Gchart := h_local_eq
  -- Differentiability of Fchart within s at y₀ (via smoothness)
  have hFchart_diff : DifferentiableWithinAt ℝ Fchart s y₀ := by
    have : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ Fchart s y₀ := by
      have hφsymm_smooth : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm s y₀ :=
        contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ hy₀_tgt
      have hF_smooth_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ F (φ.symm y₀) := by
        rw [hφ_symm_y₀]; exact hF_smooth.contMDiffAt
      have : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (F ∘ φ.symm) s y₀ :=
        hF_smooth_at.comp_contMDiffWithinAt y₀ hφsymm_smooth
      exact this
    exact (this.mdifferentiableWithinAt (by simp)).differentiableWithinAt
  -- Differentiability of Gchart: product of differentiable factors
  have hG1_diff : DifferentiableWithinAt ℝ (gTriv I M g x₀ ∘ φ.symm) s y₀ :=
    gTriv_differentiableWithinAt_chart I M g x₀
  have hΔYhat_diff : DifferentiableWithinAt ℝ (trivReadAtChart I M ΔY x₀) s y₀ :=
    trivReadAtChart_differentiableWithinAt I M ΔY x₀
  have hZhat_diff : DifferentiableWithinAt ℝ (trivReadAtChart I M Z x₀) s y₀ :=
    trivReadAtChart_differentiableWithinAt I M Z x₀
  have hG_inner_diff : DifferentiableWithinAt ℝ
      (fun z => (gTriv I M g x₀ ∘ φ.symm) z (trivReadAtChart I M ΔY x₀ z)) s y₀ :=
    hG1_diff.clm_apply hΔYhat_diff
  -- Step 4: fderivWithin Gchart s y₀ = 0 via clm_apply twice + value/deriv zero.
  have hΔYhat_val : trivReadAtChart I M ΔY x₀ y₀ = 0 :=
    trivReadAtChart_eq_zero_of_val_zero I M ΔY x₀ hΔY_val
  have hΔYhat_fderiv :
      fderivWithin ℝ (trivReadAtChart I M ΔY x₀) s y₀ = 0 :=
    fderivWithin_trivReadAtChart_zero I M ΔY x₀ hΔY_mf
  -- Intermediate: fderivWithin (gTriv-applied-to-ΔYhat) s y₀ = 0.
  have h_inner_fderiv :
      fderivWithin ℝ
        (fun z => (gTriv I M g x₀ ∘ φ.symm) z (trivReadAtChart I M ΔY x₀ z)) s y₀ = 0 := by
    rw [fderivWithin_clm_apply hUniqDiff hG1_diff hΔYhat_diff]
    rw [hΔYhat_val, hΔYhat_fderiv]
    simp
  -- Final: fderivWithin Gchart s y₀ = 0.
  have hG_fderiv : fderivWithin ℝ Gchart s y₀ = 0 := by
    rw [hGchart]
    rw [fderivWithin_clm_apply hUniqDiff hG_inner_diff hZhat_diff]
    -- first term: (G_inner y₀).comp (fderivWithin Zhat s y₀)
    -- but (G_inner y₀) = gTriv y₀ (ΔYhat y₀) = gTriv y₀ 0 = 0.
    have h0 : (gTriv I M g x₀ ∘ φ.symm) y₀ (trivReadAtChart I M ΔY x₀ y₀) = 0 := by
      rw [hΔYhat_val]; simp
    rw [h0]
    -- second term: (fderivWithin ... ).flip(Zhat y₀) = 0.flip(...) = 0.
    rw [h_inner_fderiv]
    simp
  -- Step 5: Transfer fderivWithin(Gchart) s y₀ = 0 to fderivWithin(Fchart) s y₀ = 0
  -- via h_chart_local_eq.
  have hF_fderiv : fderivWithin ℝ Fchart s y₀ = 0 := by
    rw [Filter.EventuallyEq.fderivWithin_eq h_chart_local_eq
        (h_chart_local_eq.self_of_nhdsWithin hy₀s)]
    exact hG_fderiv
  -- Step 6: mfderiv F x₀ = 0 by proving HasMFDerivAt F x₀ 0 directly.
  -- HasMFDerivAt I 𝓘(ℝ,ℝ) F x₀ 0 ↔ ContinuousAt F x₀ ∧ HasFDerivWithinAt Fchart 0 s y₀
  -- (writing Fchart = F ∘ φ.symm, which equals writtenInExtChartAt with ℝ as codomain).
  have hFchart_hasFD : HasFDerivWithinAt Fchart (0 : E →L[ℝ] ℝ) s y₀ := by
    have hFchart_D : DifferentiableWithinAt ℝ Fchart s y₀ := hFchart_diff
    have := hFchart_D.hasFDerivWithinAt
    rw [hF_fderiv] at this
    exact this
  -- Assemble HasMFDerivAt F x₀ 0.
  have hF_hasMF : HasMFDerivAt I 𝓘(ℝ, ℝ) F x₀ 0 := by
    refine ⟨hF_smooth.continuous.continuousAt, ?_⟩
    -- HasFDerivWithinAt of writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀ F at y₀ in (extChartAt⁻¹ univ ∩ range I)
    -- = (univ ∩ range I) = range I = s
    -- writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀ F = (extChartAt 𝓘(ℝ,ℝ) (F x₀)).toFun ∘ F ∘ extChartAt.symm
    -- For 𝓘(ℝ,ℝ), extChartAt is identity; so writtenInExtChartAt = F ∘ (extChartAt I x₀).symm = Fchart.
    have hwritten : writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀ F = Fchart := by
      ext z
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_self_apply]
      rfl
    rw [hwritten]
    exact hFchart_hasFD
  exact hF_hasMF.mfderiv

/-- **Scalar 1-jet lemma: ΔY in the second inner-product slot.** -/
private theorem mfderiv_gInner_snd_zero_1jet
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Z ΔY : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => g.inner y (Z y) (ΔY y)) x₀ = 0 := by
  -- Use the symmetry of g.inner to reduce to the first-slot version.
  have h_symm : (fun y => g.inner y (Z y) (ΔY y)) = (fun y => g.inner y (ΔY y) (Z y)) := by
    ext y
    exact g.symm y (Z y) (ΔY y)
  rw [h_symm]
  exact mfderiv_gInner_fst_zero_1jet I M g ΔY Z x₀ hΔY_val hΔY_mf

/-! ### Assembling the Koszul RHS 1-jet vanishing -/

/-- For a smooth section `ΔY` with zero 1-jet at `x₀`, the Koszul RHS evaluated
at `x₀` with `ΔY` in the middle slot vanishes. -/
private theorem koszul_rhs_1jet_dep_Y
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X ΔY Z : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    (koszul_rhs (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
      X ΔY Z) x₀ = 0 := by
  set emb := concreteDerivationEmbedding I M
  set met := concreteMetricDuality I M g
  -- Unfold koszul_rhs pointwise
  change (koszul_rhs emb met X ΔY Z : R_k I M) x₀ = 0
  simp only [koszul_rhs, ContMDiffMap.coe_add, ContMDiffMap.coe_sub, Pi.add_apply, Pi.sub_apply]
  -- T1: X(g(ΔY, Z)) x₀ = 0
  have hT1 : (emb.embed X) (met.g ΔY Z) x₀ = 0 := by
    change vectorFieldAction I M X (met.g ΔY Z) x₀ = 0
    simp only [vectorFieldAction]
    -- extDerivFun (met.g ΔY Z) x₀ (X x₀) = 0 via mfderiv vanishing
    have h_fn_eq : ((met.g ΔY Z) : M → ℝ) =
        (fun y => g.inner y (ΔY y) (Z y)) := by
      ext y
      exact concreteMetricDuality_g_eval I M g ΔY Z y
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    have hmf : mfderiv I 𝓘(ℝ, ℝ) ((met.g ΔY Z) : M → ℝ) x₀ = 0 := by
      rw [h_fn_eq]
      exact mfderiv_gInner_fst_zero_1jet I M g ΔY Z x₀ hΔY_val hΔY_mf
    rw [hmf]
    simp
  -- T2: ΔY(g(Z, X)) x₀ = extDerivFun (g(Z,X)) x₀ (ΔY x₀) = 0 since ΔY x₀ = 0.
  have hT2 : (emb.embed ΔY) (met.g Z X) x₀ = 0 := by
    change vectorFieldAction I M ΔY (met.g Z X) x₀ = 0
    simp only [vectorFieldAction]
    rw [hΔY_val]
    simp only [extDerivFun, map_zero]
  -- T3: Z(g(X, ΔY)) x₀ = 0 via snd version.
  have hT3 : (emb.embed Z) (met.g X ΔY) x₀ = 0 := by
    change vectorFieldAction I M Z (met.g X ΔY) x₀ = 0
    simp only [vectorFieldAction]
    have h_fn_eq : ((met.g X ΔY) : M → ℝ) =
        (fun y => g.inner y (X y) (ΔY y)) := by
      ext y
      exact concreteMetricDuality_g_eval I M g X ΔY y
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    have hmf : mfderiv I 𝓘(ℝ, ℝ) ((met.g X ΔY) : M → ℝ) x₀ = 0 := by
      rw [h_fn_eq]
      exact mfderiv_gInner_snd_zero_1jet I M g X ΔY x₀ hΔY_val hΔY_mf
    rw [hmf]
    simp
  -- T4: g(X, [ΔY, Z]) x₀ = g.inner x₀ (X x₀) 0 = 0 via Lie-bracket 1-jet.
  have hT4 : (met.g X (bracket emb ΔY Z)) x₀ = 0 := by
    rw [concreteMetricDuality_g_eval]
    rw [bracket_eq_mlieBracketSection]
    change g.inner x₀ (X x₀) (mlieBracketSection I M ΔY Z x₀) = 0
    rw [mlieBracketSection_fst_of_zero_1jet I M Z ΔY x₀ hΔY_val hΔY_mf]
    simp
  -- T5: g(ΔY, [Z, X]) x₀ = g.inner x₀ 0 ... = 0 via ΔY x₀ = 0.
  have hT5 : (met.g ΔY (bracket emb Z X)) x₀ = 0 := by
    rw [concreteMetricDuality_g_eval, hΔY_val]
    simp
  -- T6: g(Z, [X, ΔY]) x₀ = g.inner x₀ (Z x₀) 0 = 0 via Lie-bracket 1-jet (snd).
  have hT6 : (met.g Z (bracket emb X ΔY)) x₀ = 0 := by
    rw [concreteMetricDuality_g_eval]
    rw [bracket_eq_mlieBracketSection]
    change g.inner x₀ (Z x₀) (mlieBracketSection I M X ΔY x₀) = 0
    rw [mlieBracketSection_snd_of_zero_1jet I M X ΔY x₀ hΔY_val hΔY_mf]
    simp
  -- Assemble: LHS = T1 + T2 - T3 - T4 + T5 + T6 = 0.
  rw [hT1, hT2, hT3, hT4, hT5, hT6]
  ring

/-! ### Fiber-level companion to the Koszul RHS 1-jet vanishing -/

/-- For every smooth section `Z`, the inner product
`g.inner x₀ (∇_X ΔY x₀) (Z x₀)` equals zero when `ΔY` has zero 1-jet at `x₀`. -/
private theorem inner_koszul_Z_1jet_eq
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X ΔY Z : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    g.inner x₀ (concreteKoszulConnection I M g X ΔY x₀) (Z x₀) = 0 := by
  set emb := concreteDerivationEmbedding I M
  set met := concreteMetricDuality I M g
  -- From koszul_connection_spec: 2 * met.g (∇_X ΔY) Z = koszul_rhs X ΔY Z.
  have spec := koszul_connection_spec emb met X ΔY Z
  have h_eval := DFunLike.congr_fun spec x₀
  -- h_eval : (2 * met.g (koszul_connection emb met X ΔY) Z) x₀ = koszul_rhs _ _ X ΔY Z x₀
  -- concreteKoszulConnection = koszul_connection by definition.
  -- RHS: (koszul_rhs ...) x₀ = 0.
  have hRHS : (koszul_rhs emb met X ΔY Z) x₀ = 0 :=
    koszul_rhs_1jet_dep_Y I M g X ΔY Z x₀ hΔY_val hΔY_mf
  -- Combine: 2 * g.inner x₀ ∇ΔY(x₀) Z(x₀) = 0.
  have heq : (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X ΔY x₀) (Z x₀) = 0 := by
    have hcomp : ((2 : R_k I M) *
        met.g (koszul_connection emb met X ΔY) Z : R_k I M) x₀ =
        (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X ΔY x₀) (Z x₀) := by
      rw [show ((2 : R_k I M) *
          met.g (koszul_connection emb met X ΔY) Z : R_k I M) x₀
          = (2 : R_k I M) x₀ *
            (met.g (koszul_connection emb met X ΔY) Z : R_k I M) x₀ from by
        simp [ContMDiffMap.coe_mul]]
      rw [concreteMetricDuality_g_eval]
      have h2 : ((2 : R_k I M) : M → ℝ) x₀ = (2 : ℝ) := by
        change (2 : R_k I M) x₀ = (2 : ℝ)
        have h_two_eq : (2 : R_k I M) = (1 : R_k I M) + (1 : R_k I M) := by norm_num
        rw [h_two_eq]
        simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply]
        norm_num
      rw [h2]
      rfl
    rw [← hcomp, h_eval, hRHS]
  have h2_ne : (2 : ℝ) ≠ 0 := two_ne_zero
  -- From (2 * x = 0), deduce x = 0.
  have hmul : (2 : ℝ) * g.inner x₀ (concreteKoszulConnection I M g X ΔY x₀) (Z x₀) =
    (2 : ℝ) * (0 : ℝ) := by rw [heq]; ring
  exact mul_left_cancel₀ h2_ne hmul

/-! ### `concreteKoszulConnection` vanishes on zero-1-jet sections -/

/-- **Concrete Koszul connection vanishes on zero-1-jet sections.** If `ΔY` has
value zero and zero trivialization-read mfderiv at `x₀`, then
`concreteKoszulConnection I M g X ΔY x₀ = 0`. -/
private theorem concreteKoszulConnection_of_zero_1jet
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X ΔY : V_k I M) (x₀ : M)
    (hΔY_val : ΔY x₀ = 0)
    (hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑ΔY) x₀) x₀ = 0) :
    concreteKoszulConnection I M g X ΔY x₀ = 0 := by
  -- Use fiber nondegeneracy.
  apply fiber_eq_of_forall_inner_eq I M g x₀
  intro w
  -- Existence of a smooth section Z with Z x₀ = w.
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ w
  have h := inner_koszul_Z_1jet_eq I M g X ΔY Z x₀ hΔY_val hΔY_mf
  rw [hZ] at h
  rw [h]
  simp

/-! ### Main theorem: 1-jet dependence of `concreteKoszulConnection` in `Y` -/

/-- **1-jet dependence of the concrete Koszul connection in `Y`.**

If smooth sections `Y` and `Y'` agree in value at `x₀` and have matching
trivialization-read mfderivs at `x₀`, then `concreteKoszulConnection I M g X Y`
and `concreteKoszulConnection I M g X Y'` have the same value at `x₀`. -/
theorem koszul_connection_1jet_dep
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Y' : V_k I M) (x₀ : M)
    (hY_val : Y x₀ = Y' x₀)
    (hY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑Y) x₀) x₀
      = mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑Y') x₀) x₀) :
    concreteKoszulConnection I M g X Y x₀ =
    concreteKoszulConnection I M g X Y' x₀ := by
  -- Set ΔY := Y - Y'. ΔY x₀ = 0 and mfderiv triv-read = 0.
  have hΔY_val : (Y - Y' : V_k I M) x₀ = 0 :=
    sub_eq_zero_at_of_eq I M Y Y' x₀ hY_val
  have hΔY_mf : mfderiv I 𝓘(ℝ, E) (trivReadAt I M (⇑(Y - Y')) x₀) x₀ = 0 :=
    mfderiv_trivReadAt_sub_eq_zero I M Y Y' x₀ hY_mf
  have h0 : concreteKoszulConnection I M g X (Y - Y') x₀ = 0 :=
    concreteKoszulConnection_of_zero_1jet I M g X (Y - Y') x₀ hΔY_val hΔY_mf
  -- concreteKoszul_add_right: concreteKoszul X (Y - Y') = concreteKoszul X Y - concreteKoszul X Y'.
  have h_sub : concreteKoszulConnection I M g X (Y - Y') =
      concreteKoszulConnection I M g X Y - concreteKoszulConnection I M g X Y' := by
    have hadd : concreteKoszulConnection I M g X ((Y - Y') + Y') =
        concreteKoszulConnection I M g X (Y - Y') +
          concreteKoszulConnection I M g X Y' :=
      concreteKoszul_add_right I M g X (Y - Y') Y'
    have heq : (Y - Y' + Y' : V_k I M) = Y := by abel
    rw [heq] at hadd
    rw [hadd]
    abel
  -- Evaluate at x₀: 0 = concreteKoszul X Y x₀ - concreteKoszul X Y' x₀.
  have hcongr : concreteKoszulConnection I M g X (Y - Y') x₀ =
      concreteKoszulConnection I M g X Y x₀ - concreteKoszulConnection I M g X Y' x₀ := by
    conv_lhs => rw [h_sub]
    rfl
  have h_sub_at : (concreteKoszulConnection I M g X Y x₀ :
      TangentSpace I x₀) - concreteKoszulConnection I M g X Y' x₀ = 0 := by
    rw [← hcongr]; exact h0
  exact sub_eq_zero.mp h_sub_at

end KoszulGerm

end
