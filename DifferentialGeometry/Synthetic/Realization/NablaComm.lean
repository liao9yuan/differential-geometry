import DifferentialGeometry.Synthetic.Realization.Trace
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Realization.SmoothSections

/-!
# SmoothRicciFlow: ∇ commutes with the endomorphism trace

This file proves the concrete realization of the Synthetic axiom `NablaTrComm`:

  **For every smooth vector field `X` and every `C^∞(M, ℝ)`-linear endomorphism `L` of the
  space of smooth sections of the tangent bundle,**
  `X(tr L) = tr([∇_X, L])`

where `[∇_X, L] σ := ∇_X(L σ) − L(∇_X σ)` is the induced commutator.

## Main result

* `concrete_nabla_tr_comm` : the equality of smooth scalar functions
  `vectorFieldActionSmooth I M X (concreteTr I M L) =
      concreteTr I M (commutatorEndo (embedLinearMap I M X).toFun
        (concreteConn I M cov X)
        (concreteConn_add_right I M cov X) (concreteConn_leibniz I M cov X) L)`.

Wrapping this into `AbstractTrace` form is deferred to P27 (where `concreteAbstractTrace`
itself is assembled).

## Proof outline (at a point `x₀`)

Let `d := finrank ℝ E`, `e := trivializationAt E (TangentSpace I) x₀`, `b` the standard
basis of `E`, and `σ'_i` global smooth sections that agree with `e.localFrame b i` near
`x₀`.

Define the local matrix entries and "dual frame"
```
  L^j_i(x) := θ^j(x)((L σ'_i)(x))    where   θ^j(x) v := b.equivFun ((e ⟨x, v⟩).2) j
```
These are smooth on `e.baseSet` and satisfy biorthogonality at every `x ∈ e.baseSet`:
`θ^j(x)(σ'_i(x)) = [i = j]`.

**Local trace formula** (proved in `concreteTr_fun_local_formula`):
```
(concreteTr L)(x) = ∑ᵢ L^i_i(x)       for x in a nbhd of x₀.
```

**LHS.** Using the local formula and `Filter.EventuallyEq.mfderiv_eq`, we get
`X(tr L)(x₀) = ∑ᵢ X(L^i_i)(x₀)`.

**RHS.** Evaluating `concreteTr C` at `x₀` directly via the local trace formula at
`x₀`:
```
(concreteTr C)(x₀) = ∑ᵢ θ^i(x₀)((C σ'_i)(x₀))
                   = ∑ᵢ θ^i(x₀)(cov (L σ'_i) x₀ (X x₀))
                    − ∑ᵢ θ^i(x₀)((L (concreteConn cov X σ'_i))(x₀)).
```

**Christoffel cancellation.** Using the Leibniz rule for `cov` applied to the
frame-expansion `(L σ'_i) = ∑ⱼ L^j_i · σ'_j` (which holds near `x₀`), we expand
```
cov (L σ'_i) x₀ (X x₀)
  = ∑ⱼ X(L^j_i)(x₀) • σ'_j(x₀) + ∑ⱼ L^j_i(x₀) • cov σ'_j x₀ (X x₀).
```
Pairing with `θ^i(x₀)` (biorthogonal to `σ'_j(x₀)`) and summing over `i`,
the diagonal term `∑ᵢ ⟨θ^i(x₀), X(L^j_i)(x₀) σ'_j(x₀)⟩` collapses to `∑ᵢ X(L^i_i)(x₀)`,
matching the LHS; the off-diagonal Christoffel terms
`∑ᵢⱼ L^j_i(x₀) θ^i(x₀)(cov σ'_j x₀ (X x₀))` reindex exactly to the second RHS sum,
giving the cancellation.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
-- The proof of `concrete_nabla_tr_comm` involves long calc blocks over a `Fin d` local
-- frame together with elaboration-heavy bundle manipulation; the default heartbeat
-- budget is insufficient.
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative SyntheticTensor

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Finite sums: mdifferentiability and directional derivative. -/

/-- Mdifferentiability at `x` of a finite pointwise sum, given mdifferentiability of each
summand. -/
private lemma mdifferentiableAt_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact mdifferentiableAt_const
  | insert i s his ih =>
      rw [Finset.sum_insert his]
      exact MDifferentiableAt.add
        (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Directional derivative of a finite pointwise sum equals the sum of directional
derivatives. -/
private lemma extDerivFun_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    extDerivFun (I := I) (∑ i ∈ s, f i) x v =
      ∑ i ∈ s, extDerivFun (I := I) (f i) x v := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      change extDerivFun (I := I) (0 : M → ℝ) x v = 0
      rw [extDerivFun_zero]; rfl
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      have hfi : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x :=
        hf i (Finset.mem_insert_self i s)
      have hrest_each : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) x :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hrest : MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ j ∈ s, f j) x :=
        mdifferentiableAt_finset_sum I M s f x hrest_each
      rw [extDerivFun_add hfi hrest]
      simp only [ContinuousLinearMap.add_apply]
      rw [ih hrest_each]

/-! ### Smoothness of local matrix entries at x₀.

For a `C^∞(M)`-linear endomorphism `L` and a smooth section `σ`, the local matrix entry
`x ↦ b.equivFun ((e ⟨x, (L σ)(x)⟩).2) j` is smooth at `x₀`. -/

private lemma mdifferentiableAt_local_matrix_entry
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x => b.equivFun
        ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, (L σ) x⟩).2) j) x₀ := by
  have h_sect : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun x =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, (L σ) x⟩).2) x₀ :=
    (contMDiffAt_section x₀).mp (L σ).contMDiff.contMDiffAt
  have hcl : ContDiff ℝ ∞ (fun w : E => b.equivFun w j) :=
    (ContinuousLinearMap.proj j |>.comp
      b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
  exact (hcl.contDiffAt.contMDiffAt.comp _ h_sect).mdifferentiableAt (by simp)

/-! ### Biorthogonality of the local frame and its dual at `x₀`.

For `σ'_i` agreeing with `e.localFrame b i` near `x₀`, we have `σ'_i(x₀) = le₀.symm (b i)`
where `le₀ = e.linearEquivAt ℝ x₀ he`. Consequently, the dual pairing
`θ^j(x₀)(σ'_i(x₀)) = b.equivFun ((e ⟨x₀, σ'_i(x₀)⟩).2) j = [i = j]`. -/

private lemma sigma_at_base
    {x₀ : M}
    (e : Trivialization E (TotalSpace.proj :
      TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (he : x₀ ∈ e.baseSet)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x = e.localFrame b i x)
    (i : Fin (Module.finrank ℝ E)) :
    (σ' i) x₀ = (e.linearEquivAt ℝ x₀ he).symm (b i) := by
  have h := hσ'.self_of_nhds i
  rw [h]
  change e.localFrame b i x₀ = (e.linearEquivAt ℝ x₀ he).symm (b i)
  rw [e.localFrame_apply_of_mem_baseSet (hx := he)]
  simp [Trivialization.basisAt]

/-- Biorthogonality at `x₀`. -/
private lemma dual_pairing_at_base
    {x₀ : M}
    (e : Trivialization E (TotalSpace.proj :
      TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (he : x₀ ∈ e.baseSet)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x = e.localFrame b i x)
    (i j : Fin (Module.finrank ℝ E)) :
    b.equivFun ((e ⟨x₀, (σ' j) x₀⟩).2) i = if i = j then (1 : ℝ) else 0 := by
  classical
  have hσj := sigma_at_base I M e he b σ' hσ' j
  rw [hσj]
  have hev : (e ⟨x₀, (e.linearEquivAt ℝ x₀ he).symm (b j)⟩).2 = b j := by
    have h := e.linearEquivAt_apply (R := ℝ) x₀ he
      ((e.linearEquivAt ℝ x₀ he).symm (b j))
    rw [← h]
    exact (e.linearEquivAt ℝ x₀ he).apply_symm_apply (b j)
  rw [hev, b.equivFun_self j i]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-! ### Frame expansion at and near `x₀`.

Near `x₀`, every smooth section `v` satisfies
`v(x) = ∑_j b.equivFun ((e ⟨x, v(x)⟩).2) j • (σ'_j)(x)`. -/

private lemma frame_expansion_nbhd
    {x₀ : M}
    (e : Trivialization E (TotalSpace.proj :
      TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (he : x₀ ∈ e.baseSet)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x = e.localFrame b i x)
    (w : Π x : M, TangentSpace I x) :
    ∀ᶠ x in 𝓝 x₀, w x =
      ∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • (σ' j) x := by
  filter_upwards [hσ', e.open_baseSet.mem_nhds he] with x hσ'x hx
  -- Abbreviation and fact about the local linear equiv.
  set le : TangentSpace I x ≃ₗ[ℝ] E := e.linearEquivAt ℝ x hx with hle_def
  have hle_apply : ∀ v : TangentSpace I x, le v = (e ⟨x, v⟩).2 :=
    fun v => e.linearEquivAt_apply (R := ℝ) x hx v
  -- Key: σ'_j(x) = le.symm (b j).
  have h_σ_le : ∀ j, (σ' j) x = le.symm (b j) := by
    intro j
    rw [hσ'x j]
    rw [e.localFrame_apply_of_mem_baseSet (hx := hx)]
    simp [Trivialization.basisAt, le]
  -- Rewrite RHS: substitute σ'_j(x) = le.symm (b j).
  rw [show (∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • (σ' j) x) =
      (∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • le.symm (b j)) from by
        congr 1; ext j; rw [h_σ_le j]]
  -- Pull le.symm out of the sum.
  rw [show (∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • le.symm (b j)) =
      le.symm (∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • b j) from by
        rw [map_sum]; congr 1; ext j; rw [map_smul]]
  -- The inner sum equals (e ⟨x, w x⟩).2 by `b.sum_equivFun`.
  rw [show (∑ j, b.equivFun ((e ⟨x, w x⟩).2) j • b j) = (e ⟨x, w x⟩).2 from
    b.sum_equivFun ((e ⟨x, w x⟩).2)]
  -- le.symm ((e ⟨x, w x⟩).2) = le.symm (le (w x)) = w x.
  rw [show (e ⟨x, w x⟩).2 = le (w x) from (hle_apply (w x)).symm]
  exact (le.symm_apply_apply (w x)).symm

end Helpers

/-! ### The main theorem -/

section Main

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- ∇ commutes with the endomorphism trace: for every smooth vector field `X` and every
`C^∞(M, ℝ)`-linear endomorphism `L` of the space of smooth sections of `TM`,
`X(tr L) = tr([∇_X, L])`.

The commutator is built via `commutatorEndo` using the embedded derivation of `X`
(`(embedLinearMap I M X).toFun`) and the concrete connection `concreteConn cov X`,
with the specialized linearity witnesses `concreteConn_add_right I M cov X` and
`concreteConn_leibniz I M cov X`. -/
theorem concrete_nabla_tr_comm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    vectorFieldActionSmooth I M X (concreteTr I M L) =
      concreteTr I M (commutatorEndo
        (embedLinearMap I M X).toFun
        (concreteConn I M cov X)
        (concreteConn_add_right I M cov X)
        (concreteConn_leibniz I M cov X) L) := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  classical
  -- `C := [∇_X, L]` is the commutator endomorphism.
  set C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    commutatorEndo (embedLinearMap I M X).toFun
      (concreteConn I M cov X)
      (concreteConn_add_right I M cov X)
      (concreteConn_leibniz I M cov X) L with hC_def
  -- Pointwise equality at each `x₀`.
  ext x₀
  -- Local frame setup at x₀.
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  let b := Module.finBasis ℝ E
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  obtain ⟨σ', hσ'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  -- Local matrix entries: `Lji σ i j x := b.equivFun ((e ⟨x, (L σ_i)(x)⟩).2) j`.
  -- Functional abbreviation: `localEntry L' σ_i j` as a raw M → ℝ function.
  let localEntry :
      (Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) →
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →
      Fin (Module.finrank ℝ E) → M → ℝ :=
    fun L' σ j x => b.equivFun ((e ⟨x, (L' σ) x⟩).2) j
  -- Each localEntry is mdifferentiable at x₀.
  have h_Lji_mdiff : ∀ (L' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (j : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (localEntry L' σ j) x₀ := by
    intro L' σ j
    exact mdifferentiableAt_local_matrix_entry I M L' σ x₀ b j
  -- The `LinearMap.id`-like trick: to rewrite σ'_i into its local form.
  -- Useful facts for the proof.
  -- 1. σ'_i(x₀) = le₀.symm (b i).
  have hσ'_at_base := fun i =>
    sigma_at_base I M (x₀ := x₀) e he b σ' hσ' i
  -- 2. Biorthogonality at x₀.
  have hdual := fun i j =>
    dual_pairing_at_base I M (x₀ := x₀) e he b σ' hσ' i j
  ---------------------------------------------------------------
  -- STEP A: The local trace formulas for L and C (near x₀ / at x₀).
  ---------------------------------------------------------------
  -- Local formula for `concreteTr L`: applies near x₀.
  have h_trL_local : ∀ᶠ x in 𝓝 x₀,
      (concreteTr I M L : M → ℝ) x = ∑ i, localEntry L (σ' i) i x :=
    concreteTr_fun_local_formula I M L x₀ σ' hσ'
  -- Local formula for `concreteTr C`: at x₀.
  have h_trC_at : (concreteTr I M C : M → ℝ) x₀ = ∑ i, localEntry C (σ' i) i x₀ :=
    (concreteTr_fun_local_formula I M C x₀ σ' hσ').self_of_nhds
  ---------------------------------------------------------------
  -- STEP B: LHS simplification.
  ---------------------------------------------------------------
  -- LHS `(vectorFieldActionSmooth I M X (concreteTr I M L)) x₀` equals
  -- `extDerivFun (↑(concreteTr I M L)) x₀ (X x₀)`.
  change vectorFieldAction I M X (concreteTr I M L) x₀ =
    (concreteTr I M C : M → ℝ) x₀
  simp only [vectorFieldAction]
  -- Apply `Filter.EventuallyEq.mfderiv_eq` via `extDerivFun`.
  have h_ext_eq :
      extDerivFun (I := I) ((concreteTr I M L : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) =
      extDerivFun (I := I) (∑ i, localEntry L (σ' i) i) x₀ (X x₀) := by
    -- Use that extDerivFun only depends on (function, point, direction), and mfderiv
    -- respects EventuallyEq.
    have hmfd : mfderiv I 𝓘(ℝ, ℝ) ((concreteTr I M L : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
        mfderiv I 𝓘(ℝ, ℝ) (∑ i, localEntry L (σ' i) i) x₀ := by
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [h_trL_local] with x hx
      rw [hx, Finset.sum_apply]
    have hval : ((concreteTr I M L : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
        (∑ i, localEntry L (σ' i) i) x₀ := by
      have := h_trL_local.self_of_nhds
      change ((concreteTr I M L : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ = _
      rw [this, Finset.sum_apply]
    simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hmfd, hval]
  rw [h_ext_eq]
  -- Use `extDerivFun_finset_sum` to split the derivative of the sum.
  rw [extDerivFun_finset_sum I M Finset.univ (fun i => localEntry L (σ' i) i) x₀ (X x₀)
    (fun i _ => h_Lji_mdiff L (σ' i) i)]
  -- Now the goal has LHS: ∑ i, extDerivFun (localEntry L σ'_i i) x₀ (X x₀)
  -- and RHS: (concreteTr C) x₀.
  rw [h_trC_at]
  ---------------------------------------------------------------
  -- STEP C: Expand `localEntry C σ'_i i x₀` using `C` definition.
  ---------------------------------------------------------------
  -- `(C σ'_i)(x₀) = cov (L σ'_i) x₀ (X x₀) − (L (concreteConn cov X σ'_i))(x₀)`.
  have h_C_action : ∀ i,
      (C (σ' i)) x₀ = cov (L (σ' i)) x₀ (X x₀) -
        (L (concreteConn I M cov X (σ' i))) x₀ := by
    intro i
    change (commutatorEndo (embedLinearMap I M X).toFun (concreteConn I M cov X) _ _ L (σ' i)) x₀
      = cov (L (σ' i)) x₀ (X x₀) -
        (L (concreteConn I M cov X (σ' i))) x₀
    simp only [commutatorEndo, LinearMap.coe_mk, AddHom.coe_mk]
    change (concreteConn I M cov X (L (σ' i)) - L (concreteConn I M cov X (σ' i))) x₀ =
      cov (L (σ' i)) x₀ (X x₀) - (L (concreteConn I M cov X (σ' i))) x₀
    rw [ContMDiffSection.coe_sub]
    simp only [Pi.sub_apply]
    rfl
  -- `localEntry C σ'_i i x₀ = b.equivFun ((e ⟨x₀, (C σ'_i)(x₀)⟩).2) i`.
  have h_localEntry_C : ∀ i,
      localEntry C (σ' i) i x₀ =
        b.equivFun ((e ⟨x₀, cov (L (σ' i)) x₀ (X x₀) -
          (L (concreteConn I M cov X (σ' i))) x₀⟩).2) i := by
    intro i; rw [show localEntry C (σ' i) i x₀ =
      b.equivFun ((e ⟨x₀, (C (σ' i)) x₀⟩).2) i from rfl, h_C_action i]
  ---------------------------------------------------------------
  -- STEP D: Christoffel cancellation.
  --
  -- The core identity is:
  -- ∑_i X(L^i_i)(x₀) = ∑_i θ^i(x₀)(cov (L σ'_i) x₀ (X x₀))
  --                   − ∑_i θ^i(x₀)((L (concreteConn cov X σ'_i))(x₀))
  --
  -- Step D.1: Expand `cov (L σ'_i)` using frame expansion + Leibniz.
  -- On a nbhd of x₀: L σ'_i = ∑_j (localEntry L σ'_i j) • σ'_j.
  ---------------------------------------------------------------
  -- Congruence: `cov (L σ'_i) x₀ = cov (∑ j, f j • σ'_j) x₀` where f j x := localEntry L σ'_i j x.
  -- Frame expansion on nbhd of x₀.
  have h_Lsigma_expand : ∀ i, ∀ᶠ x in 𝓝 x₀,
      (L (σ' i)) x =
        ∑ j, localEntry L (σ' i) j x • (σ' j) x := by
    intro i
    exact frame_expansion_nbhd I M (x₀ := x₀) e he b σ' hσ' (L (σ' i))
  -- MDifferentiableAt for (L (σ' i)) (smooth section).
  have h_Lsigma_mdiff : ∀ i,
      MDiffAt (T% fun x => (L (σ' i)) x) x₀ :=
    fun i => (L (σ' i)).mdifferentiableAt
  -- MDifferentiableAt for σ'_j.
  have h_sigma_mdiff : ∀ j,
      MDiffAt (T% fun x => (σ' j) x) x₀ :=
    fun j => (σ' j).mdifferentiableAt
  -- For each i, the pointwise equality at x₀ of `cov (L σ'_i) x₀` and the summed form.
  have h_cov_Lsigma : ∀ i,
      cov (L (σ' i)) x₀ (X x₀) =
        ∑ j, extDerivFun (localEntry L (σ' i) j) x₀ (X x₀) • (σ' j) x₀ +
        ∑ j, localEntry L (σ' i) j x₀ • cov (σ' j) x₀ (X x₀) := by
    intro i
    -- Use congr_of_eventuallyEq to replace `L σ'_i` by the finite sum near x₀.
    have h_mdiff_sum : MDiffAt (T% fun x =>
        ∑ j, localEntry L (σ' i) j x • (σ' j) x) x₀ := by
      -- The smooth-section form: `∑ j, (localEntry-as-section) • (σ'_j)`. By Filter.EventuallyEq
      -- to `L σ'_i` which is smooth, hence mdifferentiable.
      have h_eq : (fun y => TotalSpace.mk' E (E := TangentSpace I) y ((L (σ' i)) y)) =ᶠ[𝓝 x₀]
          (fun y => TotalSpace.mk' E (E := TangentSpace I) y
            (∑ j, localEntry L (σ' i) j y • (σ' j) y)) := by
        filter_upwards [h_Lsigma_expand i] with y hy
        change TotalSpace.mk' E y ((L (σ' i)) y) =
          TotalSpace.mk' E y (∑ j, localEntry L (σ' i) j y • (σ' j) y)
        rw [hy]
      exact (h_Lsigma_mdiff i).congr_of_eventuallyEq h_eq.symm
    -- Step 1: `cov (L σ'_i) x₀ = cov (∑_j f_j • σ'_j) x₀` via congr.
    have h_congr :
        cov (L (σ' i)) x₀ = cov (fun x => ∑ j, localEntry L (σ' i) j x • (σ' j) x) x₀ := by
      refine cov.isCovariantDerivativeOn.congr_of_eventuallyEq
        (h_Lsigma_mdiff i) h_mdiff_sum (s := Set.univ) (by simp) ?_
      exact h_Lsigma_expand i
    rw [h_congr]
    -- Step 2: Expand cov of the sum. We prove a helper:
    -- For any Finset s,
    --   cov (fun x => ∑ j ∈ s, f_j(x) • σ_j(x)) x₀ (X x₀)
    --   = ∑ j ∈ s, extDerivFun(f_j) x₀ (X x₀) • σ_j(x₀)
    --     + ∑ j ∈ s, f_j(x₀) • cov σ_j x₀ (X x₀).
    -- (Using the abbreviations f_j := localEntry L (σ' i) j, σ_j := σ' j.)
    suffices h_sum_rule : ∀ (t : Finset (Fin (Module.finrank ℝ E))),
        cov (fun x => ∑ k ∈ t, localEntry L (σ' i) k x • (σ' k) x) x₀ (X x₀) =
        ∑ k ∈ t, extDerivFun (localEntry L (σ' i) k) x₀ (X x₀) • (σ' k) x₀ +
        ∑ k ∈ t, localEntry L (σ' i) k x₀ • cov (σ' k) x₀ (X x₀) by
      exact h_sum_rule Finset.univ
    -- Helper: mdifferentiability of the finite sum section.
    have h_sum_mdiff : ∀ (t₀ : Finset (Fin (Module.finrank ℝ E))),
        MDiffAt (T% fun x => ∑ l ∈ t₀, localEntry L (σ' i) l x • (σ' l) x) x₀ := by
      intro t₀
      classical
      induction t₀ using Finset.induction with
      | empty =>
        -- Empty sum is the zero section, which is smooth.
        simp only [Finset.sum_empty]
        exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (E := TangentSpace I) (F := E)
      | insert l₀ t₁ hl₀t₁ inner_ih =>
        -- Target: MDiffAt (T% fun x => ∑ l ∈ insert l₀ t₁, ...) x₀.
        -- Rewrite the sum `∑ l ∈ insert l₀ t₁, ...` as `f_l₀ x • σ_l₀ x + ∑ l ∈ t₁, ...`.
        have hma := mdifferentiableAt_add_section
          (MDifferentiableAt.smul_section (h_Lji_mdiff L (σ' i) l₀) (h_sigma_mdiff l₀))
          inner_ih
        -- hma : MDiffAt (T% ((f_l₀ • σ_l₀) + (∑ l ∈ t₁, f_l • σ_l))) x₀.
        -- We want: MDiffAt (T% fun x => ∑ l ∈ insert l₀ t₁, f_l x • σ_l x) x₀.
        -- These differ by pointwise equality of the underlying sections.
        refine hma.congr_of_eventuallyEq ?_
        filter_upwards with x
        change TotalSpace.mk' E x _ = TotalSpace.mk' E x _
        congr 1
        rw [Finset.sum_insert hl₀t₁]
        rfl
    intro t
    classical
    induction t using Finset.induction with
    | empty =>
      simp only [Finset.sum_empty, add_zero]
      have h_cov_zero : cov (fun _ : M => (0 : TangentSpace I _)) x₀ = 0 :=
        cov.isCovariantDerivativeOn.zero (hx := Set.mem_univ _)
      rw [h_cov_zero]; rfl
    | insert k t hkt ih =>
      -- Step 1: rewrite the sum inside cov to add form.
      have h_add_fun : (fun x : M => ∑ l ∈ insert k t, localEntry L (σ' i) l x • (σ' l) x) =
          (fun x => localEntry L (σ' i) k x • (σ' k) x) +
          (fun x => ∑ l ∈ t, localEntry L (σ' i) l x • (σ' l) x) := by
        ext x; rw [Finset.sum_insert hkt]; rfl
      rw [h_add_fun]
      have h_fk_mdiff : MDiffAt (localEntry L (σ' i) k) x₀ := h_Lji_mdiff L (σ' i) k
      have h_fkσk_mdiff : MDiffAt (T% fun x => localEntry L (σ' i) k x • (σ' k) x) x₀ :=
        MDifferentiableAt.smul_section h_fk_mdiff (h_sigma_mdiff k)
      have h_rest_mdiff := h_sum_mdiff t
      -- Step 2: apply `cov.isCovariantDerivativeOn.add`.
      rw [cov.isCovariantDerivativeOn.add h_fkσk_mdiff h_rest_mdiff]
      simp only [ContinuousLinearMap.add_apply]
      -- Step 3: apply `.leibniz` for the first summand.
      rw [show (fun x : M => localEntry L (σ' i) k x • (σ' k) x) =
          (localEntry L (σ' i) k : M → ℝ) • (fun x => (σ' k) x) from rfl]
      rw [cov.isCovariantDerivativeOn.leibniz (h_sigma_mdiff k) h_fk_mdiff]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      -- Step 4: use induction hypothesis for the rest.
      rw [ih]
      -- Step 5: unroll `Finset.sum_insert` on the RHS.
      rw [Finset.sum_insert hkt, Finset.sum_insert hkt]
      -- Arithmetic rearrangement.
      abel
  ---------------------------------------------------------------
  -- STEP E: Apply θ^i(x₀) to both sides of h_cov_Lsigma and sum.
  ---------------------------------------------------------------
  -- We want: ∑_i θ^i(x₀)(cov (L σ'_i) x₀ (X x₀))
  --        = ∑_i [diagonal term: X(L^i_i)(x₀)] + ∑_i [Christoffel term]
  -- Here θ^i(x₀) (v) = b.equivFun ((e ⟨x₀, v⟩).2) i.
  -- First, apply `h_cov_Lsigma` to get `cov (L σ'_i) x₀ (X x₀)` in an expanded form.
  -- Then pair with `θ^i(x₀)` (ℝ-linear as `b.equivFun ∘ (e.linearEquivAt)`).
  -- Define the linear functional θ^i(x₀) at the operator level.
  -- θ^i(x₀) v = b.equivFun ((e ⟨x₀, v⟩).2) i is ℝ-linear.
  -- The key arithmetic:
  -- (1) `b.equivFun ((e ⟨x₀, A + B⟩).2) i = b.equivFun ((e ⟨x₀, A⟩).2) i + b.equivFun ((e ⟨x₀, B⟩).2) i`
  -- (2) `b.equivFun ((e ⟨x₀, c • v⟩).2) i = c * b.equivFun ((e ⟨x₀, v⟩).2) i`
  -- (3) `b.equivFun ((e ⟨x₀, ∑_j f_j⟩).2) i = ∑_j b.equivFun ((e ⟨x₀, f_j⟩).2) i`
  -- We encapsulate θ^i(x₀) as a linear map.
  let le₀ : TangentSpace I x₀ ≃ₗ[ℝ] E := e.linearEquivAt ℝ x₀ he
  have h_coe_e : ∀ v : TangentSpace I x₀, (e ⟨x₀, v⟩).2 = le₀ v := fun v =>
    (e.linearEquivAt_apply (R := ℝ) x₀ he v).symm
  let θ : Fin (Module.finrank ℝ E) → TangentSpace I x₀ →ₗ[ℝ] ℝ :=
    fun i => (b.coord i).comp le₀.toLinearMap
  -- `θ i v = b.equivFun ((e ⟨x₀, v⟩).2) i`.
  have h_θ_eq : ∀ i v, θ i v = b.equivFun ((e ⟨x₀, v⟩).2) i := by
    intro i v
    change (b.coord i) (le₀ v) = b.equivFun ((e ⟨x₀, v⟩).2) i
    rw [h_coe_e v]
    rw [b.equivFun_apply]; rfl
  -- Biorthogonality: θ^i σ'_j x₀ = δ_ij.
  have h_θ_δ : ∀ i j, θ i ((σ' j) x₀) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [h_θ_eq i ((σ' j) x₀)]
    exact hdual i j
  -- RHS of the main goal: `∑ i, localEntry C (σ' i) i x₀`.
  -- Expand via `h_localEntry_C` and `h_cov_Lsigma`:
  have h_rhs_rewrite :
      (∑ i, localEntry C (σ' i) i x₀) =
        ∑ i, θ i (cov (L (σ' i)) x₀ (X x₀)) -
        ∑ i, θ i ((L (concreteConn I M cov X (σ' i))) x₀) := by
    -- Each i: localEntry C σ'_i i x₀ = θ i ((C σ'_i) x₀) = θ i (cov (L σ'_i) ... - L (∇_X σ'_i) ...).
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i
    rw [h_localEntry_C i]
    rw [show b.equivFun ((e ⟨x₀, cov (L (σ' i)) x₀ (X x₀) -
      (L (concreteConn I M cov X (σ' i))) x₀⟩).2) i =
      θ i (cov (L (σ' i)) x₀ (X x₀) - (L (concreteConn I M cov X (σ' i))) x₀) from by
        rw [h_θ_eq]]
    exact map_sub (θ i) _ _
  rw [h_rhs_rewrite]
  -- Now expand ∑_i θ^i(x₀)(cov (L σ'_i) x₀ (X x₀)) using h_cov_Lsigma.
  have h_cov_theta : ∀ i,
      θ i (cov (L (σ' i)) x₀ (X x₀)) =
        extDerivFun (localEntry L (σ' i) i) x₀ (X x₀) +
        ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀)) := by
    intro i
    rw [h_cov_Lsigma i]
    rw [map_add]
    -- θ i on each summand.
    congr 1
    · -- θ i (∑_j X(L^j_i) x₀ • σ'_j x₀)
      rw [map_sum]
      -- ∑ j, θ i (X(L^j_i) x₀ • σ'_j x₀) = ∑ j, X(L^j_i) x₀ • θ i (σ'_j x₀)
      -- = ∑ j, X(L^j_i) x₀ • [if i = j then 1 else 0]
      -- = X(L^i_i) x₀
      rw [show (fun j => θ i (extDerivFun (localEntry L (σ' i) j) x₀ (X x₀) • (σ' j) x₀)) =
          (fun j => extDerivFun (localEntry L (σ' i) j) x₀ (X x₀) • θ i ((σ' j) x₀)) from by
            funext j; exact map_smul (θ i) _ _]
      -- Now the sum collapses via hdual.
      rw [show (fun j => extDerivFun (localEntry L (σ' i) j) x₀ (X x₀) •
          θ i ((σ' j) x₀)) = (fun j =>
          extDerivFun (localEntry L (σ' i) j) x₀ (X x₀) •
            (if i = j then (1 : ℝ) else 0)) from by
              funext j; rw [h_θ_δ]]
      -- ∑ j, c j • (if i = j then 1 else 0) = c i.
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ i]
      simp
    · -- θ i (∑_k L^k_i x₀ • cov σ'_k x₀ (X x₀)) = ∑_k L^k_i x₀ * θ i (cov σ'_k x₀ (X x₀))
      rw [map_sum]
      congr 1; ext k
      rw [map_smul (θ i) _ _]
      exact smul_eq_mul _ _
  -- Rewrite the main equation in terms of h_cov_theta.
  rw [show ∑ i, θ i (cov (L (σ' i)) x₀ (X x₀)) =
      ∑ i, (extDerivFun (localEntry L (σ' i) i) x₀ (X x₀) +
        ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀))) from by
        congr 1; ext i; rw [h_cov_theta i]]
  rw [Finset.sum_add_distrib]
  -- The first sum matches the LHS. What remains is cancelling:
  -- ∑_i ∑_k L^k_i x₀ * θ i (cov σ'_k x₀ (X x₀)) - ∑_i θ i (L (∇_X σ'_i) x₀) = 0.
  -- Equivalently, show these sums are equal.
  -- Reduce to showing: sum(i, k) = sum(i, j). We reindex by (i,k) ↦ (j, i).
  ---------------------------------------------------------------
  -- STEP F: VBC expansion of `(L (concreteConn cov X σ'_i))(x₀)` via `vbcFiber`.
  --
  -- We have `(L τ)(x₀) = vbcFiber L x₀ (τ x₀)` (VBC).
  -- Apply with `τ = concreteConn cov X σ'_i`, so `τ x₀ = cov (σ' i) x₀ (X x₀)`.
  -- Then frame-expand `τ x₀ = ∑_k θ^k(x₀)(τ x₀) • σ'_k(x₀)` (at x₀, from duality).
  -- Apply ℝ-linear vbcFiber L x₀:
  -- `(L τ)(x₀) = ∑_k θ^k(x₀)(τ x₀) • vbcFiber L x₀ (σ'_k x₀) = ∑_k θ^k(x₀)(τ x₀) • (L σ'_k) x₀`.
  -- Apply θ^i(x₀):
  -- `θ^i (L τ x₀) = ∑_k θ^k(τ x₀) * θ^i ((L σ'_k) x₀) = ∑_k θ^k(τ x₀) * L^i_k(x₀)`.
  ---------------------------------------------------------------
  have h_L_connsigma_theta : ∀ i,
      θ i ((L (concreteConn I M cov X (σ' i))) x₀) =
        ∑ k, θ k (cov (σ' i) x₀ (X x₀)) * localEntry L (σ' k) i x₀ := by
    intro i
    -- Step F.1: `(L τ)(x₀) = vbcFiber L x₀ (τ x₀)` where τ = concreteConn cov X σ'_i.
    have h_Lτ : (L (concreteConn I M cov X (σ' i))) x₀ =
        vbcFiber I M L x₀ ((concreteConn I M cov X (σ' i)) x₀) :=
      (vbcFiber_spec I M L (concreteConn I M cov X (σ' i)) x₀).symm
    rw [h_Lτ]
    -- Step F.2: `(concreteConn cov X σ'_i) x₀ = cov (σ' i) x₀ (X x₀)`.
    have h_τ_val : (concreteConn I M cov X (σ' i)) x₀ = cov (σ' i) x₀ (X x₀) :=
      concreteConn_apply I M cov X (σ' i) x₀
    rw [h_τ_val]
    -- Step F.3: Frame expansion of `cov (σ' i) x₀ (X x₀)` at x₀.
    -- Use the basis `e.basisAt b he` of `TangentSpace I x₀`, with `basisAt k = σ'_k(x₀)`
    -- and `basisAt.equivFun v k = θ^k(x₀)(v)`.
    set b_at : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
      e.basisAt b he with hb_at_def
    have h_b_at_k : ∀ k, b_at k = (σ' k) x₀ := by
      intro k
      change (b.map (e.linearEquivAt ℝ x₀ he).symm) k = (σ' k) x₀
      rw [Module.Basis.map_apply]
      exact (hσ'_at_base k).symm
    have h_b_at_repr : ∀ (v : TangentSpace I x₀) (k : Fin (Module.finrank ℝ E)),
        b_at.equivFun v k = θ k v := by
      intro v k
      change b_at.equivFun v k = b.equivFun ((e ⟨x₀, v⟩).2) k
      rw [h_coe_e v]
      change (b.map (e.linearEquivAt ℝ x₀ he).symm).equivFun v k = b.equivFun (le₀ v) k
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
      rw [Module.Basis.map_repr]
      rfl
    have h_covσ_expand : cov (σ' i) x₀ (X x₀) =
        ∑ k, θ k (cov (σ' i) x₀ (X x₀)) • (σ' k) x₀ := by
      -- Abstract `v := cov σ'_i x₀ (X x₀)` to avoid rewriting inside sums.
      set v := cov (σ' i) x₀ (X x₀) with hv_def
      have h_sum_repr : v = ∑ k, b_at.equivFun v k • b_at k :=
        (b_at.sum_equivFun v).symm
      calc v = ∑ k, b_at.equivFun v k • b_at k := h_sum_repr
        _ = ∑ k, θ k v • (σ' k) x₀ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [h_b_at_repr _ k, h_b_at_k k]
    -- Abstract `v := cov σ'_i x₀ (X x₀)` for the rest of the computation so we can freely
    -- rewrite using the expansion without accidentally rewriting scalar `v` inside `θ k v`.
    set v := cov (σ' i) x₀ (X x₀) with hv_def
    change θ i (vbcFiber I M L x₀ v) = ∑ k, θ k v * localEntry L (σ' k) i x₀
    -- Expand v as a sum in the frame at x₀.
    conv_lhs => rw [show v = ∑ k, θ k v • (σ' k) x₀ from h_covσ_expand]
    -- Step F.4: Apply vbcFiber L x₀ (ℝ-linear).
    rw [map_sum]
    simp only [map_smul]
    rw [map_sum (θ i)]
    simp only [map_smul]
    simp only [smul_eq_mul]
    -- Goal: ∑ k, θ k v * θ i (vbcFiber I M L x₀ ((σ' k) x₀)) = ∑ k, θ k v * localEntry L (σ' k) i x₀.
    refine Finset.sum_congr rfl ?_
    intro k _
    have h_vbc := vbcFiber_spec I M L (σ' k) x₀
    -- h_vbc : vbcFiber L x₀ (σ'_k x₀) = (L σ'_k) x₀.
    rw [h_vbc]
    -- Goal: θ k v * θ i ((L σ'_k) x₀) = θ k v * localEntry L (σ' k) i x₀.
    rw [h_θ_eq i ((L (σ' k)) x₀)]
  -- Apply h_L_connsigma_theta to RHS sum.
  rw [show ∑ i, θ i ((L (concreteConn I M cov X (σ' i))) x₀) =
      ∑ i, ∑ k, θ k (cov (σ' i) x₀ (X x₀)) * localEntry L (σ' k) i x₀ from by
        congr 1; ext i; rw [h_L_connsigma_theta i]]
  -- Swap the double sum: i → new_i, k → new_k; reindex so the two off-diagonal sums match.
  -- Our LHS has: ∑ i, ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀))
  -- Our RHS has: ∑ i, ∑ k, θ k (cov (σ' i) x₀ (X x₀)) * localEntry L (σ' k) i x₀
  -- Rename in RHS: (i, k) ↦ (k', i') (i.e., swap). Then RHS = ∑ i', ∑ k', θ i' (cov (σ' k') x₀ (X x₀)) * localEntry L (σ' i') k' x₀.
  -- Equivalent: ∑ i', ∑ k', localEntry L (σ' i') k' x₀ * θ i' (cov (σ' k') x₀ (X x₀)) (by mul_comm).
  -- This matches LHS.
  ---------------------------------------------------------------
  -- STEP G: Algebraic simplification.
  ---------------------------------------------------------------
  -- The goal is now an algebraic identity. Let's unpack the goal:
  -- ∑ i, extDerivFun (localEntry L (σ' i) i) x₀ (X x₀) =
  --   ∑ i, extDerivFun (localEntry L (σ' i) i) x₀ (X x₀) +
  --   ∑ i, ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀)) -
  --   ∑ i, ∑ k, θ k (cov (σ' i) x₀ (X x₀)) * localEntry L (σ' k) i x₀
  -- We need the difference of the two off-diagonal sums to be 0.
  -- After swap on second double sum (i ↔ k), it becomes:
  -- ∑ k, ∑ i, θ i (cov (σ' k) x₀ (X x₀)) * localEntry L (σ' i) k x₀
  -- = ∑ i, ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀)) (by mul_comm and swap).
  have h_swap :
      ∑ i, ∑ k, θ k (cov (σ' i) x₀ (X x₀)) * localEntry L (σ' k) i x₀ =
      ∑ i, ∑ k, localEntry L (σ' i) k x₀ * θ i (cov (σ' k) x₀ (X x₀)) := by
    -- Swap the double sum: i ↔ k, giving ∑_i ∑_k θ^i (cov σ'_k ...) * L^k_i
    rw [Finset.sum_comm]
    congr 1; ext i
    congr 1; ext k
    exact mul_comm _ _
  rw [h_swap]
  ring
end Main

end
