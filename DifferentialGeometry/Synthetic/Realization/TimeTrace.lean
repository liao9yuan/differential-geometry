import DifferentialGeometry.Synthetic.Realization.TimeDeriv
import DifferentialGeometry.Synthetic.Realization.TensorContract

/-!
# P29.1: Concrete `TimeTrComm`

This file realizes the Synthetic-level `TimeTrComm` predicate for the canonical
concrete realization of the Ricci-flow analysis layer:

* `R := C^∞⟮I, M; ℝ⟯` — the smooth-function algebra on the manifold `M`;
* `V := Cₛ^∞⟮I; E, TangentSpace I⟯` — the `R`-module of smooth tangent sections;
* `A := SmoothTimeAlgebra I M = C^∞⟮𝓘(ℝ,ℝ).prod I, ℝ × M; ℝ⟯` — jointly-smooth
  scalar fields on `ℝ × M`;
* `Time := ℝ`.

## Main theorem

`concrete_time_tr_comm` asserts that the `TimeTrComm` predicate holds on
`(concreteAbstractTrace I M, concreteTimeDerivativeData I M)`. Unfolded, this
says: given a time-dependent `R`-linear endomorphism `L : ℝ → V →ₗ[R] V`, its
time derivative `dL`, a time `t : ℝ`, and elements
`αLv : V → (V →ₗ[R] R) → A` and `trL : A` representing the time-lifted
matrix entries and trace, we have

    (∂_t trL)(t) = tr(dL)        as elements of `R`.

## Proof strategy

We prove the equality pointwise. Fix `x₀ : M` and build (via
`Classical.choose` on the usual `isLocalFrameOn_localFrame_baseSet` existence
statement) a biorthogonal smooth tangent frame `σ' : Fin d → V` and smooth
covector frame `θ' : Fin d → Tensor0SField 1` matching the trivialization-local
frames near `x₀`. Define `α_i := covectorToFunctional I M (θ' i) : V →ₗ[R] R`.

Using `concreteTensorContract_eq_localSum` combined with the endo-trace identity
`concreteTensorContract_endo` (applied to each `L u` and to `dL`), for every
`L' : V →ₗ[R] V`:
```
concreteTr I M L' x₀ = ∑ i, (α_i (L' (σ' i))) x₀.
```

Combined with the hypothesis `h_trL_eval` and `h_αLv_eval`, this gives for all
`u : ℝ`:
```
trL (u, x₀) = ∑ i, (αLv (σ' i) α_i) (u, x₀).
```

Both sides are smooth in `u` (because `trL, αLv _ _` are joint-smooth on
`ℝ × M`), so we may differentiate at `u = t` via `deriv_fun_sum`:
```
(∂_t trL)(t, x₀) = ∑ i, (∂_t (αLv (σ' i) α_i))(t, x₀).
```

Finally, `h_dL_char` converts each per-slot time-derivative into
`α_i (dL (σ' i)) x₀`, and the same frame-sum identity (this time applied to
`dL`) rewrites the sum back to `concreteTr I M dL x₀`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff
open Bundle
open Tensor0SBundle
open SyntheticTensor
open TensorContractRealization

section ConcreteTimeTrComm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Slice smoothness: for any `F : SmoothTimeAlgebra I M` and any fixed `x : M`,
the 1-variable slice `u ↦ F (u, x)` is `C^∞` on `ℝ`. Inlined copy of
`TimeDeriv`'s `concreteDt_slice_contDiff` (which is private in that file). -/
private theorem smoothTimeAlgebra_slice_contDiff
    (F : SmoothTimeAlgebra I M) (x : M) :
    ContDiff ℝ ∞ (fun u : ℝ => F (u, x)) := by
  rw [← contMDiff_iff_contDiff]
  exact F.contMDiff.comp
    ((contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (id : ℝ → ℝ)).prodMk
      (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun _ : ℝ => x)))

/-- Slice differentiability: every slice `u ↦ F(u, x)` is differentiable at every `t`. -/
private theorem smoothTimeAlgebra_slice_differentiableAt
    (F : SmoothTimeAlgebra I M) (x : M) (t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => F (u, x)) t :=
  ((smoothTimeAlgebra_slice_contDiff I M F x).differentiable (by decide)).differentiableAt

/-- The concrete `TimeTrComm` theorem: ∂_t and the endomorphism trace commute on
the canonical joint-smooth time algebra. -/
theorem concrete_time_tr_comm :
    TimeTrComm (concreteAbstractTrace I M) (concreteTimeDerivativeData I M) := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  classical
  intro L dL t αLv trL h_αLv_eval h_trL_eval h_dL_char
  -- Abbreviations.
  set td := concreteTimeDerivativeData I M with htd_def
  -- Pointwise goal at each x₀ ∈ M.
  ext x₀
  -- Unfold the goal into a scalar equation at x₀.
  change (td.eval (td.dt trL) t : C^∞⟮I, M; ℝ⟯) x₀ =
    ((concreteAbstractTrace I M).tr dL : C^∞⟮I, M; ℝ⟯) x₀
  -- Use `(concreteAbstractTrace I M).tr = concreteTr I M`.
  rw [concreteAbstractTrace_tr]
  -- The LHS is `(concreteDt I M trL) (t, x₀) = deriv (fun u => trL (u, x₀)) t`.
  change (concreteDt I M trL) (t, x₀) = (concreteTr I M dL : C^∞⟮I, M; ℝ⟯) x₀
  change deriv (fun u : ℝ => (trL : SmoothTimeAlgebra I M) (u, x₀)) t =
    (concreteTr I M dL : C^∞⟮I, M; ℝ⟯) x₀
  -- Build local frames `σ' : tangent` and `θ' : (0,1)-bundle dual`, via the
  -- standard existence lemma applied to the trivialization at x₀.
  let e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he_tan : x₀ ∈ e_tan.baseSet := mem_baseSet_trivializationAt E _ x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  let hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  obtain ⟨σ', hσ'⟩ :=
    hframe_tan.exists_contMDiffSection_eqOn_nhd e_tan.open_baseSet he_tan
  let e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  have he_1 : x₀ ∈ e_1.baseSet := mem_baseSet_trivializationAt _ _ x₀
  let hframe_1 :=
    e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) (dualCovectorBasis' (E := E))
  obtain ⟨θ', hθ'⟩ :=
    hframe_1.exists_contMDiffSection_eqOn_nhd e_1.open_baseSet he_1
  -- Package the dual sections as `C^∞(M)`-linear functionals on `V`.
  set α_at :
      Fin (Module.finrank ℝ E) →
        (Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
    fun i => covectorToFunctional I M (θ' i) with hα_def
  -- Abbreviation for the vector frame used throughout.
  -- Core frame-sum identity for any `L'`.
  have h_tr_eq_frame_sum : ∀ (L' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (concreteTr I M L' : C^∞⟮I, M; ℝ⟯) x₀ =
        ∑ i, (α_at i (L' (σ' i))) x₀ := by
    intro L'
    -- Step 1: `concreteTensorContract_endo` rewrites `concreteTr I M L'` as
    -- `(concreteTensorContract I M 0 0 (endo_to_tensor L')) ![] ![]`.
    have h_endo : concreteTr I M L' =
        (concreteTensorContract I M 0 0 (endo_to_tensor L')) ![] ![] :=
      (concreteTensorContract_endo I M L').symm
    rw [h_endo]
    -- Step 2: `concreteTensorContract_eq_localSum` rewrites the contraction at x₀
    -- as the local-frame sum using our chosen frames `σ'` and `θ'`.
    rw [concreteTensorContract_eq_localSum I M 0 0 (endo_to_tensor L') ![] ![] x₀
      σ' θ' hσ' hθ']
    -- Step 3: Unfold `concreteTensorContract_localSum_apply`.
    rw [concreteTensorContract_localSum_apply]
    -- Step 4: Each summand simplifies using `endo_to_tensor_eval`.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `Fin.cons σ ![]` = `![σ]`.
    have h_cons_v : (Fin.cons (σ' i) ![] :
        Fin 1 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) = ![σ' i] := by
      funext k; fin_cases k; rfl
    have h_cons_c : (Fin.cons (covectorToFunctional I M (θ' i)) ![] :
        Fin 1 →
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) =
        ![covectorToFunctional I M (θ' i)] := by
      funext k; fin_cases k; rfl
    rw [h_cons_v, h_cons_c, endo_to_tensor_eval]
  -- Per-index identity: `(α_i (dL (σ' i))) x₀ = deriv slice t`.
  have h_per_index : ∀ i,
      (α_at i (dL (σ' i))) x₀ =
        deriv (fun u : ℝ => (αLv (σ' i) (α_at i) : SmoothTimeAlgebra I M) (u, x₀)) t := by
    intro i
    have hdL := h_dL_char (σ' i) (α_at i)
    -- `hdL : α_at i (dL (σ' i)) = td.eval (td.dt (αLv (σ' i) (α_at i))) t`.
    rw [hdL]
    -- Unfold to `deriv` form.
    change (concreteDt I M (αLv (σ' i) (α_at i))) (t, x₀) = _
    rfl
  -- Main identity: the slice `u ↦ trL(u, x₀)` equals the finite sum of `αLv` slices.
  have h_slice_eq :
      (fun u : ℝ => (trL : SmoothTimeAlgebra I M) (u, x₀)) =
      (fun u : ℝ =>
        ∑ i, (αLv (σ' i) (α_at i) : SmoothTimeAlgebra I M) (u, x₀)) := by
    funext u
    -- `trL (u, x₀) = (td.eval trL u) x₀ = (concreteTr I M (L u)) x₀`.
    have h_trL_u : (trL : SmoothTimeAlgebra I M) (u, x₀) =
        (concreteTr I M (L u) : C^∞⟮I, M; ℝ⟯) x₀ := by
      have hev := h_trL_eval u
      -- `hev : td.eval trL u = (concreteAbstractTrace I M).tr (L u)`.
      rw [concreteAbstractTrace_tr] at hev
      -- Evaluate both sides at x₀.
      have := DFunLike.congr_fun hev x₀
      -- LHS at x₀ is `(td.eval trL u) x₀ = (concreteEval I M trL u) x₀ = trL (u, x₀)` (rfl).
      change (trL : SmoothTimeAlgebra I M) (u, x₀) = (concreteTr I M (L u) : C^∞⟮I, M; ℝ⟯) x₀
      exact this
    rw [h_trL_u, h_tr_eq_frame_sum (L u)]
    -- Each summand: `(α_i (L u (σ' i))) x₀ = αLv (σ' i) α_i (u, x₀)`.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hev := h_αLv_eval (σ' i) (α_at i) u
    -- `hev : td.eval (αLv (σ' i) (α_at i)) u = α_at i (L u (σ' i))` in `C^∞⟮I,M;ℝ⟯`.
    -- Evaluate both sides at x₀.
    have heq := DFunLike.congr_fun hev x₀
    -- The RHS at x₀ is `(αLv (σ' i) (α_at i)) (u, x₀)` by `concreteEval` unfolding.
    change (α_at i (L u (σ' i)) : C^∞⟮I, M; ℝ⟯) x₀ =
      (αLv (σ' i) (α_at i) : SmoothTimeAlgebra I M) (u, x₀)
    exact heq.symm
  -- Differentiate both sides of `h_slice_eq` at `t`.
  rw [h_slice_eq]
  -- `deriv (fun u => ∑ i, f_i u) t = ∑ i, deriv (f_i) t`.
  rw [deriv_fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => smoothTimeAlgebra_slice_differentiableAt I M
      (αLv (σ' i) (α_at i)) x₀ t)]
  -- Rewrite the RHS using `h_tr_eq_frame_sum dL` and `h_per_index`.
  rw [h_tr_eq_frame_sum dL]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (h_per_index i).symm

end ConcreteTimeTrComm

end
