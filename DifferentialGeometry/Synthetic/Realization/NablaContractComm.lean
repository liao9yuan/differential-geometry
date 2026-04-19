import DifferentialGeometry.Synthetic.Realization.NablaComm
import DifferentialGeometry.Synthetic.Realization.TensorRSNabla
import DifferentialGeometry.Tensor.RSTensor.Contract

/-!
# SmoothRicciFlow: field-level setup for `∇` commuting with tensor contraction (P26)

This file provides the **definitional infrastructure** for the concrete realization
of the Synthetic axiom `NablaTensorContractComm`.  It defines the fiber-level and
field-level "first upper, first lower" tensor contraction used in the
`AbstractTrace.tensor_contract` convention.

## Main declarations

* `stdBasis` : the standard basis of `E = TangentSpace I x`, via `Module.finBasis ℝ E`.

* `stdDualCovector x i` : the `i`-th dual covector, realized as a `(0,1)`-tensor
  fiber element at `x`.

* `castRSComm r s x` : the identity CLM bridging `TensorRSSpace (r+1) (s+1)` and
  `TensorRSSpace (1+r) (s+1)` (since `r + 1 = 1 + r` propositionally, not
  definitionally).

* `concreteTensorContract_fiber r s x` : the fiber-level contraction CLM, a sum
  over the basis/dual-basis pair of
  `contract_contravariant_first (e^i) ∘ contract_covariant (e_i)`. The result is
  a partial trace on the first `V ⊗ V*` factor, mathematically basis-independent.

* `concreteTensorContractField_fun r s T` : the pointwise contracted tensor field
  as a `Pi` section. Smoothness is established separately.

## Convention

We match the Synthetic `AbstractTrace.tensor_contract` convention: the contraction
pairs the FIRST upper (contravariant) index with the FIRST lower (covariant) index.
For `T ∈ TensorRSSpace (r+1) (s+1) I x = Tensor0SSpace (r+1) →L Tensor0SSpace (s+1)`:
```
(cT)(β')(v₁, …, v_s) = Σ_i (T(e^i ⊗_first β'))(Fin.cons e_i (v₁, …, v_s))
```
using the basis `{e_i}` of `E` and dual basis `{e^i}`. The `⊗_first` denotes
tensor product inserting `e^i` into slot 0.

## Relationship to P25

P25 (`NablaComm.lean`) proved the special case `(r+1, s+1) = (1, 1)`: for any
`C^∞(M)`-linear endomorphism `L : Γ(TM) →ₗ Γ(TM)`, the endomorphism trace
commutes with the vector-field derivation:
```
X(tr L) = tr([∇_X, L]).
```
The general P26 theorem generalizes this from scalar trace to partial trace on the
first `V ⊗ V*` factor of a `(r+1, s+1)`-tensor.

## Outstanding work (deferred)

The **smoothness** of `concreteTensorContract_fiber` as a bundle CLM-section and
the **main commutation theorem** `concrete_nabla_contract_comm` are the subjects
of a subsequent sub-task.  In this file we establish only the fiber-level and
pointwise-field-level definitions.

The smoothness proof parallels `contract_Tensor0SField`'s proof in `Contract.lean`
(with suitable extensions for the `TensorRSSpace` bundle).

The commutation proof is the (r+1, s+1)-generalization of `concrete_nabla_tr_comm`
(P25). A local-frame argument as in P25, combined with the product-rule form of
`tensorRSCovariantDerivative_apply`, gives the desired cancellation between the
"diagonal" and "Christoffel" contributions.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace TensorContractComm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The basis and dual basis at each fiber. -/

/-- The standard basis of `E`, also serving as a basis of `TangentSpace I x = E`. -/
noncomputable def stdBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Module.finBasis ℝ E

/-- The `i`-th dual covector in `E`, realized as a `(0,1)`-tensor fiber element
at `x`.

We use `continuousMultilinearCurryFin1` to interpret the continuous linear
functional `(stdBasis).coord i : E →ₗ[ℝ] ℝ` as a multilinear map
`(Fin 1 → E) → ℝ`, then transport to `Tensor0SSpace 1 I x` via
`Tensor0SSpace.ofModel`. -/
noncomputable def stdDualCovector (x : M) (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((continuousMultilinearCurryFin1 ℝ E ℝ).symm
      ((stdBasis (E := E)).coord i).toContinuousLinearMap)

/-! ### Index-commutation cast `r + 1 = 1 + r` -/

/-- The identity CLM `TensorRSSpace (r+1) (s+1) →L[ℝ] TensorRSSpace (1+r) (s+1)`.
Because `r + 1 = 1 + r` as nats (propositionally, via `Nat.add_comm`), the
underlying carrier types agree after this identity-transport. -/
noncomputable def castRSComm (r s : ℕ) (x : M) :
    TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace (1 + r) (s + 1) I x := by
  rw [show r + 1 = 1 + r from by omega]
  exact ContinuousLinearMap.id ℝ _

/-! ### The pointwise contraction CLM. -/

/-- The pointwise contraction CLM at `x`. Defined as the basis sum
```
Σ_i contract_contravariant_first r s x (e^i) ∘ contract_covariant (1+r) s x (e_i)
```
pre-composed with the `r+1 = 1+r` type-cast.

The result is an element of `TensorRSSpace r s I x`, representing the partial
trace of the input on the first `V ⊗ V*` factor (the "first upper, first lower"
contraction in the Synthetic `AbstractTrace.tensor_contract` convention).

The Lean definition uses the fixed basis `Module.finBasis ℝ E`, but the underlying
mathematical operation is basis-independent (partial trace). -/
noncomputable def concreteTensorContract_fiber (r s : ℕ) (x : M) :
    TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace r s I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x
          (stdDualCovector I M x i)).comp
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x ((stdBasis (E := E)) i)))
    ∘L castRSComm I M r s x

/-! ### Pointwise contraction of a tensor field. -/

/-- The pointwise contraction applied to a `Pi` section.
Smoothness of this operation as a `TensorRSField` is the subject of subsequent
work (see file-level docstring). -/
noncomputable def concreteTensorContractField_fun (r s : ℕ)
    (T : Π x : M, TensorRSSpace (r + 1) (s + 1) I x) :
    Π x : M, TensorRSSpace r s I x :=
  fun x => concreteTensorContract_fiber I M r s x (T x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem concreteTensorContractField_fun_apply (r s : ℕ)
    (T : Π x : M, TensorRSSpace (r + 1) (s + 1) I x) (x : M) :
    concreteTensorContractField_fun I M r s T x =
      concreteTensorContract_fiber I M r s x (T x) := rfl

/-! ### Phase 1 — Smoothness of `concreteTensorContract_fiber` as a bundle section

Strategy: rather than prove the full smoothness of `stdBasis i` as a tangent vector
field (which would require parallelizability), we prove the smoothness locally using
a smooth local frame (via `exists_contMDiffSection_eqOn_nhd`). The fiber-level
basis-invariance of partial trace lets us switch between the `stdBasis` expression
(used in the definition of `concreteTensorContract_fiber`) and the local-frame
expression (smooth on a neighborhood). -/

/-! #### Apply lemmas for `contract_covariant` and `contract_contravariant_first`.

These show how these contractions evaluate on a `Tensor0SSpace r` input; the key
observation is that at the composed level, the cancelling `ofModel ∘ toModel` pairs
collapse to plain operations on the bundle fibers. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Applying `contract_covariant r s x v F` to a `(0,r)`-tensor `β` is `interior_product`
of `F β` with `v`. -/
private theorem contract_covariant_apply_eval (r s : ℕ) (x : M) (v : E)
    (F : TensorRSSpace r (s + 1) I x) (β : Tensor0SSpace r I x) :
    (Tensor0SBundle.contract_covariant (𝕜 := ℝ) r s x (v : TangentSpace I x) F) β =
      Tensor0SBundle.interior_product (𝕜 := ℝ) s x (v : TangentSpace I x) (F β) := by
  -- Both sides unfold to:
  --   (tensor0SSpace_cle s x).symm (model_interior_product s v ((tensor0SSpace_cle (s+1) x) (F β)))
  -- via arrowCongr's apply/symm formulas. The simp lemmas handle the unfolding.
  simp only [Tensor0SBundle.contract_covariant, Tensor0SBundle.interior_product,
    tensorRSSpace_continuousLinearEquiv, ContinuousLinearEquiv.arrowCongr_symm,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.compL_apply]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Applying `contract_contravariant_first r s x α F` to a `(0,r)`-tensor `β` gives
`F` evaluated at `(α ⊗₀ β)` (with α in slot 0). -/
private theorem contract_contravariant_first_apply_eval (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) (F : TensorRSSpace (1 + r) s I x) (β : Tensor0SSpace r I x) :
    (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x α F) β =
      F ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
        (Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α)
          ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β))) := by
  -- Unfold contract_contravariant_first via arrowCongr.
  simp only [Tensor0SBundle.contract_contravariant_first,
    tensorRSSpace_continuousLinearEquiv, ContinuousLinearEquiv.arrowCongr_symm,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]

/-! #### Dual covector bridge.

For a smooth tangent vector field `σ` on `e.baseSet`, the scalar
`x ↦ b.coord j ((e ⟨x, σ(x)⟩).2)` is smooth at every `x` in that base set. This
packages "the j-th coordinate function" in the trivialization. -/

/-- Local coordinate map: the `j`-th coordinate function in a trivialization, as a linear map on
`E = TangentSpace I x`, at every `x`. Combined with the trivialization at `x₀`, this gives a
smooth section of `Hom(TangentSpace, ℝ)` (the cotangent bundle) locally around `x₀`. -/
private noncomputable def localCoordFunctional (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  (b.coord j).toContinuousLinearMap.comp
    ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Localcoordinate functional applied to a tangent vector equals the coordinate of its
trivialized value. -/
private theorem localCoordFunctional_apply (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) (x : M) (v : TangentSpace I x) :
    localCoordFunctional I M x₀ b j x v =
      b.coord j ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x v) :=
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- The scalar function `x ↦ (localCoordFunctional x₀ b j x) (σ x)` is smooth at `x₀`,
when `σ` is a smooth section of `TM`. -/
private theorem localCoordFunctional_apply_contMDiffAt (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E))
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => localCoordFunctional I M x₀ b j x (σ x)) x₀ := by
  have h_sect : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun x => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, σ x⟩).2) x₀ :=
    (contMDiffAt_section x₀).mp σ.contMDiff.contMDiffAt
  have hcl : ContDiff ℝ ∞ (fun w : E => b.coord j w) :=
    (b.coord j).toContinuousLinearMap.contDiff
  have h_comp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => b.coord j ((trivializationAt E (TangentSpace I : M → Type _) x₀
        ⟨x, σ x⟩).2)) x₀ :=
    hcl.contDiffAt.contMDiffAt.comp _ h_sect
  refine h_comp.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  filter_upwards [hbase] with x hx
  have h_eq : localCoordFunctional I M x₀ b j x (σ x) =
    b.coord j ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x (σ x)) :=
    localCoordFunctional_apply I M x₀ b j x (σ x)
  rw [h_eq]
  congr 1
  have h_lin := (trivializationAt E (TangentSpace I : M → Type _) x₀).coe_linearMapAt_of_mem
    (R := ℝ) hx
  exact congrArg (fun f => f (σ x)) h_lin

/-! #### The Tensor0S-valued slot-0 insertion, as a smooth section.

Given smooth β : Γ(Tensor0S r), a covector α : Tensor0SSpace 1 I x (possibly a family over x),
the slot-0 insertion `(tensor0SSpace_cle (1+r) x).symm (mtwf r (toModel α) ((tensor0SSpace_cle r x) β))`
is an element of Tensor0SSpace (1+r) I x. We prove this is a smooth section when α is parameterized
by a smooth vector field (via a coord functional construction). -/

/-- The slot-0 insertion: given α : Tensor0SSpace 1 I x and β : Tensor0SSpace r I x, form
the element of Tensor0SSpace (1+r) I x given by `model_tensorWithCovector_first r (toModel α) β_model`
then lifted back. -/
private noncomputable def slot0Insert {r : ℕ} {x : M} (α : Tensor0SSpace 1 I x)
    (β : Tensor0SSpace r I x) : Tensor0SSpace (1 + r) I x :=
  (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
    (Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α)
      ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- The slot-0 insertion applied to vectors. -/
private theorem slot0Insert_apply {r : ℕ} {x : M} (α : Tensor0SSpace 1 I x)
    (β : Tensor0SSpace r I x) (v : Fin (1 + r) → TangentSpace I x) :
    slot0Insert I M α β v =
      Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) v := rfl

/-- Pointwise slot-0 insertion of a smooth `(0,1)`-tensor field into a smooth `(0,r)`-tensor
field, yielding a smooth `(0,1+r)`-tensor field. -/
noncomputable def slot0Insert_smoothField (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (β : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  refine ⟨fun x => slot0Insert I M (α x) (β x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hβ := β.contMDiff x₀
  rw [contMDiffAt_section] at hβ
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, Tensor0SModel (1 + r) ℝ E) ∞
        (fun x => model_tensorWithCovector_first_bilinear (𝕜 := ℝ) (E := E) r
          ((trivializationAt (Tensor0SModel 1 ℝ E)
            (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, α x⟩).2)
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun x => Tensor0SSpace r I x) x₀ ⟨x, β x⟩).2)) x₀ :=
    ((contMDiffAt_const
      (c := model_tensorWithCovector_first_bilinear (𝕜 := ℝ) (E := E) r)).clm_apply hα).clm_apply hβ
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  filter_upwards [hbase] with x hx
  ext v
  set symmL := (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x with hsymmL
  change Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel (α x))
      ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) (β x))
      (fun i => symmL (v i)) =
    Bundle.continuousMultilinearMap.modelProduct 1 r
      ((α x).compContinuousLinearMap (fun _ => symmL))
      ((β x).compContinuousLinearMap (fun _ => symmL)) v
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  change Bundle.continuousMultilinearMap.modelProduct 1 r (α x) (β x) (fun i => symmL (v i)) =
    (α x) (fun i => symmL ((v ∘ Fin.castAdd r) i)) *
      (β x) (fun i => symmL ((v ∘ Fin.natAdd 1) i))
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise value of `slot0Insert_smoothField`. -/
@[simp] theorem slot0Insert_smoothField_apply (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (β : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) (x : M) :
    slot0Insert_smoothField I M r α β x = slot0Insert I M (α x) (β x) := rfl

/-! #### Smooth-field versions of the index cast and contractions.

These will be assembled inline in Substep 3's main smoothness argument. -/

/-- Helper: produce a `TensorRSField` at index `k = 1 + r` from one at `r + 1`, given the
Nat-level equation `h : r + 1 = k`. This is the pointwise identity transport on the fibers.

Generalizing over `h` allows the apply lemma to close by `subst`. -/
private noncomputable def castRSFieldGen (r s : ℕ) (k : ℕ) (h : r + 1 = k)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) k (s + 1) := by
  subst h; exact T

/-- The identity cast `TensorRSField (r+1) (s+1) → TensorRSField (1+r) (s+1)`. This wraps
`castRSFieldGen` at `k = 1 + r` with proof `Nat.add_comm r 1 : r + 1 = 1 + r`. -/
noncomputable def castRSComm_smoothField (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r) (s + 1) :=
  castRSFieldGen I M r s (1 + r) (Nat.add_comm r 1) T

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Helper HEq lemma for `castRSFieldGen`. -/
private theorem castRSFieldGen_toFun_heq (r s : ℕ) (k : ℕ) (h : r + 1 = k)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    HEq (castRSFieldGen I M r s k h T).toFun T.toFun := by
  subst h
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Helper HEq lemma for `castRSComm`'s pointwise action. -/
private theorem castRSComm_apply_heq (r s : ℕ) (x : M)
    (t : TensorRSSpace (r + 1) (s + 1) I x) :
    HEq (castRSComm I M r s x t) t := by
  -- `castRSComm` is defined using `by rw [...]; exact CLM.id` which produces
  -- `Eq.mpr h (CLM.id (target))`.  Applying this to `t` gives an element of the target type
  -- which is HEq to `t`.
  -- We use generalized induction over the Nat-arith equality.
  -- First restate castRSComm in a tractable form.
  -- Direct approach: change the goal by unfolding `castRSComm` so the Eq.mpr becomes visible.
  change HEq ((by rw [show r + 1 = 1 + r from by omega]; exact ContinuousLinearMap.id ℝ _ :
    TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace (1 + r) (s + 1) I x) t) t
  -- After `change`, unfold `by rw`'s Eq.mpr via a tactic.
  -- Use a generic helper parameterized by the eq-proof.
  have key : ∀ (k : ℕ) (h : r + 1 = k)
      (u : TensorRSSpace (r + 1) (s + 1) I x),
      HEq ((by subst h; exact ContinuousLinearMap.id ℝ _ :
        TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace k (s + 1) I x) u) u := by
    intro k h u
    subst h
    rfl
  -- We can't directly use `key` because `by rw` produces `Eq.mpr` whereas `by subst` produces
  -- `h ▸` — these are different tactics producing different terms.
  -- Instead, prove directly: `Eq.mpr h X = X` as HEq.
  -- Eq.mpr h : β → α where h : α = β, so `Eq.mpr h : β = α` direction.
  -- Here h : (α →L β) = (α' →L β'), and Eq.mpr h (CLM.id_β) : α →L β'.
  -- Hmm, we need to unfold more carefully.
  -- Actually `by rw [p]; exact e` with `p : r + 1 = 1 + r` rewrites the goal:
  --   Goal: TensorRSSpace (r+1) (s+1) I x →L[ℝ] TensorRSSpace (1+r) (s+1) I x
  -- After `rw [p]` (which rewrites `r + 1` to `1 + r` in the goal), goal becomes:
  --   Goal: TensorRSSpace (1+r) (s+1) I x →L[ℝ] TensorRSSpace (1+r) (s+1) I x
  -- The `rw` inserts an `Eq.mpr` coercion on the produced term.
  -- The produced term is `Eq.mpr h_type (ContinuousLinearMap.id ℝ _)`.
  --
  -- We show that for any proof `hp : r + 1 = 1 + r`, the transport of
  -- `ContinuousLinearMap.id ℝ (TensorRSSpace (1 + r) (s + 1) I x)` along the induced type-eq
  -- applied to `t` is HEq to t.
  -- Use `hp`'s symm to subst.
  have hp : r + 1 = 1 + r := by omega
  -- Pattern-match: since subst on hp fails (neither side is a variable), use `.symm`:
  have hp_symm : 1 + r = r + 1 := hp.symm
  -- Generalize 1 + r to k via this symmetric form.
  -- Now `hp_symm : 1 + r = r + 1`, still not subst-friendly (1+r is not a free variable).
  -- Use aux generalization:
  have aux : ∀ (k : ℕ) (hpr : r + 1 = k)
      (ki : TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace k (s + 1) I x),
      HEq ki (ContinuousLinearMap.id ℝ (TensorRSSpace (r + 1) (s + 1) I x)) →
      HEq (ki t) t := by
    intro k hpr ki h
    subst hpr
    cases h
    rfl
  -- Now we'd need the HEq of `Eq.mpr h_type CLM.id` to `CLM.id` as a CLM — which is true
  -- because Eq.mpr is a transport and the CLM is identity on both sides.
  -- Apply `aux` with the appropriate ingredients.
  refine aux (1 + r) hp _ ?_
  -- Need: HEq (Eq.mpr _ CLM.id) (CLM.id).  Both are `.id`, transported along different
  -- Nat-arith proofs. Their types differ only in the 1+r vs r+1.
  -- Prove via: cast (h : A = B) (CLM.id B) = CLM.id A when A = B.
  -- Since `hp : r + 1 = 1 + r`, we can cast.
  have : ∀ (k : ℕ) (h : r + 1 = k),
      HEq ((by rw [h]; exact ContinuousLinearMap.id ℝ (TensorRSSpace k (s + 1) I x) :
        TensorRSSpace (r + 1) (s + 1) I x →L[ℝ] TensorRSSpace k (s + 1) I x))
        (ContinuousLinearMap.id ℝ (TensorRSSpace (r + 1) (s + 1) I x)) := by
    intro k h
    subst h
    rfl
  exact this (1 + r) hp

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise apply lemma for `castRSComm_smoothField`. Both sides are identity transports
of `T x` along `r + 1 = 1 + r`, so they agree by HEq/proof-irrelevance. -/
@[simp] theorem castRSComm_smoothField_apply (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x : M) :
    (castRSComm_smoothField I M r s T) x = castRSComm I M r s x (T x) := by
  -- Both LHS and RHS are HEq to `T x`. We combine via `eq_of_heq`.
  apply eq_of_heq
  -- Step 1: LHS HEq T x.
  have hLHS : HEq ((castRSComm_smoothField I M r s T) x) (T x) := by
    unfold castRSComm_smoothField
    -- Goal: HEq (castRSFieldGen I M r s (1+r) (Nat.add_comm r 1) T).toFun x) (T.toFun x).
    -- Since toFun is HEq to T.toFun, apply HEq-applied-to-x.
    have htf := castRSFieldGen_toFun_heq I M r s (1 + r) (Nat.add_comm r 1) T
    -- Hmm, `HEq f g → HEq (f x) (g x)` is not directly a standard lemma. Use congr.
    -- Actually, when f and g have different types due to dependent type, we need HEq.congr.
    -- Since both f and g are `M → _` functions with the same M and differing codomain, use
    -- `congr_fun_heq`.
    -- Actually `castRSFieldGen_toFun_heq` says HEq (castRSFieldGen T).toFun T.toFun.
    -- The types are `M → TensorRSSpace (1+r) (s+1) I x` vs `M → TensorRSSpace (r+1) (s+1) I x`.
    -- These are HEq-compatible function types.
    -- To extract HEq at x, use `Function.hfunext` or induction.
    -- Generalize the index `1 + r` to unify types.
    have : ∀ (k : ℕ) (h : r + 1 = k),
        HEq (castRSFieldGen I M r s k h T).toFun T.toFun := by
      intro k h
      subst h
      rfl
    have h' := this (1 + r) (Nat.add_comm r 1)
    -- Now use `HEq.congr_fun` or manual induction on the equation.
    -- Since the type of `.toFun` differs (codomain depends on `k`), we subst on `k`.
    -- Do it by generalizing once more.
    have key : ∀ (k : ℕ) (h : r + 1 = k)
        (tf : ∀ y : M, TensorRSSpace k (s + 1) I y),
        HEq tf T.toFun → HEq (tf x) (T.toFun x) := by
      intro k h tf heq
      subst h
      -- Now tf : ∀ y, TensorRSSpace (r+1) (s+1) I y, and heq : HEq tf T.toFun.
      -- Both tf and T.toFun have the SAME type now; heq becomes `tf = T.toFun`.
      cases heq
      rfl
    exact key (1 + r) (Nat.add_comm r 1) _ h'
  -- Step 2: RHS HEq T x.
  have hRHS : HEq (castRSComm I M r s x (T x)) (T x) := castRSComm_apply_heq I M r s x (T x)
  -- Combine.
  exact hLHS.trans hRHS.symm




/-- Pointwise contraction of an `(r, s+1)`-tensor field with a smooth vector field, giving
an `(r, s)`-tensor field. Smoothness follows the pattern of `contract_Tensor0SField`:
the trivialized value uses the bilinear model map `model_contract_covariant_bilinear`. -/
noncomputable def contract_covariant_smoothField (r s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r (s + 1)) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s := by
  refine ⟨fun x => Tensor0SBundle.contract_covariant (𝕜 := ℝ) r s x (X x) (T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
        (fun x => model_contract_covariant_bilinear (𝕜 := ℝ) (E := E) r s
          ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (TensorRSModel r (s + 1) ℝ E)
            (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    ((contMDiffAt_const
      (c := model_contract_covariant_bilinear (𝕜 := ℝ) (E := E) r s)).clm_apply hX).clm_apply hT
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hbase_r := (trivializationAt (Tensor0SModel r ℝ E)
    (fun x => Tensor0SSpace r I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_s := (trivializationAt (Tensor0SModel s ℝ E)
    (fun x => Tensor0SSpace s I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_s1 := (trivializationAt (Tensor0SModel (s + 1) ℝ E)
    (fun x => Tensor0SSpace (s + 1) I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase_tan, hbase_r, hbase_s, hbase_s1] with x hx_tan hx_r hx_s hx_s1
  -- Trivializations as abbreviations.
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀ with he_tan
  set e_r := trivializationAt (Tensor0SModel r ℝ E)
    (fun x => Tensor0SSpace r I x) x₀ with he_r
  set e_s := trivializationAt (Tensor0SModel s ℝ E)
    (fun x => Tensor0SSpace s I x) x₀ with he_s
  set e_s1 := trivializationAt (Tensor0SModel (s + 1) ℝ E)
    (fun x => Tensor0SSpace (s + 1) I x) x₀ with he_s1
  -- The LHS hom-bundle trivialization equals `inCoordinates` of the carrier value.
  rw [hom_trivializationAt_apply]
  -- Both sides are `TensorRSModel r s ℝ E` elements. Check equality via ext on the source and then on the multilinear argument.
  apply ContinuousLinearMap.ext
  intro β
  apply ContinuousMultilinearMap.ext
  intro v
  -- Set up shortcuts.
  set Xtr : E := (e_tan ⟨x, X x⟩).2 with hXtr
  have hXtr_eq : e_tan.continuousLinearMapAt ℝ x (X x) = Xtr := by
    change e_tan.linearMapAt ℝ x (X x) = _
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
  have hXround : e_tan.symmL ℝ x Xtr = X x := by
    have h := e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan (X x)
    rw [hXtr_eq] at h
    exact h
  -- Explicit `e_s.cLMA x G v = G (e_tan.symmL ∘ v)` formula for s-multilinear bundle.
  have h_sMLap : ∀ (G : Tensor0SSpace s I x) (v' : Fin s → TangentSpace I x),
      (e_s.continuousLinearMapAt ℝ x G) v' = G (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro G v'
    -- `G = e_s.symmL x (e_s.cLMA x G)` by round-trip.
    have hGfib : G = e_s.symmL ℝ x (e_s.continuousLinearMapAt ℝ x G) :=
      (e_s.symmL_continuousLinearMapAt (R := ℝ) hx_s G).symm
    -- `e_s.symmL x M = M.compCLM (fun _ => e_tan.cLMA x)`.
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan (e_s.continuousLinearMapAt ℝ x G)
    -- So `G = (e_s.cLMA x G).compCLM (fun _ => e_tan.cLMA x)`.
    rw [hsym] at hGfib
    -- Apply the equation on the RHS.
    conv_rhs => rw [hGfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  -- Same formula for (s+1)-multilinear bundle.
  have h_s1MLap : ∀ (G : Tensor0SSpace (s + 1) I x) (v' : Fin (s + 1) → TangentSpace I x),
      (e_s1.continuousLinearMapAt ℝ x G) v' = G (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro G v'
    have hGfib : G = e_s1.symmL ℝ x (e_s1.continuousLinearMapAt ℝ x G) :=
      (e_s1.symmL_continuousLinearMapAt (R := ℝ) hx_s1 G).symm
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan (e_s1.continuousLinearMapAt ℝ x G)
    rw [hsym] at hGfib
    conv_rhs => rw [hGfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  -- Main computation: both sides equal F (Fin.cons (X x) (fun i => e_tan.symmL x (v i))),
  -- where F := (T x) (e_r.symmL x β) : Tensor0SSpace (s+1) I x.
  set F : Tensor0SSpace (s + 1) I x := (T x) (e_r.symmL ℝ x β) with hFdef
  -- LHS
  change (e_s.continuousLinearMapAt ℝ x
      ((Tensor0SBundle.contract_covariant (𝕜 := ℝ) r s x (X x) (T x))
        (e_r.symmL ℝ x β))) v =
    (model_contract_covariant_bilinear (𝕜 := ℝ) (E := E) r s Xtr
      ((e_s1.continuousLinearMapAt ℝ x).comp
        ((T x).comp (e_r.symmL ℝ x)))) β v
  -- Unfold contract_covariant.
  rw [show (Tensor0SBundle.contract_covariant (𝕜 := ℝ) r s x (X x) (T x))
            (e_r.symmL ℝ x β) =
          Tensor0SBundle.interior_product (𝕜 := ℝ) s x (X x) ((T x) (e_r.symmL ℝ x β)) from by
    unfold Tensor0SBundle.contract_covariant Tensor0SBundle.interior_product
    simp only [tensorRSSpace_continuousLinearEquiv, ContinuousLinearEquiv.arrowCongr_symm,
      ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearMap.compL_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl]
  -- Unfold interior_product.
  rw [show Tensor0SBundle.interior_product (𝕜 := ℝ) s x (X x) F =
          (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) s x).symm
            (Tensor0SBundle.model_interior_product s (X x : E)
              ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (s + 1) x) F)) from rfl]
  change (e_s.continuousLinearMapAt ℝ x
      (Tensor0SBundle.model_interior_product s (X x) F)) v =
    (model_contract_covariant_bilinear (𝕜 := ℝ) (E := E) r s Xtr
      ((e_s1.continuousLinearMapAt ℝ x).comp
        ((T x).comp (e_r.symmL ℝ x)))) β v
  -- `model_interior_product s (X x) F = F.curryLeft (X x)`.
  rw [model_contract_covariant_bilinear_apply]
  -- RHS: `model_interior_product s Xtr (e_s1.cLMA x ((T x) (e_r.symmL x β)))` at v.
  change (e_s.continuousLinearMapAt ℝ x
      (Tensor0SBundle.model_interior_product s (X x) F)) v =
    Tensor0SBundle.model_interior_product s Xtr
      (e_s1.continuousLinearMapAt ℝ x F) v
  -- Work directly with `model_interior_product s v G = G.curryLeft v`, then evaluate at v.
  -- LHS:
  have hLHS : (e_s.continuousLinearMapAt ℝ x
      (Tensor0SBundle.model_interior_product s (X x) F)) v =
      F (Fin.cons (X x) (fun i => e_tan.symmL ℝ x (v i))) := by
    rw [h_sMLap (Tensor0SBundle.model_interior_product s (X x) F) v]
    -- `model_interior_product s (X x) F (w) = F.curryLeft (X x) w = F (Fin.cons (X x) w)`.
    change F.curryLeft (X x) (fun i => e_tan.symmL ℝ x (v i)) = _
    rw [ContinuousMultilinearMap.curryLeft_apply]
  -- RHS:
  have hRHS : Tensor0SBundle.model_interior_product s Xtr
      (e_s1.continuousLinearMapAt ℝ x F) v =
      F (Fin.cons (X x) (fun i => e_tan.symmL ℝ x (v i))) := by
    change (e_s1.continuousLinearMapAt ℝ x F).curryLeft Xtr v = _
    rw [ContinuousMultilinearMap.curryLeft_apply]
    rw [h_s1MLap F (Fin.cons Xtr v)]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
      exact hXround
    · intro j
      simp only [Fin.cons_succ]
  rw [hLHS, hRHS]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise value of `contract_covariant_smoothField`. -/
theorem contract_covariant_smoothField_toFun (r s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r (s + 1)) :
    (contract_covariant_smoothField I M r s X T).toFun =
      fun x => Tensor0SBundle.contract_covariant (𝕜 := ℝ) r s x (X x) (T x) := rfl

/-- Pointwise contraction of a `(1+r, s)`-tensor field with a smooth `(0,1)`-tensor field
(covector field), giving an `(r, s)`-tensor field. Smoothness mirrors
`contract_covariant_smoothField`, using `model_contract_contravariant_first_bilinear`. -/
noncomputable def contract_contravariant_first_smoothField (r s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r) s) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s := by
  refine ⟨fun x => Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (α x) (T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
        (fun x => model_contract_contravariant_first_bilinear (𝕜 := ℝ) (E := E) r s
          ((trivializationAt (Tensor0SModel 1 ℝ E)
            (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, α x⟩).2)
          ((trivializationAt (TensorRSModel (1 + r) s ℝ E)
            (fun x => TensorRSSpace (1 + r) s I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    ((contMDiffAt_const
      (c := model_contract_contravariant_first_bilinear (𝕜 := ℝ) (E := E) r s)).clm_apply
        hα).clm_apply hT
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hbase_1 := (trivializationAt (Tensor0SModel 1 ℝ E)
    (fun x => Tensor0SSpace 1 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_r := (trivializationAt (Tensor0SModel r ℝ E)
    (fun x => Tensor0SSpace r I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_s := (trivializationAt (Tensor0SModel s ℝ E)
    (fun x => Tensor0SSpace s I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_1r := (trivializationAt (Tensor0SModel (1 + r) ℝ E)
    (fun x => Tensor0SSpace (1 + r) I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase_tan, hbase_1, hbase_r, hbase_s, hbase_1r]
    with x hx_tan hx_1 hx_r hx_s hx_1r
  rw [hom_trivializationAt_apply]
  unfold ContinuousLinearMap.inCoordinates
  apply ContinuousLinearMap.ext
  intro β
  apply ContinuousMultilinearMap.ext
  intro v
  let e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  let e_r := trivializationAt (Tensor0SModel r ℝ E) (fun x => Tensor0SSpace r I x) x₀
  let e_s := trivializationAt (Tensor0SModel s ℝ E) (fun x => Tensor0SSpace s I x) x₀
  let e_1r := trivializationAt (Tensor0SModel (1 + r) ℝ E)
    (fun x => Tensor0SSpace (1 + r) I x) x₀
  -- Formula for e_1.cLMA G: applied to v', evaluates G at e_tan.symmL ∘ v'.
  have h_cLMA_1 : ∀ (G : Tensor0SSpace 1 I x) (v' : Fin 1 → TangentSpace I x),
      (e_1.continuousLinearMapAt ℝ x G) v' = G (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro G v'
    have hGfib : G = e_1.symmL ℝ x (e_1.continuousLinearMapAt ℝ x G) :=
      (e_1.symmL_continuousLinearMapAt (R := ℝ) hx_1 G).symm
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan
      (e_1.continuousLinearMapAt ℝ x G)
    rw [hsym] at hGfib
    conv_rhs => rw [hGfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  -- Formula for e_r.symmL G.
  have h_symmL_r : ∀ (G : Tensor0SModel r ℝ E) (v' : Fin r → TangentSpace I x),
      (e_r.symmL ℝ x G) v' = G (fun i => e_tan.continuousLinearMapAt ℝ x (v' i)) := by
    intro G v'
    rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx_tan]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Formula for e_1r.symmL G.
  have h_symmL_1r : ∀ (G : Tensor0SModel (1 + r) ℝ E) (v' : Fin (1 + r) → TangentSpace I x),
      (e_1r.symmL ℝ x G) v' = G (fun i => e_tan.continuousLinearMapAt ℝ x (v' i)) := by
    intro G v'
    rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx_tan]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Reshape the LHS into an explicit form.
  -- The goal has `.comp` expansions to unfold.
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  change ((trivializationAt (Tensor0SModel s ℝ E) (Tensor0SSpace s I) x₀).continuousLinearMapAt ℝ x
      ((Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (α x) (T x))
        ((trivializationAt (Tensor0SModel r ℝ E) (Tensor0SSpace r I) x₀).symmL ℝ x β))) v =
    (((model_contract_contravariant_first_bilinear (𝕜 := ℝ) (E := E) r s)
        ((trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
          ⟨x, α x⟩).2))
      ((trivializationAt (TensorRSModel (1 + r) s ℝ E)
        (fun x => TensorRSSpace (1 + r) s I x) x₀ ⟨x, T x⟩).2)) β v
  -- Unfold LHS contract_contravariant_first.
  rw [show (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (α x) (T x))
            (e_r.symmL ℝ x β) =
          (T x) ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
            (Tensor0SBundle.model_tensorWithCovector_first r
              (Tensor0SSpace.toModel (α x))
              ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x)
                (e_r.symmL ℝ x β)))) from by
    unfold Tensor0SBundle.contract_contravariant_first
    simp only [tensorRSSpace_continuousLinearEquiv, ContinuousLinearEquiv.arrowCongr_symm,
      ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearEquiv.symm_apply_apply]]
  -- The LHS after contract_contravariant_first unfolding is now:
  --   e_s.cLMA x ((T x) ((cle (1+r) x).symm (model_twCov_first r (toModel α x) ((cle r x) (e_r.symmL x β))))) v.
  -- The RHS (via model_contract_contravariant_first_bilinear_apply) is:
  --   ((cLMA (trivAt TensorRS) ⟨x, T x⟩).snd) (model_twCov_first r (α-triv) β) v.
  -- Strategy: compute both sides explicitly as scalars via ContinuousMultilinearMap.ext.
  -- First simplify via `h_symmL_1r`, etc.
  rw [model_contract_contravariant_first_bilinear_apply]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Show both sides are equal by matching. Proceed by case-by-case.
  -- Target: `e_s.cLMA x ((T x) Y) v = e_s.cLMA x ((T x) Z) v` after equating applicators.
  -- This reduces to `Y = Z` as fibers.
  have h_arg : (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
      (Tensor0SBundle.model_tensorWithCovector_first r
        (Tensor0SSpace.toModel (α x))
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x)
          (e_r.symmL ℝ x β))) =
    e_1r.symmL ℝ x (Tensor0SBundle.model_tensorWithCovector_first r
      (e_1.continuousLinearMapAt ℝ x (α x)) β) := by
    apply ContinuousMultilinearMap.ext
    intro v'
    rw [tensor0SSpace_continuousLinearEquiv_symm_apply]
    rw [h_symmL_1r _ v']
    unfold Tensor0SBundle.model_tensorWithCovector_first
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    -- Apply modelProduct_apply on the LHS explicitly.
    change (Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel (α x))
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) (e_r.symmL ℝ x β))) v' =
      (Bundle.continuousMultilinearMap.modelProduct 1 r (e_1.continuousLinearMapAt ℝ x (α x)) β)
        (fun i => e_tan.continuousLinearMapAt ℝ x (v' i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    -- Goal: (toModel (α x)) (v' ∘ Fin.castAdd r) * ((cle r x) (e_r.symmL x β)) (v' ∘ Fin.natAdd 1) =
    --       (e_1.cLMA x (α x)) (e_tan.cLMA ∘ v' ∘ Fin.castAdd r) *
    --       β (e_tan.cLMA ∘ v' ∘ Fin.natAdd 1).
    congr 1
    · -- First factor: (toModel (α x)) (v' ∘ Fin.castAdd r) =
      --              (e_1.cLMA x (α x)) (e_tan.cLMA ∘ v' ∘ Fin.castAdd r).
      -- Using h_cLMA_1 on the RHS: `e_1.cLMA x (α x) ((e_tan.cLMA ∘ v') ∘ castAdd r) =
      -- (α x) (fun i => e_tan.symmL x ((e_tan.cLMA ∘ v') ∘ castAdd r i))` = `(α x) (v' ∘ castAdd r)`.
      rw [h_cLMA_1]
      rw [show (Tensor0SSpace.toModel (α x)) = (α x) from rfl]
      congr 1
      funext i
      simp only [Function.comp_apply]
      exact (e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan _).symm
    · -- Second factor: ((cle r x) (e_r.symmL x β)) (v' ∘ Fin.natAdd 1) =
      --              β (e_tan.cLMA ∘ v' ∘ Fin.natAdd 1).
      change (e_r.symmL ℝ x β) (v' ∘ Fin.natAdd 1) = _
      rw [h_symmL_r]
      rfl
  rw [h_arg]
  -- The two sides are equal up to `(e_1 ⟨x, α x⟩).2 = e_1.cLMA x (α x)` on the base set.
  have h_e1 : ((e_1 ⟨x, α x⟩).2 : Tensor0SModel 1 ℝ E) = e_1.continuousLinearMapAt ℝ x (α x) := by
    have h := e_1.coe_linearMapAt_of_mem (R := ℝ) hx_1
    exact (congrArg (fun f => f (α x)) h).symm
  rw [← h_e1]
  -- Also unfold the RHS TRS trivialization. After `hom_trivializationAt_apply`, the RHS
  -- becomes `⟨x, inCoordinates ...⟩.2` which reduces.
  rw [hom_trivializationAt_apply]
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- The remaining diffs are eta-equivalence in the function-type arguments.
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise value of `contract_contravariant_first_smoothField`. -/
theorem contract_contravariant_first_smoothField_toFun (r s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r) s) :
    (contract_contravariant_first_smoothField I M r s α T).toFun =
      fun x => Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (α x) (T x) := rfl

/-! #### Basis-invariant expansion of the fiber contraction.

The fiber-level contraction is defined using `stdBasis` and `stdDualCov`, but is
mathematically basis-independent. We establish the identity showing it equals the same sum
with any biorthogonal pair at that fiber.

The proof uses the **trace machinery** (Path B in the implementation plan): the basis-sum
is rewritten as `LinearMap.trace ℝ E Φ` of an explicit endomorphism `Φ : E →ₗ[ℝ] E`
extracted from `T, β, v`, using `LinearMap.trace_eq_matrix_trace` and the change-of-basis
invariance of the matrix trace. -/

section BasisInvariance

/-! #### Partial-trace endomorphism.

For a tensor `T : TensorRSSpace (r+1) (s+1) I x`, a covariant input `β : Tensor0SSpace r I x`,
and a covector-slot input `v : Fin s → TangentSpace I x`, we define a linear endomorphism
`partialTraceEndo T β v : E →ₗ[ℝ] E` whose trace under any biorthogonal basis/dual pair
`(b', θ')` reproduces the partial-trace sum. -/

/-- Given fixed `T, β, v`, the scalar evaluation of the partial-trace summand on a pair
`(w, α) ∈ E × Tensor0SModel 1 ℝ E`. This is linear in each argument. -/
private noncomputable def partialTraceKernel (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x)
    (w : E) (α : Tensor0SModel 1 ℝ E) : ℝ :=
  Tensor0SSpace.toModel
    ((castRSComm I M r s x T)
      (Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))))
    (Fin.cons w v)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `partialTraceKernel` is linear in its last argument `α`. -/
private lemma partialTraceKernel_add_right (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) (w : E)
    (α₁ α₂ : Tensor0SModel 1 ℝ E) :
    partialTraceKernel I M r s x T β v w (α₁ + α₂) =
      partialTraceKernel I M r s x T β v w α₁ +
      partialTraceKernel I M r s x T β v w α₂ := by
  unfold partialTraceKernel
  have h_mp : Bundle.continuousMultilinearMap.modelProduct 1 r (α₁ + α₂) (Tensor0SSpace.toModel β) =
      Bundle.continuousMultilinearMap.modelProduct 1 r α₁ (Tensor0SSpace.toModel β) +
      Bundle.continuousMultilinearMap.modelProduct 1 r α₂ (Tensor0SSpace.toModel β) := by
    ext v'
    simp [Bundle.continuousMultilinearMap.modelProduct_apply, add_mul]
  rw [h_mp]
  -- Push `+` through `ofModel`, `castRSComm T`, `toModel`.
  rw [show (Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α₁ (Tensor0SSpace.toModel β) +
         Bundle.continuousMultilinearMap.modelProduct 1 r α₂ (Tensor0SSpace.toModel β))
        : Tensor0SSpace (1 + r) I x) =
      Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α₁ (Tensor0SSpace.toModel β)) +
      Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α₂ (Tensor0SSpace.toModel β)) from
    map_add (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm _ _]
  -- Push `+` through `castRSComm T`.
  rw [map_add (castRSComm I M r s x T)]
  -- Push `+` through `toModel`.
  rw [show (Tensor0SSpace.toModel
          ((castRSComm I M r s x T)
              (Tensor0SSpace.ofModel
                (Bundle.continuousMultilinearMap.modelProduct 1 r α₁ (Tensor0SSpace.toModel β))) +
            (castRSComm I M r s x T)
              (Tensor0SSpace.ofModel
                (Bundle.continuousMultilinearMap.modelProduct 1 r α₂ (Tensor0SSpace.toModel β))))
        : ContinuousMultilinearMap _ _ _) =
      Tensor0SSpace.toModel
          ((castRSComm I M r s x T)
            (Tensor0SSpace.ofModel
              (Bundle.continuousMultilinearMap.modelProduct 1 r α₁ (Tensor0SSpace.toModel β)))) +
        Tensor0SSpace.toModel
          ((castRSComm I M r s x T)
            (Tensor0SSpace.ofModel
              (Bundle.continuousMultilinearMap.modelProduct 1 r α₂ (Tensor0SSpace.toModel β)))) from
    map_add (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (s + 1) x) _ _]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `partialTraceKernel` is scalar-homogeneous in its last argument `α`. -/
private lemma partialTraceKernel_smul_right (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) (w : E)
    (c : ℝ) (α : Tensor0SModel 1 ℝ E) :
    partialTraceKernel I M r s x T β v w (c • α) =
      c • partialTraceKernel I M r s x T β v w α := by
  unfold partialTraceKernel
  have h_mp : Bundle.continuousMultilinearMap.modelProduct 1 r (c • α) (Tensor0SSpace.toModel β) =
      c • Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β) := by
    ext v'
    simp [Bundle.continuousMultilinearMap.modelProduct_apply, mul_assoc]
  rw [h_mp]
  -- Push `c •` through `ofModel`.
  rw [show (Tensor0SSpace.ofModel
            (c • Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))
          : Tensor0SSpace (1 + r) I x) =
        c • Tensor0SSpace.ofModel
            (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β)) from
      map_smul (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm c _]
  -- Push `c •` through `castRSComm T`.
  rw [show (castRSComm I M r s x T)
        (c • Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))) =
      c • (castRSComm I M r s x T)
        (Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))) from
    map_smul (castRSComm I M r s x T) c _]
  -- Push `c •` through `toModel`.
  rw [show (Tensor0SSpace.toModel
          (c • (castRSComm I M r s x T)
            (Tensor0SSpace.ofModel
              (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))))
        : ContinuousMultilinearMap _ _ _) =
      c • Tensor0SSpace.toModel
        ((castRSComm I M r s x T)
          (Tensor0SSpace.ofModel
            (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β)))) from
    map_smul (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (s + 1) x) c _]
  -- Finally `(c • F)(v) = c • F v`.
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `partialTraceKernel` is linear in its first argument `w`. -/
private lemma partialTraceKernel_add_left (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x)
    (w₁ w₂ : E) (α : Tensor0SModel 1 ℝ E) :
    partialTraceKernel I M r s x T β v (w₁ + w₂) α =
      partialTraceKernel I M r s x T β v w₁ α +
      partialTraceKernel I M r s x T β v w₂ α := by
  unfold partialTraceKernel
  set F := Tensor0SSpace.toModel
    ((castRSComm I M r s x T)
      (Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))))
  -- F is a ContinuousMultilinearMap on `Fin (s+1) → E`, multilinear in each slot.
  have h_cons : (Fin.cons ((w₁ + w₂ : E) : TangentSpace I x) v : Fin (s + 1) → E) =
      Function.update (Fin.cons w₁ v) 0 ((w₁ + w₂ : E) : TangentSpace I x) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  rw [h_cons, F.map_update_add]
  -- Goal: F (update (Fin.cons w₁ v) 0 w₁) + F (update (Fin.cons w₁ v) 0 w₂) =
  --       F (Fin.cons w₁ v) + F (Fin.cons w₂ v).
  have h_eq1 : Function.update (Fin.cons w₁ v : Fin (s + 1) → E) 0 (w₁ : E) = Fin.cons w₁ v := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have h_eq2 : Function.update (Fin.cons w₁ v : Fin (s + 1) → E) 0 (w₂ : E) = Fin.cons w₂ v := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  rw [h_eq1, h_eq2]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `partialTraceKernel` is scalar-homogeneous in its first argument `w`. -/
private lemma partialTraceKernel_smul_left (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x)
    (c : ℝ) (w : E) (α : Tensor0SModel 1 ℝ E) :
    partialTraceKernel I M r s x T β v (c • w) α =
      c • partialTraceKernel I M r s x T β v w α := by
  unfold partialTraceKernel
  set F := Tensor0SSpace.toModel
    ((castRSComm I M r s x T)
      (Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct 1 r α (Tensor0SSpace.toModel β))))
  have h_cons : (Fin.cons ((c • w : E) : TangentSpace I x) v : Fin (s + 1) → E) =
      Function.update (Fin.cons w v) 0 ((c • w : E) : TangentSpace I x) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  rw [h_cons, F.map_update_smul]
  -- Goal: c • F (Function.update (Fin.cons w v) 0 w) = c • F (Fin.cons w v).
  -- Since `(Fin.cons w v) 0 = w`, `Function.update (Fin.cons w v) 0 w = Fin.cons w v`.
  have : Function.update (Fin.cons w v : Fin (s + 1) → E) 0 (w : E) = Fin.cons w v := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  rw [this]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Bridge: the partial-trace kernel evaluated on `(w, toModel α)` equals the unfolded
`contract_contravariant_first ∘ contract_covariant` summand expression. -/
private lemma partialTraceKernel_eq_summand (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (α : Tensor0SSpace 1 I x) (β : Tensor0SSpace r I x) (w : E)
    (v : Fin s → TangentSpace I x) :
    partialTraceKernel I M r s x T β v w (Tensor0SSpace.toModel α) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x α
          (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
            ((w : TangentSpace I x)) (castRSComm I M r s x T)) β)
        v := by
  classical
  -- RHS: unfold `contract_contravariant_first_apply_eval` and `contract_covariant_apply_eval`.
  rw [contract_contravariant_first_apply_eval, contract_covariant_apply_eval]
  unfold partialTraceKernel
  -- Unfold interior_product and simplify.
  unfold Tensor0SBundle.interior_product
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  -- After simplification, the RHS evaluates `(cle s x).symm (model_interior_product s w (cle (s+1) x F))`
  -- at v. The evaluation = model_interior_product s w (cle (s+1) x F) v.
  -- And `model_interior_product s w G v = G (Fin.cons w v)` for G a ContinuousMultilinearMap.
  -- Similarly, `model_tensorWithCovector_first r α̃ β̃ = modelProduct 1 r α̃ β̃`.
  -- So both LHS and RHS are `(castRSComm T (ofModel (modelProduct 1 r α̃ β̃))).toModel (Fin.cons w v)`.
  -- The remaining goal should be (propositionally) `rfl`.
  change
    (Tensor0SSpace.toModel
      ((castRSComm I M r s x T)
        (Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel α)
            (Tensor0SSpace.toModel β))))) (Fin.cons w v) =
    Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (Tensor0SBundle.model_interior_product s w
          (Tensor0SSpace.toModel
            ((castRSComm I M r s x T)
              (Tensor0SSpace.ofModel
                (Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α)
                  (Tensor0SSpace.toModel β))))))) v
  rw [Tensor0SSpace.toModel_ofModel]
  -- Now unfold `model_interior_product s w G = G.curryLeft(w)` and `model_tensorWithCovector_first`.
  -- At a pointwise level: `model_interior_product s w G v = G (Fin.cons w v)`.
  -- And `model_tensorWithCovector_first r α̃ β̃ = modelProduct 1 r α̃ β̃`.
  change
    (Tensor0SSpace.toModel
      ((castRSComm I M r s x T)
        (Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel α)
            (Tensor0SSpace.toModel β))))) (Fin.cons w v) =
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).toContinuousLinearEquiv
      (Tensor0SSpace.toModel
        ((castRSComm I M r s x T)
          (Tensor0SSpace.ofModel
            (Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel α)
              (Tensor0SSpace.toModel β)))))) w v
  -- This is definitional unfolding of `model_interior_product` and `model_tensorWithCovector_first`.
  -- The `continuousMultilinearCurryLeftEquiv` applied to F at w gives F.curryLeft(w),
  -- which when applied at v gives F (Fin.cons w v).
  rfl

/-- The curried dual-functional associated to a biorthogonal family `θ'`. Given a (0,1)-tensor
`θ' i`, this extracts the corresponding linear functional on `E` via `continuousMultilinearCurryFin1`. -/
private noncomputable def curriedDual (x : M)
    (θ' : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x)
    (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ) (Tensor0SSpace.toModel (θ' i))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma curriedDual_apply (x : M)
    (θ' : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x)
    (i : Fin (Module.finrank ℝ E)) (w : E) :
    curriedDual I M x θ' i w =
      (Tensor0SSpace.toModel (θ' i)) (fun _ : Fin 1 => w) := by
  unfold curriedDual
  rw [continuousMultilinearCurryFin1_apply]
  have h_snoc : (Fin.snoc (0 : Fin 0 → E) w : Fin 1 → E) = fun _ => w := by
    funext k
    fin_cases k
    simp
  rw [h_snoc]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Biorthogonality of the standard dual covector family with the standard basis. -/
private lemma stdDualCovector_biorth (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (Tensor0SSpace.toModel (stdDualCovector I M x i)) (fun _ : Fin 1 => (stdBasis (E := E)) j) =
      if i = j then (1 : ℝ) else 0 := by
  unfold stdDualCovector
  rw [Tensor0SSpace.toModel_ofModel, continuousMultilinearCurryFin1_symm_apply]
  change (stdBasis (E := E)).coord i ((stdBasis (E := E)) j) = _
  unfold stdBasis
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · simp [h]
  · rw [Finsupp.single_apply, if_neg (fun heq => h heq.symm), if_neg h]

end BasisInvariance

/-! #### The partial-trace endomorphism and its trace. -/

section PartialTraceEndo

/-- The partial-trace endomorphism: for fixed `T, β, v`, the map `E →ₗ[ℝ] E` defined by
```
Φ(w) = ∑_j K(w, toModel stdDual_j) • stdBasis_j
```
where `K = partialTraceKernel T β v`. This is a finite-dimensional "pairing vector" that
turns the bilinear form `K` into an endomorphism, whose trace is the partial-trace sum.

The construction uses `stdBasis` explicitly, but only as a computational vehicle: the
*trace* of `Φ` is basis-independent (proved via `LinearMap.trace_eq_matrix_trace` below). -/
private noncomputable def partialTraceEndo (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) : E →ₗ[ℝ] E where
  toFun := fun w =>
    ∑ j : Fin (Module.finrank ℝ E),
      partialTraceKernel I M r s x T β v w
        (Tensor0SSpace.toModel (stdDualCovector I M x j)) • (stdBasis (E := E)) j
  map_add' := by
    intro w₁ w₂
    simp only [← Finset.sum_add_distrib]
    congr 1
    ext j
    rw [partialTraceKernel_add_left, add_smul]
  map_smul' := by
    intro c w
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [partialTraceKernel_smul_left]
    rw [smul_assoc]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma partialTraceEndo_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) (w : E) :
    partialTraceEndo I M r s x T β v w =
      ∑ j : Fin (Module.finrank ℝ E),
        partialTraceKernel I M r s x T β v w
          (Tensor0SSpace.toModel (stdDualCovector I M x j)) • (stdBasis (E := E)) j := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Dual-basis expansion at the tensor level.** Any `α : Tensor0SModel 1 ℝ E` can be
reconstructed from its values on the standard basis:
```
α = ∑_j α(fun _ => stdBasis_j) • toModel(stdDual_j)    (at the Tensor0SModel 1 ℝ E level)
```
This is the tensor-level analogue of the dual-basis expansion
`ζ = ∑_j ζ(stdBasis_j) • stdBasis.coord j` for `ζ : E →L[ℝ] ℝ`. -/
private lemma dualBasisExpansion_tensor (x : M) (α : Tensor0SModel 1 ℝ E) :
    α = ∑ j : Fin (Module.finrank ℝ E),
        α (fun _ : Fin 1 => ((stdBasis (E := E)) j : E)) •
          Tensor0SSpace.toModel (stdDualCovector I M x j) := by
  classical
  -- We prove equality of `ContinuousMultilinearMap` by evaluating on all `v : Fin 1 → E`.
  ext v
  -- LHS = α v, where v : Fin 1 → E and α is a continuous multilinear map.
  -- RHS = ∑_j α(fun _ => stdBasis_j) • (toModel stdDual_j)(v)
  --     = ∑_j α(fun _ => stdBasis_j) * (stdBasis.coord j)(v 0)   [via stdDualCovector unfold]
  -- We also know: α v = (continuousMultilinearCurryFin1)(α) (v 0), and
  -- for any ζ : E →L[ℝ] ℝ, ζ = ∑_j ζ(stdBasis_j) • stdBasis.coord j, so ζ(v 0) = RHS.
  rw [show ∑ j : Fin (Module.finrank ℝ E),
        α (fun _ : Fin 1 => ((stdBasis (E := E)) j : E)) •
          Tensor0SSpace.toModel (stdDualCovector I M x j) =
      (Finset.univ.sum (fun j =>
        α (fun _ : Fin 1 => ((stdBasis (E := E)) j : E)) •
          Tensor0SSpace.toModel (stdDualCovector I M x j))) from rfl]
  rw [ContinuousMultilinearMap.sum_apply]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  -- Goal: α v = ∑ j, α(fun _ => stdBasis j) * (toModel stdDual j) v.
  -- Evaluate `(toModel stdDual j) v` using `stdDualCovector` unfold.
  have h_toModel_eval : ∀ j : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel (stdDualCovector I M x j)) v =
      (stdBasis (E := E)).coord j (v 0) := by
    intro j
    unfold stdDualCovector
    rw [Tensor0SSpace.toModel_ofModel]
    rw [continuousMultilinearCurryFin1_symm_apply]
    rfl
  simp_rw [h_toModel_eval]
  -- Goal: α v = ∑ j, α(fun _ => stdBasis j) * (stdBasis).coord j (v 0).
  -- Note: v = Fin.snoc 0 (v 0) (for Fin 1, this is equivalent to `fun _ => v 0`).
  have h_v : v = fun _ : Fin 1 => v 0 := by
    funext k
    fin_cases k
    rfl
  rw [h_v]
  -- Goal: α (fun _ => v 0) = ∑ j, α(fun _ => stdBasis j) * stdBasis.coord j (v 0).
  -- Use: v 0 = ∑_j stdBasis.coord j (v 0) • stdBasis j, hence
  --   α (fun _ => v 0) = ∑_j stdBasis.coord j (v 0) * α (fun _ => stdBasis j)
  -- by linearity of α in slot 0.
  set w : E := v 0 with hw_def
  -- Expand w = ∑_j (stdBasis).repr w j • stdBasis j (dual-basis expansion).
  have h_w_expansion : w = ∑ j, (stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E) :=
    ((stdBasis (E := E)).sum_equivFun w).symm
  -- To move `∑` outside of `α (fun _ => ·)`, use map_update_sum on the 0-th slot of the FIN-1 list.
  -- Since α is multilinear and the list has length 1, the 0-th slot is the only slot,
  -- so applying `α` to `fun _ => w` with `w` expanded via the basis sum uses multilinearity.
  have h_cml : α (fun _ : Fin 1 => w) =
      ∑ j, (stdBasis (E := E)).repr w j • α (fun _ : Fin 1 => ((stdBasis (E := E)) j : E)) := by
    classical
    -- Work through `α.toMultilinearMap` to apply `map_update_sum`.
    -- Step 1: use the base-case update: `fun _ => w = update (fun _ => 0) 0 w`.
    have h_upd : (fun _ : Fin 1 => w) =
        Function.update (fun _ : Fin 1 => (0 : E)) 0 w := by
      funext k; fin_cases k; simp
    conv_lhs => rw [h_upd, show w = ∑ j : Fin (Module.finrank ℝ E),
            (stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E) from h_w_expansion]
    -- Apply `α.toMultilinearMap.map_update_sum`.
    rw [show α (Function.update (fun _ : Fin 1 => (0 : E)) 0
            (∑ j : Fin (Module.finrank ℝ E),
              (stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E))) =
          ∑ j : Fin (Module.finrank ℝ E), α (Function.update (fun _ : Fin 1 => (0 : E)) 0
              ((stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E))) from
      α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        0
        (fun j => (stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E))
        (fun _ : Fin 1 => (0 : E))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show α (Function.update (fun _ : Fin 1 => (0 : E)) 0
            ((stdBasis (E := E)).repr w j • ((stdBasis (E := E)) j : E))) =
          (stdBasis (E := E)).repr w j • α (Function.update (fun _ : Fin 1 => (0 : E)) 0
            ((stdBasis (E := E)) j : E)) from
      α.toMultilinearMap.map_update_smul (fun _ : Fin 1 => (0 : E)) 0
        ((stdBasis (E := E)).repr w j) ((stdBasis (E := E)) j)]
    -- Goal: (stdBasis).repr w j • α (update (fun _ => 0) 0 (stdBasis j)) = (stdBasis).repr w j • α (fun _ => stdBasis j).
    congr 1
    -- Goal: α (update (fun _ => 0) 0 (stdBasis j)) = α (fun _ => stdBasis j).
    congr 1
    funext k; fin_cases k; simp
  rw [h_cml]
  -- Goal: ∑ j, (stdBasis).repr w j • α (fun _ => stdBasis j) =
  --       ∑ j, α (fun _ => stdBasis j) * (stdBasis).coord j w.
  congr 1
  ext j
  rw [Module.Basis.coord_apply]
  rw [smul_eq_mul, mul_comm]

end PartialTraceEndo

section MainLemma

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Partial-trace basis-invariance at a fiber.**
The basis sum `∑_i contract_contravariant_first θ'_i ∘ contract_covariant b'_i (cast T)`
is independent of the choice of biorthogonal basis/dual pair `(b', θ')`: it equals the same
expression computed with the standard basis/dual pair from `stdBasis` and `stdDualCovector`.

Proof strategy (Path B): reduce both sides, via `contract_*_apply_eval` and `slot0Insert`
unfolding, to basis sums of the bilinear form `partialTraceKernel T β v w α` over
`(b'_i, toModel θ'_i)` vs. `(stdBasis_i, toModel stdDual_i)`. These sums equal the trace
of an explicit endomorphism `partialTraceEndo' T β v : E →ₗ[ℝ] E`, which is basis-independent
via `LinearMap.trace_eq_matrix_trace` + `LinearMap.trace_conj'`. -/
private theorem partial_trace_basis_invariant_at_fiber (r s : ℕ) (x : M)
    (b' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (θ' : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x)
    (h_biorth : ∀ i j, (Tensor0SSpace.toModel (θ' i)) (fun _ => b' j) =
      (if i = j then (1 : ℝ) else 0))
    (h_basis : LinearIndependent ℝ b' ∧ Submodule.span ℝ (Set.range b') = ⊤)
    (T : TensorRSSpace (r + 1) (s + 1) I x) :
    ∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ' i)
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
          ((b' i : TangentSpace I x)) (castRSComm I M r s x T)) =
      concreteTensorContract_fiber I M r s x T := by
  classical
  -- Reduce to CLM equality pointwise on β : Tensor0SSpace r.
  refine ContinuousLinearMap.ext (fun β => ?_)
  -- Rewrite the RHS.
  rw [concreteTensorContract_fiber]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
  -- After unfolding `concreteTensorContract_fiber`, RHS is the std-basis sum; LHS is the b'-sum.
  -- Both apply `.comp` to `castRSComm T` — but the LHS has `contract_contravariant_first (θ' i) ∘
  -- contract_covariant (b' i)` and RHS has the std variant.
  -- We reduce to Tensor0SSpace (s)-equality pointwise on v.
  -- First, apply ContinuousLinearMap.ext_iff... but Tensor0S is a ContinuousMultilinearMap, so use
  -- `Tensor0SSpace.toModel` and then `ContinuousMultilinearMap.ext`.
  apply (Tensor0SSpace.toModel_injective)
  apply ContinuousMultilinearMap.ext
  intro v
  -- Now v : Fin s → TangentSpace I x = E.
  -- Unfold LHS and RHS to `∑_i toModel(summand)(v)` sums, apply `partialTraceKernel_eq_summand`.
  -- Step: the LHS sum, applied at β then at v.
  have h_lhs_apply :
      (Tensor0SSpace.toModel (∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ' i)
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x ((b' i : TangentSpace I x))
          (castRSComm I M r s x T)) β) : ContinuousMultilinearMap _ _ _) v =
      ∑ i, partialTraceKernel I M r s x T β v (b' i : E) (Tensor0SSpace.toModel (θ' i)) := by
    rw [show (Tensor0SSpace.toModel
          (∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ' i)
            (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x ((b' i : TangentSpace I x))
              (castRSComm I M r s x T)) β) : ContinuousMultilinearMap _ _ _) =
        ∑ i, Tensor0SSpace.toModel
          (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ' i)
            (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x ((b' i : TangentSpace I x))
              (castRSComm I M r s x T)) β) from
      map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) s x) _ _]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialTraceKernel_eq_summand]
  have h_rhs_apply :
      (Tensor0SSpace.toModel (∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x
        (stdDualCovector I M x i)
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
          (((stdBasis (E := E)) i : TangentSpace I x)) (castRSComm I M r s x T)) β)
        : ContinuousMultilinearMap _ _ _) v =
      ∑ i, partialTraceKernel I M r s x T β v ((stdBasis (E := E)) i : E)
        (Tensor0SSpace.toModel (stdDualCovector I M x i)) := by
    rw [show (Tensor0SSpace.toModel
          (∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x
            (stdDualCovector I M x i)
            (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
              (((stdBasis (E := E)) i : TangentSpace I x)) (castRSComm I M r s x T)) β)
          : ContinuousMultilinearMap _ _ _) =
        ∑ i, Tensor0SSpace.toModel
          (Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x
            (stdDualCovector I M x i)
            (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
              (((stdBasis (E := E)) i : TangentSpace I x)) (castRSComm I M r s x T)) β) from
      map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) s x) _ _]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialTraceKernel_eq_summand]
  rw [h_lhs_apply, h_rhs_apply]
  -- Now we need: ∑_i K(b'_i, toModel θ'_i) = ∑_i K(stdBasis_i, toModel stdDual_i).
  -- Strategy: express both sums as LinearMap.trace of `partialTraceEndo T β v`.
  set Φ := partialTraceEndo I M r s x T β v with hΦ_def
  -- Claim 1: ∑_i K(stdBasis_i, toModel stdDual_i) = tr(Φ) (in basis stdBasis).
  have h_std_eq_trace :
      ∑ i, partialTraceKernel I M r s x T β v ((stdBasis (E := E)) i : E)
          (Tensor0SSpace.toModel (stdDualCovector I M x i)) =
      LinearMap.trace ℝ E Φ := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (stdBasis (E := E))]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Goal: K(stdBasis_i, toModel stdDual_i) = (stdBasis).repr (Φ (stdBasis i)) i.
    rw [hΦ_def, partialTraceEndo_apply]
    rw [map_sum, Finsupp.finset_sum_apply]
    -- Now RHS: ∑ j, (stdBasis.repr (K(...) • stdBasis j)) i = ∑ j, K(...) * (stdBasis.repr (stdBasis j)) i.
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, partialTraceKernel I M r s x T β v ((stdBasis (E := E)) i : E)
            (Tensor0SSpace.toModel (stdDualCovector I M x j)) *
          ((stdBasis (E := E)).repr ((stdBasis (E := E)) j)) i) =
        (∑ j, if i = j then
          partialTraceKernel I M r s x T β v ((stdBasis (E := E)) i : E)
            (Tensor0SSpace.toModel (stdDualCovector I M x j))
        else 0) from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      by_cases h : j = i
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (fun heq => h heq.symm), mul_zero]]
    rw [Finset.sum_ite_eq Finset.univ i (fun j =>
      partialTraceKernel I M r s x T β v ((stdBasis (E := E)) i : E)
        (Tensor0SSpace.toModel (stdDualCovector I M x j)))]
    simp
  -- Claim 2: ∑_i K(b'_i, toModel θ'_i) = tr(Φ) (in basis b').
  -- Convert (b', θ') to a `Module.Basis` via `Basis.mk`.
  let bPrimeBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.Basis.mk h_basis.1 (le_of_eq h_basis.2.symm)
  have h_bPrime_apply : ∀ i, bPrimeBasis i = b' i := fun i => by
    change (Module.Basis.mk h_basis.1 (le_of_eq h_basis.2.symm)) i = b' i
    rw [Module.Basis.mk_apply]
  -- The `coord i` functional of bPrimeBasis equals `curriedDual θ' i`, via biorthogonality.
  have h_coord_eq : ∀ i, bPrimeBasis.coord i = (curriedDual I M x θ' i : E →ₗ[ℝ] ℝ) := by
    intro i
    apply bPrimeBasis.ext
    intro j
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [h_bPrime_apply]
    -- Goal: Finsupp.single j 1 i = ↑(curriedDual I M x θ' i) (b' j).
    change Finsupp.single j 1 i = curriedDual I M x θ' i (b' j)
    rw [curriedDual_apply, h_biorth, Finsupp.single_apply]
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun heq => h heq.symm)]
  have h_prime_eq_trace :
      ∑ i, partialTraceKernel I M r s x T β v (b' i : E)
          (Tensor0SSpace.toModel (θ' i)) =
      LinearMap.trace ℝ E Φ := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bPrimeBasis]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_bPrime_apply]
    -- Goal: `K(b' i, toModel θ'_i) = bPrimeBasis.repr (Φ (b' i)) i`.
    rw [← Module.Basis.coord_apply]
    rw [h_coord_eq]
    -- Goal: `K(b' i, toModel θ'_i) = (curriedDual θ' i) (Φ (b' i))`.
    change partialTraceKernel I M r s x T β v (b' i : E) (Tensor0SSpace.toModel (θ' i)) =
      curriedDual I M x θ' i (Φ (b' i))
    rw [hΦ_def, partialTraceEndo_apply]
    rw [map_sum]
    -- RHS: ∑ j, curriedDual θ' i (K(b'_i, toModel stdDual_j) • stdBasis j).
    -- Use map_smul to pull out the scalar.
    rw [show (∑ j, (curriedDual I M x θ' i)
            (partialTraceKernel I M r s x T β v (b' i : E)
              (Tensor0SSpace.toModel (stdDualCovector I M x j)) • ((stdBasis (E := E)) j : E))) =
        (∑ j, partialTraceKernel I M r s x T β v (b' i : E)
            (Tensor0SSpace.toModel (stdDualCovector I M x j)) *
          (Tensor0SSpace.toModel (θ' i))
            (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x))) from by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, curriedDual_apply]]
    -- Goal: ∑ j, K(b'_i, toModel stdDual_j) * toModel(θ'_i)(fun _ => stdBasis j) = K(b'_i, toModel θ'_i).
    -- Step 1: rewrite each summand to factor out the smul-scaling on the α-slot, applying
    -- the right-linearity of K.
    have h_step : ∀ j : Fin (Module.finrank ℝ E),
        partialTraceKernel I M r s x T β v (b' i : E)
            (Tensor0SSpace.toModel (stdDualCovector I M x j)) *
          (Tensor0SSpace.toModel (θ' i))
            (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x)) =
        partialTraceKernel I M r s x T β v (b' i : E)
          ((Tensor0SSpace.toModel (θ' i))
              (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x)) •
            Tensor0SSpace.toModel (stdDualCovector I M x j)) := by
      intro j
      rw [partialTraceKernel_smul_right, smul_eq_mul, mul_comm]
    simp_rw [h_step]
    -- Step 2: pull the sum inside using iterated additivity of K in α.
    have h_sum_pull :
        (∑ j, partialTraceKernel I M r s x T β v (b' i : E)
              ((Tensor0SSpace.toModel (θ' i))
                (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x)) •
                Tensor0SSpace.toModel (stdDualCovector I M x j))) =
        partialTraceKernel I M r s x T β v (b' i : E)
          (∑ j, (Tensor0SSpace.toModel (θ' i))
              (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x)) •
            Tensor0SSpace.toModel (stdDualCovector I M x j)) := by
      -- Iterated K-additivity via induction on the sum.
      let f : Fin (Module.finrank ℝ E) → Tensor0SModel 1 ℝ E := fun j =>
        (Tensor0SSpace.toModel (θ' i))
            (fun _ : Fin 1 => ((stdBasis (E := E)) j : TangentSpace I x)) •
          Tensor0SSpace.toModel (stdDualCovector I M x j)
      change (∑ j, partialTraceKernel I M r s x T β v (b' i : E) (f j)) =
        partialTraceKernel I M r s x T β v (b' i : E) (∑ j, f j)
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          -- K(b'_i, 0) = 0 by right-additivity with α = 0.
          have h_zero : partialTraceKernel I M r s x T β v (b' i : E) 0 = 0 := by
            have h := partialTraceKernel_add_right I M r s x T β v (b' i) 0 0
            have h0 : (0 : Tensor0SModel 1 ℝ E) + 0 = 0 := add_zero 0
            rw [h0] at h
            linarith
          exact h_zero.symm
      | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, ih,
            ← partialTraceKernel_add_right]
    rw [h_sum_pull]
    -- Step 3: the inner sum equals `toModel (θ' i)` by `dualBasisExpansion_tensor`.
    congr 1
    rw [← dualBasisExpansion_tensor I M x (Tensor0SSpace.toModel (θ' i))]
  -- Combine the two claims.
  rw [h_prime_eq_trace, h_std_eq_trace]

end MainLemma

/-! #### Local frame formula.

Given a smooth local frame `σ'` and its biorthogonal dual (a pointwise family `θ'`),
the fiber-level contraction at each `x` near `x₀` equals the basis sum in the local frame. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Local frame formula.** Near `x₀`, the contraction `concreteTensorContract_fiber`
equals the basis sum in any smooth local frame `σ'` that agrees with
`(trivializationAt x₀).localFrame (finBasis ℝ E)` near `x₀`, together with any pointwise
family `θ'` that is biorthogonal to `σ'` near `x₀`.

Note: we take `θ'` as a pointwise family rather than a smooth section; only biorthogonality
is required for the equality, while smoothness packaging is handled in Substep 3. -/
theorem concreteTensorContract_fiber_local_formula (r s : ℕ)
    (T : Π x : M, TensorRSSpace (r + 1) (s + 1) I x) (x₀ : M)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ' : Fin (Module.finrank ℝ E) → Π x : M, Tensor0SSpace 1 I x)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x)
    (hθ' : ∀ᶠ x in 𝓝 x₀, ∀ i j,
      (Tensor0SSpace.toModel (θ' i x)) (fun _ => (σ' j) x) =
        (if i = j then (1 : ℝ) else 0)) :
    ∀ᶠ x in 𝓝 x₀,
      concreteTensorContract_fiber I M r s x (T x) =
        ∑ i, Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ' i x)
          (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x
            ((σ' i) x) (castRSComm I M r s x (T x))) := by
  -- Use the trivialization at x₀.
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  -- filter_upwards: combine hσ', hθ', and `x ∈ e.baseSet`.
  filter_upwards [hσ', hθ', e.open_baseSet.mem_nhds he] with x hσ'x hθ'x hx
  -- At this x, (σ' i x, θ' i x) is a biorthogonal pair.
  -- σ' i x = e.localFrame b i x = e.basisAt b hx i = (e.linearEquivAt ℝ x hx).symm (b i).
  -- So {σ' i x} is a basis of TangentSpace I x (maps b via linearEquivAt.symm).
  let le : TangentSpace I x ≃ₗ[ℝ] E := e.linearEquivAt ℝ x hx
  have hσ'_eq : ∀ i, (σ' i) x = le.symm (b i) := by
    intro i
    rw [hσ'x i]
    change e.localFrame b i x = le.symm (b i)
    rw [e.localFrame_apply_of_mem_baseSet (hx := hx)]
    simp [Trivialization.basisAt, le]
  -- The linear independence and spanning of {σ' i x}.
  have h_linind : LinearIndependent ℝ (fun i => (σ' i) x) := by
    -- Map of linear independence under le.symm.
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ' i) x) = (fun i => le.symm (b i)) := funext hσ'_eq
    rw [h2]
    exact h1
  have h_span : Submodule.span ℝ (Set.range (fun i => (σ' i) x)) = ⊤ := by
    have h2 : (fun i => (σ' i) x) = (fun i => le.symm (b i)) := funext hσ'_eq
    rw [h2]
    rw [show Set.range (fun i => le.symm (b i)) =
        le.symm.toLinearMap '' Set.range b by
      ext w; simp [Set.mem_range, Set.mem_image]]
    rw [Submodule.span_image]
    rw [b.span_eq]
    simp
  -- Apply the fiber-level basis-invariance theorem.
  have h_inv := partial_trace_basis_invariant_at_fiber I M r s x
    (fun i => (σ' i) x) (fun i => θ' i x) hθ'x ⟨h_linind, h_span⟩ (T x)
  -- The target equation is h_inv.symm.
  exact h_inv.symm

/-! ### Part B: packaging the pointwise field contraction as a smooth TensorRSField.

The smoothness of `x ↦ concreteTensorContract_fiber r s x (T x)` is proved by working on a
neighborhood of any base point `x₀`, using:

* a smooth local frame `σ' : Fin _ → Γ(TM)` matching the tangent-bundle local frame at `x₀`,
  obtained by `exists_contMDiffSection_eqOn_nhd`;
* a smooth local "dual frame" `θ' : Fin _ → Γ(Tensor0S 1)` matching the dual local frame at
  `x₀` for the `dualCovectorBasis` of `Tensor0SModel 1 ℝ E`;
* biorthogonality of `(σ' i x, θ' i x)` near `x₀`, verified using the round-trip identities
  of the tangent trivialization;
* `concreteTensorContract_fiber_local_formula` to replace `concreteTensorContract_fiber`
  pointwise on a neighborhood of `x₀` with a finite sum of
  `contract_contravariant_first ∘ contract_covariant ∘ castRSComm` summands.

Each summand is packaged as a smooth `TensorRSField` via
`partialTraceSummand_smoothField`, which composes Part A's `contract_*_smoothField` helpers
with `castRSComm_smoothField`. The finite sum is smooth, and `congr_of_eventuallyEq` finishes.

NOTE: the core identity `(castRSComm_smoothField I M r s T) x = castRSComm I M r s x (T x)`
reflects that both sides are identity-transports of `T x` along the Nat-arith equation
`r + 1 = 1 + r`. Lean does not see them as definitionally equal (different `Eq.mpr` cast
structures), but they agree up to `HEq`; the main theorem handles this via a
`congr`-and-`eq_of_heq` step. -/

/-- The biorthogonal basis of `Tensor0SModel 1 ℝ E` used to build the dual frame `θ'`.
The `i`-th element corresponds to the coordinate functional `(finBasis ℝ E).coord i`,
promoted to a continuous linear functional on `E` and then curried to a
`ContinuousMultilinearMap (fun _ : Fin 1 => E) ℝ = Tensor0SModel 1 ℝ E`.

Implementation: `Module.Basis.dualBasis` produces a basis in `Module.Dual ℝ E` (linear
duals). We use `Module.Basis.map` along the composite equivalence
`(E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ) ≃ₗ[ℝ] Tensor0SModel 1 ℝ E` via
`LinearMap.toContinuousLinearMap` and `continuousMultilinearCurryFin1.symm`. -/
private noncomputable def dualCovectorBasis :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (Tensor0SModel 1 ℝ E) :=
  ((Module.finBasis ℝ E).dualBasis).map
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).trans
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearEquiv)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `dualCovectorBasis i` evaluated on a constant vector function equals the `i`-th coordinate
of that vector in the standard basis. -/
private lemma dualCovectorBasis_apply (i : Fin (Module.finrank ℝ E)) (w : E) :
    (dualCovectorBasis (E := E) i) (fun _ : Fin 1 => w) =
      (Module.finBasis ℝ E).coord i w := by
  unfold dualCovectorBasis
  rw [Module.Basis.map_apply]
  change (continuousMultilinearCurryFin1 ℝ E ℝ).symm
      ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))
        ((Module.finBasis ℝ E).dualBasis i)) (fun _ : Fin 1 => w) = _
  rw [continuousMultilinearCurryFin1_symm_apply]
  change ((Module.finBasis ℝ E).dualBasis i) w = (Module.finBasis ℝ E).coord i w
  rw [Module.Basis.dualBasis_apply, Module.Basis.coord_apply]

/-- A single summand of the partial-trace sum as a smooth `TensorRSField`. Takes a smooth
vector field `σ`, a smooth covector field `θ`, and a smooth `(r+1, s+1)` tensor field `T`,
and returns the smooth `(r, s)` tensor field whose pointwise value is
`contract_contravariant_first (θ x) (contract_covariant (σ x) (castRSComm (T x)))`.

Smoothness is inherited from Part A's smooth-field helpers. -/
private noncomputable def partialTraceSummand_smoothField (r s : ℕ)
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s :=
  contract_contravariant_first_smoothField I M r s θ
    (contract_covariant_smoothField I M (1 + r) s σ (castRSComm_smoothField I M r s T))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise value of `partialTraceSummand_smoothField`, by `rfl`. -/
private lemma partialTraceSummand_smoothField_apply (r s : ℕ)
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x : M) :
    (partialTraceSummand_smoothField I M r s σ θ T) x =
      Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x (θ x)
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x (σ x)
          ((castRSComm_smoothField I M r s T) x)) := rfl


/-! #### Smooth dual covector frame via the (0,1)-bundle's local frame.

Instead of attempting to show that `stdDualCovector I M · i` is a smooth section (which
involves reconciling `ofModel` with the bundle's `symmL`), we obtain a smooth dual frame by
calling `exists_contMDiffSection_eqOn_nhd` on the (0,1)-bundle's local frame for
`dualCovectorBasis`. The smooth frame `θ_smooth_i` equals `e_1.localFrame dualCovectorBasis i x`
on a neighborhood of `x₀`; biorthogonality with `σ' j` (the tangent-bundle local frame) then
follows from a direct computation on the base sets. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Biorthogonality of matching local frames.** Let `σ' j x = e_tan.localFrame b j x` and
`θ_smooth i x = e_1.localFrame dualCovectorBasis i x` on a neighborhood of `x₀`. Then on
`e_tan.baseSet ∩ e_1.baseSet`, we have
`(toModel (θ_smooth i x)) (fun _ => σ' j x) = if i = j then 1 else 0`. -/
private lemma matching_frames_biorth (x₀ : M) (x : M)
    (hx_tan : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hx_1 : x ∈ (trivializationAt (Tensor0SModel 1 ℝ E)
      (fun x => Tensor0SSpace 1 I x) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    (Tensor0SSpace.toModel
        ((trivializationAt (Tensor0SModel 1 ℝ E)
          (fun x => Tensor0SSpace 1 I x) x₀).localFrame (dualCovectorBasis (E := E)) i x))
        (fun _ : Fin 1 =>
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
            (Module.finBasis ℝ E) j x : TangentSpace I x)) =
      (if i = j then (1 : ℝ) else 0) := by
  -- Set up abbreviations.
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  set b := Module.finBasis (R := ℝ) (M := E)
  -- Step 1: rewrite localFrame as (linearEquivAt).symm on basis.
  rw [e_1.localFrame_apply_of_mem_baseSet (hx := hx_1)]
  rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hx_tan)]
  simp only [Trivialization.basisAt, Module.Basis.map_apply]
  -- LHS: toModel((e_1.linearEquivAt x hx_1).symm (dualCovectorBasis i))
  --   evaluated at (fun _ => (e_tan.linearEquivAt x hx_tan).symm (b j)).
  -- Use: `(e_1.linearEquivAt).symm M = e_1.symmL x M` on baseSet (definitionally).
  -- And `e_1.symmL x M = compCLM(e_tan.cLMA x) (M)` (via triv_symmL_eq).
  -- So LHS = toModel(compCLM(e_tan.cLMA x) (dualCovectorBasis i)) eval at ... .
  -- This requires evaluating via Tensor0SSpace.toModel (which is the plain bundle round-trip).
  -- Alternate: use the direct relationship between e_tan.linearEquivAt and (e_1.linearEquivAt).
  -- For the tensor0S bundle, (e_1.linearEquivAt ℝ x).symm M = ContMLM.compCLM M (e_tan.cLMA x).
  -- Then toModel((e_1.linearEquivAt).symm M) = M — not directly. Let's compute via Tensor0SSpace.toModel_ofModel.
  -- We only need a direct calculation of the applied value.
  have h_toModel_symm : ∀ (M : Tensor0SModel 1 ℝ E) (v : Fin 1 → TangentSpace I x),
      (Tensor0SSpace.toModel
        ((e_1.linearEquivAt ℝ x hx_1).symm M) : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ)
        v =
      M (fun i => e_tan.continuousLinearMapAt ℝ x (v i)) := by
    intro M v
    -- (e_1.linearEquivAt ℝ x hx_1).symm M = e_1.symmL x M on baseSet.
    have h_symm_eq : ((e_1.linearEquivAt ℝ x hx_1).symm M : Tensor0SSpace 1 I x) =
        e_1.symmL ℝ x M := by
      rfl
    rw [h_symm_eq]
    -- e_1.symmL x M = compCLM(e_tan.cLMA x) M via triv_symmL_eq.
    rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx_tan]
    -- toModel(compCLM(e_tan.cLMA x) M) applied at v = ?
    -- The issue: toModel is `tensor0SSpace_cle 1 x`, while compCLM is a different ContMLM.
    -- For the Tensor0S bundle, toModel of compCLM(CLMA)(M) evaluates by applying compCLM.
    rfl
  rw [h_toModel_symm (dualCovectorBasis i)
    (fun _ : Fin 1 => (e_tan.linearEquivAt ℝ x hx_tan).symm (b j))]
  -- Now RHS: dualCovectorBasis i (fun i => e_tan.cLMA x ((e_tan.linearEquivAt).symm (b j))).
  -- Use: e_tan.cLMA x ((e_tan.linearEquivAt).symm (b j)) = b j on baseSet (round-trip).
  have h_round : e_tan.continuousLinearMapAt ℝ x ((e_tan.linearEquivAt ℝ x hx_tan).symm (b j)) =
      b j := by
    change e_tan.linearMapAt ℝ x ((e_tan.linearEquivAt ℝ x hx_tan).symm (b j)) = b j
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
    change (e_tan.linearEquivAt ℝ x hx_tan) ((e_tan.linearEquivAt ℝ x hx_tan).symm (b j)) = b j
    rw [LinearEquiv.apply_symm_apply]
  -- Substitute h_round in the evaluation.
  have h_funext : (fun _k : Fin 1 => e_tan.continuousLinearMapAt ℝ x
        ((e_tan.linearEquivAt ℝ x hx_tan).symm (b j))) =
      (fun _ : Fin 1 => b j) := by
    funext k; exact h_round
  rw [h_funext]
  -- Goal: dualCovectorBasis i (fun _ => b j) = if i = j then 1 else 0.
  rw [dualCovectorBasis_apply]
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun heq => h heq.symm)]

set_option maxHeartbeats 2000000 in
-- The proof combines `contMDiffAt_section` with local-frame setups on both the tangent and
-- (0,1) bundles, and typeclass synthesis for the interacting bundle topologies exceeds the
-- default heartbeat limit; raise it for this single theorem.
omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- The main deliverable B.1: the pointwise contraction of a smooth tensor field is a smooth
section of the contracted tensor bundle.

The proof uses the local-frame formula `concreteTensorContract_fiber_local_formula`. We take:
* `σ'` obtained from the tangent bundle's local frame for `b := finBasis ℝ E`.
* `θ_smooth` obtained from the (0,1)-bundle's local frame for `dualCovectorBasis`.

Biorthogonality of `(σ' j, θ_smooth i)` on the intersection of base sets follows from
`matching_frames_biorth`. Each summand is a smooth section via `partialTraceSummand_smoothField`.
The sum-of-smooth-sections is smooth, and `congr_of_eventuallyEq` aligns it with the
pointwise contraction via `concreteTensorContract_fiber_local_formula`. -/
theorem concreteTensorContractField_fun_smooth_section (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x
        (concreteTensorContractField_fun I M r s (fun x => T x) x)) := by
  intro x₀
  -- Tangent bundle setup.
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀ with he_tan_def
  have he_tan_base : x₀ ∈ e_tan.baseSet := mem_baseSet_trivializationAt _ _ x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  have hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  obtain ⟨σ', hσ'⟩ := hframe_tan.exists_contMDiffSection_eqOn_nhd
    e_tan.open_baseSet he_tan_base
  -- (0,1)-bundle setup.
  set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
    with he_1_def
  have he_1_base : x₀ ∈ e_1.baseSet := mem_baseSet_trivializationAt _ _ x₀
  have hframe_1 := e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞))
    (dualCovectorBasis (E := E))
  obtain ⟨θ_smooth, hθ_smooth⟩ := hframe_1.exists_contMDiffSection_eqOn_nhd
    e_1.open_baseSet he_1_base
  -- Biorthogonality of `(σ' j, θ_smooth i)` near x₀.
  let θ' : Fin (Module.finrank ℝ E) → (x : M) → Tensor0SSpace 1 I x :=
    fun i x => (θ_smooth i) x
  have hθ'_biorth : ∀ᶠ x in 𝓝 x₀, ∀ i j,
      (Tensor0SSpace.toModel (θ' i x)) (fun _ => ((σ' j) x : TangentSpace I x)) =
        (if i = j then (1 : ℝ) else 0) := by
    filter_upwards [hσ', hθ_smooth, e_tan.open_baseSet.mem_nhds he_tan_base,
      e_1.open_baseSet.mem_nhds he_1_base]
      with x hσ'x hθ_smoothx hx_tan hx_1 i j
    change (Tensor0SSpace.toModel ((θ_smooth i) x)) (fun _ => ((σ' j) x : TangentSpace I x)) = _
    rw [hσ'x j, hθ_smoothx i]
    exact matching_frames_biorth I M x₀ x hx_tan hx_1 i j
  -- Apply the local-frame formula for concreteTensorContract_fiber.
  have h_formula := concreteTensorContract_fiber_local_formula I M r s (fun x => T x) x₀ σ' θ'
    hσ' hθ'_biorth
  -- Work at the pointwise section level (not trivialized).  This avoids the issue of
  -- distributing the trivialization through a sum.
  -- Reduce to contMDiff of the sum of smooth sections via extensional equality.
  -- We use: (∑_i partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T).toFun = concreteTensorContractField_fun I M r s T
  -- on a neighborhood of x₀, via h_formula.
  have h_sum_field : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x
        ((∑ i, partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) x)) := by
    exact (∑ i, partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T).contMDiff
  -- Now use congr_of_eventuallyEq to transfer smoothness through the formula.
  refine (h_sum_field x₀).congr_of_eventuallyEq ?_
  filter_upwards [h_formula] with x hx
  -- Need: TotalSpace.mk' _ x ((∑_i partialTraceSummand _) x) =
  --       TotalSpace.mk' _ x (concreteTensorContractField_fun _ x).
  -- Since TotalSpace.mk' is defined by `⟨x, v⟩`, this reduces to equality of the 2nd component.
  congr 1
  -- Now goal: (∑ i, partialTraceSummand_smoothField _ _ _ _ _ T) x =
  --          concreteTensorContractField_fun _ _ _ _ T x.
  -- Evaluate both sides.
  rw [concreteTensorContractField_fun_apply]
  rw [hx]
  -- Goal: (∑ i, partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) x =
  --        ∑ i, [expressions involving σ', θ', castRSComm, T].
  -- Use that `(∑ i, S_i).toFun x = ∑ i, (S_i).toFun x` and the apply lemma.
  simp only [ContMDiffSection.finset_sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [partialTraceSummand_smoothField_apply]
  -- partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T x =
  --   contract_contravariant_first (θ_smooth i x) (contract_covariant (σ' i x) (castRSComm_smoothField T x)).
  -- From h_formula: contract_contravariant_first (θ' i x) (contract_covariant (σ' i x) (castRSComm I M r s x (T x))).
  -- These differ by: castRSComm_smoothField T x vs castRSComm I M r s x (T x). Use the apply lemma.
  rw [castRSComm_smoothField_apply]

/-- The field-level packaging (B.2). -/
noncomputable def concreteTensorContractField (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1)) :
    TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s :=
  ⟨concreteTensorContractField_fun I M r s (fun x => T x),
   concreteTensorContractField_fun_smooth_section I M r s T⟩

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- The apply lemma (B.3). -/
@[simp] theorem concreteTensorContractField_apply (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x : M) :
    concreteTensorContractField I M r s T x = concreteTensorContract_fiber I M r s x (T x) := rfl

/-! ### Substep 4: Phase 3a reductions for `concrete_nabla_contract_comm`

At a fixed base point `x₀`, we set up a smooth tangent local frame `σ'` and a smooth (0,1)
local frame `θ_smooth`, then reduce both sides of the commutation theorem to a finite sum
indexed by the frame. These private lemmas are consumed by the Substep 6 closing step, where
the summand-level equality is established via the Hom-bundle product rule and Christoffel
cancellation. -/

open TensorRSNabla in
/-- The `i`-th summand on the LHS of `concrete_nabla_contract_comm`: the covariant derivative
of the `i`-th smooth partial-trace summand, evaluated at `x₀` in direction `X x₀`. -/
private noncomputable def LHS_summand
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) : TensorRSSpace r s I x₀ :=
  tensorRSCovariantDerivative I M r s cov
    (partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) x₀ (X x₀)

open TensorRSNabla in
/-- The `i`-th summand on the RHS of `concrete_nabla_contract_comm`: the fiber-level
partial-trace summand applied to `(∇_X T)` at `x₀`. -/
private noncomputable def RHS_summand
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) : TensorRSSpace r s I x₀ :=
  Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x₀ ((θ_smooth i) x₀)
    (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x₀ ((σ' i) x₀)
      (castRSComm I M r s x₀
        (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀))))

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Frame setup.** At any base point `x₀`, there exist smooth local frames `σ'` (tangent)
and `θ_smooth` (dual, as smooth (0,1) sections) satisfying all the `∀ᶠ`-hypotheses needed to
apply `concreteTensorContract_fiber_local_formula`. -/
private lemma concrete_nabla_contract_comm_frames_exist (x₀ : M) :
    ∃ (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (θ_smooth : Fin (Module.finrank ℝ E) →
        Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1),
      (∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
          (Module.finBasis ℝ E) i x) ∧
      (∀ᶠ x in 𝓝 x₀, ∀ i,
        (θ_smooth i) x =
          (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
            (dualCovectorBasis (E := E)) i x) := by
  -- Tangent bundle setup.
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he_tan_base : x₀ ∈ e_tan.baseSet := mem_baseSet_trivializationAt _ _ x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  have hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  obtain ⟨σ', hσ'⟩ := hframe_tan.exists_contMDiffSection_eqOn_nhd
    e_tan.open_baseSet he_tan_base
  -- (0,1)-bundle setup.
  set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  have he_1_base : x₀ ∈ e_1.baseSet := mem_baseSet_trivializationAt _ _ x₀
  have hframe_1 := e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞))
    (dualCovectorBasis (E := E))
  obtain ⟨θ_smooth, hθ_smooth⟩ := hframe_1.exists_contMDiffSection_eqOn_nhd
    e_1.open_baseSet he_1_base
  exact ⟨σ', θ_smooth, hσ', hθ_smooth⟩

set_option maxHeartbeats 2000000 in
-- The proof combines the Substep 2b local formula, a covariant-derivative congruence via
-- `congr_of_eventuallyEq`, and a Finset induction distributing `cov` over the sum. The
-- number of typeclass-resolution steps across `TensorRSField`, `ContMDiffSection`, and the
-- induced covariant-derivative bundle exceeds the default heartbeat limit.
open TensorRSNabla in
/-- **Part B: LHS reduction.** The covariant derivative of `concreteTensorContractField T` at
`x₀` in direction `X x₀` equals a finite sum of summands, each corresponding to one frame
index.

Uses:
1. `concreteTensorContractField` equals `∑ i, partialTraceSummand_smoothField ...` on a
   neighborhood of `x₀` (via Substep 2b's local formula + Substep 3's packaging).
2. Covariant derivative distributes over finite sum (via `.isCovariantDerivativeOnUniv.add`
   + Finset induction).
3. Each `cov (partialTraceSummand_smoothField ...) x₀ (X x₀)` equals `LHS_summand i` by
   definition. -/
private lemma concrete_nabla_contract_comm_lhs_as_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x₀ : M)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x)
    (hθ_smooth : ∀ᶠ x in 𝓝 x₀, ∀ i,
      (θ_smooth i) x =
        (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
          (dualCovectorBasis (E := E)) i x) :
    tensorRSCovariantDerivative I M r s cov (concreteTensorContractField I M r s T) x₀ (X x₀) =
      ∑ i, LHS_summand I M cov X r s T σ' θ_smooth x₀ i := by
  classical
  -- Abbreviate the induced covariant derivative on the (r,s)-tensor bundle.
  set covRS := tensorRSCovariantDerivative I M r s cov with hcovRS_def
  -- Abbreviate each summand section and the total summed section.
  set f : Fin (Module.finrank ℝ E) →
      TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s :=
    fun i => partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T with hf_def
  -- The summed smooth section.
  set f_sum : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s :=
    ∑ i, f i with hf_sum_def
  -- The pointwise family (Pi.add form) of the summed section.
  set f_pi : Π x : M, TensorRSSpace r s I x :=
    fun x => ∑ i, (f i) x with hf_pi_def
  -- Step 1: biorthogonality of (σ' i, θ_smooth i) near x₀.
  let θ' : Fin (Module.finrank ℝ E) → Π x : M, Tensor0SSpace 1 I x :=
    fun i x => (θ_smooth i) x
  have e_tan_base : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have e_1_base : x₀ ∈ (trivializationAt (Tensor0SModel 1 ℝ E)
      (fun x => Tensor0SSpace 1 I x) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have hθ'_biorth : ∀ᶠ x in 𝓝 x₀, ∀ i j,
      (Tensor0SSpace.toModel (θ' i x)) (fun _ => ((σ' j) x : TangentSpace I x)) =
        (if i = j then (1 : ℝ) else 0) := by
    filter_upwards [hσ', hθ_smooth,
      (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds e_tan_base,
      (trivializationAt (Tensor0SModel 1 ℝ E)
        (fun x => Tensor0SSpace 1 I x) x₀).open_baseSet.mem_nhds e_1_base]
      with x hσ'x hθ_smoothx hx_tan hx_1 i j
    change (Tensor0SSpace.toModel ((θ_smooth i) x)) (fun _ =>
      ((σ' j) x : TangentSpace I x)) = _
    rw [hσ'x j, hθ_smoothx i]
    exact matching_frames_biorth I M x₀ x hx_tan hx_1 i j
  -- Step 2: local-frame formula for concreteTensorContract_fiber.
  have h_formula :=
    concreteTensorContract_fiber_local_formula I M r s (fun x => T x) x₀ σ' θ' hσ' hθ'_biorth
  -- Step 3: show the smooth section `f_sum` agrees with `concreteTensorContractField T`
  -- on a neighborhood of x₀.
  have h_sections_eq : ∀ᶠ x in 𝓝 x₀,
      (concreteTensorContractField I M r s T) x = f_sum x := by
    filter_upwards [h_formula] with x hx
    rw [concreteTensorContractField_apply, hx]
    rw [hf_sum_def, ContMDiffSection.finset_sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf_def, partialTraceSummand_smoothField_apply, castRSComm_smoothField_apply]
  -- Step 4: mdifferentiability of the two sections at x₀.
  have h_lhs_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x
          ((concreteTensorContractField I M r s T) x)) x₀ :=
    (concreteTensorContractField I M r s T).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have h_sum_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (f_sum x)) x₀ :=
    f_sum.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- Step 5: use congr_of_eventuallyEq to replace concreteTensorContractField by the smooth sum.
  have h_cov_congr :
      covRS (concreteTensorContractField I M r s T) x₀ =
        covRS (fun x => f_sum x) x₀ := by
    refine covRS.isCovariantDerivativeOn.congr_of_eventuallyEq
      h_lhs_mdiff h_sum_mdiff (s := Set.univ) (by simp) ?_
    exact h_sections_eq
  -- Apply to (X x₀).
  have h_step5 :
      covRS (concreteTensorContractField I M r s T) x₀ (X x₀) =
        covRS (fun x => f_sum x) x₀ (X x₀) := by
    rw [h_cov_congr]
  rw [h_step5]
  -- Step 6: transform the summed ContMDiffSection into pointwise (Pi.add) form.
  have h_toPi : (fun x => f_sum x) = f_pi := by
    funext x
    rw [hf_sum_def, ContMDiffSection.finset_sum_apply]
  rw [h_toPi]
  -- Step 7: distribute covRS over the finite sum by Finset induction.
  -- We work at the level of Pi-functions; each individual summand f i is mdifferentiable.
  have h_each_mdiff : ∀ i,
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x ((f i) x)) x₀ :=
    fun i => (f i).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- Helper: mdifferentiability of a partial finset sum.
  have h_partial_mdiff : ∀ (t : Finset (Fin (Module.finrank ℝ E))),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (∑ i ∈ t, (f i) x)) x₀ := by
    intro t
    induction t using Finset.induction with
    | empty =>
      simp only [Finset.sum_empty]
      exact mdifferentiableAt_zeroSection
        (𝕜 := ℝ) (E := fun x : M => TensorRSSpace r s I x) (F := TensorRSModel r s ℝ E)
    | insert k t hkt ih =>
      have hk := h_each_mdiff k
      have hma := mdifferentiableAt_add_section (F := TensorRSModel r s ℝ E) hk ih
      refine hma.congr_of_eventuallyEq ?_
      filter_upwards with x
      change TotalSpace.mk' (TensorRSModel r s ℝ E) x _ =
        TotalSpace.mk' (TensorRSModel r s ℝ E) x _
      congr 1
      rw [Finset.sum_insert hkt]
      rfl
  -- Finset induction on the universal finset.
  suffices h_sum_rule : ∀ (t : Finset (Fin (Module.finrank ℝ E))),
      covRS (fun x => ∑ i ∈ t, (f i) x) x₀ (X x₀) =
      ∑ i ∈ t, covRS (fun x => (f i) x) x₀ (X x₀) by
    -- Apply at the universal finset.
    have hgoal := h_sum_rule Finset.univ
    -- Both sums are `∑ i : Fin _, ...` which is by definition `∑ i ∈ Finset.univ, ...`.
    -- LHS of `hgoal`: `covRS (fun x => ∑ i ∈ univ, f i x)`; this is the same as
    -- `covRS f_pi` since `f_pi x = ∑ i, f i x = ∑ i ∈ univ, f i x`.
    -- RHS of `hgoal`: `∑ i ∈ univ, covRS ...`; this is definitionally `∑ i, LHS_summand ...`.
    exact hgoal
  -- Prove the sum rule by Finset induction.
  intro t
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have : covRS (fun _ : M => (0 : TensorRSSpace r s I _)) x₀ = 0 :=
      covRS.isCovariantDerivativeOn.zero (hx := Set.mem_univ _)
    rw [this]; rfl
  | insert k t hkt ih =>
    -- `fun x => ∑ i ∈ insert k t, f i x = (fun x => f k x) + (fun x => ∑ i ∈ t, f i x)` (Pi.add).
    have h_add_fun : (fun x : M => ∑ i ∈ insert k t, (f i) x) =
        (fun x => (f k) x) + (fun x => ∑ i ∈ t, (f i) x) := by
      ext x; rw [Finset.sum_insert hkt]; rfl
    rw [h_add_fun]
    have hk_mdiff := h_each_mdiff k
    have h_rest_mdiff := h_partial_mdiff t
    rw [covRS.isCovariantDerivativeOn.add hk_mdiff h_rest_mdiff]
    simp only [ContinuousLinearMap.add_apply]
    rw [ih, Finset.sum_insert hkt]

open TensorRSNabla in
/-- **Part C: RHS reduction.** The fiber contraction of `(∇_X T)` at `x₀` equals a finite
sum, each term corresponding to one frame index. Uses Substep 2a's fiber-level basis
invariance (`partial_trace_basis_invariant_at_fiber`) directly at `x = x₀`. -/
private lemma concrete_nabla_contract_comm_rhs_as_sum
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x₀ : M)
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hσ' : ∀ᶠ x in 𝓝 x₀, ∀ i, (σ' i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x)
    (hθ_smooth : ∀ᶠ x in 𝓝 x₀, ∀ i,
      (θ_smooth i) x =
        (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
          (dualCovectorBasis (E := E)) i x) :
    concreteTensorContract_fiber I M r s x₀
        (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀)) =
      ∑ i, RHS_summand I M cov X r s T σ' θ_smooth x₀ i := by
  classical
  -- Set up notation and extract pointwise values at x₀.
  set T_tilde : TensorRSSpace (r + 1) (s + 1) I x₀ :=
    tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀) with hT_tilde_def
  -- At x₀, (σ' i) x₀ and (θ_smooth i) x₀ agree with the trivialization local frames.
  have hσ'_at : ∀ i, (σ' i) x₀ =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x₀ := hσ'.self_of_nhds
  have hθ_smooth_at : ∀ i, (θ_smooth i) x₀ =
      (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis (E := E)) i x₀ := hθ_smooth.self_of_nhds
  -- Membership of x₀ in the base sets.
  have hx_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have hx_1 : x₀ ∈ (trivializationAt (Tensor0SModel 1 ℝ E)
      (fun x => Tensor0SSpace 1 I x) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  -- Biorthogonality at x₀.
  have h_biorth : ∀ i j,
      (Tensor0SSpace.toModel ((θ_smooth i) x₀)) (fun _ => ((σ' j) x₀ : TangentSpace I x₀)) =
        (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [hσ'_at j, hθ_smooth_at i]
    exact matching_frames_biorth I M x₀ x₀ hx_tan hx_1 i j
  -- Linear independence and spanning of {(σ' i) x₀ : Fin _ → TangentSpace I x₀}.
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  let le : TangentSpace I x₀ ≃ₗ[ℝ] E := e_tan.linearEquivAt ℝ x₀ hx_tan
  have hσ'_eq : ∀ i, (σ' i) x₀ = le.symm (b i) := by
    intro i
    rw [hσ'_at i]
    change e_tan.localFrame b i x₀ = le.symm (b i)
    rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hx_tan)]
    simp [Trivialization.basisAt, le]
  have h_linind : LinearIndependent ℝ (fun i => (σ' i) x₀) := by
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ' i) x₀) = (fun i => le.symm (b i)) := funext hσ'_eq
    rw [h2]; exact h1
  have h_span : Submodule.span ℝ (Set.range (fun i => (σ' i) x₀)) = ⊤ := by
    have h2 : (fun i => (σ' i) x₀) = (fun i => le.symm (b i)) := funext hσ'_eq
    rw [h2]
    rw [show Set.range (fun i => le.symm (b i)) =
        le.symm.toLinearMap '' Set.range b by
      ext w; simp [Set.mem_range, Set.mem_image]]
    rw [Submodule.span_image, b.span_eq]
    simp
  -- Apply the fiber-level basis-invariance theorem.
  have h_inv :=
    partial_trace_basis_invariant_at_fiber I M r s x₀
      (fun i => (σ' i) x₀) (fun i => (θ_smooth i) x₀)
      h_biorth ⟨h_linind, h_span⟩ T_tilde
  -- The target equation is h_inv.symm, modulo unfolding RHS_summand.
  rw [← h_inv]
  rfl

end TensorContractComm

end
