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

/-! ### Index-commutation cast `1 + r = r + 1` on `Tensor0SSpace`

The identity-cast bridge `Tensor0SSpace (1 + r) → Tensor0SSpace (r + 1)`.  This is the
OPPOSITE direction of `castRSComm` and services `slot0Insert_smoothField`'s `(1 + r)`-
output feeding into `tensor0SCovariantDerivative` at index `s.succ = r + 1` in
subsequent steps of the P26 commutation proof.
-/

/-- The identity CLM `Tensor0SSpace (1 + r) →L[ℝ] Tensor0SSpace (r + 1)`.
Because `1 + r = r + 1` as nats (propositionally, via `Nat.add_comm`), the
underlying carrier types agree after this identity-transport. -/
private noncomputable def castTensor0SComm (r : ℕ) (x : M) :
    Tensor0SSpace (1 + r) I x →L[ℝ] Tensor0SSpace (r + 1) I x := by
  rw [show 1 + r = r + 1 from by omega]
  exact ContinuousLinearMap.id ℝ _

/-- Helper: produce a `Tensor0SField` at index `k` from one at `1 + r`, given the
Nat-level equation `h : 1 + r = k`. This is the pointwise identity transport on the fibers.

Generalizing over `h` allows the apply lemma to close by `subst`. -/
private noncomputable def castTensor0SFieldGen (r : ℕ) (k : ℕ) (h : 1 + r = k)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r)) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) k := by
  subst h; exact α

/-- The identity cast `Tensor0SField (1+r) → Tensor0SField (r+1)`. This wraps
`castTensor0SFieldGen` at `k = r + 1` with proof `Nat.add_comm 1 r : 1 + r = r + 1`. -/
noncomputable def castTensor0SComm_smoothField (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r)) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) :=
  castTensor0SFieldGen I M r (r + 1) (Nat.add_comm 1 r) α

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Helper HEq lemma for `castTensor0SFieldGen`. -/
private theorem castTensor0SFieldGen_toFun_heq (r : ℕ) (k : ℕ) (h : 1 + r = k)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r)) :
    HEq (castTensor0SFieldGen I M r k h α).toFun α.toFun := by
  subst h
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Helper HEq lemma for `castTensor0SComm`'s pointwise action. -/
private theorem castTensor0SComm_apply_heq (r : ℕ) (x : M)
    (α : Tensor0SSpace (1 + r) I x) :
    HEq (castTensor0SComm I M r x α) α := by
  -- Mirrors `castRSComm_apply_heq`: `castTensor0SComm` is defined via `by rw`, which produces
  -- `Eq.mpr h (CLM.id target)`. Applying this to `α` yields an element of the target type
  -- which is HEq to `α`.
  change HEq ((by rw [show 1 + r = r + 1 from by omega]; exact ContinuousLinearMap.id ℝ _ :
    Tensor0SSpace (1 + r) I x →L[ℝ] Tensor0SSpace (r + 1) I x) α) α
  have hp : 1 + r = r + 1 := by omega
  have aux : ∀ (k : ℕ) (hpr : 1 + r = k)
      (ki : Tensor0SSpace (1 + r) I x →L[ℝ] Tensor0SSpace k I x),
      HEq ki (ContinuousLinearMap.id ℝ (Tensor0SSpace (1 + r) I x)) →
      HEq (ki α) α := by
    intro k hpr ki h
    subst hpr
    cases h
    rfl
  refine aux (r + 1) hp _ ?_
  have : ∀ (k : ℕ) (h : 1 + r = k),
      HEq ((by rw [h]; exact ContinuousLinearMap.id ℝ (Tensor0SSpace k I x) :
        Tensor0SSpace (1 + r) I x →L[ℝ] Tensor0SSpace k I x))
        (ContinuousLinearMap.id ℝ (Tensor0SSpace (1 + r) I x)) := by
    intro k h
    subst h
    rfl
  exact this (r + 1) hp

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise apply lemma for `castTensor0SComm_smoothField`. Both sides are identity
transports of `α x` along `1 + r = r + 1`, so they agree by HEq/proof-irrelevance. -/
@[simp] theorem castTensor0SComm_smoothField_apply (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r))
    (x : M) :
    (castTensor0SComm_smoothField I M r α) x = castTensor0SComm I M r x (α x) := by
  -- Both LHS and RHS are HEq to `α x`. We combine via `eq_of_heq`.
  apply eq_of_heq
  -- Step 1: LHS HEq α x.
  have hLHS : HEq ((castTensor0SComm_smoothField I M r α) x) (α x) := by
    unfold castTensor0SComm_smoothField
    have : ∀ (k : ℕ) (h : 1 + r = k),
        HEq (castTensor0SFieldGen I M r k h α).toFun α.toFun := by
      intro k h
      subst h
      rfl
    have h' := this (r + 1) (Nat.add_comm 1 r)
    have key : ∀ (k : ℕ) (h : 1 + r = k)
        (tf : ∀ y : M, Tensor0SSpace k I y),
        HEq tf α.toFun → HEq (tf x) (α.toFun x) := by
      intro k h tf heq
      subst h
      cases heq
      rfl
    exact key (r + 1) (Nat.add_comm 1 r) _ h'
  -- Step 2: RHS HEq α x.
  have hRHS : HEq (castTensor0SComm I M r x (α x)) (α x) := castTensor0SComm_apply_heq I M r x (α x)
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

/-! ### Substep 5: Phase 3b — per-index summand expansion

For each frame index `i`, we expand `LHS_summand i` using the Hom-bundle product-rule formula
`tensorRSCovariantDerivative_apply`. Applied to the `(0,r)`-test section `w`, the LHS summand
splits into an "outer" term (the `(0,s)`-covariant derivative of the partial-trace summand
contracted with `w`) and an "inner" term (the partial-trace summand applied to the
`(0,r)`-covariant derivative of `w`). No cancellation yet — that is deferred to Substep 6.

The RHS summand is already in a clean form — its definition directly exposes the
`(∇^{(r+1,s+1)}_X T)`-based expression that will be matched against the LHS "inner" term in
Substep 6. We record it here as a named `rfl`-unfold lemma so that Substep 6 has explicit
hooks. -/

open TensorRSNabla in
/-- The "outer" term of the LHS summand decomposition: the `(0,s)`-covariant derivative of
`y ↦ (partialTraceSummand_smoothField σ' i θ i T) y (w y)` at `x₀` in direction `X x₀`.
Depends on the choice of test section `w`. -/
private noncomputable def LHS_Term_outer
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) :
    Tensor0SSpace s I x₀ :=
  Tensor0SNabla.tensor0SCovariantDerivative I M s cov
    (fun y => (partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) y (w y))
    x₀ (X x₀)

open TensorRSNabla in
/-- The "inner" term of the LHS summand decomposition: the partial-trace summand at `x₀`
applied to the `(0,r)`-covariant derivative of `w` at `x₀` in direction `X x₀`. Depends on
the choice of test section `w`. -/
private noncomputable def LHS_Term_inner
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) :
    Tensor0SSpace s I x₀ :=
  (partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) x₀
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov (fun y => w y) x₀ (X x₀))

open TensorRSNabla in
/-- **Deliverable 5a.** Two-term decomposition of `LHS_summand i` via the Hom-bundle
product-rule formula `tensorRSCovariantDerivative_apply`. Evaluated against any smooth
`(0,r)`-test section `w`, the CLM `LHS_summand i : TensorRSSpace r s I x₀` splits as the
difference of the outer and inner terms. -/
private lemma LHS_summand_as_outer_inner
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) :
    LHS_summand I M cov X r s T σ' θ_smooth x₀ i (w x₀) =
      LHS_Term_outer I M cov X r s T σ' θ_smooth x₀ i w -
      LHS_Term_inner I M cov X r s T σ' θ_smooth x₀ i w := by
  unfold LHS_summand LHS_Term_outer LHS_Term_inner
  exact tensorRSCovariantDerivative_apply I M r s cov
    (partialTraceSummand_smoothField I M r s (σ' i) (θ_smooth i) T) w x₀ (X x₀)

open TensorRSNabla in
/-- **Deliverable 5b.** Structural unfolding of `RHS_summand i`. This is a `rfl`-apply lemma
providing Substep 6 an explicit hook to the `(∇^{(r+1,s+1)}_X T)`-based form of the RHS
summand, which is the clean expression that should equal `LHS_Term_inner` up to the
Christoffel corrections proved in Substep 6. -/
private lemma RHS_summand_unfold
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    RHS_summand I M cov X r s T σ' θ_smooth x₀ i =
      Tensor0SBundle.contract_contravariant_first (𝕜 := ℝ) r s x₀ ((θ_smooth i) x₀)
        (Tensor0SBundle.contract_covariant (𝕜 := ℝ) (1 + r) s x₀ ((σ' i) x₀)
          (castRSComm I M r s x₀
            (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀)))) := rfl

/-! ### Substep 6: D0 — Helper 2 (vector-contraction Leibniz rule for (0,s+1)-tensors)

The first key helper for the sum-level identity: given smooth `τ : Tensor0SField (s+1)` and
smooth vector field `σ`, the covariant derivative of the pointwise interior product
`y ↦ interior_product s y (σ y) (τ y)` is related to the covariant derivative of `τ` by the
product rule

  `cov_s (ι_σ τ) x₀ v (u) =
      (cov_{s+1} τ x₀ v) (Fin.cons (σ x₀) u)
    + (τ x₀) (Fin.cons (∇σ x₀ v) u)`

where `u : Fin s → TangentSpace I x₀`, `v = X x₀`.

The proof works by reducing to the generic Hom-bundle product rule
`homBundleCovariantDerivative_apply` applied to `curriedSection τ`. The key identity is
that applying the curried section at a vector gives the interior product. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `tensor0S_curry` evaluated: for τ : Tensor0SSpace (s+1), the Hom value at v equals
`interior_product s x v τ` in Tensor0SSpace s. This is a definitional unfolding. -/
private lemma tensor0S_curry_eq_interior_product (s : ℕ) (x : M)
    (τ : Tensor0SSpace (s+1) I x) (v : TangentSpace I x) :
    tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x τ v =
      Tensor0SBundle.interior_product (𝕜 := ℝ) s x v τ := by
  -- Both sides unfold to
  --   (tensor0SSpace_cle s x).symm (model_interior_product s v ((tensor0SSpace_cle (s+1) x) τ))
  -- after expanding tensor0S_curry via `.trans`/`.arrowCongr` and
  -- model_interior_product via `continuousMultilinearCurryLeftEquiv`.
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Evaluation of `(tensor0S_curry).symm G` via `toModel`: the underlying multilinear map
evaluated at `Fin.cons v u` equals `toModel (G v)` applied to `u`. -/
private lemma toModel_tensor0S_curry_symm_cons (s : ℕ) (x : M)
    (G : TangentSpace I x →L[ℝ] Tensor0SSpace s I x)
    (v : TangentSpace I x) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x).symm G)
        (Fin.cons (v : E) u) =
      Tensor0SSpace.toModel (G v) u := by
  -- `tensor0S_curry.symm G` unfolds as
  --   cle_{s+1}.symm(curryLeftEquiv.symm(cle_s ∘ G))
  -- so `toModel(tensor0S_curry.symm G) = curryLeftEquiv.symm(cle_s ∘ G)`.
  -- Applied to `Fin.cons v u`, this is `((cle_s ∘ G) v) u = cle_s(G v)(u) = toModel(G v) u`.
  rfl

/-- The section-level identity: for τ : Tensor0SField (s+1) and σ : vector field, the
pointwise interior product `y ↦ interior_product s y (σ y) (τ y)` equals the section
`y ↦ (curriedSection τ y)(σ y)`. This is a pointwise equality of functions. -/
private lemma interior_product_eq_curriedSection_apply (s : ℕ)
    (τ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (s + 1))
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) s y (σ y) (τ y)) =
    (fun y => Tensor0SNabla.curriedSection I M (fun x => τ x) y (σ y)) := by
  funext y
  rw [Tensor0SNabla.curriedSection_apply]
  rw [tensor0S_curry_eq_interior_product]

/-- Smoothness of the `curriedSection τ` as a bundle section, given τ is a smooth
(0,s+1)-tensor field. Packaged as a `Cₛ^∞⟮...⟯` for feeding into
`homBundleCovariantDerivative_apply`. -/
private noncomputable def curriedSection_smoothSection (s : ℕ)
    (τ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (s + 1)) :
    Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)⟯ := by
  refine ⟨fun y => Tensor0SNabla.curriedSection I M (fun x => τ x) y, ?_⟩
  -- Smoothness via the bridge:
  --   τ is smooth (in bundle topology of Tensor0S (s+1)) → curriedSection τ is smooth
  --   (in bundle topology of Hom(TM, Tensor0S s)).
  apply (Tensor0SNabla.contMDiff_curriedSection_iff_section I M (fun x => τ x)).mp
  -- `τ` is smooth as a section by definition.
  exact τ.contMDiff

/-- Pointwise evaluation of `curriedSection_smoothSection`. -/
private lemma curriedSection_smoothSection_apply (s : ℕ)
    (τ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (s + 1)) (y : M) :
    (curriedSection_smoothSection I M s τ) y =
      Tensor0SNabla.curriedSection I M (fun x => τ x) y := rfl

set_option maxHeartbeats 2000000 in
-- Non-trivial chain of `tensor0S_curry` and Hom-bundle apply lemmas. The inner
-- `homBundleCovariantDerivative_apply` needs to resolve typeclasses for both `TangentSpace`
-- and `Tensor0SSpace s`, and the final `rfl`-chasing goes through multiple CLE layers;
-- the default heartbeat limit is insufficient.
/-- **Helper 2 (D0): Vector-contraction Leibniz rule.** For smooth τ : (0,s+1)-field and
smooth vector field σ, the product rule

  `∇^{(0,s)}_X (y ↦ interior_product τ σ) x₀ v (u) =
      (∇^{(0,s+1)}_X τ x₀ v) (Fin.cons (σ x₀) u)
    + (τ x₀) (Fin.cons (∇σ x₀ v) u)`

holds at every `x₀ : M`, `u : Fin s → TangentSpace I x₀`. The proof reduces via
`tensor0S_curry` to the generic Hom-bundle product rule. -/
private lemma tensor0S_apply_vector_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (s : ℕ)
    (τ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (s + 1))
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x₀ : M) (u : Fin s → TangentSpace I x₀) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s cov
          (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) s y (σ y) (τ y)) x₀ (X x₀)) u
      = Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s+1) cov
            (fun y => τ y) x₀ (X x₀)) (Fin.cons (σ x₀ : E) u)
        + Tensor0SSpace.toModel (τ x₀)
            (Fin.cons (cov σ x₀ (X x₀) : E) u) := by
  classical
  -- Step 1: let cov_s := tensor0SCovariantDerivative I M s cov.
  set cov_s := Tensor0SNabla.tensor0SCovariantDerivative I M s cov with hcov_s_def
  -- Step 2: build `curriedSection τ` as a smooth Hom-bundle section.
  let τ_hom := curriedSection_smoothSection I M s τ
  -- Step 3: rewrite LHS's functional argument: interior_product ↔ curriedSection apply.
  rw [show (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) s y (σ y) (τ y)) =
      (fun y => Tensor0SNabla.curriedSection I M (fun x => τ x) y (σ y)) from
        interior_product_eq_curriedSection_apply I M s τ σ]
  -- Step 4: Apply homBundleCovariantDerivative_apply.
  -- The Hom-bundle covariant derivative on Hom(TM, Tensor0SSpace s) agrees with the one used
  -- in tensor0SCovariantDerivative_succ via `HomConnection.homBundleCovariantDerivativeFun`.
  -- Specifically:
  --   (homBundleCovariantDerivative cov cov_s τ_hom x₀ v) (σ x₀)
  --     = cov_s (fun y => τ_hom y (σ y)) x₀ v - τ_hom x₀ (cov σ x₀ v)
  have h_hom_apply :
      (HomConnection.homBundleCovariantDerivative I M (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) cov cov_s τ_hom x₀ (X x₀))
        ((σ : Π x : M, TangentSpace I x) x₀) =
        cov_s (fun y => τ_hom y (σ y)) x₀ (X x₀) -
          τ_hom x₀ (cov σ x₀ (X x₀)) :=
    HomConnection.homBundleCovariantDerivative_apply I M (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) cov cov_s τ_hom σ x₀ (X x₀)
  -- Step 5: The Hom-bundle covariant derivative of `curriedSection τ` connects to
  -- `tensor0SCovariantDerivative_succ` via the apply formula.
  -- Specifically, `tensor0SCovariantDerivative (s+1) cov τ x₀ (X x₀)` =
  --   `(tensor0S_curry s x₀).symm (homBundleCovariantDerivativeFun (curriedSection τ) x₀ (X x₀))`.
  have h_succ_eq :
      Tensor0SNabla.tensor0SCovariantDerivative I M (s+1) cov (fun y => τ y) x₀ (X x₀) =
      (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x₀).symm
        (HomConnection.homBundleCovariantDerivativeFun I M (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) cov cov_s
          (Tensor0SNabla.curriedSection I M (fun y => τ y)) x₀ (X x₀)) := by
    rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_eq]
    rfl
  -- Step 6: apply `toModel` to both sides of `h_succ_eq` and evaluate at `Fin.cons (σ x₀) u`.
  -- Use `toModel_tensor0S_curry_symm_cons`:
  --   toModel((tensor0S_curry).symm G) (Fin.cons v u) = toModel(G v) u.
  have h_succ_eval :
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s+1) cov (fun y => τ y) x₀ (X x₀))
          (Fin.cons (σ x₀ : E) u) =
      Tensor0SSpace.toModel
          ((HomConnection.homBundleCovariantDerivativeFun I M (Tensor0SModel s ℝ E)
            (fun x : M => Tensor0SSpace s I x) cov cov_s
            (Tensor0SNabla.curriedSection I M (fun y => τ y)) x₀ (X x₀))
            (σ x₀)) u := by
    rw [h_succ_eq]
    exact toModel_tensor0S_curry_symm_cons I M s x₀ _ (σ x₀) u
  -- Step 7: Note homBundleCovariantDerivative = ⟨homBundleCovariantDerivativeFun, ...⟩,
  -- so `homBundleCovariantDerivative cov cov_s τ_hom x₀ v = homBundleCovariantDerivativeFun ... x₀ v`.
  -- Also `τ_hom y = curriedSection τ y` by `curriedSection_smoothSection_apply`.
  have h_hom_fun_eq :
      (HomConnection.homBundleCovariantDerivative I M (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) cov cov_s τ_hom x₀ (X x₀))
          ((σ : Π x : M, TangentSpace I x) x₀) =
      (HomConnection.homBundleCovariantDerivativeFun I M (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) cov cov_s
          (Tensor0SNabla.curriedSection I M (fun y => τ y)) x₀ (X x₀))
          ((σ : Π x : M, TangentSpace I x) x₀) := rfl
  -- Step 8: apply `toModel` to Step 4's identity and evaluate at u.
  --   toModel (homBundleCov τ_hom x₀ v (σ x₀)) u
  --     = toModel (cov_s (τ_hom · σ) x₀ v) u - toModel (τ_hom x₀ (cov σ x₀ v)) u.
  -- Note: τ_hom · σ = (fun y => (curriedSection τ y)(σ y)).
  have h_toModel_apply_eval :
      Tensor0SSpace.toModel
          ((HomConnection.homBundleCovariantDerivative I M (Tensor0SModel s ℝ E)
            (fun x : M => Tensor0SSpace s I x) cov cov_s τ_hom x₀ (X x₀))
            ((σ : Π x : M, TangentSpace I x) x₀)) u =
      Tensor0SSpace.toModel
          (cov_s (fun y => τ_hom y (σ y)) x₀ (X x₀)) u -
      Tensor0SSpace.toModel
          (τ_hom x₀ (cov σ x₀ (X x₀))) u := by
    rw [h_hom_apply, Tensor0SSpace.toModel_sub]
    rfl
  -- Step 9: relate τ_hom · σ to the pointwise interior product / curriedSection apply.
  -- Here τ_hom y (σ y) = curriedSection τ y (σ y) = tensor0S_curry s y (τ y)(σ y)
  --   = interior_product s y (σ y) (τ y). But we've already rewritten the LHS's argument to
  --   the curriedSection-apply form, so we just need `τ_hom y (σ y) = curriedSection τ y (σ y)`.
  have h_τhom_σ : (fun y => τ_hom y (σ y)) =
      (fun y => Tensor0SNabla.curriedSection I M (fun x => τ x) y (σ y)) := rfl
  rw [h_τhom_σ] at h_toModel_apply_eval
  -- Step 10: we also have τ_hom x₀ (cov σ x₀ (X x₀)) = curriedSection τ x₀ (cov σ x₀ (X x₀))
  --   = tensor0S_curry s x₀ (τ x₀) (cov σ x₀ (X x₀))
  --   = interior_product s x₀ (cov σ x₀ (X x₀)) (τ x₀).
  have h_τhom_at :
      τ_hom x₀ (cov σ x₀ (X x₀)) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) s x₀ (cov σ x₀ (X x₀)) (τ x₀) := by
    change Tensor0SNabla.curriedSection I M (fun x => τ x) x₀ (cov σ x₀ (X x₀)) = _
    rw [Tensor0SNabla.curriedSection_apply]
    exact tensor0S_curry_eq_interior_product I M s x₀ (τ x₀) (cov σ x₀ (X x₀))
  rw [h_τhom_at] at h_toModel_apply_eval
  -- Step 11: evaluate `toModel (interior_product s x₀ v' τ₀) u = toModel τ₀ (Fin.cons v' u)`.
  have h_ip_toModel : ∀ (v' : TangentSpace I x₀),
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) s x₀ v' (τ x₀)) u =
      Tensor0SSpace.toModel (τ x₀) (Fin.cons (v' : E) u) := by
    intro v'
    -- interior_product unfolds to (cle_s).symm (model_interior_product s v' (cle_{s+1} τ)).
    -- toModel(interior_product ...) = model_interior_product s v' (cle_{s+1} τ)
    --                              = (cle_{s+1} τ).curryLeft(v').
    -- Applied at u: (cle_{s+1} τ).curryLeft(v')(u) = (cle_{s+1} τ)(Fin.cons v' u) = toModel(τ)(Fin.cons v' u).
    rfl
  -- Step 12: combine everything. The LHS of the goal is `toModel(cov_s ... x₀ (X x₀)) u`.
  -- Using h_toModel_apply_eval:
  --   toModel(cov_s ... x₀ (X x₀)) u - toModel(interior_product ...) u
  --     = toModel(homBundleCov τ_hom x₀ (X x₀) (σ x₀)) u.
  -- i.e. toModel(cov_s ...) u = toModel(homBundleCov ...) u + toModel(interior_product ...) u.
  -- And by h_hom_fun_eq + h_succ_eval, the middle term equals
  --   toModel(∇^{(0,s+1)} τ x₀ (X x₀)) (Fin.cons (σ x₀) u).
  -- And by h_ip_toModel, the right term equals
  --   toModel(τ x₀) (Fin.cons (cov σ x₀ (X x₀)) u).
  have h_final : Tensor0SSpace.toModel
        (cov_s (fun y => Tensor0SNabla.curriedSection I M (fun x => τ x) y (σ y)) x₀ (X x₀)) u =
      Tensor0SSpace.toModel
          ((HomConnection.homBundleCovariantDerivative I M (Tensor0SModel s ℝ E)
            (fun x : M => Tensor0SSpace s I x) cov cov_s τ_hom x₀ (X x₀))
            ((σ : Π x : M, TangentSpace I x) x₀)) u +
      Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) s x₀ (cov σ x₀ (X x₀)) (τ x₀)) u := by
    rw [h_toModel_apply_eval]; abel
  rw [h_final]
  -- Now apply h_hom_fun_eq (Hom.Cov = Hom.Cov_Fun at our data) and h_succ_eval to rewrite
  -- the "homBundleCov" term as `toModel(∇^{(0,s+1)} τ x₀ (X x₀)) (Fin.cons (σ x₀) u)`.
  -- Also apply h_ip_toModel to rewrite the interior_product term.
  rw [h_hom_fun_eq, ← h_succ_eval]
  rw [h_ip_toModel]

/-! ### D2 — Helper 3 (biorthogonality Christoffel identity)

When `α` is a (0,1)-field and `σ` a vector field such that `α(σ)` is locally constant
near `x₀`, the sum `(∇α)(σ) + α(∇σ)` vanishes at `x₀` (evaluated on the unique Fin 1 →
TangentSpace I x₀ = constant-to-σ function). This is a direct consequence of Helper 2 at
`s = 0`: the (0,0)-covariant derivative of the locally constant scalar `α(σ)` is zero. -/

set_option maxHeartbeats 800000 in
-- Proof threads `scalarFn` / `tensor0Iso` / `extDerivFun` / `mfderiv_const` together; typeclass
-- resolution for `Tensor0SSpace 0` and `(0,1)`-tensor bundles in combination exceeds the default.
/-- **Helper 3 (D2): Biorthogonality Christoffel identity.** For α : (0,1)-field, σ :
vector field with `α(σ) = c` (constant) near x₀, the sum `(∇α)(σ) + α(∇σ)` vanishes. -/
private lemma biorth_christoffel_identity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x₀ : M)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (c : ℝ)
    (h : ∀ᶠ y in 𝓝 x₀, (Tensor0SSpace.toModel (α y)) (fun _ => σ y) = c) :
    (Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)))
      (fun _ => σ x₀)
      + (Tensor0SSpace.toModel (α x₀))
        (fun _ => (cov σ x₀ (X x₀) : E))
      = 0 := by
  classical
  -- Let S := (fun y => interior_product 0 y (σ y) (α y)) : Π y, Tensor0SSpace 0 I y.
  -- scalarFn S y = toModel(α y)(fun _ => σ y) = c on the neighborhood of x₀.
  -- So cov_0 S x₀ (X x₀) = 0.
  -- By Helper 2 at s = 0:
  --   toModel(cov_0 S x₀ (X x₀)) u₀ = toModel(cov_1 α x₀ (X x₀)) (Fin.cons (σ x₀) u₀)
  --                                 + toModel(α x₀) (Fin.cons (cov σ x₀ (X x₀)) u₀)
  -- where u₀ : Fin 0 → TangentSpace I x₀ is the empty function.
  -- Since LHS = 0 (locally constant scalar), we get the desired identity.
  set u₀ : Fin 0 → TangentSpace I x₀ := Fin.elim0 with hu₀_def
  -- Apply Helper 2 at s = 0.
  have h_lei := tensor0S_apply_vector_leibniz I M cov X 0 α σ x₀ u₀
  -- Simplify `Fin.cons v u₀ = fun _ : Fin 1 => v`:
  -- In Fin 1, the unique index is 0, and Fin.cons v u₀ 0 = v (by Fin.cons_zero).
  have h_cons_σ : (Fin.cons (σ x₀ : E) u₀ : Fin 1 → E) = fun _ : Fin 1 => σ x₀ := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    · simp [Fin.cons_zero]
  have h_cons_covσ : (Fin.cons (cov σ x₀ (X x₀) : E) u₀ : Fin 1 → E) =
      fun _ : Fin 1 => cov σ x₀ (X x₀) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    · simp [Fin.cons_zero]
  rw [h_cons_σ, h_cons_covσ] at h_lei
  -- Show the LHS of Helper 2 (in h_lei) is zero: cov_0 of a locally constant section.
  -- By the s=0 apply formula: cov_0 S x v = (tensor0Iso).symm (extDerivFun(scalarFn S) x v).
  -- scalarFn S y = toModel(α y)(fun _ => σ y) (by definitional unfolding of interior_product at s=0).
  -- This is locally constant = c near x₀, so extDerivFun vanishes.
  -- Key: `scalarFn S =ᶠ[𝓝 x₀] c` for the (0,0)-section S := y ↦ interior_product σ(y) α(y).
  have h_scalar_const : Tensor0SNabla.scalarFn I M
      (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y)) =ᶠ[𝓝 x₀]
        (fun _ => c) := by
    filter_upwards [h] with y hy
    change (Tensor0SNabla.tensor0Iso I M y
      (Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y)) : ℝ) = c
    change ((continuousMultilinearCurryFin0 ℝ E ℝ)
      (Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y)))) = c
    rw [continuousMultilinearCurryFin0_apply]
    change ((Tensor0SSpace.toModel (α y)).curryLeft (σ y)) 0 = c
    rw [ContinuousMultilinearMap.curryLeft_apply]
    have h_cons_y : (Fin.cons (σ y : E) (0 : Fin 0 → E) : Fin 1 → E) = fun _ : Fin 1 => σ y := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      · rfl
    rw [h_cons_y]
    exact hy
  -- Using the s=0 apply formula, cov_0 S x₀ v = (tensor0Iso x₀).symm (extDerivFun(scalarFn S) x₀ v).
  have h_cov0_zero :
      Tensor0SNabla.tensor0SCovariantDerivative I M 0 cov
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y)) x₀ (X x₀) = 0 := by
    rw [Tensor0SNabla.tensor0SCovariantDerivative_apply_zero]
    -- Goal: (tensor0Iso x₀).symm (extDerivFun (scalarFn S) x₀ (X x₀)) = 0.
    -- Show extDerivFun (scalarFn S) x₀ (X x₀) = 0 via mfderiv congruence + mfderiv_const.
    -- extDerivFun g x v = (fromTangentSpace (g x)).toCLM (mfderiv g x v).
    have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) (Tensor0SNabla.scalarFn I M
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y))) x₀ =
        mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) x₀ := h_scalar_const.mfderiv_eq
    have h_const_val : Tensor0SNabla.scalarFn I M
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y)) x₀ = c :=
      h_scalar_const.eq_of_nhds
    -- Rewrite to extDerivFun of a constant, then use mfderiv_const.
    change (Tensor0SNabla.tensor0Iso I M x₀).symm
      (extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y))) x₀ (X x₀)) = 0
    -- Unfold extDerivFun via its abbrev.
    have h_arg_zero : extDerivFun (I := I) (Tensor0SNabla.scalarFn I M
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (σ y) (α y))) x₀ (X x₀) = 0 := by
      change (NormedSpace.fromTangentSpace _).toContinuousLinearMap
        (mfderiv I 𝓘(ℝ, ℝ) _ x₀ (X x₀)) = 0
      rw [h_mfderiv_eq]
      rw [mfderiv_const]
      rfl
    rw [h_arg_zero]
    exact map_zero _
  -- Substitute zero into h_lei's LHS.
  rw [h_cov0_zero] at h_lei
  rw [Tensor0SSpace.toModel_zero] at h_lei
  -- h_lei : 0 = toModel(cov_1 α x₀ (X x₀))(fun _ => σ x₀) + toModel(α x₀)(fun _ => cov σ x₀ (X x₀)).
  have h_zero_apply : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) u₀ = 0 := rfl
  rw [h_zero_apply] at h_lei
  linarith

/-! ### Substep 6.2 — Covariant Leibniz rule for `slot0Insert_smoothField`

This section proves that the `(0, 1+r)`-covariant derivative of a slot-0 insertion
`slot0Insert_smoothField r α β` obeys the bilinear Leibniz rule:
```
∇^{(0,1+r)}_X (y ↦ slot0Insert(α y, β y)) x₀ (X x₀)
  = slot0Insert (∇^{(0,1)}_X α x₀ (X x₀)) (β x₀)
  + slot0Insert (α x₀) (∇^{(0,r)}_X β x₀ (X x₀))
```

The proof relies on D0 (`tensor0S_apply_vector_leibniz`) as the main computational
engine, applied after casting the `(1+r)`-indexed input through
`castTensor0SComm_smoothField` to land in the `(s+1) = (r+1)` setting that matches D0's
signature. A helper vector field `V_field` extending an arbitrary tangent vector `w` at
`x₀` lets us evaluate both sides pointwise on an arbitrary `Fin.cons w u`. The
"∇ V_field" term arising from D0 cancels via the multilinearity structure of
`slot0Insert`. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- The `toModel` of `slot0Insert α β` (lives in `Tensor0SSpace (1+r)`) evaluated on
any `v : Fin (1+r) → E` satisfying the "first slot is constant = w" and "rest is u"
conditions factors as `(toModel α)(fun _ => w) * (toModel β)(u)`. Direct unfolding of the
underlying `modelProduct` structure. -/
private theorem toModel_slot0Insert_apply (r : ℕ) {y : M}
    (α' : Tensor0SSpace 1 I y) (β' : Tensor0SSpace r I y)
    (v : Fin (1 + r) → E) (w : E) (u : Fin r → E)
    (hv_first : v ∘ Fin.castAdd r = fun _ => w)
    (hv_rest : v ∘ Fin.natAdd 1 = u) :
    Tensor0SSpace.toModel (slot0Insert I M α' β') v =
      (Tensor0SSpace.toModel α') (fun _ => w) * (Tensor0SSpace.toModel β') u := by
  change (Bundle.continuousMultilinearMap.modelProduct 1 r
      (Tensor0SSpace.toModel α') (Tensor0SSpace.toModel β')) v = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [hv_first, hv_rest]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise interior product of the cast `slot0Insert_smoothField r α β` at a vector `w`
evaluated as a multilinear map on `u : Fin r → E` equals the scalar-multiplication formula
`(toModel α y)(fun _ => w) * (toModel β y)(u)`. This is the key fact exposing the scalar
structure of `slot0Insert` after casting to the `(r+1)`-indexed form, enabling the Leibniz
rule to reduce to a scalar-valued Leibniz on the product `(toModel α)(σ) · β`.

The proof threads the Nat-arith `1 + r = r + 1` through a `subst`-based generalization. -/
private theorem interior_product_cast_slot0Insert_toModel_apply (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (β : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
    (y : M) (w : TangentSpace I y) (u : Fin r → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) r y w
          ((castTensor0SComm_smoothField I M r (slot0Insert_smoothField I M r α β)) y)) u =
      (Tensor0SSpace.toModel (α y)) (fun _ => (w : E)) *
        (Tensor0SSpace.toModel (β y)) u := by
  -- Reduce the cast to `castTensor0SComm` at y, and reduce slot0Insert_smoothField to slot0Insert.
  rw [castTensor0SComm_smoothField_apply I M r (slot0Insert_smoothField I M r α β) y]
  rw [slot0Insert_smoothField_apply I M r α β y]
  -- `toModel (interior_product r y w T) u = (toModel T).curryLeft w u = (toModel T)(Fin.cons w u)`
  -- where `T : Tensor0SSpace (r+1) I y`. Here T = castTensor0SComm ... (slot0Insert α β).
  change ((Tensor0SSpace.toModel
      (castTensor0SComm I M r y (slot0Insert I M (α y) (β y)))).curryLeft
        (w : E)) u = _
  rw [ContinuousMultilinearMap.curryLeft_apply]
  -- Goal: toModel(castTensor0SComm ... (slot0Insert α β))(Fin.cons w u : Fin (r+1) → E)
  --     = α(fun _ => w) * β(u).
  -- Now we need to relate `toModel(castTensor0SComm ... t)(vk)` to `toModel t (v1r)` where
  -- `vk : Fin (r+1) → E` is HEq-transported to `v1r : Fin (1+r) → E`. The transport is
  -- via `Fin.cast` / subst on Nat-arith.
  -- Use a generalized subst lemma.
  have hp : 1 + r = r + 1 := Nat.add_comm 1 r
  -- We'll manipulate both sides under subst-equivalence.
  -- Define `v1r : Fin (1+r) → E` as the transported version of Fin.cons w u.
  let v1r : Fin (1 + r) → E := (Fin.cons (w : E) u : Fin (r + 1) → E) ∘ Fin.cast hp
  -- Claim 1: `toModel(castTensor0SComm ... t)(Fin.cons w u : Fin (r+1)) = toModel t (v1r)`.
  have claim1 : (Tensor0SSpace.toModel
      (castTensor0SComm I M r y (slot0Insert I M (α y) (β y))))
      (Fin.cons (w : E) u : Fin (r + 1) → E) =
    Tensor0SSpace.toModel (slot0Insert I M (α y) (β y)) v1r := by
    -- Generalize over k with h : 1 + r = k and over a function Fin k → E.
    have gen : ∀ (k : ℕ) (h : 1 + r = k)
        (t_k : Tensor0SSpace k I y) (t_1r : Tensor0SSpace (1 + r) I y),
        HEq t_k t_1r →
        ∀ (vk : Fin k → E),
        Tensor0SSpace.toModel t_k vk =
          Tensor0SSpace.toModel t_1r (vk ∘ Fin.cast h) := by
      intro k h t_k t_1r heq_t vk
      subst h
      cases heq_t
      rfl
    exact gen (r + 1) hp (castTensor0SComm I M r y (slot0Insert I M (α y) (β y)))
      (slot0Insert I M (α y) (β y))
      (castTensor0SComm_apply_heq I M r y (slot0Insert I M (α y) (β y)))
      (Fin.cons (w : E) u)
  rw [claim1]
  -- Goal: toModel(slot0Insert α β)(v1r) = α(fun _ => w) * β(u).
  -- Check the "first slot" and "rest" conditions of v1r.
  have h_first : v1r ∘ Fin.castAdd r = fun _ => (w : E) := by
    funext i
    fin_cases i
    rfl
  have h_rest : v1r ∘ Fin.natAdd 1 = u := by
    funext i
    -- v1r = Fin.cons w u ∘ Fin.cast hp.
    -- v1r (Fin.natAdd 1 i) = Fin.cons w u (Fin.cast hp (Fin.natAdd 1 i)) = Fin.cons w u (Fin.succ i) = u i
    -- (where the last step uses Fin.cons_succ).
    change (Fin.cons (w : E) u : Fin (r + 1) → E) (Fin.cast hp (Fin.natAdd 1 i)) = u i
    have : Fin.cast hp (Fin.natAdd 1 i) = Fin.succ i := by
      apply Fin.ext
      simp [Fin.cast, Fin.natAdd, Fin.succ, Nat.add_comm]
    rw [this]
    rw [Fin.cons_succ]
  exact toModel_slot0Insert_apply I M r (α y) (β y) v1r (w : E) u h_first h_rest

/-! #### Structural identity: transport of `∇^{(0,1+r)}` to `∇^{(0,r+1)}`.

Since `tensor0SCovariantDerivative I M k cov` is recursively defined on `k`, at `k = 1 + r`
Lean cannot reduce it without knowing the structure of `1 + r`. We provide an HEq-based
transport lemma relating `∇^{(0,1+r)}` applied to a `Tensor0SField (1+r)` section to
`∇^{(0,r+1)}` applied to the `(r+1)`-cast section. -/

set_option maxHeartbeats 800000 in
-- The `subst h` on the Nat-arith `1 + r = k` inside `gen` pushes typeclass resolution for
-- `Tensor0SSpace k` above the default budget; the additional heartbeats are required.
/-- HEq transport: the `(0,1+r)`-covariant derivative of a `(1+r)`-section at `x₀` (X x₀)
equals the `(0,r+1)`-covariant derivative of the cast section, up to the Nat-arith HEq. -/
private lemma tensor0SCovariantDerivative_cast_heq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r : ℕ)
    (Θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r))
    (x₀ : M) :
    HEq (Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov (fun y => Θ y) x₀ (X x₀))
        (Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov
          (fun y => castTensor0SComm_smoothField I M r Θ y) x₀ (X x₀)) := by
  -- Generalize over k : ℕ with h : 1 + r = k. After subst, both sides become the same.
  have gen : ∀ (k : ℕ) (h : 1 + r = k)
      (Θ' : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) k),
      HEq Θ.toFun Θ'.toFun →
      HEq (Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov (fun y => Θ y) x₀ (X x₀))
          (Tensor0SNabla.tensor0SCovariantDerivative I M k cov (fun y => Θ' y) x₀ (X x₀)) := by
    intro k h Θ' hfun
    subst h
    -- Now both sides have type Tensor0SSpace (1+r) I x₀; HEq becomes Eq.
    have h_funeq : (fun y => Θ y) = fun y => Θ' y := by
      have h_toFun : Θ.toFun = Θ'.toFun := eq_of_heq hfun
      funext y
      exact congr_fun h_toFun y
    rw [h_funeq]
  -- Apply gen with k := r + 1.
  refine gen (r + 1) (Nat.add_comm 1 r) (castTensor0SComm_smoothField I M r Θ) ?_
  -- Need HEq Θ.toFun (castTensor0SComm_smoothField I M r Θ).toFun.
  unfold castTensor0SComm_smoothField
  exact (castTensor0SFieldGen_toFun_heq I M r (r + 1) (Nat.add_comm 1 r) Θ).symm

/-! #### The main Leibniz rule for `slot0Insert_smoothField`. -/

set_option maxHeartbeats 2400000 in
-- This proof orchestrates: (i) the HEq transport `tensor0SCovariantDerivative_cast_heq` from
-- `(1+r)` to `(r+1)`, (ii) the Hom-bundle structure via `_succ_apply`, (iii) the Hom-Leibniz
-- rule, (iv) D0 / D2 for the auxiliary scalar derivative, and (v) bookkeeping of `Fin.cons`
-- decomposition via `Fin.cast`. Each layer pushes typeclass resolution above defaults. -/
/-- **Substep 6.2 main deliverable.** The `(0, 1+r)`-covariant derivative of the slot-0
insertion `y ↦ slot0Insert (α y) (β y)` obeys the bilinear Leibniz rule:

  `∇^{(0,1+r)}_X (slot0Insert α β) x₀ (X x₀)`
    = `slot0Insert (∇^{(0,1)}_X α x₀ (X x₀)) (β x₀)`
    + `slot0Insert (α x₀) (∇^{(0,r)}_X β x₀ (X x₀))`.

This is the key combinatorial identity feeding into the partial-trace commutation proof (P26). -/
private lemma slot0Insert_smoothField_cov_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (β : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
    (x₀ : M) :
    Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov
      (fun y => slot0Insert_smoothField I M r α β y) x₀ (X x₀)
    = slot0Insert I M
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)) (β x₀)
      + slot0Insert I M (α x₀)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r cov β x₀ (X x₀)) := by
  classical
  -- It suffices to prove equality after applying `castTensor0SComm I M r x₀`, since that CLM
  -- is HEq to the identity (hence injective on `Tensor0SSpace (1+r)`).
  apply eq_of_heq
  -- Chain of HEqs:
  --   LHS ≃heq castTensor0SComm LHS   (inverse HEq by castTensor0SComm_apply_heq)
  --   castTensor0SComm LHS = ∇^{(0,r+1)} (cast_field Θ) x₀ (X x₀)   (by transport)
  --   = [expression to be computed]
  --   = castTensor0SComm (slot0Insert(∇α,β)) + castTensor0SComm (slot0Insert(α,∇β))   [by sum/linearity]
  --   ≃heq slot0Insert(∇α,β) + slot0Insert(α,∇β) = RHS.
  -- We'll build this chain step by step.
  set Θ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (1 + r) :=
    slot0Insert_smoothField I M r α β with hΘ
  set Θ' : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) :=
    castTensor0SComm_smoothField I M r Θ with hΘ'
  -- Step A: cov_(1+r) Θ ≃heq cov_(r+1) Θ'.
  have h_transport :
      HEq (Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov (fun y => Θ y) x₀ (X x₀))
          (Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov (fun y => Θ' y) x₀ (X x₀)) :=
    tensor0SCovariantDerivative_cast_heq I M cov X r Θ x₀
  -- Step B: cov_(r+1) Θ' x₀ (X x₀) = [some element of Tensor0SSpace (r+1) I x₀].
  -- We compute it via D0 applied at `s = r`.
  set cov_r := Tensor0SNabla.tensor0SCovariantDerivative I M r cov with h_cov_r
  -- We compute `toModel(cov_(r+1) Θ' x₀ (X x₀))` applied to `Fin.cons w u : Fin (r+1) → E`
  -- for arbitrary `w, u`. The result is the sum of two scalar-product terms.
  have h_r_plus_1 :
    ∀ (w : E) (u : Fin r → E),
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov (fun y => Θ' y) x₀ (X x₀))
          (Fin.cons (w : E) u) =
        (Tensor0SSpace.toModel (α x₀)) (fun _ => w) *
          (Tensor0SSpace.toModel (cov_r β x₀ (X x₀))) u +
        (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)))
          (fun _ => w) *
          (Tensor0SSpace.toModel (β x₀)) u := by
    intro w u
    -- Obtain a smooth vector field Y with Y x₀ = w.
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ w
    -- Transfer: replace w with Y x₀.
    rw [show w = (Y : Π y : M, TangentSpace I y) x₀ from hY.symm]
    -- Apply D0 (tensor0S_apply_vector_leibniz) at s = r with τ = Θ', σ = Y.
    --   toModel(∇^{(0,r)}_X (y ↦ interior_product r y (Y y) (Θ' y)) x₀ (X x₀)) u
    --     = toModel(∇^{(0,r+1)}_X Θ' x₀ (X x₀)) (Fin.cons (Y x₀) u)
    --       + toModel(Θ' x₀)(Fin.cons (∇Y x₀ (X x₀)) u).
    have hD0 := tensor0S_apply_vector_leibniz I M cov X r Θ' Y x₀ u
    -- Rearrange to isolate the RHS we want.
    have h_isolate :
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov (fun y => Θ' y) x₀ (X x₀))
          (Fin.cons ((Y : Π y : M, TangentSpace I y) x₀ : E) u) =
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M r cov
            (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) r y (Y y) (Θ' y)) x₀ (X x₀)) u -
        Tensor0SSpace.toModel (Θ' x₀)
          (Fin.cons (cov Y x₀ (X x₀) : E) u) := by
      linarith [hD0]
    rw [h_isolate]
    -- Now simplify each term:
    -- Term 1: interior_product at each y is the scalar-multiplication `g_Y(y) • β(y)`.
    -- Term 2: Θ' x₀ evaluated on Fin.cons (∇Y x₀ (X x₀)) u factors as a scalar product.
    -- Set up g_Y and the section-equality.
    set g_Y : M → ℝ := fun y => (Tensor0SSpace.toModel (α y)) (fun _ => (Y y : E)) with h_gY_def
    have h_section_eq :
        (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) r y (Y y) (Θ' y)) =
          g_Y • (fun y => β y) := by
      funext y
      apply (Tensor0SSpace.toModel_injective (I := I) (x := y) (𝕜 := ℝ))
      apply ContinuousMultilinearMap.ext
      intro v_r
      rw [interior_product_cast_slot0Insert_toModel_apply I M r α β y (Y y) v_r]
      change _ = Tensor0SSpace.toModel (g_Y y • β y) v_r
      rw [Tensor0SSpace.toModel_smul]
      simp [g_Y]
    rw [h_section_eq]
    -- Apply the Leibniz rule for cov_r on the scalar-mult section.
    have hβ_mdiff := β.mdifferentiableAt (x := x₀)
    have hgY_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) g_Y x₀ := by
      -- g_Y = scalarFn of the interior product section.
      have h_scalar_eq :
          g_Y = Tensor0SNabla.scalarFn I M
            (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (Y y) (α y)) := by
        funext y
        change (Tensor0SSpace.toModel (α y)) (fun _ => (Y y : E)) =
          Tensor0SNabla.tensor0Iso I M y
            (Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (Y y) (α y))
        change _ = (continuousMultilinearCurryFin0 ℝ E ℝ)
          (Tensor0SSpace.toModel
            (Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (Y y) (α y)))
        rw [continuousMultilinearCurryFin0_apply]
        change _ = ((Tensor0SSpace.toModel (α y)).curryLeft (Y y)) 0
        rw [ContinuousMultilinearMap.curryLeft_apply]
        have h_cons_y : (Fin.cons (Y y : E) (0 : Fin 0 → E) : Fin 1 → E) = fun _ : Fin 1 => Y y := by
          funext i
          refine Fin.cases ?_ (fun j => Fin.elim0 j) i
          · rfl
        rw [h_cons_y]
      rw [h_scalar_eq]
      -- scalarFn of a smooth (0,0)-section is smooth ↔ the bundle-section is smooth.
      -- Use the bundle-smoothness of contract_Tensor0SField α Y.
      rw [Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section]
      -- Goal: MDifferentiableAt of the bundle-topology section `y ↦ ⟨y, interior_product 0 y (Y y) (α y)⟩`.
      -- This is the bundle section of `contract_Tensor0SField 0 α Y`.
      have h_ip_smooth := (contract_Tensor0SField (𝕜 := ℝ) (n := ∞) 0 α Y).contMDiff
      have h_mdiffAt := h_ip_smooth.contMDiffAt (x := x₀)
      exact h_mdiffAt.mdifferentiableAt (by norm_num)
    have h_cov_r_leibniz :
        cov_r (g_Y • fun y => β y) x₀ =
          g_Y x₀ • cov_r (fun y => β y) x₀ +
            (extDerivFun (I := I) g_Y x₀).smulRight ((fun y => β y) x₀) :=
      (Tensor0SNabla.tensor0SCovariantDerivative I M r cov).isCovariantDerivativeOnUniv.leibniz
        hβ_mdiff hgY_mdiff
    rw [h_cov_r_leibniz]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    -- Compute extDerivFun g_Y x₀ (X x₀) using D0 at s = 0.
    set S := fun y : M => Tensor0SBundle.interior_product (𝕜 := ℝ) 0 y (Y y) (α y) with h_S_def
    have h_gY_eq_scalar : g_Y = Tensor0SNabla.scalarFn I M S := by
      funext y
      change (Tensor0SSpace.toModel (α y)) (fun _ => (Y y : E)) =
        Tensor0SNabla.tensor0Iso I M y (S y)
      change _ = (continuousMultilinearCurryFin0 ℝ E ℝ)
        (Tensor0SSpace.toModel (S y))
      rw [continuousMultilinearCurryFin0_apply]
      change _ = ((Tensor0SSpace.toModel (α y)).curryLeft (Y y)) 0
      rw [ContinuousMultilinearMap.curryLeft_apply]
      have h_cons_y : (Fin.cons (Y y : E) (0 : Fin 0 → E) : Fin 1 → E) = fun _ : Fin 1 => Y y := by
        funext i
        refine Fin.cases ?_ (fun j => Fin.elim0 j) i
        · rfl
      rw [h_cons_y]
    have h_extDerivFun_gY :
        extDerivFun (I := I) g_Y x₀ (X x₀) =
          (Tensor0SSpace.toModel
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)))
            (fun _ => (Y x₀ : E)) +
          (Tensor0SSpace.toModel (α x₀))
            (fun _ => (cov Y x₀ (X x₀) : E)) := by
      have hD0_s0 := tensor0S_apply_vector_leibniz I M cov X 0 α Y x₀
        (Fin.elim0 : Fin 0 → TangentSpace I x₀)
      have h_cons_simp : ∀ (v' : E),
          (Fin.cons v' (Fin.elim0 : Fin 0 → E) : Fin 1 → E) = fun _ : Fin 1 => v' := by
        intro v'
        funext i
        refine Fin.cases ?_ (fun j => Fin.elim0 j) i
        · rfl
      rw [h_cons_simp, h_cons_simp] at hD0_s0
      have h_cov0 : (Tensor0SSpace.toModel
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 cov S x₀ (X x₀)))
            (Fin.elim0 : Fin 0 → E) = extDerivFun (I := I) g_Y x₀ (X x₀) := by
        rw [Tensor0SNabla.tensor0SCovariantDerivative_apply_zero]
        rw [h_gY_eq_scalar]
        change ((continuousMultilinearCurryFin0 ℝ E ℝ).symm
            (extDerivFun (I := I) (Tensor0SNabla.scalarFn I M S) x₀ (X x₀))) (Fin.elim0) = _
        rw [continuousMultilinearCurryFin0_symm_apply_apply]
      rw [h_cov0] at hD0_s0
      exact hD0_s0
    have h_gY_at : g_Y x₀ = (Tensor0SSpace.toModel (α x₀)) (fun _ => (Y x₀ : E)) := rfl
    -- Compute the Fin.cons (∇Y x₀ (X x₀)) u term on Θ' x₀.
    have h_cons_term :
        Tensor0SSpace.toModel (Θ' x₀) (Fin.cons (cov Y x₀ (X x₀) : E) u) =
          (Tensor0SSpace.toModel (α x₀)) (fun _ => (cov Y x₀ (X x₀) : E)) *
            (Tensor0SSpace.toModel (β x₀)) u := by
      -- Θ' x₀ = castTensor0SComm_smoothField r Θ at x₀; interior_product r y w (Θ' y)'s toModel
      -- factoring applies. Use Fin.cons = curryLeft inversion.
      have : (Tensor0SSpace.toModel (Θ' x₀)).curryLeft (cov Y x₀ (X x₀) : E) u =
          (Tensor0SSpace.toModel (α x₀)) (fun _ => (cov Y x₀ (X x₀) : E)) *
            (Tensor0SSpace.toModel (β x₀)) u := by
        change Tensor0SSpace.toModel
            (Tensor0SBundle.interior_product (𝕜 := ℝ) r x₀ (cov Y x₀ (X x₀)) (Θ' x₀)) u = _
        exact interior_product_cast_slot0Insert_toModel_apply I M r α β x₀
          (cov Y x₀ (X x₀)) u
      rw [← ContinuousMultilinearMap.curryLeft_apply]
      exact this
    rw [h_cons_term]
    rw [h_gY_at, h_extDerivFun_gY]
    -- Push toModel through the scalar-mult via toModel_smul + CMLM.smul_apply.
    rw [Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  -- Step D: extensionality in Tensor0SSpace (r+1) via toModel_injective + ext on Fin (r+1) → E.
  -- Show: cov_(r+1) Θ' x₀ (X x₀) = (castTensor0SComm I M r x₀) RHS_of_main.
  -- i.e., HEq cov_(r+1) ... (RHS in (1+r))... Actually we want:
  --   HEq LHS RHS, where LHS : Tensor0SSpace (1+r), RHS : Tensor0SSpace (1+r).
  -- From h_transport: LHS ≃heq cov_(r+1) Θ'.
  -- We construct: HEq cov_(r+1) Θ' RHS via: cov_(r+1) Θ' = castTensor0SComm RHS, and castTensor0SComm RHS ≃heq RHS.
  have h_rhs_cast :
      Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov (fun y => Θ' y) x₀ (X x₀) =
      castTensor0SComm I M r x₀
        (slot0Insert I M (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)) (β x₀)
         + slot0Insert I M (α x₀)
             (Tensor0SNabla.tensor0SCovariantDerivative I M r cov β x₀ (X x₀))) := by
    apply Tensor0SSpace.toModel_injective (I := I) (x := x₀) (𝕜 := ℝ)
    apply ContinuousMultilinearMap.ext
    intro v_r
    -- v_r : Fin (r+1) → E. Rewrite as Fin.cons w u where w = v_r 0, u = v_r ∘ Fin.succ.
    -- Use ContinuousMultilinearMap.cons_succ_ext-style reasoning.
    have h_decomp : v_r = Fin.cons (v_r 0) (fun i => v_r i.succ) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
    rw [h_decomp]
    rw [h_r_plus_1 (v_r 0) (fun i => v_r i.succ)]
    -- RHS: toModel(castTensor0SComm ... (S1 + S2)) (Fin.cons (v_r 0) ... ) = ...
    -- castTensor0SComm preserves addition (it's a CLM). toModel preserves addition.
    rw [map_add (castTensor0SComm I M r x₀)]
    simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    -- Now we have toModel(castTensor0SComm (slot0Insert(∇α) β))(Fin.cons w u)
    --           + toModel(castTensor0SComm (slot0Insert α (∇β)))(Fin.cons w u).
    -- Each term: toModel(castTensor0SComm(slot0Insert(A)(B)))(Fin.cons w u)
    --         = toModel(slot0Insert(A)(B))(v1r)  where v1r = Fin.cons w u ∘ Fin.cast.
    --         = A(fun _ => w) * B(u).
    -- Use `toModel_slot0Insert_apply` via the cast-lemma chain.
    have h_term : ∀ (A : Tensor0SSpace 1 I x₀) (B : Tensor0SSpace r I x₀)
        (w' : E) (u' : Fin r → E),
        Tensor0SSpace.toModel (castTensor0SComm I M r x₀ (slot0Insert I M A B))
          (Fin.cons (w' : E) u') =
          (Tensor0SSpace.toModel A) (fun _ => w') *
            (Tensor0SSpace.toModel B) u' := by
      intro A B w' u'
      -- Use the same HEq-cast reasoning.
      have hp : 1 + r = r + 1 := Nat.add_comm 1 r
      let v1r : Fin (1 + r) → E := (Fin.cons (w' : E) u' : Fin (r + 1) → E) ∘ Fin.cast hp
      have claim_cast :
          Tensor0SSpace.toModel
              (castTensor0SComm I M r x₀ (slot0Insert I M A B))
              (Fin.cons (w' : E) u' : Fin (r + 1) → E) =
            Tensor0SSpace.toModel (slot0Insert I M A B) v1r := by
        have gen : ∀ (k : ℕ) (h : 1 + r = k)
            (t_k : Tensor0SSpace k I x₀) (t_1r : Tensor0SSpace (1 + r) I x₀),
            HEq t_k t_1r →
            ∀ (vk : Fin k → E),
            Tensor0SSpace.toModel t_k vk =
              Tensor0SSpace.toModel t_1r (vk ∘ Fin.cast h) := by
          intro k h t_k t_1r heq_t vk
          subst h
          cases heq_t
          rfl
        exact gen (r + 1) hp (castTensor0SComm I M r x₀ (slot0Insert I M A B))
          (slot0Insert I M A B)
          (castTensor0SComm_apply_heq I M r x₀ (slot0Insert I M A B))
          (Fin.cons (w' : E) u')
      rw [claim_cast]
      have h_first : v1r ∘ Fin.castAdd r = fun _ => (w' : E) := by
        funext i
        fin_cases i
        rfl
      have h_rest : v1r ∘ Fin.natAdd 1 = u' := by
        funext i
        change (Fin.cons (w' : E) u' : Fin (r + 1) → E) (Fin.cast hp (Fin.natAdd 1 i)) = u' i
        have : Fin.cast hp (Fin.natAdd 1 i) = Fin.succ i := by
          apply Fin.ext
          simp [Fin.cast, Fin.natAdd, Fin.succ, Nat.add_comm]
        rw [this]
        rw [Fin.cons_succ]
      exact toModel_slot0Insert_apply I M r A B v1r (w' : E) u' h_first h_rest
    rw [h_term, h_term]
    ring
  -- h_rhs_cast : cov_(r+1) Θ' = castTensor0SComm ... RHS.
  -- Combined with h_transport: HEq cov_(1+r) Θ (castTensor0SComm RHS).
  -- Then HEq (castTensor0SComm RHS) RHS via castTensor0SComm_apply_heq. By transitivity, HEq LHS RHS.
  have h_heq_step1 :
      HEq (Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov (fun y => Θ y) x₀ (X x₀))
          (castTensor0SComm I M r x₀
            (slot0Insert I M (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)) (β x₀)
             + slot0Insert I M (α x₀)
                 (Tensor0SNabla.tensor0SCovariantDerivative I M r cov β x₀ (X x₀)))) := by
    rw [← h_rhs_cast]
    exact h_transport
  have h_heq_step2 :
      HEq (castTensor0SComm I M r x₀
            (slot0Insert I M (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)) (β x₀)
             + slot0Insert I M (α x₀)
                 (Tensor0SNabla.tensor0SCovariantDerivative I M r cov β x₀ (X x₀))))
          (slot0Insert I M (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov α x₀ (X x₀)) (β x₀)
           + slot0Insert I M (α x₀)
               (Tensor0SNabla.tensor0SCovariantDerivative I M r cov β x₀ (X x₀))) :=
    castTensor0SComm_apply_heq I M r x₀ _
  exact h_heq_step1.trans h_heq_step2

/-! ### Substep 6.3 — Frame-expansion lemmas and Christoffel sum cancellation

This section provides the algebraic engine consumed by Substep 6.4's `sum_eq` step:

* `tangent_expand_in_frame_at` : expansion of a tangent vector in a biorthogonal primal frame.
* `tensor0S1_expand_in_dualFrame_at` : expansion of a `(0,1)`-tensor in the dual frame.
* `christoffel_sum_zero` : the pointwise-cancellation identity for the two Christoffel sums.

All three are proved at the fiber level via `Module.Basis.mk` on the primal frame, paired with
D2 (`biorth_christoffel_identity`) for the sum cancellation. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Tangent-vector expansion in the primal frame.** Given a biorthogonal basis/dual pair
`(σ', θ)` at `x₀` with basis hypothesis, any tangent vector `v` expands as
`v = ∑_j θ_j(v) • σ'_j`. -/
private lemma tangent_expand_in_frame_at {x₀ : M}
    (v : TangentSpace I x₀)
    (σ' : Fin (Module.finrank ℝ E) → TangentSpace I x₀)
    (θ : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x₀)
    (h_biorth : ∀ i j, (Tensor0SSpace.toModel (θ i)) (fun _ : Fin 1 => σ' j) =
      (if i = j then (1 : ℝ) else 0))
    (h_basis : LinearIndependent ℝ σ' ∧ Submodule.span ℝ (Set.range σ') = ⊤) :
    v = ∑ j, (Tensor0SSpace.toModel (θ j)) (fun _ : Fin 1 => v) • σ' j := by
  classical
  -- Promote σ' to a `Module.Basis` of `TangentSpace I x₀` via `Module.Basis.mk`.
  let bPrime : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis.1 (le_of_eq h_basis.2.symm)
  have hb_apply : ∀ i, bPrime i = σ' i := fun i => Module.Basis.mk_apply _ _ _
  -- Claim: for each `j`, `bPrime.coord j = curriedDual I M x₀ θ j` as
  -- `TangentSpace I x₀ →ₗ[ℝ] ℝ` (using `TangentSpace = E` defeq).
  -- Both are linear functionals; check on basis via `bPrime.ext`.
  have h_lmap_eq : ∀ j, (bPrime.coord j : TangentSpace I x₀ →ₗ[ℝ] ℝ) =
      ((curriedDual I M x₀ θ j : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) := by
    intro j
    apply bPrime.ext
    intro i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [hb_apply]
    -- Goal: `Finsupp.single i 1 j = (curriedDual I M x₀ θ j : E →ₗ[ℝ] ℝ) (σ' i)`.
    -- RHS: coerce CLM to LinearMap, then evaluate.
    change Finsupp.single i 1 j = (curriedDual I M x₀ θ j) (σ' i)
    rw [curriedDual_apply, h_biorth, Finsupp.single_apply]
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun heq => h heq.symm)]
  -- Now use `bPrime.sum_repr` to expand `v`.
  have h_sum_repr : ∑ j, bPrime.repr v j • bPrime j = v := bPrime.sum_repr v
  -- Transform: `bPrime.repr v j = bPrime.coord j v = (toModel (θ j))(fun _ => v)`
  --           `bPrime j = σ' j`.
  calc v = ∑ j, bPrime.repr v j • bPrime j := h_sum_repr.symm
    _ = ∑ j, bPrime.coord j v • bPrime j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Module.Basis.coord_apply]
    _ = ∑ j, (Tensor0SSpace.toModel (θ j)) (fun _ : Fin 1 => v) • σ' j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        -- Goal: `bPrime.coord j v • bPrime j = (toModel (θ j))(fun _ => v) • σ' j`.
        -- Use `h_lmap_eq` applied at `v`, plus `hb_apply` for bPrime j.
        have hf_eq : (bPrime.coord j) v = (curriedDual I M x₀ θ j) v := by
          rw [show (bPrime.coord j) v = (bPrime.coord j : TangentSpace I x₀ →ₗ[ℝ] ℝ) v from rfl]
          rw [h_lmap_eq j]
          rfl
        rw [hf_eq, curriedDual_apply, hb_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **(0,1)-tensor expansion in the dual frame.** Given a biorthogonal basis/dual pair
`(σ', θ)` at `x₀` with basis hypothesis, any `α : Tensor0SSpace 1 I x₀` expands as
`α = ∑_j toModel(α)(fun _ => σ'_j) • θ_j`. -/
private lemma tensor0S1_expand_in_dualFrame_at {x₀ : M}
    (α : Tensor0SSpace 1 I x₀)
    (σ' : Fin (Module.finrank ℝ E) → TangentSpace I x₀)
    (θ : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x₀)
    (h_biorth : ∀ i j, (Tensor0SSpace.toModel (θ i)) (fun _ : Fin 1 => σ' j) =
      (if i = j then (1 : ℝ) else 0))
    (h_basis : LinearIndependent ℝ σ' ∧ Submodule.span ℝ (Set.range σ') = ⊤) :
    α = ∑ j, (Tensor0SSpace.toModel α) (fun _ : Fin 1 => σ' j) • θ j := by
  classical
  -- Reduce to equality of `Tensor0SModel 1 ℝ E = ContinuousMultilinearMap ℝ (Fin 1 → E) ℝ`.
  apply Tensor0SSpace.toModel_injective (I := I) (x := x₀) (𝕜 := ℝ)
  -- Push `toModel` through the sum on the RHS via `toModelL` (the bundled CLM).
  change Tensor0SSpace.toModel α =
    Tensor0SSpace.toModel (∑ j, (Tensor0SSpace.toModel α) (fun _ : Fin 1 => σ' j) • θ j)
  rw [show (Tensor0SSpace.toModel
        (∑ j, (Tensor0SSpace.toModel α) (fun _ : Fin 1 => σ' j) • θ j) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) =
      ∑ j, Tensor0SSpace.toModel
        ((Tensor0SSpace.toModel α) (fun _ : Fin 1 => σ' j) • θ j) from
    map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) 1 x₀) _ _]
  simp only [Tensor0SSpace.toModel_smul]
  -- Reduce to pointwise equality on `v : Fin 1 → E`.
  apply ContinuousMultilinearMap.ext
  intro v
  -- `v = fun _ => v 0`.
  have h_v : v = fun _ : Fin 1 => v 0 := by
    funext k
    fin_cases k
    rfl
  rw [h_v]
  -- Expand `v 0 : TangentSpace I x₀` using Deliverable 1.
  have h_v0 : (v 0 : TangentSpace I x₀) =
      ∑ j, (Tensor0SSpace.toModel (θ j)) (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j :=
    tangent_expand_in_frame_at I M (v 0 : TangentSpace I x₀) σ' θ h_biorth h_basis
  -- LHS: `(toModel α) (fun _ => v 0)`. Expand via `h_v0` and push through multilinearity.
  -- RHS: `(∑_j (toModel α)(fun _ => σ' j) • toModel (θ j)) (fun _ => v 0)`
  --    = `∑_j (toModel α)(fun _ => σ' j) • (toModel (θ j))(fun _ => v 0)`.
  rw [ContinuousMultilinearMap.sum_apply]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  -- Goal: `(toModel α)(fun _ => v 0) =
  --        ∑ j, (toModel α)(fun _ => σ' j) * (toModel (θ j))(fun _ => v 0)`.
  -- Step 1: Rewrite `v 0` using `h_v0`.
  conv_lhs => rw [show (v 0 : TangentSpace I x₀) =
      ∑ j, (Tensor0SSpace.toModel (θ j))
        (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j from h_v0]
  -- Step 2: `(toModel α)(fun _ => ∑_j c_j • σ' j)` via update + map_update_sum.
  have h_update : (fun _ : Fin 1 => (∑ j,
        (Tensor0SSpace.toModel (θ j))
          (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j : TangentSpace I x₀)) =
      Function.update (fun _ : Fin 1 => (0 : E)) 0 (∑ j,
        (Tensor0SSpace.toModel (θ j))
          (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j) := by
    funext k; fin_cases k; simp
  rw [h_update]
  rw [show (Tensor0SSpace.toModel α) (Function.update (fun _ : Fin 1 => (0 : E)) 0
        (∑ j, (Tensor0SSpace.toModel (θ j))
          (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j)) =
      ∑ j, (Tensor0SSpace.toModel α) (Function.update (fun _ : Fin 1 => (0 : E)) 0
        ((Tensor0SSpace.toModel (θ j))
          (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j)) from
    (Tensor0SSpace.toModel α).toMultilinearMap.map_update_sum
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) 0
      (fun j => (Tensor0SSpace.toModel (θ j))
        (fun _ : Fin 1 => (v 0 : TangentSpace I x₀)) • σ' j)
      (fun _ : Fin 1 => (0 : E))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Goal: `(toModel α)(update (fun _ => 0) 0 (c_j • σ' j))
  --       = (toModel α)(fun _ => σ' j) * (toModel (θ j))(fun _ => v 0)`,
  -- where `c_j = (toModel (θ j))(fun _ => v 0)`.
  -- Pull out the scalar `c_j` using multilinearity on slot 0.
  rw [(Tensor0SSpace.toModel α).map_update_smul (fun _ : Fin 1 => (0 : E)) 0
    ((Tensor0SSpace.toModel (θ j))
      (fun _ : Fin 1 => (v 0 : TangentSpace I x₀))) (σ' j)]
  -- Goal: `c_j • (toModel α)(update (fun _ => 0) 0 (σ' j))
  --       = (toModel α)(fun _ => σ' j) * c_j`.
  rw [smul_eq_mul]
  have h_update2 : Function.update (fun _ : Fin 1 => (0 : E)) 0 (σ' j) =
      (fun _ : Fin 1 => (σ' j : E)) := by
    funext k; fin_cases k; simp
  rw [h_update2]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Local constancy of the biorthogonal pairing.** If smooth frames `σ'` (tangent) and
`θ_smooth` (dual `(0,1)`-tensor) agree with the trivialization `localFrame` near `x₀`, then
the biorthogonal pairing `toModel((θ_smooth i) y)(fun _ => (σ' j) y)` equals the Kronecker
`δ_{ij}` (as an ℝ-valued function) on an entire neighborhood of `x₀`.

This upgrades `matching_frames_biorth` (pointwise on the base-set intersection) to an
`eventually`-filter statement on `𝓝 x₀`, which is the form consumed by
`biorth_christoffel_identity` (D2). -/
private lemma biorth_pair_locally_const
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
          (dualCovectorBasis (E := E)) i x)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ᶠ y in 𝓝 x₀,
      (Tensor0SSpace.toModel ((θ_smooth i) y)) (fun _ : Fin 1 =>
        ((σ' j) y : TangentSpace I y)) =
      (if i = j then (1 : ℝ) else 0) := by
  have hx_tan_nhds :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E _ x₀)
  have hx_1_nhds :=
    (trivializationAt (Tensor0SModel 1 ℝ E)
      (fun x => Tensor0SSpace 1 I x) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hσ', hθ_smooth, hx_tan_nhds, hx_1_nhds]
    with y hσ'y hθ_smoothy hy_tan hy_1
  rw [hσ'y j, hθ_smoothy i]
  exact matching_frames_biorth I M x₀ y hy_tan hy_1 i j

/-- **Christoffel sum cancellation.** Given smooth local frames `σ'` (tangent) and
`θ_smooth` (dual) agreeing with trivialization-local frames near `x₀` (so that biorthogonality
is locally constant), and ANY `F : Fin d × Fin d → V` over any ℝ-module `V`, the two
Christoffel sums
  `∑_i ∑_j (∇θ_i)(σ'_j) • F i j` and `∑_i ∑_j θ_i(∇σ'_j) • F i j`
cancel pairwise via the D2 biorthogonality identity. -/
private lemma christoffel_sum_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
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
          (dualCovectorBasis (E := E)) i x)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → V) :
    (∑ i, ∑ j,
        (Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (fun y => (θ_smooth i) y) x₀ (X x₀)))
          (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)) • F i j)
    + (∑ i, ∑ j,
        (Tensor0SSpace.toModel ((θ_smooth i) x₀))
          (fun _ : Fin 1 => (cov (σ' j) x₀ (X x₀) : E)) • F i j) = 0 := by
  classical
  -- Step 1: Pull the local-constancy hypothesis from the named lemma
  -- `biorth_pair_locally_const`.
  have hpair_const : ∀ i j, ∀ᶠ y in 𝓝 x₀,
      (Tensor0SSpace.toModel ((θ_smooth i) y)) (fun _ : Fin 1 =>
        ((σ' j) y : TangentSpace I y)) =
      (if i = j then (1 : ℝ) else 0) :=
    fun i j => biorth_pair_locally_const I M x₀ σ' θ_smooth hσ' hθ_smooth i j
  -- Step 2: Combine the two sums into one via Finset.sum_add_distrib (twice).
  rw [← Finset.sum_add_distrib]
  have h_inner_combine : ∀ i,
      (∑ j,
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov
              (fun y => (θ_smooth i) y) x₀ (X x₀)))
            (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)) • F i j)
      + (∑ j,
          (Tensor0SSpace.toModel ((θ_smooth i) x₀))
            (fun _ : Fin 1 => (cov (σ' j) x₀ (X x₀) : E)) • F i j) =
      ∑ j,
        ((Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov
            (fun y => (θ_smooth i) y) x₀ (X x₀)))
          (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀))
        + (Tensor0SSpace.toModel ((θ_smooth i) x₀))
            (fun _ : Fin 1 => (cov (σ' j) x₀ (X x₀) : E))) • F i j := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_smul]
  -- Step 3: Replace the outer ∑ with ∑ i, (combined sum), then show each outer summand = 0.
  refine Finset.sum_eq_zero (fun i _ => ?_)
  -- Goal now: ((the full (i-inner) expression)) = 0.
  -- First: rewrite the outer-fixed (i-combined) sum as a single ∑_j ....
  rw [h_inner_combine i]
  -- Goal: ∑ j, (coefficient_ij) • F i j = 0.
  -- Step 4: For each j, apply D2 (biorth_christoffel_identity) to get coefficient_ij = 0.
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_coeff_zero :
      (Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov
          (fun y => (θ_smooth i) y) x₀ (X x₀)))
        (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀))
      + (Tensor0SSpace.toModel ((θ_smooth i) x₀))
          (fun _ : Fin 1 => (cov (σ' j) x₀ (X x₀) : E)) = 0 :=
    biorth_christoffel_identity I M cov X x₀ (θ_smooth i) (σ' j)
      (if i = j then (1 : ℝ) else 0) (hpair_const i j)
  rw [h_coeff_zero, zero_smul]

/-! ### Substep 6.4 — Closing the P26 commutation theorem

This section combines all Substeps 6.1–6.3 with the generic Hom-bundle product rule
(`tensorRSCovariantDerivative_apply`) to close the main P26 theorem
`concrete_nabla_contract_comm`. -/

/-! #### Helper H1: fiber-level bridge between `castRSComm` and `castTensor0SComm`

Applied in Substep 6.4 to match the `(∇T)(w')` expansion against the RHS summand form. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Cast-Hom bridge.** For any `T : TensorRSSpace (r+1)(s+1) I x` and
`β : Tensor0SSpace (1+r) I x`:
`(castRSComm r s x T) β = T (castTensor0SComm r x β)`.

Both sides live in `Tensor0SSpace (s+1) I x`; equality is the identity-transport
reflection of the fact that `castRSComm` on the Hom-source and `castTensor0SComm` on
the input are both identity maps on the underlying Nat-arith swap. -/
private lemma castRSComm_eval_castTensor0SComm (r s : ℕ) {x : M}
    (T : TensorRSSpace (r + 1) (s + 1) I x)
    (β : Tensor0SSpace (1 + r) I x) :
    (castRSComm I M r s x T) β = T (castTensor0SComm I M r x β) := by
  -- Both sides live in `Tensor0SSpace (s+1) I x`. We show equality via
  -- `eq_of_heq` after computing HEqs of the two sides to the common element `T β''`
  -- where `β''` gets HEq-transported.
  -- Step A: apply `eq_of_heq` to the goal.
  apply eq_of_heq
  -- Step B: HEq of LHS = (castRSComm T) β to T β (reinterpreting β as Tensor0SSpace (r+1)).
  -- Use: HEq (castRSComm T) T (from castRSComm_apply_heq) implies
  -- HEq ((castRSComm T) β) (T β') for any β, β' with HEq β β'.
  -- Step C: HEq of RHS = T (castTensor0SComm β) to T β''.
  -- We have HEq (castTensor0SComm β) β, so T applied to both sides gives HEq.
  -- Set γ := castTensor0SComm I M r x β : Tensor0SSpace (r+1) I x. Then HEq γ β.
  -- So T γ : Tensor0SSpace (s+1), and we want to show HEq ((castRSComm T) β) (T γ).
  -- Via HEq (castRSComm T) T: HEq ((castRSComm T) β) (T β). But T is not applicable to β (wrong type).
  -- Let's use a generic subst argument.
  have gen :
      ∀ (k : ℕ) (h : r + 1 = k)
        (T_k : Tensor0SSpace k I x →L[ℝ] Tensor0SSpace (s + 1) I x)
        (_hT_k : HEq T_k T)
        (β_k : Tensor0SSpace k I x)
        (_hβ_k : HEq β_k β),
        HEq (T_k β_k) (T (castTensor0SComm I M r x β)) := by
    intro k h T_k hT_k β_k hβ_k
    subst h
    -- Now k = r + 1, so T_k : Tensor0SSpace (r+1) →L Tensor0SSpace (s+1) with HEq T_k T.
    cases hT_k
    -- Now T_k = T.
    -- β_k : Tensor0SSpace (r+1) with HEq β_k β where β : Tensor0SSpace (1+r).
    -- We need HEq (T β_k) (T (castTensor0SComm β)).
    -- `castTensor0SComm β : Tensor0SSpace (r+1)` with `HEq (castTensor0SComm β) β`.
    have hcast : HEq (castTensor0SComm I M r x β) β :=
      castTensor0SComm_apply_heq I M r x β
    -- From HEq β_k β and HEq (castTensor0SComm β) β, we get HEq β_k (castTensor0SComm β).
    have hβ_cast : HEq β_k (castTensor0SComm I M r x β) := hβ_k.trans hcast.symm
    -- Both β_k and castTensor0SComm β are in Tensor0SSpace (r+1); HEq becomes Eq.
    have heq_eq : β_k = castTensor0SComm I M r x β := eq_of_heq hβ_cast
    rw [heq_eq]
  -- Now apply `gen` at k = 1 + r with T_k = castRSComm I M r s x T and β_k = β.
  -- HEq (castRSComm T) T and HEq β β.
  have hT_1r : HEq (castRSComm I M r s x T) T :=
    castRSComm_apply_heq I M r s x T
  exact gen (1 + r) (by omega) (castRSComm I M r s x T) hT_1r β HEq.rfl

/-! #### Helper H2: smooth packaging of `y ↦ T y (w y)` as a `Tensor0SField s`

For a smooth `(r, s)`-tensor field `T` and a smooth `(0, r)`-tensor field `w`, the pointwise
application `y ↦ T y (w y)` is a smooth `(0, s)`-tensor field. Smoothness follows from
`ContMDiffAt.clm_bundle_apply`, which says a smooth Hom-bundle-section applied to a smooth
base-section is smooth. -/

/-- Smooth packaging of `y ↦ T y (w y)` as a `Tensor0SField s` section. The smoothness
follows from the smooth-CLM-section-applied-to-smooth-vector-section pattern (a bundled
Hom-section applied to a bundled domain-section is smooth). -/
noncomputable def homApplyTensor0S_smoothField (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s)
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨fun x => T x (w x), ?_⟩
  intro x₀
  -- Goal: ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
  --   (fun x => TotalSpace.mk' (Tensor0SModel s ℝ E) x (T x (w x))) x₀
  -- Use ContMDiffAt.clm_bundle_apply.
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (T x)) x₀ :=
    T.contMDiff x₀
  have hw : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E) x (w x)) x₀ :=
    w.contMDiff x₀
  exact ContMDiffAt.clm_bundle_apply (b := id) hT hw

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem homApplyTensor0S_smoothField_apply (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r s)
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r) (x : M) :
    homApplyTensor0S_smoothField I M r s T w x = T x (w x) := rfl

/-! #### Helper: scalar evaluation of `RHS_summand i`.

Directly unfolds via the `_apply_eval` lemmas for `contract_contravariant_first` and
`contract_covariant`, combined with H1. -/

open TensorRSNabla in
/-- The `RHS_summand i`, applied to a test vector `β` and evaluated at `u`, equals a scalar
expression involving the `∇T` Hom-application combined via `slot0Insert`. -/
private lemma RHS_summand_toModel_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (β : Tensor0SSpace r I x₀) (u : Fin s → E) :
    Tensor0SSpace.toModel (RHS_summand I M cov X r s T σ' θ_smooth x₀ i β) u =
      Tensor0SSpace.toModel
        (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀)
          (castTensor0SComm I M r x₀ (slot0Insert I M ((θ_smooth i) x₀) β)))
        (Fin.cons ((σ' i) x₀ : E) u) := by
  -- Unfold RHS_summand → contract_contravariant_first → contract_covariant → castRSComm.
  rw [RHS_summand_unfold]
  -- Goal: toModel (contract_contravariant_first ... (contract_covariant ... (castRSComm ∇T)) β) u = ...
  rw [contract_contravariant_first_apply_eval]
  rw [contract_covariant_apply_eval]
  -- Goal: toModel (interior_product s x₀ (σ' i x₀)
  --   ((castRSComm I M r s x₀ (∇T)) (...))) u = ...
  -- The inner argument: `(cle (1+r) x₀).symm (model_tensorWithCovector_first r (toModel θ)
  --  ((cle r x₀) β))` = `slot0Insert I M (θ x₀) β` by definition.
  have h_arg : (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x₀).symm
      (Tensor0SBundle.model_tensorWithCovector_first r
        (Tensor0SSpace.toModel ((θ_smooth i) x₀))
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x₀) β)) =
      slot0Insert I M ((θ_smooth i) x₀) β := rfl
  rw [h_arg]
  -- Goal: toModel (interior_product s x₀ (σ' i x₀) ((castRSComm ∇T) (slot0Insert θ β))) u = ...
  -- Use H1: (castRSComm T') β' = T' (castTensor0SComm β').
  rw [castRSComm_eval_castTensor0SComm I M r s
    (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀))
    (slot0Insert I M ((θ_smooth i) x₀) β)]
  -- Goal: toModel(interior_product s x₀ (σ' i x₀) (∇T (castTensor0SComm (slot0Insert ...)))) u = RHS.
  -- Reduce `toModel(interior_product s v G) u = toModel(G)(Fin.cons v u)` via def.
  rfl

/-! #### Helper: expansion of `LHS_Term_outer i` via D0 and D1.

For each frame index `i` and test section `w`, the `LHS_Term_outer i w` scalar value decomposes
into the sum of a "main" term (involving `∇^{(r+1, s+1)}_X T`) plus Christoffel residuals. -/

open TensorRSNabla in
set_option maxHeartbeats 4000000 in
-- This is the main algebraic chain of Substep 6.4. Decomposing LHS_Term_outer via D0
-- + D1 + tensorRSCovariantDerivative_apply + H1 pushes typeclass resolution above
-- the default budget; the additional heartbeats are required.
/-- **LHS-Term-outer decomposition.** For each frame index `i` and smooth test section `w`,
```
toModel (LHS_Term_outer i w) u =
    toModel (∇^{(r+1,s+1)}_X T x₀ (X x₀) (w' x₀)) (Fin.cons (σ' i x₀) u)
  + toModel ((castRSComm T x₀) (slot0Insert (∇θ_i) w x₀)) (Fin.cons (σ' i x₀) u)
  + toModel ((castRSComm T x₀) (slot0Insert (θ_i x₀) (∇w x₀))) (Fin.cons (σ' i x₀) u)
  + toModel (T x₀ (castTensor0SComm (slot0Insert (θ_i x₀) (w x₀)))) (Fin.cons (cov (σ' i) x₀ (X x₀)) u)
```
(NOTE: the second and third terms come from D1's expansion of `∇^{(0,1+r)}_X slot0Insert`;
the fourth term comes from D0's expansion at `s+1`). -/
private lemma LHS_Term_outer_decompose
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
    (u : Fin s → E) :
    Tensor0SSpace.toModel (LHS_Term_outer I M cov X r s T σ' θ_smooth x₀ i w) u =
      Tensor0SSpace.toModel
        (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀)
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀) (w x₀))))
        (Fin.cons ((σ' i) x₀ : E) u)
      + Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀))
              (w x₀))))
          (Fin.cons ((σ' i) x₀ : E) u)
      + Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)))))
          (Fin.cons ((σ' i) x₀ : E) u)
      + Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀) (w x₀))))
          (Fin.cons (cov (σ' i) x₀ (X x₀) : E) u) := by
  -- Step 1: set up `τ_i` := homApplyTensor0S_smoothField (1+r) (s+1) (castRSComm_smoothField T)
  --   (slot0Insert_smoothField I M r θ w), a smooth Tensor0SField (s+1).
  set θi := θ_smooth i with hθi_def
  set α := slot0Insert_smoothField I M r θi w with hα_def
  -- `α : Tensor0SField (𝕜 := ℝ) ... (1 + r)`.
  set αc := castTensor0SComm_smoothField I M r α with hαc_def
  -- `αc : Tensor0SField (𝕜 := ℝ) ... (r + 1)`.
  set τ_i : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (s+1) :=
    homApplyTensor0S_smoothField I M (r+1) (s+1) T αc with hτi_def
  -- Step 2: prove `y ↦ partialTraceSummand y (w y) = y ↦ interior_product s y (σ'_i y) (τ_i y)`.
  -- This unfolds the contract_* on partialTraceSummand and applies H1.
  have h_eq_fn :
      (fun y => partialTraceSummand_smoothField I M r s (σ' i) θi T y (w y)) =
      (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) s y ((σ' i) y) (τ_i y)) := by
    funext y
    rw [partialTraceSummand_smoothField_apply]
    -- Goal: contract_contravariant_first r s y (θi y) (contract_covariant (1+r) s y (σ'_i y)
    --   ((castRSComm_smoothField I M r s T) y)) (w y)
    --   = interior_product s y (σ'_i y) (τ_i y).
    rw [contract_contravariant_first_apply_eval]
    -- Goal: (contract_covariant (1+r) s y (σ' i y) (castRSComm_smoothField T y))
    --   ((cle (1+r) y).symm (model_twCov_first r (toModel (θi y)) ((cle r y) (w y)))) = ...
    -- The inner argument is `slot0Insert (θi y) (w y)` by definition.
    have h_inner : (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) y).symm
        (Tensor0SBundle.model_tensorWithCovector_first r
          (Tensor0SSpace.toModel (θi y))
          ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r y) (w y))) =
        slot0Insert I M (θi y) (w y) := rfl
    rw [h_inner]
    rw [contract_covariant_apply_eval]
    -- Goal: interior_product s y (σ' i y) ((castRSComm_smoothField T y) (slot0Insert (θi y) (w y)))
    --     = interior_product s y (σ' i y) (τ_i y).
    -- τ_i y = (castRSComm_smoothField T) y (slot0Insert_smoothField ... y)
    --       = castRSComm I M r s y (T y) (slot0Insert I M (θi y) (w y))   [by simp lemmas]
    --       = T y (castTensor0SComm I M r y (slot0Insert I M (θi y) (w y)))   [by H1]
    -- Meanwhile: (castRSComm_smoothField T) y = castRSComm I M r s y (T y), so the two sides
    -- are identical by unfolding `τ_i`, `αc`, `α`, and `castRSComm_smoothField_apply` +
    -- `slot0Insert_smoothField_apply`. But we don't want to rewrite with H1 — the τ_i is defined
    -- as `T y (αc y)`, which equals `T y (castTensor0SComm I M r y (slot0Insert I M (θi y) (w y)))`.
    -- The LHS uses `(castRSComm_smoothField T y) (slot0Insert ...)`.
    -- By castRSComm_smoothField_apply: castRSComm_smoothField T y = castRSComm I M r s y (T y).
    -- By H1: castRSComm I M r s y (T y) (slot0Insert I M (θi y) (w y))
    --      = T y (castTensor0SComm I M r y (slot0Insert I M (θi y) (w y)))
    --      = T y (αc y) [by castTensor0SComm_smoothField_apply + slot0Insert_smoothField_apply]
    --      = τ_i y.
    congr 1
    rw [castRSComm_smoothField_apply]
    rw [castRSComm_eval_castTensor0SComm]
    -- Goal: T y (castTensor0SComm I M r y (slot0Insert I M (θi y) (w y))) = τ_i y.
    -- τ_i y := T y (αc y). αc y = castTensor0SComm I M r y (α y) = castTensor0SComm I M r y
    --   (slot0Insert I M (θi y) (w y)).
    change T y _ = homApplyTensor0S_smoothField I M (r+1) (s+1) T αc y
    rw [homApplyTensor0S_smoothField_apply]
    rw [hαc_def, castTensor0SComm_smoothField_apply, hα_def, slot0Insert_smoothField_apply]
  -- Step 3: apply D0 (tensor0S_apply_vector_leibniz) with τ = τ_i, σ = σ' i:
  --   toModel(∇^{(0,s)}_X (y ↦ ι_{σ'i y} τ_i y) x₀ (X x₀)) u
  --   = toModel(∇^{(0,s+1)}_X τ_i x₀ (X x₀)) (Fin.cons (σ' i x₀) u)
  --   + toModel(τ_i x₀) (Fin.cons (cov σ'_i x₀ (X x₀)) u).
  have hD0 := tensor0S_apply_vector_leibniz I M cov X s τ_i (σ' i) x₀ u
  -- Step 4: rewrite LHS_Term_outer via `h_eq_fn`, then use hD0.
  have h_outer_expand :
      Tensor0SSpace.toModel (LHS_Term_outer I M cov X r s T σ' θ_smooth x₀ i w) u =
        Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M s cov
            (fun y => Tensor0SBundle.interior_product (𝕜 := ℝ) s y ((σ' i) y) (τ_i y))
            x₀ (X x₀)) u := by
    unfold LHS_Term_outer
    rw [h_eq_fn]
  rw [h_outer_expand, hD0]
  -- Now goal: toModel(∇^{(0,s+1)}_X τ_i ...)(Fin.cons σ'i u) + toModel(τ_i x₀)(Fin.cons cov_σ'i u)
  -- = ... (4 terms).
  -- Step 5: compute toModel(τ_i x₀) = toModel(T x₀ (αc x₀)).
  -- αc x₀ = castTensor0SComm I M r x₀ (slot0Insert I M (θi x₀) (w x₀)).
  have h_τi_at :
      τ_i x₀ = T x₀ (castTensor0SComm I M r x₀ (slot0Insert I M (θi x₀) (w x₀))) := by
    change homApplyTensor0S_smoothField I M (r+1) (s+1) T αc x₀ = _
    rw [homApplyTensor0S_smoothField_apply]
    rw [hαc_def, castTensor0SComm_smoothField_apply, hα_def, slot0Insert_smoothField_apply]
  -- Step 6: expand ∇^{(0,s+1)} τ_i via tensorRSCovariantDerivative_apply at (r+1, s+1) with
  --   test `αc`, reinterpreting `τ_i = homApplyTensor0S_smoothField T αc`.
  -- `tensorRSCovariantDerivative_apply r+1 s+1 cov T αc x₀ (X x₀)`:
  --   `(∇^{(r+1,s+1)}_X T x₀ (X x₀)) (αc x₀) =
  --     ∇^{(0,s+1)}_X (y ↦ T y (αc y)) x₀ (X x₀)
  --     - T x₀ (∇^{(0,r+1)}_X αc x₀ (X x₀))`.
  -- Since `τ_i y = T y (αc y)`, this rearranges to:
  --   `∇^{(0,s+1)}_X τ_i x₀ (X x₀) = (∇^{(r+1,s+1)}_X T x₀ (X x₀))(αc x₀) + T x₀ (∇^{(0,r+1)}_X αc x₀ (X x₀))`.
  have h_tau_τi : (fun y => τ_i y) = (fun y => T y (αc y)) := rfl
  have h_rs := tensorRSCovariantDerivative_apply I M (r+1) (s+1) cov T αc x₀ (X x₀)
  -- h_rs : (∇^{(r+1,s+1)}_X T x₀ (X x₀)) (αc x₀) = ∇^{(0,s+1)}_X (fun y => T y (αc y)) x₀ (X x₀)
  --   - T x₀ (∇^{(0,r+1)}_X αc x₀ (X x₀)).
  have h_covs1_τi :
      Tensor0SNabla.tensor0SCovariantDerivative I M (s+1) cov (fun y => τ_i y) x₀ (X x₀) =
      tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀) (αc x₀)
      + T x₀ (Tensor0SNabla.tensor0SCovariantDerivative I M (r+1) cov αc x₀ (X x₀)) := by
    rw [h_tau_τi]
    -- h_rs : A = B - C where A := (∇T) αc, B := ∇^(0,s+1)(T·αc), C := T (∇αc).
    -- We want B = A + C. Rewrite via sub_eq_iff_eq_add.
    rw [eq_sub_iff_add_eq] at h_rs
    exact h_rs.symm
  -- Evaluate via toModel + (Fin.cons (σ' i x₀) u).
  have h_covs1_τi_eval :
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s+1) cov (fun y => τ_i y) x₀ (X x₀))
          (Fin.cons ((σ' i) x₀ : E) u) =
        Tensor0SSpace.toModel
          (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀) (αc x₀))
          (Fin.cons ((σ' i) x₀ : E) u) +
        Tensor0SSpace.toModel
          (T x₀ (Tensor0SNabla.tensor0SCovariantDerivative I M (r+1) cov αc x₀ (X x₀)))
          (Fin.cons ((σ' i) x₀ : E) u) := by
    rw [h_covs1_τi, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [h_covs1_τi_eval]
  -- Now rewrite τ_i x₀ via h_τi_at.
  rw [h_τi_at]
  -- Current goal:
  --   toModel(∇^{(r+1,s+1)}_X T x₀ (X x₀) (αc x₀))(Fin.cons σ'_i u)
  --   + toModel(T x₀ (∇^{(0,r+1)}_X αc x₀ (X x₀)))(Fin.cons σ'_i u)
  --   + toModel(T x₀ (castTensor0SComm (slot0Insert θi w x₀)))(Fin.cons cov_σ'_i u)
  -- = RHS (4-term expansion).
  -- RHS Decomposition:
  --   Term 1 = toModel(∇T (castTensor0SComm (slot0Insert θi w)))(Fin.cons σ'_i u)
  --   Term 2 = toModel(T (castTensor0SComm (slot0Insert ∇θi w)))(Fin.cons σ'_i u)
  --   Term 3 = toModel(T (castTensor0SComm (slot0Insert θi ∇w)))(Fin.cons σ'_i u)
  --   Term 4 = toModel(T (castTensor0SComm (slot0Insert θi w)))(Fin.cons cov_σ'_i u)
  -- Note `αc x₀ = castTensor0SComm I M r x₀ (slot0Insert I M (θi x₀) (w x₀))`.
  have h_αc_at : αc x₀ = castTensor0SComm I M r x₀ (slot0Insert I M (θi x₀) (w x₀)) := by
    rw [hαc_def, castTensor0SComm_smoothField_apply, hα_def, slot0Insert_smoothField_apply]
  -- Step 7: expand ∇^{(0,r+1)}_X αc x₀ (X x₀) via D1 (slot0Insert_smoothField_cov_leibniz).
  -- D1 gives: ∇^{(0,1+r)}_X (slot0Insert_smoothField θi w) x₀ (X x₀)
  --   = slot0Insert (∇θi, w) + slot0Insert (θi, ∇w).
  -- Then use tensor0SCovariantDerivative_cast_heq to transport to ∇^{(0,r+1)}_X αc.
  have hD1 :
      Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov
        (fun y => slot0Insert_smoothField I M r θi w y) x₀ (X x₀) =
      slot0Insert I M
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov θi x₀ (X x₀)) (w x₀)
        + slot0Insert I M (θi x₀)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)) :=
    slot0Insert_smoothField_cov_leibniz I M cov X r θi w x₀
  -- Now transport via tensor0SCovariantDerivative_cast_heq.
  have h_αc_cov :
      T x₀ (Tensor0SNabla.tensor0SCovariantDerivative I M (r+1) cov αc x₀ (X x₀)) =
      T x₀ (castTensor0SComm I M r x₀
          (slot0Insert I M
            (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov θi x₀ (X x₀)) (w x₀)
            + slot0Insert I M (θi x₀)
                (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)))) := by
    -- Key: HEq ∇^{(0,1+r)}_X (slot0Insert_smoothField θi w) x₀ (X x₀) (∇^{(0,r+1)}_X αc x₀ (X x₀)).
    have h_transport :
        HEq (Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov
              (fun y => slot0Insert_smoothField I M r θi w y) x₀ (X x₀))
            (Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov
              (fun y => castTensor0SComm_smoothField I M r
                (slot0Insert_smoothField I M r θi w) y) x₀ (X x₀)) :=
      tensor0SCovariantDerivative_cast_heq I M cov X r
        (slot0Insert_smoothField I M r θi w) x₀
    -- Apply T x₀ to both sides, noting that the function passed to ∇^{(0,r+1)} is `αc`.
    -- Since `α = slot0Insert_smoothField I M r θi w` and `αc = castTensor0SComm_smoothField I M r α`,
    -- we have `(fun y => castTensor0SComm_smoothField I M r α y) = (fun y => αc y)`.
    have h_rhs_rewrite :
        Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov
          (fun y => castTensor0SComm_smoothField I M r
            (slot0Insert_smoothField I M r θi w) y) x₀ (X x₀) =
        Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov
          (fun y => αc y) x₀ (X x₀) := by
      rfl
    -- Let `P := ∇^{(0,1+r)} α x₀ (X x₀)`, `Q := ∇^{(0,r+1)} αc x₀ (X x₀)`. HEq P Q.
    -- By D1: P = slot0Insert ∇θi w + slot0Insert θi ∇w.
    -- So HEq Q (slot0Insert ∇θi w + slot0Insert θi ∇w) (via transport).
    -- And HEq (castTensor0SComm x₀ (slot0Insert ∇θi w + slot0Insert θi ∇w))
    --        (slot0Insert ∇θi w + slot0Insert θi ∇w)  [by castTensor0SComm_apply_heq].
    -- So HEq Q (castTensor0SComm x₀ (slot0Insert ∇θi w + slot0Insert θi ∇w)).
    -- Both Q and the RHS are in Tensor0SSpace (r+1), so HEq → Eq.
    set P := Tensor0SNabla.tensor0SCovariantDerivative I M (1 + r) cov
      (fun y => slot0Insert_smoothField I M r θi w y) x₀ (X x₀) with hP_def
    set Q := Tensor0SNabla.tensor0SCovariantDerivative I M (r + 1) cov
      (fun y => αc y) x₀ (X x₀) with hQ_def
    set V₀ : Tensor0SSpace (1 + r) I x₀ := slot0Insert I M
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov θi x₀ (X x₀)) (w x₀)
      + slot0Insert I M (θi x₀)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)) with hV₀_def
    have h_P_eq_V₀ : P = V₀ := hD1
    have h_heq_PQ : HEq P Q := by
      -- h_transport has ... (fun y => castTensor0SComm_smoothField I M r (slot0Insert_smoothField I M r θi w) y) y)
      -- which reduces to (fun y => αc y) since α := slot0Insert_smoothField I M r θi w.
      rw [h_rhs_rewrite] at h_transport
      exact h_transport
    have h_heq_QV₀ : HEq Q V₀ := h_heq_PQ.symm.trans (heq_of_eq h_P_eq_V₀)
    have h_cast_V₀_heq : HEq (castTensor0SComm I M r x₀ V₀) V₀ :=
      castTensor0SComm_apply_heq I M r x₀ V₀
    have h_heq_Q_cast : HEq Q (castTensor0SComm I M r x₀ V₀) :=
      h_heq_QV₀.trans h_cast_V₀_heq.symm
    -- Both sides live in Tensor0SSpace (r+1), so HEq → Eq.
    have h_eq_Q : Q = castTensor0SComm I M r x₀ V₀ := eq_of_heq h_heq_Q_cast
    -- Rewrite the goal via Q's definition + h_eq_Q.
    change T x₀ (Tensor0SNabla.tensor0SCovariantDerivative I M (r+1) cov
      (fun y => αc y) x₀ (X x₀)) = T x₀ (castTensor0SComm I M r x₀ V₀)
    rw [← hQ_def]
    rw [h_eq_Q]
  rw [h_αc_cov]
  -- Current goal:
  --   toModel(∇^{(r+1,s+1)} T x₀ (X x₀) (αc x₀))(Fin.cons σ'_i u)
  --   + toModel(T x₀ (castTensor0SComm (slot0Insert ∇θi w + slot0Insert θi ∇w)))(Fin.cons σ'_i u)
  --   + toModel(T x₀ (castTensor0SComm (slot0Insert θi w)))(Fin.cons cov σ'_i u)
  -- = RHS (4 terms).
  -- Use `map_add (castTensor0SComm I M r x₀)` and `map_add (T x₀)` and toModel_add.
  rw [h_αc_at]
  rw [map_add (castTensor0SComm I M r x₀)]
  rw [map_add (T x₀)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  ring

/-! #### Helper: scalar evaluation of `LHS_Term_inner i`.

Direct unfolding to match the ChriW term in `LHS_Term_outer_decompose`. -/

open TensorRSNabla in
/-- The `LHS_Term_inner i w` value. Unfolds `partialTraceSummand_smoothField` + H1. -/
private lemma LHS_Term_inner_toModel_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M) (i : Fin (Module.finrank ℝ E))
    (w : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) r)
    (u : Fin s → E) :
    Tensor0SSpace.toModel (LHS_Term_inner I M cov X r s T σ' θ_smooth x₀ i w) u =
      Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)))))
          (Fin.cons ((σ' i) x₀ : E) u) := by
  unfold LHS_Term_inner
  rw [partialTraceSummand_smoothField_apply]
  rw [contract_contravariant_first_apply_eval]
  -- Goal: toModel (contract_covariant (1+r) s x₀ (σ'_i x₀) (castRSComm_smoothField T x₀))
  --   ((cle (1+r) x₀).symm (model_twCov_first r (toModel θi x₀) ((cle r x₀) ∇w))) u = ...
  -- The inner argument is slot0Insert (θi x₀) ∇w.
  have h_inner : (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x₀).symm
      (Tensor0SBundle.model_tensorWithCovector_first r
        (Tensor0SSpace.toModel ((θ_smooth i) x₀))
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x₀)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)))) =
      slot0Insert I M ((θ_smooth i) x₀)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x₀ (X x₀)) := rfl
  rw [h_inner]
  rw [contract_covariant_apply_eval]
  -- Goal: toModel(interior_product s x₀ (σ'_i x₀) ((castRSComm_smoothField T x₀) (slot0Insert θi ∇w))) u = ...
  -- Simplify `interior_product ... G u = toModel G (Fin.cons (σ'_i x₀) u)` by def.
  rw [castRSComm_smoothField_apply]
  rw [castRSComm_eval_castTensor0SComm]
  -- Goal: toModel(interior_product s x₀ (σ'_i x₀) (T x₀ (castTensor0SComm (slot0Insert θi ∇w)))) u = ...
  rfl

/-! #### Helper: multi-linear expansion of `slot0Insert` and `toModel(T(castTensor0SComm(slot0Insert)))`.

These helpers distribute scalar-sums through the slot0Insert / castTensor0SComm / T / toModel chain
so that we can apply `christoffel_sum_zero`. -/

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `slot0Insert` is `ℝ`-linear in its first argument (the covector). -/
private lemma slot0Insert_add_first {r : ℕ} {x : M}
    (α₁ α₂ : Tensor0SSpace 1 I x) (β : Tensor0SSpace r I x) :
    slot0Insert I M (α₁ + α₂) β = slot0Insert I M α₁ β + slot0Insert I M α₂ β := by
  unfold slot0Insert
  -- Use map_add on the embedded model structures.
  rw [Tensor0SSpace.toModel_add]
  change (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
      (Tensor0SBundle.model_tensorWithCovector_first r
        (Tensor0SSpace.toModel α₁ + Tensor0SSpace.toModel α₂)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) = _
  rw [show (Tensor0SBundle.model_tensorWithCovector_first r
        (Tensor0SSpace.toModel α₁ + Tensor0SSpace.toModel α₂)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) =
      Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α₁)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) +
      Tensor0SSpace.toModel ((slot0Insert I M α₂ β :
        Tensor0SSpace (1 + r) I x)) from ?_]
  · rw [map_add]
    rfl
  · -- model_tensorWithCovector_first r is bilinear in (α, β) via modelProduct; linear in α.
    ext v
    simp only [ContinuousMultilinearMap.add_apply]
    unfold Tensor0SBundle.model_tensorWithCovector_first
    change (Bundle.continuousMultilinearMap.modelProduct 1 r
        (Tensor0SSpace.toModel α₁ + Tensor0SSpace.toModel α₂)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) v = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [ContinuousMultilinearMap.add_apply, add_mul]
    change _ =
      (Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel α₁)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) v +
      Tensor0SSpace.toModel (slot0Insert I M α₂ β) v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `slot0Insert` is ℝ-scalar-homogeneous in its first argument. -/
private lemma slot0Insert_smul_first {r : ℕ} {x : M}
    (c : ℝ) (α : Tensor0SSpace 1 I x) (β : Tensor0SSpace r I x) :
    slot0Insert I M (c • α) β = c • slot0Insert I M α β := by
  unfold slot0Insert
  rw [Tensor0SSpace.toModel_smul]
  change (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) (1 + r) x).symm
      (Tensor0SBundle.model_tensorWithCovector_first r (c • Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) = _
  rw [show Tensor0SBundle.model_tensorWithCovector_first r (c • Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) =
      c • Tensor0SBundle.model_tensorWithCovector_first r (Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) from ?_]
  · rw [map_smul]
  · ext v
    unfold Tensor0SBundle.model_tensorWithCovector_first
    change (Bundle.continuousMultilinearMap.modelProduct 1 r
        (c • Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) v = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [ContinuousMultilinearMap.smul_apply]
    change _ = (c •
      Bundle.continuousMultilinearMap.modelProduct 1 r (Tensor0SSpace.toModel α)
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β)) v
    rw [ContinuousMultilinearMap.smul_apply]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [smul_eq_mul, smul_eq_mul]
    ring_nf

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `slot0Insert` commutes with `Finset.sum` in its first argument. -/
private lemma slot0Insert_sum_first {r : ℕ} {x : M} {ι : Type*} (t : Finset ι)
    (f : ι → Tensor0SSpace 1 I x) (β : Tensor0SSpace r I x) :
    slot0Insert I M (∑ i ∈ t, f i) β = ∑ i ∈ t, slot0Insert I M (f i) β := by
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    -- slot0Insert 0 β = 0.
    unfold slot0Insert
    rw [show (Tensor0SSpace.toModel (0 : Tensor0SSpace 1 I x) :
      ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) = 0 from
      Tensor0SSpace.toModel_zero]
    rw [show Tensor0SBundle.model_tensorWithCovector_first r (0 : Tensor0SModel 1 ℝ E)
          ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) =
        (0 : Tensor0SModel (1 + r) ℝ E) from ?_]
    · rw [map_zero]
    · ext v
      unfold Tensor0SBundle.model_tensorWithCovector_first
      change Bundle.continuousMultilinearMap.modelProduct 1 r 0
        ((tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) r x) β) v = _
      rw [Bundle.continuousMultilinearMap.modelProduct_apply]
      simp
  | insert k t hkt ih =>
    rw [Finset.sum_insert hkt, Finset.sum_insert hkt]
    rw [slot0Insert_add_first]
    rw [ih]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- `toModel (T x₀ (castTensor0SComm x₀ (slot0Insert (∑ j, c_j • θ_j) w)))(v)`
distributes over sums/scalar products via linearity of `slot0Insert` / `castTensor0SComm` / `T x₀` / `toModel`. -/
private lemma toModel_T_castTensor0SComm_slot0Insert_sum_smul_first (r s : ℕ)
    {x₀ : M}
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x₀_val : Tensor0SSpace r I x₀)
    (d : Fin (Module.finrank ℝ E) → ℝ)
    (θ : Fin (Module.finrank ℝ E) → Tensor0SSpace 1 I x₀)
    (v : Fin (s + 1) → E) :
    Tensor0SSpace.toModel
        (T x₀ (castTensor0SComm I M r x₀
          (slot0Insert I M (∑ j, d j • θ j) x₀_val))) v =
      ∑ j, d j •
        Tensor0SSpace.toModel
          (T x₀ (castTensor0SComm I M r x₀ (slot0Insert I M (θ j) x₀_val))) v := by
  classical
  rw [show (∑ j, d j • θ j) = ∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), d j • θ j
    from rfl]
  rw [slot0Insert_sum_first]
  -- Push the sum through castTensor0SComm, T x₀, toModelL. For the `toModel` we use its
  -- bundled form `toModelL` via `change`.
  rw [map_sum (castTensor0SComm I M r x₀)]
  rw [map_sum (T x₀)]
  change Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) (s + 1) x₀
      (∑ j ∈ Finset.univ, T x₀ ((castTensor0SComm I M r x₀)
        (slot0Insert I M (d j • θ j) x₀_val))) v = _
  rw [map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) (s + 1) x₀)]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- For each j, handle the scalar multiplication.
  rw [slot0Insert_smul_first]
  rw [map_smul (castTensor0SComm I M r x₀)]
  rw [map_smul (T x₀)]
  change (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) (s + 1) x₀
      (d j • T x₀ ((castTensor0SComm I M r x₀) (slot0Insert I M (θ j) x₀_val)))) v = _
  rw [map_smul (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) (s + 1) x₀)]
  rw [ContinuousMultilinearMap.smul_apply]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Multilinearity at slot 0 of `toModel (T x₀ (castTensor0SComm (slot0Insert θi w x₀)))`
applied at `Fin.cons v u`, when `v` itself is a sum `∑ l, e_l • σ'_l`. -/
private lemma toModel_Fin_cons_sum_first (s : ℕ) {x₀ : M}
    (G : Tensor0SSpace (s + 1) I x₀)
    (e : Fin (Module.finrank ℝ E) → ℝ)
    (σ' : Fin (Module.finrank ℝ E) → TangentSpace I x₀)
    (u : Fin s → E) :
    Tensor0SSpace.toModel G (Fin.cons ((∑ l, e l • σ' l) : E) u) =
      ∑ l, e l • Tensor0SSpace.toModel G (Fin.cons ((σ' l : E)) u) := by
  classical
  -- The key lemma: `ContinuousMultilinearMap.map_update_sum` and `map_update_smul`.
  -- First, rewrite `Fin.cons (∑ l, e l • σ' l) u` as `update (fun _ => 0) 0 (sum ...) + ...` form.
  -- Actually simpler: Fin.cons v u is a function indexed by Fin (s+1). At slot 0, it's v;
  -- at slot i.succ, it's u i. We want multilinearity at slot 0.
  have h_cons : (Fin.cons ((∑ l, e l • σ' l : E) : E) u : Fin (s + 1) → E) =
      Function.update (Fin.cons ((0 : E) : E) u) 0 (∑ l, e l • σ' l) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · simp
    · intro j
      simp
  rw [h_cons]
  -- Push the sum through via MultilinearMap.map_update_sum (via .toMultilinearMap).
  rw [show (Tensor0SSpace.toModel G) (Function.update (Fin.cons ((0 : E) : E) u) 0 (∑ l, e l • σ' l))
      = (Tensor0SSpace.toModel G).toMultilinearMap
        (Function.update (Fin.cons ((0 : E) : E) u) 0 (∑ l, e l • σ' l)) from rfl]
  rw [MultilinearMap.map_update_sum
    (Tensor0SSpace.toModel G).toMultilinearMap
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))) 0
    (fun l => e l • σ' l) (Fin.cons ((0 : E) : E) u)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [MultilinearMap.map_update_smul]
  -- Now have to show: e l • toModel G (update (Fin.cons 0 u) 0 (σ'_l)) =
  --                 e l • toModel G (Fin.cons (σ'_l) u).
  congr 1
  change (Tensor0SSpace.toModel G) _ = _
  congr 1
  funext k
  refine Fin.cases ?_ ?_ k
  · simp
  · intro j
    simp

open TensorRSNabla in
set_option maxHeartbeats 8000000 in
-- Heavy chain of frame expansion + multilinear distribution + christoffel cancellation.
-- Each step pushes typeclass resolution above defaults; ample budget needed.
/-- **D3: Summand equality.** `∑_i LHS_summand i = ∑_i RHS_summand i` as elements of
`TensorRSSpace r s I x₀`. Proof proceeds by extensionality on a test vector `β`, evaluation via
`toModel` at an arbitrary `u : Fin s → E`, decomposition via D0/D1 and H1, and final Christoffel
cancellation via `christoffel_sum_zero`. -/
private lemma concrete_nabla_contract_comm_sum_eq
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
    (hθ_smooth : ∀ᶠ x in 𝓝 x₀, ∀ i, (θ_smooth i) x =
      (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis (E := E)) i x) :
    (∑ i, LHS_summand I M cov X r s T σ' θ_smooth x₀ i) =
    (∑ i, RHS_summand I M cov X r s T σ' θ_smooth x₀ i) := by
  classical
  -- Step 1: extensionality on a test vector β ∈ Tensor0SSpace r I x₀.
  apply ContinuousLinearMap.ext
  intro β
  -- Step 2: toModel_injective + ext on u : Fin s → E.
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  apply Tensor0SSpace.toModel_injective (I := I) (x := x₀) (𝕜 := ℝ)
  apply ContinuousMultilinearMap.ext
  intro u
  -- Step 3: lift β to a smooth Tensor0SField r via exists_eq_at.
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I) (F := Tensor0SModel r ℝ E)
    (V := fun x => Tensor0SSpace r I x) (n := (⊤ : ℕ∞)) x₀ β
  -- Replace β by w x₀.
  rw [show β = w x₀ from hw.symm]
  -- Step 4: push sum + evaluation.
  -- Goal: toModel(∑ i, LHS_summand i (w x₀))(u) = toModel(∑ i, RHS_summand i (w x₀))(u).
  have h_lhs_split :
      Tensor0SSpace.toModel
        (∑ d, LHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀)) =
      (∑ d, Tensor0SSpace.toModel
        (LHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀))
          : ContinuousMultilinearMap _ _ _) :=
    map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) s x₀) _ _
  have h_rhs_split :
      Tensor0SSpace.toModel
        (∑ d, RHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀)) =
      (∑ d, Tensor0SSpace.toModel
        (RHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀))
          : ContinuousMultilinearMap _ _ _) :=
    map_sum (Tensor0SSpace.toModelL (𝕜 := ℝ) (I := I) s x₀) _ _
  change Tensor0SSpace.toModel
      (∑ d, LHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀)) u =
    Tensor0SSpace.toModel
      (∑ d, RHS_summand I M cov X r s T σ' θ_smooth x₀ d (w x₀)) u
  rw [h_lhs_split, h_rhs_split]
  rw [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  -- Step 5: per-i decomposition.
  -- For each i: LHS_summand i (w x₀) = LHS_Term_outer i w − LHS_Term_inner i w.
  -- toModel(LHS_summand i (w x₀))(u) = toModel(LHS_Term_outer i w)(u) - toModel(LHS_Term_inner i w)(u).
  -- toModel(LHS_Term_outer i w)(u) = MAIN_i + ChriT_i + ChriW_i + MAIN_Tw_i
  --   where:
  --     MAIN_i = toModel(∇T(castTensor0SComm(slot0Insert θi w_x₀))) (Fin.cons σ'_i u)
  --     ChriT_i = toModel(T(castTensor0SComm(slot0Insert ∇θi w_x₀))) (Fin.cons σ'_i u)
  --     ChriW_i = toModel(T(castTensor0SComm(slot0Insert θi ∇w_x₀))) (Fin.cons σ'_i u)
  --     MAIN_Tw_i = toModel(T(castTensor0SComm(slot0Insert θi w_x₀))) (Fin.cons cov_σ'_i u)
  -- toModel(LHS_Term_inner i w)(u) = ChriW_i (same as above).
  -- toModel(RHS_summand i (w x₀))(u) = MAIN_i (same as above).
  -- So toModel(LHS_summand i (w x₀))(u) - toModel(RHS_summand i (w x₀))(u)
  --   = ChriT_i + MAIN_Tw_i.
  have h_per_i : ∀ i,
      Tensor0SSpace.toModel (LHS_summand I M cov X r s T σ' θ_smooth x₀ i (w x₀)) u -
      Tensor0SSpace.toModel (RHS_summand I M cov X r s T σ' θ_smooth x₀ i (w x₀)) u =
      Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀))
              (w x₀))))
          (Fin.cons ((σ' i) x₀ : E) u)
      + Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀) (w x₀))))
          (Fin.cons (cov (σ' i) x₀ (X x₀) : E) u) := by
    intro i
    -- LHS_summand i (w x₀) = LHS_Term_outer i w - LHS_Term_inner i w.
    rw [LHS_summand_as_outer_inner I M cov X r s T σ' θ_smooth x₀ i w]
    -- toModel_sub first.
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
    -- LHS_Term_outer decomposition.
    rw [LHS_Term_outer_decompose I M cov X r s T σ' θ_smooth x₀ i w u]
    -- LHS_Term_inner decomposition.
    rw [LHS_Term_inner_toModel_apply I M cov X r s T σ' θ_smooth x₀ i w u]
    -- RHS_summand decomposition.
    rw [RHS_summand_toModel_apply I M cov X r s T σ' θ_smooth x₀ i (w x₀) u]
    -- After these rewrites, we have (4 terms - 1 term - 1 term = 2 terms).
    ring
  -- Step 6: rewrite ∑ LHS - ∑ RHS = ∑ (LHS_i - RHS_i) = ∑ (ChriT_i + MAIN_Tw_i).
  rw [← sub_eq_zero]
  rw [← Finset.sum_sub_distrib]
  simp only [h_per_i]
  rw [Finset.sum_add_distrib]
  -- Goal: (∑ i, ChriT_i (Fin.cons σ'_i u)) + (∑ i, MAIN_Tw_i (Fin.cons cov_σ'_i u)) = 0.
  -- Step 7: expand ChriT_i via tensor0S1_expand_in_dualFrame_at on ∇θ_i.
  -- First, get the biorthogonality and basis hypotheses at x₀.
  have hσ'_at : ∀ i, (σ' i) x₀ =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x₀ := hσ'.self_of_nhds
  have hθ_smooth_at : ∀ i, (θ_smooth i) x₀ =
      (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis (E := E)) i x₀ := hθ_smooth.self_of_nhds
  have hx_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have hx_1 : x₀ ∈ (trivializationAt (Tensor0SModel 1 ℝ E)
      (fun x => Tensor0SSpace 1 I x) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have h_biorth : ∀ i j,
      (Tensor0SSpace.toModel ((θ_smooth i) x₀)) (fun _ => ((σ' j) x₀ : TangentSpace I x₀)) =
        (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [hσ'_at j, hθ_smooth_at i]
    exact matching_frames_biorth I M x₀ x₀ hx_tan hx_1 i j
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let bE := Module.finBasis (R := ℝ) (M := E)
  let le : TangentSpace I x₀ ≃ₗ[ℝ] E := e_tan.linearEquivAt ℝ x₀ hx_tan
  have hσ'_eq : ∀ i, (σ' i) x₀ = le.symm (bE i) := by
    intro i
    rw [hσ'_at i]
    change e_tan.localFrame bE i x₀ = le.symm (bE i)
    rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hx_tan)]
    simp [Trivialization.basisAt, le]
  have h_linind : LinearIndependent ℝ (fun i => (σ' i) x₀) := by
    have h1 : LinearIndependent ℝ (fun i => le.symm (bE i)) :=
      bE.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ' i) x₀) = (fun i => le.symm (bE i)) := funext hσ'_eq
    rw [h2]; exact h1
  have h_span : Submodule.span ℝ (Set.range (fun i => (σ' i) x₀)) = ⊤ := by
    have h2 : (fun i => (σ' i) x₀) = (fun i => le.symm (bE i)) := funext hσ'_eq
    rw [h2]
    rw [show Set.range (fun i => le.symm (bE i)) =
        le.symm.toLinearMap '' Set.range bE by
      ext w'; simp [Set.mem_range, Set.mem_image]]
    rw [Submodule.span_image, bE.span_eq]
    simp
  have h_basis : LinearIndependent ℝ (fun i => ((σ' i) x₀ : TangentSpace I x₀)) ∧
      Submodule.span ℝ (Set.range (fun i => ((σ' i) x₀ : TangentSpace I x₀))) = ⊤ :=
    ⟨h_linind, h_span⟩
  -- Step 8: For each i, expand ∇θ_i via tensor0S1_expand_in_dualFrame_at.
  have h_expand_θ : ∀ i,
      Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀) =
      ∑ j, (Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀)))
          (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)) • (θ_smooth j) x₀ := by
    intro i
    exact tensor0S1_expand_in_dualFrame_at I M
      (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀))
      (fun j => (σ' j) x₀) (fun j => (θ_smooth j) x₀) h_biorth h_basis
  -- Step 9: For each i, expand cov σ'_i via tangent_expand_in_frame_at.
  have h_expand_σ : ∀ i,
      cov (σ' i) x₀ (X x₀) =
      ∑ l, (Tensor0SSpace.toModel ((θ_smooth l) x₀))
          (fun _ : Fin 1 => (cov (σ' i) x₀ (X x₀) : TangentSpace I x₀)) • (σ' l) x₀ := by
    intro i
    exact tangent_expand_in_frame_at I M (cov (σ' i) x₀ (X x₀))
      (fun l => (σ' l) x₀) (fun l => (θ_smooth l) x₀) h_biorth h_basis
  -- Step 10: substitute these expansions and push the scalar sums through to match the
  -- christoffel_sum_zero canonical form.
  -- Define F(i, j) := toModel(T(castTensor0SComm(slot0Insert θ_j w x₀)))(Fin.cons σ'_i u).
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      Tensor0SSpace.toModel
        (T x₀ (castTensor0SComm I M r x₀
          (slot0Insert I M ((θ_smooth j) x₀) (w x₀))))
        (Fin.cons ((σ' i) x₀ : E) u) with hF_def
  -- Apply Christoffel sum zero at F.
  have hCsz := christoffel_sum_zero I M cov X x₀ σ' θ_smooth hσ' hθ_smooth F
  -- hCsz: ∑_i ∑_j (∇θ_i)(σ'_j) • F i j + ∑_i ∑_j θ_i(cov σ'_j) • F i j = 0.
  -- Our goal: ∑_i (ChriT_i) + ∑_i (MAIN_Tw_i) = 0.
  -- Show ∑_i (ChriT_i) = ∑_i ∑_j (∇θ_i)(σ'_j) • F i j:
  have h_ChriT_eq :
      (∑ i, Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M
              (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀))
              (w x₀))))
          (Fin.cons ((σ' i) x₀ : E) u)) =
      ∑ i, ∑ j,
        (Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀)))
          (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)) • F i j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Rewrite LHS: slot0Insert (∇θ_i) (w x₀) → slot0Insert (∑_j ... • θ_j) (w x₀).
    have h_pull :
        Tensor0SSpace.toModel (T x₀
            (castTensor0SComm I M r x₀
              (slot0Insert I M
                (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀))
                (w x₀))))
            (Fin.cons ((σ' i) x₀ : E) u) =
        Tensor0SSpace.toModel (T x₀
            (castTensor0SComm I M r x₀
              (slot0Insert I M
                (∑ j, (Tensor0SSpace.toModel
                  (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀)))
                  (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)) • (θ_smooth j) x₀)
                (w x₀))))
            (Fin.cons ((σ' i) x₀ : E) u) := by
      rw [← h_expand_θ i]
    rw [h_pull]
    rw [toModel_T_castTensor0SComm_slot0Insert_sum_smul_first I M r s T (w x₀)
      (fun j => (Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 cov (θ_smooth i) x₀ (X x₀)))
        (fun _ : Fin 1 => ((σ' j) x₀ : TangentSpace I x₀)))
      (fun j => (θ_smooth j) x₀)
      (Fin.cons ((σ' i) x₀ : E) u)]
  -- Show ∑_i (MAIN_Tw_i) = ∑_i ∑_l θ_l(cov σ'_i) • F l i = ∑_j ∑_i θ_i(cov σ'_j) • F i j
  -- (via Finset.sum_comm and reindexing).
  have h_MAIN_Tw_eq :
      (∑ i, Tensor0SSpace.toModel (T x₀
          (castTensor0SComm I M r x₀
            (slot0Insert I M ((θ_smooth i) x₀) (w x₀))))
          (Fin.cons (cov (σ' i) x₀ (X x₀) : E) u)) =
      ∑ i, ∑ j,
        (Tensor0SSpace.toModel ((θ_smooth i) x₀))
          (fun _ : Fin 1 => (cov (σ' j) x₀ (X x₀) : E)) • F i j := by
    -- Rewrite RHS via sum_comm (swap i ↔ j) to match the MAIN_Tw form.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun iout _ => ?_)
    -- Use congr_arg on `toModel ... (Fin.cons · u)` to rewrite `cov σ'_iout x₀ (X x₀)` only in the
    -- Fin.cons slot (not in the inner coefficient).
    have h_pull :
        Tensor0SSpace.toModel (T x₀
            (castTensor0SComm I M r x₀
              (slot0Insert I M ((θ_smooth iout) x₀) (w x₀))))
            (Fin.cons (cov (σ' iout) x₀ (X x₀) : E) u) =
        Tensor0SSpace.toModel (T x₀
            (castTensor0SComm I M r x₀
              (slot0Insert I M ((θ_smooth iout) x₀) (w x₀))))
            (Fin.cons
              ((∑ l, (Tensor0SSpace.toModel ((θ_smooth l) x₀))
                (fun _ : Fin 1 => (cov (σ' iout) x₀ (X x₀) : TangentSpace I x₀)) •
                (σ' l) x₀ : TangentSpace I x₀) : E) u) := by
      rw [← h_expand_σ iout]
    rw [h_pull]
    -- Push the sum through Fin.cons slot 0 via toModel_Fin_cons_sum_first.
    rw [toModel_Fin_cons_sum_first I M s
      (T x₀ (castTensor0SComm I M r x₀ (slot0Insert I M ((θ_smooth iout) x₀) (w x₀))))
      (fun l => (Tensor0SSpace.toModel ((θ_smooth l) x₀))
        (fun _ : Fin 1 => (cov (σ' iout) x₀ (X x₀) : TangentSpace I x₀)))
      (fun l => ((σ' l) x₀ : TangentSpace I x₀))
      u]
    -- Goal: ∑ l, θ_l(cov σ'_iout) • toModel(...) (Fin.cons σ'_l u)
    --   = ∑ iin, θ_iin(cov σ'_iout) • F iin iout.
    -- By definition of F: F l iout = toModel(T(castTensor0SComm(slot0Insert θ_iout w)))(Fin.cons σ'_l u).
  rw [h_ChriT_eq, h_MAIN_Tw_eq]
  -- Goal matches christoffel_sum_zero structure.
  -- hCsz's second sum evaluates θ_i at cov σ'_j (exactly our form).
  exact hCsz

open TensorRSNabla in
/-- **P26 main theorem.** The covariant derivative `∇` commutes with tensor contraction at
the bundle-field level: for any smooth covariant derivative `cov` on `TM`, smooth vector
field `X`, smooth `(r+1, s+1)`-tensor field `T`, and base point `x₀`,
`∇^{(r,s)}_X (concreteTensorContractField T) x₀ (X x₀) =
  concreteTensorContract_fiber r s x₀ (∇^{(r+1, s+1)}_X T x₀ (X x₀))`. -/
theorem concrete_nabla_contract_comm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (r s : ℕ)
    (T : TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (r + 1) (s + 1))
    (x₀ : M) :
    tensorRSCovariantDerivative I M r s cov
        (concreteTensorContractField I M r s T) x₀ (X x₀) =
    concreteTensorContract_fiber I M r s x₀
      (tensorRSCovariantDerivative I M (r+1) (s+1) cov T x₀ (X x₀)) := by
  obtain ⟨σ', θ_smooth, hσ', hθ_smooth⟩ := concrete_nabla_contract_comm_frames_exist I M x₀
  rw [concrete_nabla_contract_comm_lhs_as_sum I M cov X r s T x₀ σ' θ_smooth hσ' hθ_smooth,
      concrete_nabla_contract_comm_rhs_as_sum I M cov X r s T x₀ σ' θ_smooth hσ' hθ_smooth]
  exact concrete_nabla_contract_comm_sum_eq I M cov X r s T x₀ σ' θ_smooth hσ' hθ_smooth

end TensorContractComm

end
