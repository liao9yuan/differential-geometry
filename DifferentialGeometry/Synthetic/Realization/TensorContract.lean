import DifferentialGeometry.Synthetic.Realization.TensorRSNabla
import DifferentialGeometry.Synthetic.Realization.NablaComm
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Tensor.RSTensor.Field

/-!
# SmoothRicciFlow: TensorData-level contraction (P27.1)

This file develops the infrastructure for the `TensorData`-level contraction operation

```
concreteTensorContract r s :
    TensorData (C^∞(M, ℝ)) (Γ(TM)) (r+1) (s+1) →
    TensorData (C^∞(M, ℝ)) (Γ(TM))  r    s
```

used by the Synthetic `AbstractTrace.tensor_contract` structure field.

## Strategy

Given `T : TensorData R V (r+1) (s+1)` and inputs `(m : Fin s → V, n : Fin r → V →ₗR)`,
the contracted value at each `x₀ ∈ M` is computed as a finite sum using a local smooth
frame near `x₀`:
```
(concreteTensorContract T m n) x₀
  = ∑ᵢ T(Fin.cons σ'_i m)(Fin.cons (covectorToFunctional θ'_i) n)(x₀)
```
where `σ' : Fin d → Γ(TM)` and `θ' : Fin d → Γ(T⁰₁M)` are biorthogonal smooth frames
agreeing with `trivializationAt x₀`'s local frames on a neighborhood of `x₀`.

Since `T` is `R_ := C^∞(M, ℝ)`-multilinear and its outputs live in `R_`, the local sum
is immediately a smooth function on the neighborhood where the frames are defined; we
take this local smooth function's value at `x₀` as the pointwise value of the contraction.

## Main declarations

* `covectorToFunctional I M α` : convert a smooth `(0,1)`-tensor field `α` to a
  `C^∞(M, ℝ)`-linear functional on `Γ(TM)`, via pointwise evaluation. This is the
  forward direction of the canonical isomorphism `(0,1)-tensor fields ≃ C^∞(M)-linear
  functionals on Γ(TM)`.

* `concreteTensorContract_localSum I M r s T σ' θ_smooth m n` : the finite-sum
  smooth function on `M` whose value at each `x` is the indexed sum contracting
  `T` on the first `V ⊗ V*` pair, using a tangent frame `σ'` and dual frame
  `θ_smooth`.

* `dualCovectorBasis'` : the dual basis of `Tensor0SModel 1 ℝ E`, used for the
  dual-bundle's local frame.

* `chooseLocalFrames I M x₀` : via `Classical.choose`, a canonical pair of smooth
  tangent frame + smooth dual frame on a neighborhood of `x₀`, matching the
  trivialization-local frames of the tangent and `(0,1)` bundles respectively.

* `concreteTensorContract_fun I M r s T m n` : the pointwise contracted function
  `M → ℝ`. At each `x₀`, the value is the local sum using `chooseLocalFrames x₀`
  evaluated at `x₀`.

* `chooseLocalFrames_biorth_eventually` : biorthogonality of the matching local
  frames on a neighborhood of `x₀`, a prerequisite for reducing to the fiber-level
  basis-invariance theorem.

## Remaining work (future subtasks)

Packaging `concreteTensorContract_fun` as a full `TensorData (R_) (V_) r s`
additionally requires:

1. Smoothness of `concreteTensorContract_fun T m n : M → ℝ` (so it can be wrapped
   as a `C^∞(M, ℝ)`).
2. Multilinearity of the resulting map in the `m` and `n` arguments.

Both reduce to a multilinear-VBC-style reduction: that any `C^∞(M, ℝ)`-multilinear
map on smooth sections factors through the tensor bundle's fibers. This is the
content of a multilinear generalization of `ContMDiffVectorBundleHom.ofTensorialAt`
that is not presently available in the codebase. The definitional bridge via the
local-frame formula (established in this file) is the foundation for that further
step.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle
open Tensor0SBundle
open SyntheticTensor

namespace TensorContractRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Shorthand: the `C^∞(M, ℝ)` algebra (the scalar ring `R` in the Synthetic layer). -/
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-- Shorthand: the `C^∞(M, ℝ)`-module of smooth tangent sections (the module `V`
in the Synthetic layer). -/
private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯

/-! ### Chunk 1 — `covectorToFunctional`

Given a smooth `(0,1)`-tensor field `ω` and a smooth tangent vector field `X`, the pointwise
evaluation `(Tensor0SSpace.toModel (ω x)) (fun _ : Fin 1 => X x) : ℝ` is a smooth function
on `M`. This packages `ω` as a `C^∞(M, ℝ)`-linear functional on `Γ(TM)`. -/

section Chunk1

/-- Pointwise pairing of a `(0,1)`-tensor field with a tangent vector field, yielding a
smooth scalar function. This is the forward direction of the canonical isomorphism
`(0,1)-tensor fields ≃ C^∞(M)-linear functionals on Γ(TM)`.

Smoothness follows from the bilinear continuous model evaluation, combined with the
trivialization round-trip identity — the same pattern as
`contract_Tensor0SField` in `Contract.lean`. -/
private noncomputable def covectorFieldPair
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (X : V_ I M) : M → ℝ :=
  fun x => (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- The scalar function `covectorFieldPair α X` is smooth. -/
private theorem covectorFieldPair_contMDiff
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (X : V_ I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (covectorFieldPair I M α X) := by
  intro x₀
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  -- The pairing is bilinear-continuous as a map from
  -- `Tensor0SModel 1 ℝ E × E → ℝ`, namely `(β, v) ↦ β (fun _ => v)`.
  let evalCLM : Tensor0SModel 1 ℝ E →L[ℝ] E →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearMap
  have hcl : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun x => evalCLM ((trivializationAt (Tensor0SModel 1 ℝ E)
        (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    (contMDiffAt_const (c := evalCLM)).clm_apply hα
  have h_combine : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => evalCLM ((trivializationAt (Tensor0SModel 1 ℝ E)
          (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, α x⟩).2)
        ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, X x⟩).2)) x₀ :=
    hcl.clm_apply hX
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hbase_1 := (trivializationAt (Tensor0SModel 1 ℝ E)
    (fun x => Tensor0SSpace 1 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase_tan, hbase_1] with x hx_tan hx_1
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  change (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) =
    evalCLM ((e_1 ⟨x, α x⟩).2) ((e_tan ⟨x, X x⟩).2)
  set β : Tensor0SModel 1 ℝ E := (e_1 ⟨x, α x⟩).2 with hβ
  set v : E := (e_tan ⟨x, X x⟩).2 with hv
  change (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) =
    evalCLM β v
  change (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) =
    continuousMultilinearCurryFin1 ℝ E ℝ β v
  rw [continuousMultilinearCurryFin1_apply]
  -- Goal: (toModel (α x)) (fun _ => X x) = β (fun _ => v).
  have h_eq : β = e_1.continuousLinearMapAt ℝ x (α x) := by
    change (e_1 ⟨x, α x⟩).2 = e_1.linearMapAt ℝ x (α x)
    rw [e_1.coe_linearMapAt_of_mem (R := ℝ) hx_1]
  have h_eq_v : v = e_tan.continuousLinearMapAt ℝ x (X x) := by
    change (e_tan ⟨x, X x⟩).2 = e_tan.linearMapAt ℝ x (X x)
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
  rw [h_eq, h_eq_v]
  have h_round : e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (X x)) = X x :=
    e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan (X x)
  have h_1MLap : ∀ (G : Tensor0SSpace 1 I x) (v' : Fin 1 → TangentSpace I x),
      (e_1.continuousLinearMapAt ℝ x G) v' = G (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro G v'
    have hGfib : G = e_1.symmL ℝ x (e_1.continuousLinearMapAt ℝ x G) :=
      (e_1.symmL_continuousLinearMapAt (R := ℝ) hx_1 G).symm
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan (e_1.continuousLinearMapAt ℝ x G)
    rw [hsym] at hGfib
    conv_rhs => rw [hGfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  -- The `continuousMultilinearCurryFin1_apply` form uses `Fin.snoc 0 (e_tan.cLMA x (X x))`.
  -- Convert it to `fun _ : Fin 1 => e_tan.cLMA x (X x)`.
  rw [show (Fin.snoc 0 ((e_tan.continuousLinearMapAt ℝ x) (X x))
        : Fin 1 → TangentSpace I x) =
      (fun _ : Fin 1 => e_tan.continuousLinearMapAt ℝ x (X x)) by
    funext i; fin_cases i; rfl]
  rw [h_1MLap (α x) (fun _ : Fin 1 => e_tan.continuousLinearMapAt ℝ x (X x))]
  congr 1
  funext i
  exact h_round.symm

/-- A smooth `(0,1)`-tensor field `α` acts on smooth vector fields by pointwise evaluation,
producing a `C^∞(M, ℝ)`-linear functional on `Γ(TM)`. -/
noncomputable def covectorToFunctional
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1) :
    V_ I M →ₗ[R_ I M] R_ I M where
  toFun X := ⟨covectorFieldPair I M α X, covectorFieldPair_contMDiff I M α X⟩
  map_add' X Y := by
    apply ContMDiffMap.ext; intro x
    change (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => (X + Y) x) =
      (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) +
      (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => Y x)
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [show (fun _ : Fin 1 => X x + Y x) =
          Function.update (fun _ : Fin 1 => X x) 0 (X x + Y x) by
      funext k; fin_cases k; rfl]
    rw [show ((Tensor0SSpace.toModel (α x))
          (Function.update (fun _ : Fin 1 => X x) 0 (X x + Y x))) =
        ((Tensor0SSpace.toModel (α x))
          (Function.update (fun _ : Fin 1 => X x) 0 (X x))) +
        ((Tensor0SSpace.toModel (α x))
          (Function.update (fun _ : Fin 1 => X x) 0 (Y x))) from
      (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_add
        (fun _ : Fin 1 => X x) 0 (X x) (Y x)]
    congr 1
    · rw [show Function.update (fun _ : Fin 1 => X x) 0 (X x) = (fun _ : Fin 1 => X x) by
        funext k; fin_cases k; rfl]
    · rw [show Function.update (fun _ : Fin 1 => X x) 0 (Y x) = (fun _ : Fin 1 => Y x) by
        funext k; fin_cases k; rfl]
  map_smul' f X := by
    apply ContMDiffMap.ext; intro x
    change (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => (f • X) x) =
      f x * (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x)
    simp only [ContMDiffSection.coe_smulContMDiffMap]
    rw [show (fun _ : Fin 1 => (f x : ℝ) • X x) =
          Function.update (fun _ : Fin 1 => X x) 0 ((f x : ℝ) • X x) by
      funext k; fin_cases k; rfl]
    rw [show ((Tensor0SSpace.toModel (α x))
          (Function.update (fun _ : Fin 1 => X x) 0 ((f x : ℝ) • X x))) =
        (f x : ℝ) • ((Tensor0SSpace.toModel (α x))
          (Function.update (fun _ : Fin 1 => X x) 0 (X x))) from
      (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_smul
        (fun _ : Fin 1 => X x) 0 (f x) (X x)]
    rw [show Function.update (fun _ : Fin 1 => X x) 0 (X x) = (fun _ : Fin 1 => X x) by
      funext k; fin_cases k; rfl]
    simp [smul_eq_mul]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem covectorToFunctional_apply
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (X : V_ I M) (x : M) :
    (covectorToFunctional I M α X) x =
      (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) := rfl

end Chunk1

/-! ### Chunk 2 — `concreteTensorContract_localSum`

Given a smooth tangent frame `σ'` and smooth covector frame `θ_smooth`, the local-frame
indexed sum expressing the partial-trace on the first `V ⊗ V*` pair. -/

section Chunk2

/-- The local-frame indexed sum: given smooth frames `σ'` (tangent) and `θ_smooth` (dual), the
smooth function `M → ℝ` representing the `(r+1, s+1) → (r, s)` partial trace of `T` on the
first `V ⊗ V*` factor, evaluated at fixed `m : Fin s → V_` vectors and
`n : Fin r → V_ →ₗ[R_] R_` covectors:
```
(concreteTensorContract_localSum T σ' θ_smooth m n)(x)
  = ∑ᵢ T(Fin.cons σ'_i m)(Fin.cons (covectorToFunctional θ_smooth_i) n)(x).
```
Smoothness is free: `T` is `R_`-multilinear and `R_ = C^∞(M, ℝ)`. -/
noncomputable def concreteTensorContract_localSum (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → V_ I M)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) : R_ I M :=
  ∑ i, T (Fin.cons (σ' i) m) (Fin.cons (covectorToFunctional I M (θ_smooth i)) n)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise value of `concreteTensorContract_localSum`: the sum commutes with pointwise
evaluation. -/
@[simp] theorem concreteTensorContract_localSum_apply (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → V_ I M)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x : M) :
    (concreteTensorContract_localSum I M r s T σ' θ_smooth m n) x =
      ∑ i, (T (Fin.cons (σ' i) m)
        (Fin.cons (covectorToFunctional I M (θ_smooth i)) n)) x := by
  -- `∑_i f_i` in `C^∞(M, ℝ)` evaluated at `x` equals `∑_i (f_i x)` in `ℝ`.
  -- Use evaluation at `x` as a ring hom from `C^∞(M, ℝ)` to `ℝ`.
  let evalAt : C^∞⟮I, M; ℝ⟯ →+* ℝ := ContMDiffMap.evalRingHom x
  change evalAt (∑ i, T (Fin.cons (σ' i) m)
      (Fin.cons (covectorToFunctional I M (θ_smooth i)) n)) = _
  rw [map_sum]
  rfl

end Chunk2

/-! ### Chunk 3 — Local dual-covector basis and pointwise canonical formula

The `(0,1)`-bundle has a local frame defined by the tangent bundle's local frame's
dual. We declare `dualCovectorBasis'` here to obtain a smooth dual frame via
`exists_contMDiffSection_eqOn_nhd`. -/

section Chunk3

/-- The biorthogonal basis of `Tensor0SModel 1 ℝ E` — the dual of `Module.finBasis ℝ E`,
transported to `Tensor0SModel 1 ℝ E = ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ`
via the duality `(E →ₗ[ℝ] ℝ) ≃ (E →L[ℝ] ℝ) ≃ Tensor0SModel 1 ℝ E`. -/
noncomputable def dualCovectorBasis' :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (Tensor0SModel 1 ℝ E) :=
  ((Module.finBasis ℝ E).dualBasis).map
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).trans
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearEquiv)

/-- For a given `x₀`, pick smooth frames `σ' : Fin d → V_` (tangent) and
`θ_smooth : Fin d → Tensor0SField ∞ 1` (dual) agreeing with
`trivializationAt x₀`'s local frames on a neighborhood of `x₀`.
Uses `Classical.choose` to produce a deterministic pair. -/
private noncomputable def chooseLocalFrames (x₀ : M) :
    (Fin (Module.finrank ℝ E) → V_ I M) ×
    (Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1) :=
  let e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  let hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  let e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  let hframe_1 := e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞))
    (dualCovectorBasis' (E := E))
  (Classical.choose (hframe_tan.exists_contMDiffSection_eqOn_nhd
      e_tan.open_baseSet (mem_baseSet_trivializationAt _ _ x₀)),
   Classical.choose (hframe_1.exists_contMDiffSection_eqOn_nhd
      e_1.open_baseSet (mem_baseSet_trivializationAt _ _ x₀)))

/-- The tangent frame chosen by `chooseLocalFrames x₀` agrees with `trivializationAt x₀`'s
local frame on a neighborhood of `x₀`. -/
private lemma chooseLocalFrames_σ_eqOn (x₀ : M) :
    ∀ᶠ x in nhds x₀, ∀ i, ((chooseLocalFrames I M x₀).1 i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x := by
  let e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  let hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  exact Classical.choose_spec (hframe_tan.exists_contMDiffSection_eqOn_nhd
    e_tan.open_baseSet (mem_baseSet_trivializationAt _ _ x₀))

/-- The dual frame chosen by `chooseLocalFrames x₀` agrees with the `(0,1)`-bundle's local
frame for `dualCovectorBasis'` on a neighborhood of `x₀`. -/
private lemma chooseLocalFrames_θ_eqOn (x₀ : M) :
    ∀ᶠ x in nhds x₀, ∀ i, ((chooseLocalFrames I M x₀).2 i) x =
      (trivializationAt (Tensor0SModel 1 ℝ E)
        (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis' (E := E)) i x := by
  let e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  let hframe_1 := e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞))
    (dualCovectorBasis' (E := E))
  exact Classical.choose_spec (hframe_1.exists_contMDiffSection_eqOn_nhd
    e_1.open_baseSet (mem_baseSet_trivializationAt _ _ x₀))

end Chunk3

/-! ### Chunk 4 — `concreteTensorContract_fun`

Pointwise contraction function: at each `x₀`, use `chooseLocalFrames x₀` (a canonical
choice via `Classical.choose`) and evaluate the local sum at `x₀`. -/

section Chunk4

/-- The pointwise contracted function `M → ℝ`. At each `x₀`, the value is
`(concreteTensorContract_localSum T (σ'_at x₀) (θ_at x₀) m n)(x₀)`.

The value at each point is determined by the `Classical.choose`-picked local frames
matching `trivializationAt x₀`'s local frame on a neighborhood of `x₀`. -/
noncomputable def concreteTensorContract_fun (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) : M → ℝ :=
  fun x₀ =>
    let frames := chooseLocalFrames I M x₀
    (concreteTensorContract_localSum I M r s T frames.1 frames.2 m n) x₀

/-- Unfolding lemma: the pointwise value of `concreteTensorContract_fun` at `x₀` is the
local-frame sum at `x₀` using `chooseLocalFrames x₀`. -/
@[simp] theorem concreteTensorContract_fun_apply (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M) :
    concreteTensorContract_fun I M r s T m n x₀ =
      ∑ i, (T (Fin.cons ((chooseLocalFrames I M x₀).1 i) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) n)) x₀ := by
  change (concreteTensorContract_localSum I M r s T
      (chooseLocalFrames I M x₀).1 (chooseLocalFrames I M x₀).2 m n) x₀ = _
  rw [concreteTensorContract_localSum_apply]

end Chunk4

/-! ### Chunk 5 — Local-frame formula (canonical expansion)

The pointwise value of `concreteTensorContract_fun` admits a local expansion in terms of
any smooth local frame matching `trivializationAt x₀`'s local frame near `x₀`. This is the
TensorData-level analogue of `concreteTensorContract_fiber_local_formula`.

The proof relies on the fact that `T` is `C^∞(M, ℝ)`-multilinear, hence factors through the
tensor bundle's fibers (a vector bundle characterization for multilinear tensors). The
full proof is deferred to subsequent work; here we only formulate the target statement
and expose the `chooseLocalFrames` interface. -/

section Chunk5

/-- The frames chosen at `x₀` (via `Classical.choose`) form a biorthogonal pair at every
point `y` in a neighborhood of `x₀`: the dual-covector frame evaluated against the tangent
frame gives the identity matrix.

This follows from `matching_frames_biorth` (applied on the appropriate intersection of base
sets) combined with `chooseLocalFrames_σ_eqOn` and `chooseLocalFrames_θ_eqOn`. -/
private lemma chooseLocalFrames_biorth_eventually (x₀ : M) :
    ∀ᶠ y in nhds x₀, ∀ i j : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel ((chooseLocalFrames I M x₀).2 i y))
        (fun _ : Fin 1 => (((chooseLocalFrames I M x₀).1 j) y : TangentSpace I y)) =
        (if i = j then (1 : ℝ) else 0) := by
  have hσ := chooseLocalFrames_σ_eqOn I M x₀
  have hθ := chooseLocalFrames_θ_eqOn I M x₀
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  have hbase_1 := (trivializationAt (Tensor0SModel 1 ℝ E)
    (fun x => Tensor0SSpace 1 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hσ, hθ, hbase_tan, hbase_1] with y hσy hθy hy_tan hy_1 i j
  rw [hσy j, hθy i]
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  set b := Module.finBasis (R := ℝ) (M := E)
  rw [e_1.localFrame_apply_of_mem_baseSet (hx := hy_1)]
  rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hy_tan)]
  simp only [Trivialization.basisAt, Module.Basis.map_apply]
  have h_toModel_symm : ∀ (M : Tensor0SModel 1 ℝ E) (v : Fin 1 → TangentSpace I y),
      (Tensor0SSpace.toModel
        ((e_1.linearEquivAt ℝ y hy_1).symm M) : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ)
        v =
      M (fun i => e_tan.continuousLinearMapAt ℝ y (v i)) := by
    intro M v
    have h_symm_eq : ((e_1.linearEquivAt ℝ y hy_1).symm M : Tensor0SSpace 1 I y) =
        e_1.symmL ℝ y M := by rfl
    rw [h_symm_eq]
    rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ y hy_tan]
    rfl
  rw [h_toModel_symm (dualCovectorBasis' i)
    (fun _ : Fin 1 => (e_tan.linearEquivAt ℝ y hy_tan).symm (b j))]
  have h_round : e_tan.continuousLinearMapAt ℝ y ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) =
      b j := by
    change e_tan.linearMapAt ℝ y ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) = b j
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hy_tan]
    change (e_tan.linearEquivAt ℝ y hy_tan) ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) = b j
    rw [LinearEquiv.apply_symm_apply]
  have h_funext : (fun _k : Fin 1 => e_tan.continuousLinearMapAt ℝ y
        ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j))) =
      (fun _ : Fin 1 => b j) := by
    funext k; exact h_round
  rw [h_funext]
  -- Goal: dualCovectorBasis' i (fun _ => b j) = if i = j then 1 else 0.
  -- `dualCovectorBasis'` is the dual basis, so this is biorthogonality.
  unfold dualCovectorBasis'
  rw [Module.Basis.map_apply]
  change (continuousMultilinearCurryFin1 ℝ E ℝ).symm
      ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))
        ((Module.finBasis ℝ E).dualBasis i)) (fun _ : Fin 1 => b j) = _
  rw [continuousMultilinearCurryFin1_symm_apply]
  change ((Module.finBasis ℝ E).dualBasis i) (b j) = _
  change ((Module.finBasis ℝ E).dualBasis i) ((Module.finBasis ℝ E) j) =
    if i = j then (1 : ℝ) else 0
  simp only [Module.Basis.dualBasis_apply, Module.Basis.repr_self]
  by_cases h : j = i
  · rw [if_pos h.symm, Finsupp.single_apply, if_pos h]
  · rw [if_neg (fun heq => h heq.symm), Finsupp.single_apply, if_neg h]

end Chunk5

/-! ### Chunk 6 — Multilinear pointwise evaluation

A key `C^∞(M,ℝ)`-multilinear-VBC bridge: a `TensorData`-valued evaluation at `x₀`
depends only on the fiber values of the vector inputs and the pointwise action of the
covector inputs. This is established via iterated application of
`smoothLinearMap_acts_pointwise` (for vector slots) and a covector-analog lemma
`smoothLinearMap_acts_pointwise_covector` (for covector slots). -/

section Chunk6

open scoped Topology

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- Pointwise ring-evaluation at `x₀` respects finite sums in `R_ = C^∞(M, ℝ)`. -/
private lemma R_evalAt_sum {ι : Type*} (s : Finset ι) (f : ι → R_ I M) (x₀ : M) :
    (∑ i ∈ s, f i) x₀ = ∑ i ∈ s, (f i) x₀ := by
  let evalAt : C^∞⟮I, M; ℝ⟯ →+* ℝ := ContMDiffMap.evalRingHom x₀
  change evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, evalAt (f i)
  exact map_sum evalAt f s

/-- **Covector-slot pointwise action.** Given an `R_`-linear functional
`F : (V_ →ₗ[R_] R_) →ₗ[R_] R_`, if two smooth covectors `β₁, β₂ : V_ →ₗ[R_] R_` produce
the same value at `x₀` on every smooth vector field `X`, i.e. `β₁ X x₀ = β₂ X x₀`, then
`F β₁ x₀ = F β₂ x₀`.

Proved by: subtracting to get `ψ := β₁ - β₂` with `ψ X x₀ = 0` for every `X`, then using
a smooth bump `χ` with `χ x₀ = 1` and a local biorthogonal frame to show `χ • ψ` equals
a finite `R_`-linear combination of basis covectors `covectorToFunctional θ'_i`, whose
coefficients vanish at `x₀`. Applying `F` and `R_`-linearity gives `F ψ x₀ = 0`. -/
theorem smoothLinearMap_acts_pointwise_covector
    (F : (V_ I M →ₗ[R_ I M] R_ I M) →ₗ[R_ I M] R_ I M)
    (β₁ β₂ : V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M)
    (h : ∀ X : V_ I M, (β₁ X) x₀ = (β₂ X) x₀) :
    (F β₁) x₀ = (F β₂) x₀ := by
  -- Reduce to showing `F ψ x₀ = 0` for `ψ := β₁ - β₂` with `ψ X x₀ = 0` for every X.
  suffices h_zero : ∀ ψ : V_ I M →ₗ[R_ I M] R_ I M,
      (∀ X : V_ I M, (ψ X) x₀ = 0) → (F ψ) x₀ = 0 by
    have hψ : ∀ X : V_ I M, ((β₁ - β₂) X) x₀ = 0 := fun X => by
      simp only [LinearMap.sub_apply, ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero]
      exact h X
    have := h_zero (β₁ - β₂) hψ
    rw [map_sub, ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at this
    exact this
  intro ψ hψ
  -- Set up local biorthogonal frames and smooth bump.
  have hσ := chooseLocalFrames_σ_eqOn I M x₀
  have hθ := chooseLocalFrames_θ_eqOn I M x₀
  have hbiorth := chooseLocalFrames_biorth_eventually I M x₀
  -- Choose a smooth bump function χ with χ x₀ = 1, supp ⊂ nbhd where frames agree.
  obtain ⟨U, hU_nhds, hU_biorth⟩ := hbiorth.exists_mem
  obtain ⟨Uσ, hUσ_nhds, hUσ_eq⟩ := hσ.exists_mem
  obtain ⟨Uθ, hUθ_nhds, hUθ_eq⟩ := hθ.exists_mem
  -- Also require the tangent trivialization base set, for fiberwise basis expansion.
  have hbase_tan_nhds :
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ nhds x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
  have hUinter_nhds : U ∩ Uσ ∩ Uθ ∩
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ nhds x₀ :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hU_nhds hUσ_nhds) hUθ_nhds)
      hbase_tan_nhds
  obtain ⟨χ, hχ_supp_inter, hχ_tsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp hUinter_nhds
  -- Set up notation for frames.
  set σ' := (chooseLocalFrames I M x₀).1 with hσ'_def
  set θ' := (chooseLocalFrames I M x₀).2 with hθ'_def
  -- The smooth bump as `R_`.
  let χ' : R_ I M := ⟨χ, χ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  have hχ'_at_x₀ : χ' x₀ = 1 := χ.eq_one
  -- The smoothly-extended pointwise-evaluating covectors `covectorToFunctional (θ' i) : V_ →ₗ[R_] R_`.
  let θ_funct : Fin (Module.finrank ℝ E) → (V_ I M →ₗ[R_ I M] R_ I M) :=
    fun i => covectorToFunctional I M (θ' i)
  -- The local coefficient `ψ σ' i ∈ R_`. At x₀, this evaluates to `(ψ (σ' i)) x₀ = 0`.
  let a : Fin (Module.finrank ℝ E) → R_ I M := fun i => ψ (σ' i)
  have ha_at_x₀ : ∀ i, (a i) x₀ = 0 := fun i => hψ (σ' i)
  -- `χ' • ψ = ∑_i (χ' * a i) • θ_funct i` as elements of `V_ →ₗ[R_] R_`.
  -- Because on supp(χ'), for every X, ψ X = ∑_i ((θ_funct i) X) • (a i) (biorth expansion).
  -- And outside supp(χ'), both sides are 0.
  have h_decomp : χ' • ψ = ∑ i, (χ' * a i) • θ_funct i := by
    refine LinearMap.ext (fun X => ?_)
    -- Show: (χ' • ψ) X = (∑_i (χ' * a i) • θ_funct i) X as elements of R_.
    -- Equivalently, as smooth functions at every y : M.
    refine ContMDiffMap.ext (fun y => ?_)
    change (χ' • (ψ X) : R_ I M) y = ((∑ i, (χ' * a i) • θ_funct i) X) y
    change ((χ' : R_ I M) * (ψ X)) y = ((∑ i, (χ' * a i) • θ_funct i) X) y
    change ((χ' y : ℝ) * (ψ X) y) = ((∑ i, (χ' * a i) • θ_funct i) X) y
    -- The LinearMap.finset_sum_apply collapses the sum of LinearMaps applied to X.
    rw [show ((∑ i, (χ' * a i) • θ_funct i) X : R_ I M) =
          (∑ i : Fin (Module.finrank ℝ E), ((χ' * a i) • θ_funct i) X) from by
      rw [LinearMap.sum_apply]]
    rw [R_evalAt_sum]
    -- Two cases: y ∈ tsupport χ or not.
    by_cases hy : y ∈ tsupport (χ : M → ℝ)
    · -- y is in the biorthogonal nbhd.
      have hy_all := hχ_tsupp hy
      have hy_U : y ∈ U := hy_all.1.1.1
      have hy_Uσ : y ∈ Uσ := hy_all.1.1.2
      have hy_Uθ : y ∈ Uθ := hy_all.1.2
      have hy_base_tan : y ∈
          (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := hy_all.2
      have hbiorth_y := hU_biorth y hy_U
      have hσ_y := hUσ_eq y hy_Uσ
      have hθ_y := hUθ_eq y hy_Uθ
      -- Fiberwise biorth expansion of X y in the basis {σ' i y}.
      set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
      let le_y : TangentSpace I y ≃ₗ[ℝ] E := e_tan.linearEquivAt ℝ y hy_base_tan
      let b := Module.finBasis (R := ℝ) (M := E)
      -- `σ' i y = le_y.symm (b i)`, hence `{σ' i y}` is a basis of TangentSpace I y.
      have hσ'_eq_y : ∀ i, (σ' i) y = le_y.symm (b i) := by
        intro i
        rw [hσ_y i]
        change e_tan.localFrame b i y = le_y.symm (b i)
        rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hy_base_tan)]
        simp [Trivialization.basisAt, le_y]
      -- The biorthogonal basis `σBasis : Basis (Fin d) ℝ (TangentSpace I y)`.
      let σBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
        b.map le_y.symm
      have hσBasis_apply : ∀ i, σBasis i = (σ' i) y := fun i => by
        change (b.map le_y.symm) i = (σ' i) y
        rw [Module.Basis.map_apply, ← hσ'_eq_y i]
      -- X y decomposes as X y = ∑_i σBasis.coord i (X y) • σBasis i.
      have hX_decomp : X y = ∑ i, (σBasis.coord i) (X y) • ((σ' i) y : TangentSpace I y) := by
        conv_lhs => rw [← σBasis.sum_repr (X y)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [σBasis.coord_apply, hσBasis_apply]
      -- `σBasis.coord i (X y) = (θ_funct i X) y`.
      -- Because (θ_funct i X) y = toModel(θ' i y) (fun _ => X y), and by biorthogonality
      -- this equals the `i`-th coordinate in the dual basis.
      have h_coord_eq : ∀ i, (σBasis.coord i) (X y) = ((θ_funct i) X) y := by
        intro i
        -- σBasis.coord i applied to any basis element σBasis j gives if i=j then 1 else 0.
        -- Similarly, Tensor0SSpace.toModel(θ' i y) (fun _ => σBasis j) also does.
        -- So both are determined by biorth; and on the whole space, they agree by basis extension.
        -- Write X y via σBasis and use biorth.
        have h_toModel_of_sum : ∀ (v : TangentSpace I y),
            (Tensor0SSpace.toModel ((θ' i) y)) (fun _ : Fin 1 => v) = σBasis.coord i v := by
          intro v
          -- By linearity in v, reduce to basis elements.
          have h1 : v = ∑ j, σBasis.repr v j • σBasis j := (σBasis.sum_repr v).symm
          -- Apply the linear map to both sides.
          conv_lhs => rw [h1]
          -- Use linearity of (toModel θ'_i) in its vector argument.
          have h_lin_v : (Tensor0SSpace.toModel ((θ' i) y))
              (fun _ : Fin 1 => ∑ j, σBasis.repr v j • σBasis j) =
              ∑ j, σBasis.repr v j *
                (Tensor0SSpace.toModel ((θ' i) y)) (fun _ : Fin 1 => σBasis j) := by
            -- Use MultilinearMap.map_update_sum + map_update_smul on the underlying MultilinearMap.
            set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I y) ℝ :=
              (Tensor0SSpace.toModel ((θ' i) y)).toMultilinearMap with htm
            change tm (fun _ : Fin 1 => ∑ j, σBasis.repr v j • σBasis j) =
              ∑ j, σBasis.repr v j * tm (fun _ : Fin 1 => σBasis j)
            rw [show (fun _ : Fin 1 => ∑ j, σBasis.repr v j • σBasis j) =
              Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
                (∑ j, σBasis.repr v j • σBasis j) from by
                funext k; fin_cases k; rfl]
            rw [tm.map_update_sum
              (t := Finset.univ)
              (g := fun j => σBasis.repr v j • σBasis j)
              (m := fun _ : Fin 1 => (0 : TangentSpace I y)) (i := 0)]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [tm.map_update_smul
              (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 (σBasis.repr v j) (σBasis j)]
            rw [smul_eq_mul]
            congr 1
            change tm (Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 (σBasis j)) =
              tm (fun _ : Fin 1 => σBasis j)
            congr 1; funext k; fin_cases k; rfl
          rw [h_lin_v]
          -- σBasis j = σ' j y = (via biorth at y) gives toModel θ' i y (fun _ => σBasis j) = if i=j then 1 else 0.
          have h_biorth_via_σBasis : ∀ j,
              (Tensor0SSpace.toModel ((θ' i) y)) (fun _ : Fin 1 => σBasis j) =
                (if i = j then (1 : ℝ) else 0) := by
            intro j
            rw [hσBasis_apply]; exact hbiorth_y i j
          simp_rw [h_biorth_via_σBasis]
          -- ∑ j, σBasis.repr v j * (if i = j then 1 else 0) = σBasis.repr v i = σBasis.coord i v.
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl, mul_one, σBasis.coord_apply]
          · intro j _ hji
            rw [if_neg (fun heq => hji heq.symm), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
        -- So σBasis.coord i (X y) = toModel(θ' i y)(fun _ => X y) = (covectorToFunctional θ' i X) y.
        rw [← h_toModel_of_sum (X y)]
        rfl
      -- Combine: X y = ∑_i ((θ_funct i X) y) • σ' i y.
      have hX_decomp' : X y = ∑ i, (((θ_funct i) X) y) • ((σ' i) y : TangentSpace I y) := by
        rw [hX_decomp]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [h_coord_eq]
      -- Now use ψ's R_-linearity. We show (ψ X) y = ∑_i ((θ_funct i X) y) * (ψ σ' i) y.
      -- Bridge: use smoothLinearMap_acts_pointwise on ψ, swapping X with a combo that agrees at y.
      -- Construct combo: ψ_combo := ∑_i ((θ_funct i X) : R_) • σ' i. This has
      --   ψ_combo y = ∑_i ((θ_funct i X) y) • σ' i y = X y.
      let ψ_combo : V_ I M := ∑ i, ((θ_funct i) X) • (σ' i)
      have hψ_combo_y : ψ_combo y = X y := by
        change (∑ i, ((θ_funct i) X) • (σ' i)) y = X y
        simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
        change ∑ i, (((θ_funct i) X) y : ℝ) • ((σ' i) y : TangentSpace I y) = X y
        -- hX_decomp' gives the result.
        rw [← hX_decomp']
      -- ψ acts pointwise at y: ψ X y = ψ ψ_combo y.
      have h_ψ_eq_y : (ψ X) y = (ψ ψ_combo) y :=
        smoothLinearMap_acts_pointwise I M ψ X ψ_combo y hψ_combo_y.symm
      -- ψ ψ_combo = ∑_i (θ_funct i X) * (ψ σ' i), as elements of R_. Evaluate at y.
      have h_ψ_combo_expand : ψ ψ_combo = ∑ i, ((θ_funct i) X) * (ψ (σ' i)) := by
        change ψ (∑ i, ((θ_funct i) X) • (σ' i)) = _
        rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ψ.map_smul]
        rfl
      rw [h_ψ_eq_y, h_ψ_combo_expand]
      rw [R_evalAt_sum]
      -- Left side: (χ' y) * ∑_i ((θ_funct i X) y) * (ψ σ' i) y, which we rewrite as the RHS sum.
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      -- RHS: ((χ' * a i) • θ_funct i) X y = ((χ' * a i) y) * (θ_funct i X) y.
      change (χ' y : ℝ) * (((θ_funct i) X) y * (ψ (σ' i)) y) =
        ((χ' * a i) y : ℝ) * ((θ_funct i) X) y
      change (χ' y : ℝ) * (((θ_funct i) X) y * (a i) y) =
        ((χ' y : ℝ) * (a i) y) * ((θ_funct i) X) y
      ring
    · -- Outside tsupport χ, χ y = 0.
      have hχ_zero : (χ : M → ℝ) y = 0 := image_eq_zero_of_notMem_tsupport hy
      have hχ'_zero : (χ' y : ℝ) = 0 := hχ_zero
      rw [hχ'_zero, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro i _
      change ((χ' * a i) • θ_funct i) X y = 0
      change ((χ' * a i) y : ℝ) * ((θ_funct i) X) y = 0
      change ((χ' y : ℝ) * (a i) y) * ((θ_funct i) X) y = 0
      rw [hχ'_zero, zero_mul, zero_mul]
  -- Now apply F to both sides and evaluate at x₀.
  have h_goal : (F (χ' • ψ)) x₀ = (F (∑ i, (χ' * a i) • θ_funct i)) x₀ :=
    congrArg (· x₀) (congrArg F h_decomp)
  -- LHS: F (χ' • ψ) x₀ = χ' x₀ * F ψ x₀ = F ψ x₀.
  have h_lhs : (F (χ' • ψ)) x₀ = (F ψ) x₀ := by
    rw [F.map_smul]
    change ((χ' • F ψ) : R_ I M) x₀ = (F ψ) x₀
    change ((χ' : C^∞⟮I, M; ℝ⟯) * F ψ) x₀ = (F ψ) x₀
    change (χ' x₀ : ℝ) * (F ψ) x₀ = (F ψ) x₀
    rw [hχ'_at_x₀, one_mul]
  -- RHS: F (∑_i (χ' * a i) • θ_funct i) x₀ = ∑_i ((χ' * a i) x₀) * (F (θ_funct i)) x₀ = 0.
  have h_rhs : (F (∑ i, (χ' * a i) • θ_funct i)) x₀ = 0 := by
    rw [map_sum]
    rw [R_evalAt_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [F.map_smul]
    change ((χ' * a i) • F (θ_funct i) : R_ I M) x₀ = 0
    change ((χ' * a i) x₀ : ℝ) * (F (θ_funct i)) x₀ = 0
    change ((χ' x₀ : ℝ) * (a i) x₀) * (F (θ_funct i)) x₀ = 0
    rw [ha_at_x₀ i, mul_zero, zero_mul]
  rw [h_lhs, h_rhs] at h_goal
  exact h_goal

/-- **Vector-slot replacement at a fiber.** For any `TensorData` `T` and fixed `m, n` with a
single slot `i` in the vector layer replaced between `X₁` and `X₂` that agree at `x₀`, the
value `T (update m i X) n x₀` is unchanged. Proved by applying
`smoothLinearMap_acts_pointwise` to the `R_`-linear map
`X ↦ T (update m i X) n : V_ →ₗ[R_] R_`. -/
private theorem tensorData_vec_slot_pointwise (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) r (s + 1))
    (m : Fin (s + 1) → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (i : Fin (s + 1)) (X₁ X₂ : V_ I M) (x₀ : M) (h : X₁ x₀ = X₂ x₀) :
    (T (Function.update m i X₁) n) x₀ = (T (Function.update m i X₂) n) x₀ := by
  -- Build the R_-linear map `φ : V_ →ₗ[R_] R_` sending X to `T (update m i X) n`.
  let φ : V_ I M →ₗ[R_ I M] R_ I M :=
    { toFun := fun X => T (Function.update m i X) n
      map_add' := fun X Y => by
        rw [T.map_update_add]; rfl
      map_smul' := fun c X => by
        rw [T.map_update_smul]; rfl }
  exact smoothLinearMap_acts_pointwise I M φ X₁ X₂ x₀ h

/-- **Covector-slot replacement at a fiber.** For any `TensorData` `T` and fixed `m, n` with a
single slot `j` in the covector layer replaced between `β₁` and `β₂` whose values at `x₀` agree
on every vector, the value `T m (update n j β) x₀` is unchanged. Proved by applying
`smoothLinearMap_acts_pointwise_covector` to the `R_`-linear map
`β ↦ T m (update n j β) : (V_ →ₗ[R_] R_) →ₗ[R_] R_`. -/
private theorem tensorData_cov_slot_pointwise (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) s)
    (m : Fin s → V_ I M)
    (n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
    (j : Fin (r + 1)) (β₁ β₂ : V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M)
    (h : ∀ X : V_ I M, (β₁ X) x₀ = (β₂ X) x₀) :
    (T m (Function.update n j β₁)) x₀ = (T m (Function.update n j β₂)) x₀ := by
  -- Build the R_-linear map `F : (V_ →ₗ[R_] R_) →ₗ[R_] R_`.
  -- The output `T m : MultilinearMap R_ (Fin (r+1) → V_ →ₗ R_) R_` is R_-linear in each covector
  -- slot by its `map_update_add'` / `map_update_smul'` fields.
  let Tm : MultilinearMap (R_ I M) (fun _ : Fin (r + 1) => V_ I M →ₗ[R_ I M] R_ I M) (R_ I M) :=
    T m
  let F : (V_ I M →ₗ[R_ I M] R_ I M) →ₗ[R_ I M] R_ I M :=
    { toFun := fun β => Tm (Function.update n j β)
      map_add' := fun β₁' β₂' => by rw [Tm.map_update_add]
      map_smul' := fun c β' => by rw [Tm.map_update_smul]; rfl }
  exact smoothLinearMap_acts_pointwise_covector I M F β₁ β₂ x₀ h

/-- **Multi-slot vector replacement.** For fixed `n`, if two families `m₁, m₂ : Fin s' → V_`
agree pointwise at `x₀`, then `T m₁ n x₀ = T m₂ n x₀`. Proved by induction on `s'`. -/
private theorem tensorData_vec_multi_pointwise (r : ℕ) :
    ∀ (s' : ℕ)
      (T : TensorData (R_ I M) (V_ I M) r s')
      (m₁ m₂ : Fin s' → V_ I M)
      (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
      (x₀ : M),
      (∀ i, (m₁ i) x₀ = (m₂ i) x₀) →
      (T m₁ n) x₀ = (T m₂ n) x₀ := by
  intro s'
  induction s' with
  | zero =>
      intro T m₁ m₂ n x₀ _
      have h_eq : m₁ = m₂ := funext (fun i => i.elim0)
      rw [h_eq]
  | succ s' ih =>
      intro T m₁ m₂ n x₀ hm
      -- Replace `m₁ 0` with `m₂ 0` using vec_slot_pointwise at slot 0, then apply ih on tails.
      -- Strategy: let m_mid := Fin.cons (m₂ 0) (Fin.tail m₁). Show T m₁ n = T m_mid n at x₀
      -- (vec-slot pointwise at slot 0), then T m_mid n = T m₂ n at x₀ (ih on tails using
      -- the currified multilinear structure).
      -- Easier: replace one slot at a time via Function.update and tensorData_vec_slot_pointwise.
      -- Step 1: T m₁ n x₀ = T (update m₁ 0 (m₂ 0)) n x₀.
      have hstep : (T m₁ n) x₀ = (T (Function.update m₁ 0 (m₂ 0)) n) x₀ := by
        have := tensorData_vec_slot_pointwise I M r s' T m₁ n 0 (m₁ 0) (m₂ 0) x₀ (hm 0)
        rw [Function.update_eq_self] at this
        exact this
      rw [hstep]
      -- Step 2: define T' : TensorData ... r s' by fixing slot 0 = m₂ 0, via curryLeft.
      -- Then apply `ih` on tails.
      -- Directly: decompose `Function.update m₁ 0 (m₂ 0) = Fin.cons (m₂ 0) (Fin.tail m₁)`.
      -- But that would be a rewriting; let's work with Function.update throughout.
      -- Redefine: let m_mid := Function.update m₁ 0 (m₂ 0). Want: T m_mid n x₀ = T m₂ n x₀.
      -- Note: (m_mid 0) = m₂ 0, and (m_mid i.succ) = m₁ i.succ. While we want m₂ i.succ.
      -- Use ih: for the (s')-tensor T' := fun mtail => T (Fin.cons (m₂ 0) mtail) n, T' is
      -- a MultilinearMap R_ (Fin s' → V_) R_ (via currying via Fin.cons).
      -- Apply ih on m₁'s tail vs m₂'s tail.
      -- Now have: T (update m₁ 0 (m₂ 0)) n x₀ = T m₂ n x₀. Curry at slot 0 with value m₂ 0.
      set v₀ := m₂ 0 with hv₀
      have hm_mid_eq_cons : Function.update m₁ 0 v₀ = Fin.cons v₀ (Fin.tail m₁) := by
        funext i
        induction i using Fin.cases with
        | zero => simp [Function.update]
        | succ i =>
            simp only [Fin.cons_succ, Function.update, Fin.tail]
            split_ifs with h
            · exfalso; exact Fin.succ_ne_zero i h
            · rfl
      have hm₂_eq_cons : m₂ = Fin.cons v₀ (Fin.tail m₂) := (Fin.cons_self_tail _).symm
      rw [hm_mid_eq_cons]
      conv_rhs => rw [hm₂_eq_cons]
      -- Now we have: T (cons v₀ (tail m₁)) n = T (cons v₀ (tail m₂)) n at x₀.
      -- Curry T at slot 0 with value v₀ to obtain a (r, s')-tensor.
      let T_cons : TensorData (R_ I M) (V_ I M) r s' := T.curryLeft v₀
      have hT_cons_apply : ∀ (mtail : Fin s' → V_ I M),
          T_cons mtail = T (Fin.cons v₀ mtail) := fun mtail => rfl
      rw [show T (Fin.cons v₀ (Fin.tail m₁)) = T_cons (Fin.tail m₁) from
        (hT_cons_apply _).symm,
        show T (Fin.cons v₀ (Fin.tail m₂)) = T_cons (Fin.tail m₂) from
        (hT_cons_apply _).symm]
      exact ih T_cons (Fin.tail m₁) (Fin.tail m₂) n x₀
        (fun i => hm i.succ)

/-- **Multi-slot covector replacement.** For fixed `m`, if two families
`n₁, n₂ : Fin r' → V_ →ₗ[R_] R_` agree pointwise at `x₀` (i.e. `n₁ j X x₀ = n₂ j X x₀` for
all j, X), then `T m n₁ x₀ = T m n₂ x₀`. Proved by induction on `r'`. -/
private theorem tensorData_cov_multi_pointwise :
    ∀ (r' s : ℕ)
      (T : TensorData (R_ I M) (V_ I M) r' s)
      (m : Fin s → V_ I M)
      (n₁ n₂ : Fin r' → V_ I M →ₗ[R_ I M] R_ I M)
      (x₀ : M),
      (∀ j X, (n₁ j X) x₀ = (n₂ j X) x₀) →
      (T m n₁) x₀ = (T m n₂) x₀ := by
  intro r'
  induction r' with
  | zero =>
      intro s T m n₁ n₂ x₀ _
      have h_eq : n₁ = n₂ := funext (fun j => j.elim0)
      rw [h_eq]
  | succ r' ih =>
      intro s T m n₁ n₂ x₀ hn
      have hstep : (T m n₁) x₀ = (T m (Function.update n₁ 0 (n₂ 0))) x₀ := by
        have := tensorData_cov_slot_pointwise I M r' s T m n₁ 0 (n₁ 0) (n₂ 0) x₀ (hn 0)
        rw [Function.update_eq_self] at this
        exact this
      rw [hstep]
      set α₀ := n₂ 0 with hα₀
      have hn_mid_eq_cons : Function.update n₁ 0 α₀ = Fin.cons α₀ (Fin.tail n₁) := by
        funext j
        induction j using Fin.cases with
        | zero => simp [Function.update]
        | succ j =>
            simp only [Fin.cons_succ, Function.update, Fin.tail]
            split_ifs with h
            · exfalso; exact Fin.succ_ne_zero j h
            · rfl
      have hn₂_eq_cons : n₂ = Fin.cons α₀ (Fin.tail n₂) := (Fin.cons_self_tail _).symm
      rw [hn_mid_eq_cons]
      conv_rhs => rw [hn₂_eq_cons]
      -- Build T_cons : TensorData (R_) (V_) r' s obtained by plugging α₀ into the first covector slot.
      -- For each fixed m', T m' is a MultilinearMap on covectors. Curry at slot 0 with α₀.
      let T_cons : TensorData (R_ I M) (V_ I M) r' s :=
        { toFun := fun m' => (T m').curryLeft α₀
          map_update_add' := fun m' i v₁ v₂ => by
            ext ntail
            rw [MultilinearMap.curryLeft_apply, T.map_update_add]
            rfl
          map_update_smul' := fun m' i c v => by
            ext ntail
            rw [MultilinearMap.curryLeft_apply, T.map_update_smul]
            rfl }
      have hT_cons_apply : ∀ (m' : Fin s → V_ I M) (ntail : Fin r' → V_ I M →ₗ[R_ I M] R_ I M),
          T_cons m' ntail = T m' (Fin.cons α₀ ntail) := fun m' ntail => rfl
      rw [show T m (Fin.cons α₀ (Fin.tail n₁)) = T_cons m (Fin.tail n₁) from
        (hT_cons_apply _ _).symm,
        show T m (Fin.cons α₀ (Fin.tail n₂)) = T_cons m (Fin.tail n₂) from
        (hT_cons_apply _ _).symm]
      exact ih s T_cons m (Fin.tail n₁) (Fin.tail n₂) x₀
        (fun j X => hn j.succ X)

/-- **Tensor evaluation depends only on fiber data.** The full multi-slot pointwise-evaluation
statement: given `T : TensorData R_ V_ r s`, two families of vectors `m₁, m₂` agreeing at `x₀`
and two families of covectors `n₁, n₂` agreeing pointwise at `x₀`, the value `T m n x₀`
is invariant. -/
theorem tensorData_eval_pointwise (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) r s)
    (m₁ m₂ : Fin s → V_ I M)
    (n₁ n₂ : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M)
    (hm : ∀ i, (m₁ i) x₀ = (m₂ i) x₀)
    (hn : ∀ j X, (n₁ j X) x₀ = (n₂ j X) x₀) :
    (T m₁ n₁) x₀ = (T m₂ n₂) x₀ := by
  have h1 : (T m₁ n₁) x₀ = (T m₂ n₁) x₀ :=
    tensorData_vec_multi_pointwise I M r s T m₁ m₂ n₁ x₀ hm
  have h2 : (T m₂ n₁) x₀ = (T m₂ n₂) x₀ :=
    tensorData_cov_multi_pointwise I M r s T m₂ n₁ n₂ x₀ hn
  exact h1.trans h2

end Chunk6

/-! ### Chunk 7 — Frame-independence at a fiber

The pointwise value of `concreteTensorContract_localSum T σ' θ_smooth m n x₀` depends only
on the biorthogonal fiber data `(σ'_i x₀, Tensor0SSpace.toModel(θ'_i x₀))` at `x₀` (via
`tensorData_eval_pointwise`), and the bilinear sum over biorthogonal fiber bases is precisely
a trace. The trace is basis-independent (`LinearMap.trace_eq_matrix_trace` +
`LinearMap.trace_conj`), hence any two biorthogonal pairs give the same sum at `x₀`. -/

section Chunk7

/-- **Bilinear scalar `bilinForm T m n x₀ v α`**: at the fiber `x₀`, for `v ∈ TangentSpace I x₀` and
`α ∈ Tensor0SSpace 1 I x₀`, the scalar
`(T (cons v_ext m) (cons (covectorToFunctional α_ext) n)) x₀`
where `v_ext` is any smooth extension of `v` and `α_ext` is any smooth extension of `α`. -/
private noncomputable def bilinForm (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (v : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀) : ℝ :=
  let v_ext := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v).choose
  let α_ext := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α).choose
  (T (Fin.cons v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀

/-- `bilinForm T m n x₀ v α` depends only on (v, α) — not on the choice of smooth extension. -/
private theorem bilinForm_well_defined (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (v : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀)
    (v_ext₁ v_ext₂ : V_ I M)
    (α_ext₁ α_ext₂ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hv₁ : v_ext₁ x₀ = v) (hv₂ : v_ext₂ x₀ = v)
    (hα₁ : α_ext₁ x₀ = α) (hα₂ : α_ext₂ x₀ = α) :
    (T (Fin.cons v_ext₁ m) (Fin.cons (covectorToFunctional I M α_ext₁) n)) x₀ =
      (T (Fin.cons v_ext₂ m) (Fin.cons (covectorToFunctional I M α_ext₂) n)) x₀ := by
  refine tensorData_eval_pointwise I M (r + 1) (s + 1) T _ _ _ _ x₀ ?_ ?_
  · intro i
    induction i using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [hv₁, hv₂]
    | succ i =>
        simp only [Fin.cons_succ]
  · intro j X
    induction j using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [covectorToFunctional_apply, covectorToFunctional_apply, hα₁, hα₂]
    | succ j =>
        simp only [Fin.cons_succ]

/-- Specialization of `bilinForm_well_defined`: if `v_ext` and `α_ext` are any particular
smooth extensions of `v` and `α`, then `bilinForm` equals the expected evaluation. -/
private theorem bilinForm_eval (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (v : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀)
    (v_ext : V_ I M)
    (α_ext : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hv : v_ext x₀ = v) (hα : α_ext x₀ = α) :
    bilinForm I M r s T m n x₀ v α =
      (T (Fin.cons v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀ := by
  classical
  unfold bilinForm
  set v₀ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v).choose
  have hv₀ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v).choose_spec
  set α₀ := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α).choose
  have hα₀ := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α).choose_spec
  exact bilinForm_well_defined I M r s T m n x₀ v α v₀ v_ext α₀ α_ext hv₀ hv hα₀ hα

/-- `bilinForm T m n x₀` is a bilinear form in (v, α). -/
private theorem bilinForm_add_left (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (v w : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀) :
    bilinForm I M r s T m n x₀ (v + w) α =
      bilinForm I M r s T m n x₀ v α + bilinForm I M r s T m n x₀ w α := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v
  obtain ⟨w_ext, hw⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ w
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α
  have hvw : (v_ext + w_ext) x₀ = v + w := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, hv, hw]
  rw [bilinForm_eval I M r s T m n x₀ v α v_ext α_ext hv hα,
    bilinForm_eval I M r s T m n x₀ w α w_ext α_ext hw hα,
    bilinForm_eval I M r s T m n x₀ (v + w) α (v_ext + w_ext) α_ext hvw hα]
  -- By curryLeft, T (cons X m) = (T.curryLeft X) m. Use linearity in X.
  change ((T.curryLeft (v_ext + w_ext) m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀ =
    ((T.curryLeft v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀ +
    ((T.curryLeft w_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀
  rw [map_add]
  rfl

private theorem bilinForm_smul_left (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (c : ℝ) (v : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀) :
    bilinForm I M r s T m n x₀ (c • v) α = c * bilinForm I M r s T m n x₀ v α := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α
  let c' : R_ I M := ⟨fun _ => c, contMDiff_const⟩
  have hcv : (c' • v_ext) x₀ = c • v := by
    rw [ContMDiffSection.coe_smulContMDiffMap]
    change c • v_ext x₀ = c • v
    rw [hv]
  rw [bilinForm_eval I M r s T m n x₀ v α v_ext α_ext hv hα,
    bilinForm_eval I M r s T m n x₀ (c • v) α (c' • v_ext) α_ext hcv hα]
  change ((T.curryLeft (c' • v_ext) m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀ =
    c * ((T.curryLeft v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) x₀
  rw [map_smul]
  rfl

private theorem bilinForm_add_right (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (v : TangentSpace I x₀) (α β : Tensor0SSpace 1 I x₀) :
    bilinForm I M r s T m n x₀ v (α + β) =
      bilinForm I M r s T m n x₀ v α + bilinForm I M r s T m n x₀ v β := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α
  obtain ⟨β_ext, hβ⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ β
  have hαβ : (α_ext + β_ext) x₀ = α + β := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, hα, hβ]
  rw [bilinForm_eval I M r s T m n x₀ v α v_ext α_ext hv hα,
    bilinForm_eval I M r s T m n x₀ v β v_ext β_ext hv hβ,
    bilinForm_eval I M r s T m n x₀ v (α + β) v_ext (α_ext + β_ext) hv hαβ]
  -- `covectorToFunctional (α_ext + β_ext) = covectorToFunctional α_ext + covectorToFunctional β_ext`.
  have h_sum_funct :
      covectorToFunctional I M (α_ext + β_ext) =
        covectorToFunctional I M α_ext + covectorToFunctional I M β_ext := by
    refine LinearMap.ext (fun X => ?_)
    apply ContMDiffMap.ext; intro x
    change (Tensor0SSpace.toModel ((α_ext + β_ext) x)) (fun _ : Fin 1 => X x) =
      ((covectorToFunctional I M α_ext + covectorToFunctional I M β_ext) X) x
    rw [ContMDiffSection.coe_add, Pi.add_apply]
    rw [show Tensor0SSpace.toModel (α_ext x + β_ext x) =
        Tensor0SSpace.toModel (α_ext x) + Tensor0SSpace.toModel (β_ext x) from by
      change (Tensor0SSpace.toModelL 1 x) (α_ext x + β_ext x) =
        (Tensor0SSpace.toModelL 1 x) (α_ext x) + (Tensor0SSpace.toModelL 1 x) (β_ext x)
      rw [map_add]]
    rw [ContinuousMultilinearMap.add_apply]
    rfl
  rw [h_sum_funct]
  -- Use currying on the covector slot: `(T m').curryLeft` makes the 0th covector slot linear.
  change ((T (Fin.cons v_ext m)).curryLeft
      (covectorToFunctional I M α_ext + covectorToFunctional I M β_ext) n) x₀ =
    ((T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M α_ext) n) x₀ +
    ((T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M β_ext) n) x₀
  rw [map_add]
  rfl

private theorem bilinForm_smul_right (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (c : ℝ) (v : TangentSpace I x₀) (α : Tensor0SSpace 1 I x₀) :
    bilinForm I M r s T m n x₀ v (c • α) = c * bilinForm I M r s T m n x₀ v α := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x₀ v
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) x₀ α
  let c' : R_ I M := ⟨fun _ => c, contMDiff_const⟩
  have hcα : (c' • α_ext) x₀ = c • α := by
    rw [ContMDiffSection.coe_smulContMDiffMap]
    change c • α_ext x₀ = c • α
    rw [hα]
  rw [bilinForm_eval I M r s T m n x₀ v α v_ext α_ext hv hα,
    bilinForm_eval I M r s T m n x₀ v (c • α) v_ext (c' • α_ext) hv hcα]
  -- `covectorToFunctional (c' • α_ext) = c' • covectorToFunctional α_ext`.
  have h_smul_funct :
      covectorToFunctional I M (c' • α_ext) = c' • covectorToFunctional I M α_ext := by
    refine LinearMap.ext (fun X => ?_)
    apply ContMDiffMap.ext; intro x
    change (Tensor0SSpace.toModel ((c' • α_ext) x)) (fun _ : Fin 1 => X x) =
      (c' • covectorToFunctional I M α_ext X) x
    rw [ContMDiffSection.coe_smulContMDiffMap]
    rw [show Tensor0SSpace.toModel ((c' x : ℝ) • α_ext x) =
        (c' x : ℝ) • Tensor0SSpace.toModel (α_ext x) from by
      change (Tensor0SSpace.toModelL 1 x) ((c' x : ℝ) • α_ext x) =
        (c' x : ℝ) • (Tensor0SSpace.toModelL 1 x) (α_ext x)
      rw [map_smul]]
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    -- Goal: (c' x : ℝ) * (α_ext x).toModel (fun _ => X x) = (c' • covectorToFunctional I M α_ext X) x.
    rfl
  rw [h_smul_funct]
  change ((T (Fin.cons v_ext m)).curryLeft (c' • covectorToFunctional I M α_ext) n) x₀ =
    c * ((T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M α_ext) n) x₀
  rw [map_smul]
  -- The scalar is c' (a function of C^∞), but at x₀ it's c.
  change ((c' : R_ I M) • (T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M α_ext) n) x₀ =
    c * ((T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M α_ext) n) x₀
  change ((c' : R_ I M) *
    (T (Fin.cons v_ext m)).curryLeft (covectorToFunctional I M α_ext) n) x₀ = _
  rfl

/-- The bilinear form, packaged as a `ℝ`-linear map in each argument. -/
private noncomputable def bilinFormLin (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    TangentSpace I x₀ →ₗ[ℝ] Tensor0SSpace 1 I x₀ →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun α => bilinForm I M r s T m n x₀ v α
      map_add' := fun α β => bilinForm_add_right I M r s T m n x₀ v α β
      map_smul' := fun c α => by
        rw [bilinForm_smul_right I M r s T m n x₀ c v α]; rfl }
  map_add' v w := by
    refine LinearMap.ext (fun α => ?_)
    exact bilinForm_add_left I M r s T m n x₀ v w α
  map_smul' c v := by
    refine LinearMap.ext (fun α => ?_)
    change bilinForm I M r s T m n x₀ (c • v) α = c * bilinForm I M r s T m n x₀ v α
    exact bilinForm_smul_left I M r s T m n x₀ c v α

/-- **Fiber-level trace formula.** At `x₀`, the local-frame sum equals the trace of
an explicit endomorphism determined by `T`, `m`, `n`. Since trace is basis-independent,
this gives frame-independence (the next theorem). -/
private theorem concreteTensorContract_localSum_eq_bilinForm_sum (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (σ' : Fin (Module.finrank ℝ E) → V_ I M)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    (concreteTensorContract_localSum I M r s T σ' θ_smooth m n) x₀ =
      ∑ i, bilinForm I M r s T m n x₀ ((σ' i) x₀) ((θ_smooth i) x₀) := by
  rw [concreteTensorContract_localSum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [bilinForm_eval I M r s T m n x₀ ((σ' i) x₀) ((θ_smooth i) x₀) (σ' i) (θ_smooth i) rfl rfl]

/-- **Frame independence at a fiber.** At `x₀`, for any two biorthogonal frame pairs
that each form a basis of the fiber, the local-frame sums coincide.

Strategy: Both sums equal the trace of the endomorphism determined by `bilinFormLin`
using any basis + its dual. Since trace is basis-independent, the two sums agree. -/
private theorem concreteTensorContract_localSum_frame_indep (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (σ'₁ σ'₂ : Fin (Module.finrank ℝ E) → V_ I M)
    (θ'₁ θ'₂ : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M)
    (h_biorth₁ : ∀ i j, (Tensor0SSpace.toModel (θ'₁ i x₀))
      (fun _ : Fin 1 => (σ'₁ j x₀ : TangentSpace I x₀)) = if i = j then 1 else 0)
    (h_biorth₂ : ∀ i j, (Tensor0SSpace.toModel (θ'₂ i x₀))
      (fun _ : Fin 1 => (σ'₂ j x₀ : TangentSpace I x₀)) = if i = j then 1 else 0)
    (h_basis₁ : LinearIndependent ℝ (fun i => (σ'₁ i x₀ : TangentSpace I x₀)) ∧
      Submodule.span ℝ (Set.range (fun i => (σ'₁ i x₀ : TangentSpace I x₀))) = ⊤)
    (h_basis₂ : LinearIndependent ℝ (fun i => (σ'₂ i x₀ : TangentSpace I x₀)) ∧
      Submodule.span ℝ (Set.range (fun i => (σ'₂ i x₀ : TangentSpace I x₀))) = ⊤) :
    (concreteTensorContract_localSum I M r s T σ'₁ θ'₁ m n) x₀ =
      (concreteTensorContract_localSum I M r s T σ'₂ θ'₂ m n) x₀ := by
  -- Convert both sums to bilinFormLin-sum.
  rw [concreteTensorContract_localSum_eq_bilinForm_sum,
    concreteTensorContract_localSum_eq_bilinForm_sum]
  -- Each sum equals the trace of the endomorphism `Φ : TangentSpace I x₀ →ₗ[ℝ] TangentSpace I x₀`
  -- that represents `bilinFormLin` via the double-dual isomorphism in finite-dim.
  -- Fiber-level: the bilinear form `(v, α) ↦ bilinForm v α` determines a linear map Φ via
  -- v ↦ the double-dual element. Then `∑_i bilinForm (b_i) (b*_i) = tr(Φ)`.
  -- Apply `LinearMap.trace_eq_sum_dualBasis_coord_apply`-style identity.
  classical
  -- Construct a basis.
  let basis₁ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis₁.1 (le_of_eq h_basis₁.2.symm)
  let basis₂ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis₂.1 (le_of_eq h_basis₂.2.symm)
  have hb₁_apply : ∀ i, basis₁ i = (σ'₁ i) x₀ := fun i => Module.Basis.mk_apply _ _ _
  have hb₂_apply : ∀ i, basis₂ i = (σ'₂ i) x₀ := fun i => Module.Basis.mk_apply _ _ _
  -- Define the endomorphism Φ : TangentSpace I x₀ →ₗ[ℝ] TangentSpace I x₀.
  -- Use the isomorphism `TangentSpace ≃ (Tensor0SSpace 1)*` via `Tensor0SSpace.toModel`+fin1 curry+dual.
  -- For v ∈ TangentSpace, define Φ(v) ∈ TangentSpace such that
  --   ∀ α, (toModel α)(fun _ => Φ v) = bilinForm v α.
  -- Using finite-dim duality: fix a basis, use its coord functionals.
  -- Concretely: `Φ v := ∑_k (bilinFormLin v (θ'₁ k x₀)) • (σ'₁ k x₀)` works IF the θ'₁'s are the dual basis of σ'₁'s. By `h_biorth₁`, they are.
  let Φ : TangentSpace I x₀ →ₗ[ℝ] TangentSpace I x₀ :=
    ∑ k : Fin (Module.finrank ℝ E),
      (((bilinFormLin I M r s T m n x₀).flip) ((θ'₁ k) x₀)).smulRight (((σ'₁ k) x₀ : TangentSpace I x₀))
  -- Step 1: trace of Φ in basis₁ equals S(σ'₁, θ'₁).
  have h_trace_in_basis₁ : LinearMap.trace ℝ (TangentSpace I x₀) Φ =
      ∑ i, bilinForm I M r s T m n x₀ ((σ'₁ i) x₀) ((θ'₁ i) x₀) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ basis₁]
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Matrix entry (i,i) = basis₁.repr (Φ (basis₁ i)) i.
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hb₁_apply]
    -- Unfold Φ applied to (σ'₁ i x₀): Φ (σ'₁ i x₀) = ∑ k, (bilinFormLin (σ'₁ i x₀) (θ'₁ k x₀)) • (σ'₁ k x₀).
    have hΦ_apply : Φ ((σ'₁ i) x₀) =
        ∑ k, ((bilinFormLin I M r s T m n x₀ ((σ'₁ i) x₀)) ((θ'₁ k) x₀)) • (((σ'₁ k) x₀) : TangentSpace I x₀) := by
      change (∑ k, ((bilinFormLin I M r s T m n x₀).flip ((θ'₁ k) x₀)).smulRight (((σ'₁ k) x₀ : TangentSpace I x₀))) ((σ'₁ i) x₀) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [hΦ_apply, map_sum]
    have h_coord_σ : ∀ k, (basis₁.coord i) ((σ'₁ k) x₀ : TangentSpace I x₀) = if i = k then 1 else 0 := by
      intro k
      rw [← hb₁_apply k]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hik : k = i
      · rw [if_pos hik, if_pos hik.symm]
      · rw [if_neg hik, if_neg (fun h => hik h.symm)]
    simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_coord_σ]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]; rfl
    · intro k _ hki; rw [if_neg (fun h => hki h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Step 2: trace of Φ in basis₂ equals S(σ'₂, θ'₂).
  have h_trace_in_basis₂ : LinearMap.trace ℝ (TangentSpace I x₀) Φ =
      ∑ i, bilinForm I M r s T m n x₀ ((σ'₂ i) x₀) ((θ'₂ i) x₀) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ basis₂]
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hb₂_apply]
    change (basis₂.coord i) (Φ ((σ'₂ i) x₀)) = _
    -- For basis₂ and θ'₂, we need: basis₂.coord i = (Tensor0SSpace.toModel(θ'₂_i x₀)(fun _ => ·))
    -- as linear functionals on TangentSpace I x₀.
    -- This follows from h_biorth₂ and basis₂ = σ'₂.
    -- Use the fact that (σ'₂ j x₀) and (θ'₂ i x₀) form a biorthogonal pair.
    have h_coord_eq : ∀ v : TangentSpace I x₀,
        (basis₂.coord i) v = (Tensor0SSpace.toModel ((θ'₂ i) x₀)) (fun _ : Fin 1 => v) := by
      intro v
      -- By linearity in v, it suffices to check on basis elements.
      -- `basis₂.coord i (basis₂ j) = if i = j then 1 else 0`.
      -- `toModel(θ'₂_i x₀)(fun _ => σ'₂_j x₀) = if i = j then 1 else 0` by h_biorth₂.
      -- Two linear maps agreeing on a basis are equal.
      have h_on_basis : ∀ j,
          (basis₂.coord i) (basis₂ j) =
            (Tensor0SSpace.toModel ((θ'₂ i) x₀)) (fun _ : Fin 1 => basis₂ j) := by
        intro j
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb₂_apply]
        rw [h_biorth₂ i j]
        by_cases hij : j = i
        · rw [if_pos hij, if_pos hij.symm]
        · rw [if_neg hij, if_neg (fun h => hij h.symm)]
      -- Extend from basis-equality to all v.
      have h1 := basis₂.sum_repr v
      -- v = ∑_j basis₂.repr v j • basis₂ j.
      rw [← h1, map_sum]
      -- LHS: ∑_j basis₂.repr v j * basis₂.coord i (basis₂ j). RHS via h_on_basis similar.
      set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
        (Tensor0SSpace.toModel ((θ'₂ i) x₀)).toMultilinearMap
      change _ = tm (fun _ : Fin 1 => ∑ j, basis₂.repr v j • basis₂ j)
      rw [show (fun _ : Fin 1 => ∑ j, basis₂.repr v j • basis₂ j) =
        Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
          (∑ j, basis₂.repr v j • basis₂ j) from by
          funext k; fin_cases k; rfl]
      rw [tm.map_update_sum (t := Finset.univ)
        (g := fun j => basis₂.repr v j • basis₂ j)
        (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
      simp_rw [map_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [tm.map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
        (basis₂.repr v j) (basis₂ j)]
      rw [smul_eq_mul]
      -- Goal: basis₂.repr v j • basis₂.coord i (basis₂ j) = basis₂.repr v j * tm (update (fun _ => 0) 0 (basis₂ j))
      change basis₂.repr v j • basis₂.coord i (basis₂ j) = _
      rw [smul_eq_mul, h_on_basis j]
      -- Reduce: tm (update (fun _ => 0) 0 (basis₂ j)) = tm (fun _ => basis₂ j).
      have h_upd_const : Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0 (basis₂ j) =
          (fun _ : Fin 1 => basis₂ j) := by
        funext k; fin_cases k; rfl
      rw [h_upd_const, smul_eq_mul]
      rfl
    -- Now unfold Φ applied and use h_coord_eq.
    -- Simpler: Φ v = ∑_k (bilinFormLin v θ'₁_k) • σ'₁_k.
    -- So basis₂.coord i (Φ v) = ∑_k bilinFormLin(v, θ'₁_k) * basis₂.coord i (σ'₁_k).
    -- By h_coord_eq, basis₂.coord i (σ'₁_k) = toModel(θ'₂_i x₀)(fun _ => σ'₁_k x₀).
    -- We want to show this equals bilinForm(σ'₂_i x₀, θ'₂_i x₀).
    -- Use bilinearity of bilinFormLin and the dual expansion of (θ'₂_i x₀) in {θ'₁_k x₀}'s basis.
    have hΦ_apply₂ : Φ ((σ'₂ i) x₀) =
        ∑ k, ((bilinFormLin I M r s T m n x₀ ((σ'₂ i) x₀)) ((θ'₁ k) x₀)) •
          (((σ'₁ k) x₀) : TangentSpace I x₀) := by
      change (∑ k, ((bilinFormLin I M r s T m n x₀).flip ((θ'₁ k) x₀)).smulRight (((σ'₁ k) x₀ : TangentSpace I x₀))) ((σ'₂ i) x₀) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [hΦ_apply₂, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_coord_eq]
    -- Goal: ∑ k, bilinFormLin(σ'₂_i x₀, θ'₁_k x₀) * toModel(θ'₂_i x₀)(fun _ => σ'₁_k x₀) =
    --       bilinFormLin(σ'₂_i x₀, θ'₂_i x₀).
    -- Use bilinearity: LHS = bilinFormLin(σ'₂_i x₀, ∑_k toModel(θ'₂_i x₀)(σ'₁_k x₀) • θ'₁_k x₀).
    -- And ∑_k toModel(θ'₂_i x₀)(σ'₁_k x₀) • θ'₁_k x₀ = θ'₂_i x₀ (by dual-basis expansion
    -- of θ'₂_i x₀ in dual basis {θ'₁_k x₀} of the basis {σ'₁_k x₀}).
    rw [show ∑ k, (bilinFormLin I M r s T m n x₀ ((σ'₂ i) x₀)) ((θ'₁ k) x₀) *
          (Tensor0SSpace.toModel ((θ'₂ i) x₀)) (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀)) =
        (bilinFormLin I M r s T m n x₀ ((σ'₂ i) x₀))
          (∑ k, (Tensor0SSpace.toModel ((θ'₂ i) x₀)
              (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀)) from by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, smul_eq_mul, mul_comm]]
    -- Now show ∑_k toModel(θ'₂_i x₀)(σ'₁_k x₀) • θ'₁_k x₀ = θ'₂_i x₀.
    have h_dual_expand :
        ∑ k, (Tensor0SSpace.toModel ((θ'₂ i) x₀)
            (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀) =
        (θ'₂ i) x₀ := by
      -- The `θ'₁_k x₀`'s form a dual basis of `σ'₁_k x₀`'s (by h_biorth₁).
      -- So for any α ∈ Tensor0SSpace 1 I x₀, α = ∑_k toModel(α)(fun _ => σ'₁_k x₀) • θ'₁_k x₀.
      -- This is the tensor-level dual-basis expansion.
      -- Prove by evaluating both sides on an arbitrary v ∈ TangentSpace I x₀.
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      change (Tensor0SSpace.toModel (∑ k, (Tensor0SSpace.toModel ((θ'₂ i) x₀)
          (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀))) v =
        (Tensor0SSpace.toModel ((θ'₂ i) x₀)) v
      rw [show (Tensor0SSpace.toModel
          (∑ k, (Tensor0SSpace.toModel ((θ'₂ i) x₀)
            (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ) =
        ∑ k, Tensor0SSpace.toModel (
          (Tensor0SSpace.toModel ((θ'₂ i) x₀)
            (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀)) from by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 x₀) _ = _
        rw [map_sum]; rfl]
      rw [ContinuousMultilinearMap.sum_apply]
      simp_rw [show ∀ k,
          (Tensor0SSpace.toModel
            ((Tensor0SSpace.toModel ((θ'₂ i) x₀)
              (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) • ((θ'₁ k) x₀))) =
          (Tensor0SSpace.toModel ((θ'₂ i) x₀)
            (fun _ : Fin 1 => ((σ'₁ k) x₀ : TangentSpace I x₀))) •
            Tensor0SSpace.toModel ((θ'₁ k) x₀) from fun k => by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 x₀) _ = _
        rw [map_smul]; rfl]
      simp_rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      -- LHS: ∑_k toModel(θ'₂_i x₀)(fun _ => σ'₁_k x₀) * toModel(θ'₁_k x₀) v.
      -- RHS: toModel(θ'₂_i x₀) v.
      -- This is the bilinear identity: α = ∑_k α(σ'₁_k x₀) • θ'₁_k x₀ in the dual basis.
      -- At the functional level: for any v, toModel(α)(v) = ∑_k α(σ'₁_k) * toModel(θ'₁_k)(v).
      -- This holds by finite-dim dual-basis expansion.
      -- Specifically: v_0 := v 0 ∈ TangentSpace I x₀. Expand v_0 = ∑_k basis₁.repr v_0 k • σ'₁_k x₀.
      -- Then toModel(θ'₂_i x₀)(fun _ => v_0) = ∑_k basis₁.repr v_0 k * toModel(θ'₂_i)(σ'₁_k).
      -- And toModel(θ'₁_k)(fun _ => v_0) = ∑_l basis₁.repr v_0 l * toModel(θ'₁_k)(σ'₁_l)
      --                                  = basis₁.repr v_0 k  (by h_biorth₁).
      -- So ∑_k toModel(θ'₂_i)(σ'₁_k) * toModel(θ'₁_k)(fun _ => v_0) = ∑_k toModel(θ'₂_i)(σ'₁_k) * basis₁.repr v_0 k.
      -- This equals toModel(θ'₂_i)(fun _ => v_0).
      set w := v 0 with hw
      have hv : v = fun _ : Fin 1 => w := by funext k; fin_cases k; rfl
      rw [hv]
      set tm₂ : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
        (Tensor0SSpace.toModel ((θ'₂ i) x₀)).toMultilinearMap
      have h_tm₂_eq : ∀ u : TangentSpace I x₀,
          (Tensor0SSpace.toModel ((θ'₂ i) x₀)) (fun _ : Fin 1 => u) = tm₂ (fun _ : Fin 1 => u) :=
        fun _ => rfl
      simp_rw [h_tm₂_eq]
      -- Expand w in basis₁.
      have hw_expand : w = ∑ k, basis₁.repr w k • basis₁ k := (basis₁.sum_repr w).symm
      conv_rhs => rw [show (fun _ : Fin 1 => w) =
          Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0 w from by
            funext k; fin_cases k; rfl, hw_expand]
      rw [tm₂.map_update_sum (t := Finset.univ) (g := fun k => basis₁.repr w k • basis₁ k)
        (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
      -- Simplify each summand.
      have h_upd_smul : ∀ k, tm₂ (Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
              (basis₁.repr w k • basis₁ k)) =
            basis₁.repr w k * tm₂ (fun _ : Fin 1 => basis₁ k) := fun k => by
        rw [tm₂.map_update_smul]
        rw [show Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
            (basis₁ k) = (fun _ : Fin 1 => basis₁ k) from by funext m; fin_cases m; rfl]
        rw [smul_eq_mul]
      simp_rw [h_upd_smul]
      -- LHS: ∑ k, toModel(θ'₂)(fun _ => σ'₁_k x₀) * toModel(θ'₁_k)(fun _ => w).
      -- Using basis₁ k = σ'₁_k x₀, this equals ∑ k, toModel(θ'₂)(fun _ => basis₁ k) * toModel(θ'₁_k)(fun _ => w).
      -- For each k: toModel(θ'₁_k)(fun _ => w) = ∑_l basis₁.repr w l * toModel(θ'₁_k)(fun _ => basis₁ l)
      --                                      = basis₁.repr w k (by h_biorth₁ and basis₁).
      have h_θ₁_eval : ∀ k,
          (Tensor0SSpace.toModel ((θ'₁ k) x₀)) (fun _ : Fin 1 => w) = basis₁.repr w k := by
        intro k
        set tm₁ : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
          (Tensor0SSpace.toModel ((θ'₁ k) x₀)).toMultilinearMap
        have : (Tensor0SSpace.toModel ((θ'₁ k) x₀)) (fun _ : Fin 1 => w) = tm₁ (fun _ : Fin 1 => w) :=
          rfl
        rw [this, hw_expand]
        rw [show (fun _ : Fin 1 => ∑ l, basis₁.repr w l • basis₁ l) =
          Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
            (∑ l, basis₁.repr w l • basis₁ l) from by
            funext m; fin_cases m; rfl]
        rw [tm₁.map_update_sum (t := Finset.univ) (g := fun l => basis₁.repr w l • basis₁ l)
          (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
        have h_upd_smul₁ : ∀ l, tm₁ (Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
                (basis₁.repr w l • basis₁ l)) =
              basis₁.repr w l * tm₁ (fun _ : Fin 1 => basis₁ l) := fun l => by
          rw [tm₁.map_update_smul, show Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
              (basis₁ l) = (fun _ : Fin 1 => basis₁ l) from by funext m; fin_cases m; rfl]
          rw [smul_eq_mul]
        simp_rw [h_upd_smul₁]
        -- ∑_l basis₁.repr w l * tm₁(fun _ => basis₁ l) = basis₁.repr w k * 1 = basis₁.repr w k.
        -- tm₁(fun _ => basis₁ l) = toModel(θ'₁ k x₀)(fun _ => σ'₁ l x₀) = if k = l then 1 else 0.
        have h_tm₁_basis : ∀ l, tm₁ (fun _ : Fin 1 => basis₁ l) = (if k = l then (1 : ℝ) else 0) := by
          intro l
          change (Tensor0SSpace.toModel ((θ'₁ k) x₀)) (fun _ : Fin 1 => basis₁ l) = _
          rw [hb₁_apply]
          exact h_biorth₁ k l
        simp_rw [h_tm₁_basis]
        rw [basis₁.sum_repr]
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl, mul_one]
        · intro l _ hlk; rw [if_neg (fun h => hlk h.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ k) h
      simp_rw [h_θ₁_eval]
      -- LHS: ∑ k, toModel(θ'₂_i)(fun _ => σ'₁_k x₀) * basis₁.repr w k.
      -- RHS: ∑ k, basis₁.repr w k * tm₂ (fun _ => basis₁ k) = ∑ k, basis₁.repr w k * toModel(θ'₂_i)(fun _ => σ'₁_k).
      -- Equal by commuting multiplication.
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hb₁_apply]
      rw [mul_comm]
    -- Done: we've shown ∑_k ... = θ'₂_i x₀.
    rw [h_dual_expand]
    rfl
  -- Combine both traces:
  rw [← h_trace_in_basis₁, ← h_trace_in_basis₂]

end Chunk7

/-! ### Chunk 8 — Smoothness of `concreteTensorContract_fun`

At each base point `x₀`, the function `concreteTensorContract_fun T m n` agrees on a
neighborhood of `x₀` with the smooth local-frame sum using `chooseLocalFrames x₀`'s frames
(which are smooth on M). Frame-independence (Chunk 7) gives the congruence. -/

section Chunk8

open scoped Topology

/-- **Smoothness of `concreteTensorContract_fun`.** For every input `m, n`, the pointwise
contracted function `M → ℝ` is smooth. -/
theorem concreteTensorContract_fun_smooth (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (concreteTensorContract_fun I M r s T m n) := by
  intro x₀
  -- Fix frames at x₀: σ_x₀, θ_x₀.
  set σ_x₀ := (chooseLocalFrames I M x₀).1 with hσ_x₀
  set θ_x₀ := (chooseLocalFrames I M x₀).2 with hθ_x₀
  -- The fixed-frame sum is smooth (it's in R_).
  have hsum_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (concreteTensorContract_localSum I M r s T σ_x₀ θ_x₀ m n) y) x₀ :=
    (concreteTensorContract_localSum I M r s T σ_x₀ θ_x₀ m n).contMDiff.contMDiffAt
  refine hsum_smooth.congr_of_eventuallyEq ?_
  -- Eventually at y, `concreteTensorContract_fun T m n y = concreteTensorContract_localSum T σ_x₀ θ_x₀ m n y`.
  -- Via frame-independence: at y, chooseLocalFrames y's frames and σ_x₀, θ_x₀ (evaluated at y) are both biorthogonal bases.
  -- Need both biorths to hold at y: one from `chooseLocalFrames_biorth_eventually x₀`, one from
  -- `chooseLocalFrames_biorth_eventually y` (which is only about y's own frames).
  -- The simpler approach: `chooseLocalFrames_biorth_eventually x₀` gives biorth of σ_x₀, θ_x₀ at y
  -- for y in a nbhd of x₀. We need to apply Chunk 7's frame-independence at y using (σ_x₀, θ_x₀) and
  -- (chooseLocalFrames y's frames at y).
  -- For the latter, `chooseLocalFrames_biorth_eventually y` at y gives the biorth. BUT this lives in
  -- a nbhd of y, not x₀. At y = x₀ itself, both biorths hold (x₀ is in both nbhds).
  -- For y ≠ x₀ in the nbhd, `chooseLocalFrames_biorth_eventually y` says biorth holds in a nbhd of y
  -- — in particular at y itself (taking the `self_of_nhds`).
  -- A cleaner formulation: directly use `chooseLocalFrames_biorth_eventually y` at y.
  -- So we need a lemma saying `chooseLocalFrames_biorth_eventually y` evaluated at y.
  -- Note: `(chooseLocalFrames y).2 i y.toModel fun _ => (chooseLocalFrames y).1 j y = δ_ij`.
  -- For this to hold, the Filter.Eventually is about a nbhd of y, but evaluating at y itself
  -- should work (since y ∈ every nbhd of y).
  -- Let's extract:
  have hbiorth_x₀_at_y : ∀ᶠ y in nhds x₀, ∀ i j,
      (Tensor0SSpace.toModel ((θ_x₀ i) y)) (fun _ : Fin 1 => (σ_x₀ j y : TangentSpace I y)) =
        (if i = j then (1 : ℝ) else 0) :=
    chooseLocalFrames_biorth_eventually I M x₀
  -- Also need: at y, (chooseLocalFrames y) is biorth at y itself.
  -- This follows from `chooseLocalFrames_biorth_eventually y` applied at y via `Filter.Eventually.self_of_nhds`.
  -- And σ_x₀_i y is a basis of TangentSpace I y (via the trivialization).
  -- Let's also require y ∈ e_tan.baseSet for basis property of σ_x₀ frame and σ_y frame.
  have hσ_eqOn : ∀ᶠ y in nhds x₀, ∀ i, (σ_x₀ i) y =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i y :=
    chooseLocalFrames_σ_eqOn I M x₀
  have hbase_x₀_nhds :
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ nhds x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbiorth_x₀_at_y, hσ_eqOn, hbase_x₀_nhds] with y hbiorth_y hσ_y hy_base
  -- At y: we need `concreteTensorContract_fun T m n y = concreteTensorContract_localSum T σ_x₀ θ_x₀ m n y`.
  -- `concreteTensorContract_fun T m n y = concreteTensorContract_localSum T (chooseLocalFrames y).1
  --                                         (chooseLocalFrames y).2 m n y` (by definition).
  -- So use frame-independence at y: both pairs are biorth at y and form bases of TangentSpace I y.
  symm
  change (concreteTensorContract_localSum I M r s T σ_x₀ θ_x₀ m n) y =
    concreteTensorContract_fun I M r s T m n y
  rw [concreteTensorContract_fun_apply]
  -- Unfold RHS sum.
  set σ_y := (chooseLocalFrames I M y).1
  set θ_y := (chooseLocalFrames I M y).2
  rw [← concreteTensorContract_localSum_apply I M r s T σ_y θ_y m n y]
  -- Prepare biorth and basis conditions for both pairs.
  have hbiorth_y_at_y := Filter.Eventually.self_of_nhds (chooseLocalFrames_biorth_eventually I M y)
  -- σ_x₀ i y is a basis of TangentSpace I y.
  -- `σ_x₀ i y = e_tan_x₀.localFrame (finBasis ℝ E) i y` (hσ_y).
  -- Since y ∈ e_tan_x₀.baseSet, `e_tan_x₀.localFrame b i y = (linearEquivAt y).symm (b i)`.
  -- And `{linearEquivAt y).symm (b i)}` is a basis (map of basis via LinearEquiv.symm).
  have h_basis_σ_x₀ : LinearIndependent ℝ (fun i => (σ_x₀ i) y : Fin (Module.finrank ℝ E) →
    TangentSpace I y) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_x₀ i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y)) = ⊤ := by
    let le : TangentSpace I y ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ y hy_base
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_x₀ i) y = le.symm (b i) := fun i => by
      rw [hσ_y i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i y = le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hy_base)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_x₀ i) y : Fin (Module.finrank ℝ E) → TangentSpace I y) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I y)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  -- σ_y i y is a basis of TangentSpace I y (similarly).
  have h_basis_σ_y : LinearIndependent ℝ (fun i => (σ_y i) y : Fin (Module.finrank ℝ E) →
    TangentSpace I y) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_y i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y)) = ⊤ := by
    have hσ_y_eq := Filter.Eventually.self_of_nhds (chooseLocalFrames_σ_eqOn I M y)
    have hy_base_y : y ∈ (trivializationAt E (TangentSpace I : M → Type _) y).baseSet :=
      mem_baseSet_trivializationAt _ _ y
    let le : TangentSpace I y ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) y).linearEquivAt ℝ y hy_base_y
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_y i) y = le.symm (b i) := fun i => by
      rw [hσ_y_eq i]
      change (trivializationAt E (TangentSpace I : M → Type _) y).localFrame b i y = le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) y).localFrame_apply_of_mem_baseSet
        (hx := hy_base_y)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_y i) y : Fin (Module.finrank ℝ E) → TangentSpace I y) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I y)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  exact concreteTensorContract_localSum_frame_indep I M r s T σ_x₀ σ_y θ_x₀ θ_y m n y
    hbiorth_y hbiorth_y_at_y h_basis_σ_x₀ h_basis_σ_y

end Chunk8

/-! ### Chunk 9 — Multilinearity of `concreteTensorContract_fun`

The function `concreteTensorContract_fun T m n` is `R_`-multilinear in both `m` and `n`
(at each slot). This follows from T's multilinearity, via the `Fin.cons_update` commuting
identity on the first-slot covariant/contravariant layers. -/

section Chunk9

/-- Additivity of `concreteTensorContract_fun` in a vector slot. -/
private theorem concreteTensorContract_fun_map_update_add_m (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    [inst_s : DecidableEq (Fin s)]
    (m : Fin s → V_ I M) (i : Fin s) (X Y : V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    concreteTensorContract_fun I M r s T (Function.update m i (X + Y)) n =
      concreteTensorContract_fun I M r s T (Function.update m i X) n +
      concreteTensorContract_fun I M r s T (Function.update m i Y) n := by
  funext x₀
  simp only [concreteTensorContract_fun_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Use: T (cons σ_k m) is curryLeft-ed for σ_k. Take T.curryLeft to move vars.
  -- Equivalent: T (Fin.cons σ (update m i X)) Y = T.curryLeft σ (update m i X) Y = (T.curryLeft σ).map_update_add on slot i.
  -- Simpler: use the fact that cons σ_k (update m i Z) = (T.curryLeft σ_k) applied.
  change (T.curryLeft ((chooseLocalFrames I M x₀).1 k) (Function.update m i (X + Y))
    (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n)) x₀ = _
  rw [MultilinearMap.map_update_add]
  rfl

/-- Homogeneity of `concreteTensorContract_fun` in a vector slot. -/
private theorem concreteTensorContract_fun_map_update_smul_m (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    [inst_s : DecidableEq (Fin s)]
    (m : Fin s → V_ I M) (i : Fin s) (c : R_ I M) (X : V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M) :
    concreteTensorContract_fun I M r s T (Function.update m i (c • X)) n x₀ =
      (c x₀ : ℝ) * concreteTensorContract_fun I M r s T (Function.update m i X) n x₀ := by
  simp only [concreteTensorContract_fun_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change (T.curryLeft ((chooseLocalFrames I M x₀).1 k) (Function.update m i (c • X))
    (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n)) x₀ = _
  rw [MultilinearMap.map_update_smul]
  rfl

/-- Additivity of `concreteTensorContract_fun` in a covector slot. -/
private theorem concreteTensorContract_fun_map_update_add_n (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    [inst_r : DecidableEq (Fin r)]
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (j : Fin r) (α β : V_ I M →ₗ[R_ I M] R_ I M) :
    concreteTensorContract_fun I M r s T m (Function.update n j (α + β)) =
      concreteTensorContract_fun I M r s T m (Function.update n j α) +
      concreteTensorContract_fun I M r s T m (Function.update n j β) := by
  funext x₀
  simp only [concreteTensorContract_fun_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change ((T (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)).curryLeft
    (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k))
    (Function.update n j (α + β))) x₀ = _
  rw [MultilinearMap.map_update_add]
  rfl

/-- Homogeneity of `concreteTensorContract_fun` in a covector slot. -/
private theorem concreteTensorContract_fun_map_update_smul_n (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    [inst_r : DecidableEq (Fin r)]
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (j : Fin r) (c : R_ I M) (α : V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M) :
    concreteTensorContract_fun I M r s T m (Function.update n j (c • α)) x₀ =
      (c x₀ : ℝ) * concreteTensorContract_fun I M r s T m (Function.update n j α) x₀ := by
  simp only [concreteTensorContract_fun_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change ((T (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)).curryLeft
    (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k))
    (Function.update n j (c • α))) x₀ = _
  rw [MultilinearMap.map_update_smul]
  rfl

end Chunk9

/-! ### Chunk 10 — `concreteTensorContract : TensorData → TensorData` -/

section Chunk10

/-- The `(r, s)` TensorData contraction of a `(r+1, s+1)` tensor field. -/
noncomputable def concreteTensorContract (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1)) :
    TensorData (R_ I M) (V_ I M) r s where
  toFun m :=
    { toFun := fun n => ⟨concreteTensorContract_fun I M r s T m n,
                        concreteTensorContract_fun_smooth I M r s T m n⟩
      map_update_add' := fun n j α β => by
        apply ContMDiffMap.ext
        intro x₀
        have h := congrFun (concreteTensorContract_fun_map_update_add_n I M r s T m n j α β) x₀
        simp only [Pi.add_apply] at h
        exact h
      map_update_smul' := fun n j c α => by
        apply ContMDiffMap.ext
        intro x₀
        exact concreteTensorContract_fun_map_update_smul_n I M r s T m n j c α x₀ }
  map_update_add' m' i X Y := by
    refine MultilinearMap.ext (fun n => ?_)
    apply ContMDiffMap.ext
    intro x₀
    have h := congrFun (concreteTensorContract_fun_map_update_add_m I M r s T m' i X Y n) x₀
    simp only [Pi.add_apply] at h
    exact h
  map_update_smul' m' i c X := by
    refine MultilinearMap.ext (fun n => ?_)
    apply ContMDiffMap.ext
    intro x₀
    exact concreteTensorContract_fun_map_update_smul_m I M r s T m' i c X n x₀

end Chunk10

/-! ### Chunk 11 — Apply lemma and pointwise formula -/

section Chunk11

/-- `concreteTensorContract` evaluates pointwise to `concreteTensorContract_fun`. -/
@[simp] theorem concreteTensorContract_apply (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M) :
    (concreteTensorContract I M r s T m n) x₀ =
      concreteTensorContract_fun I M r s T m n x₀ := rfl

/-- **Pointwise formula.** At any `x₀`, the `TensorData`-level contraction equals the
local-frame sum using any smooth biorthogonal frame pair matching `trivializationAt x₀`'s
frames near `x₀`. -/
theorem concreteTensorContract_eq_localSum (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M)
    (σ' : Fin (Module.finrank ℝ E) → V_ I M)
    (θ_smooth : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hσ' : ∀ᶠ x in nhds x₀, ∀ i, (σ' i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x)
    (hθ' : ∀ᶠ x in nhds x₀, ∀ i, (θ_smooth i) x =
      (trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis' (E := E)) i x) :
    (concreteTensorContract I M r s T m n) x₀ =
      (concreteTensorContract_localSum I M r s T σ' θ_smooth m n) x₀ := by
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply,
    ← concreteTensorContract_localSum_apply]
  -- σ' and chooseLocalFrames x₀'s frame are both biorth at x₀ (in fact, at x₀ both equal the
  -- trivialization's frames). So apply frame_indep.
  set σ_x₀ := (chooseLocalFrames I M x₀).1
  set θ_x₀ := (chooseLocalFrames I M x₀).2
  -- Biorth of (σ_x₀, θ_x₀) at x₀.
  have hbiorth_x₀ := Filter.Eventually.self_of_nhds
    (chooseLocalFrames_biorth_eventually I M x₀)
  -- Biorth of (σ', θ_smooth) at x₀: follows from hσ', hθ' + trivialization biorth.
  have hbase_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have hbase_1 : x₀ ∈ (trivializationAt (Tensor0SModel 1 ℝ E)
    (fun x => Tensor0SSpace 1 I x) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have hσ'_x₀ := Filter.Eventually.self_of_nhds hσ'
  have hθ'_x₀ := Filter.Eventually.self_of_nhds hθ'
  -- Compute biorth of (σ', θ_smooth) at x₀ directly using hσ'_x₀ + hθ'_x₀ + trivialization biorth.
  have hbiorth' : ∀ i j,
      (Tensor0SSpace.toModel ((θ_smooth i) x₀))
        (fun _ : Fin 1 => (σ' j x₀ : TangentSpace I x₀)) =
      (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [hσ'_x₀ j, hθ'_x₀ i]
    -- Inline the biorth computation (same as `chooseLocalFrames_biorth_eventually`).
    set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
    set e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
    set b := Module.finBasis (R := ℝ) (M := E)
    rw [e_1.localFrame_apply_of_mem_baseSet (hx := hbase_1)]
    rw [e_tan.localFrame_apply_of_mem_baseSet (hx := hbase_tan)]
    simp only [Trivialization.basisAt, Module.Basis.map_apply]
    have h_toModel_symm : ∀ (N : Tensor0SModel 1 ℝ E) (v : Fin 1 → TangentSpace I x₀),
        (Tensor0SSpace.toModel
          ((e_1.linearEquivAt ℝ x₀ hbase_1).symm N) :
            ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) v =
        N (fun i => e_tan.continuousLinearMapAt ℝ x₀ (v i)) := by
      intro N v
      have h_symm_eq : ((e_1.linearEquivAt ℝ x₀ hbase_1).symm N : Tensor0SSpace 1 I x₀) =
          e_1.symmL ℝ x₀ N := by rfl
      rw [h_symm_eq]
      rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
        (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x₀ hbase_tan N]
      rfl
    rw [h_toModel_symm (dualCovectorBasis' i)
      (fun _ : Fin 1 => (e_tan.linearEquivAt ℝ x₀ hbase_tan).symm (b j))]
    have h_round : e_tan.continuousLinearMapAt ℝ x₀
        ((e_tan.linearEquivAt ℝ x₀ hbase_tan).symm (b j)) = b j := by
      change e_tan.linearMapAt ℝ x₀ ((e_tan.linearEquivAt ℝ x₀ hbase_tan).symm (b j)) = b j
      rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hbase_tan]
      change (e_tan.linearEquivAt ℝ x₀ hbase_tan)
        ((e_tan.linearEquivAt ℝ x₀ hbase_tan).symm (b j)) = b j
      rw [LinearEquiv.apply_symm_apply]
    have h_funext : (fun _k : Fin 1 => e_tan.continuousLinearMapAt ℝ x₀
          ((e_tan.linearEquivAt ℝ x₀ hbase_tan).symm (b j))) =
        (fun _ : Fin 1 => b j) := by
      funext k; exact h_round
    rw [h_funext]
    unfold dualCovectorBasis'
    rw [Module.Basis.map_apply]
    change (continuousMultilinearCurryFin1 ℝ E ℝ).symm
        ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))
          ((Module.finBasis ℝ E).dualBasis i)) (fun _ : Fin 1 => b j) = _
    rw [continuousMultilinearCurryFin1_symm_apply]
    change ((Module.finBasis ℝ E).dualBasis i) (b j) = _
    change ((Module.finBasis ℝ E).dualBasis i) ((Module.finBasis ℝ E) j) =
      if i = j then (1 : ℝ) else 0
    simp only [Module.Basis.dualBasis_apply, Module.Basis.repr_self]
    by_cases h : j = i
    · rw [if_pos h.symm, Finsupp.single_apply, if_pos h]
    · rw [if_neg (fun heq => h heq.symm), Finsupp.single_apply, if_neg h]
  -- Basis conditions at x₀ for both frame pairs.
  have h_basis_σ_x₀ : LinearIndependent ℝ (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) →
    TangentSpace I x₀) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) →
        TangentSpace I x₀)) = ⊤ := by
    have hσ_x₀_eq := Filter.Eventually.self_of_nhds (chooseLocalFrames_σ_eqOn I M x₀)
    let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_x₀ i) x₀ = le.symm (b i) := fun i => by
      rw [hσ_x₀_eq i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hbase_tan)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  have h_basis_σ' : LinearIndependent ℝ (fun i => (σ' i) x₀ : Fin (Module.finrank ℝ E) →
    TangentSpace I x₀) ∧
      Submodule.span ℝ (Set.range (fun i => (σ' i) x₀ : Fin (Module.finrank ℝ E) →
        TangentSpace I x₀)) = ⊤ := by
    let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ' i) x₀ = le.symm (b i) := fun i => by
      rw [hσ'_x₀ i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hbase_tan)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ' i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  exact concreteTensorContract_localSum_frame_indep I M r s T σ_x₀ σ' θ_x₀ θ_smooth m n x₀
    hbiorth_x₀ hbiorth' h_basis_σ_x₀ h_basis_σ'

end Chunk11

/-! ### Chunk 12 — Additivity/homogeneity of `concreteTensorContract` and endo-trace identity

Three axiom-theorems preparing for the `AbstractTrace` assembly:

* `concreteTensorContract_add` : `concreteTensorContract` is additive in `T`.
* `concreteTensorContract_smul` : `concreteTensorContract` is `R_`-homogeneous in `T`.
* `concreteTensorContract_endo` : the `(1,1)` contraction of the tensor representation of
  an endomorphism agrees with the `concreteTr` endomorphism trace.
-/

section Chunk12

/-- **Additivity.** The contraction is additive in the tensor argument. -/
theorem concreteTensorContract_add (r s : ℕ)
    (T₁ T₂ : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1)) :
    concreteTensorContract I M r s (T₁ + T₂) =
      concreteTensorContract I M r s T₁ + concreteTensorContract I M r s T₂ := by
  refine MultilinearMap.ext (fun m => ?_)
  refine MultilinearMap.ext (fun n => ?_)
  apply ContMDiffMap.ext
  intro x₀
  -- LHS: unfold `concreteTensorContract (T₁ + T₂)`.
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- RHS: the addition of MultilinearMap-valued outer + inner applications at x₀.
  change _ = ((concreteTensorContract I M r s T₁ m n) +
              (concreteTensorContract I M r s T₂ m n)) x₀
  rw [ContMDiffMap.coe_add, Pi.add_apply]
  rw [concreteTensorContract_apply, concreteTensorContract_apply,
    concreteTensorContract_fun_apply, concreteTensorContract_fun_apply]
  -- Goal: ∑ i, ((T₁ + T₂) (Fin.cons σ_i m) (Fin.cons θ_i n)) x₀ =
  --        ∑ i, (T₁ (...) (...)) x₀ + ∑ i, (T₂ (...) (...)) x₀.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Apply MultilinearMap.add_apply twice.
  rw [show ((T₁ + T₂) (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M) =
      (T₁ (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M) +
      (T₂ (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M) from
    by rw [MultilinearMap.add_apply]; rfl]
  rw [ContMDiffMap.coe_add, Pi.add_apply]

/-- **`R_`-homogeneity.** The contraction is `R_`-linear in the tensor argument. -/
theorem concreteTensorContract_smul (r s : ℕ)
    (c : R_ I M)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1)) :
    concreteTensorContract I M r s (c • T) = c • concreteTensorContract I M r s T := by
  refine MultilinearMap.ext (fun m => ?_)
  refine MultilinearMap.ext (fun n => ?_)
  apply ContMDiffMap.ext
  intro x₀
  -- LHS: unfold.
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- RHS: c • (concreteTensorContract T m n) at x₀ = c x₀ * (concreteTensorContract T m n) x₀.
  change _ = (c • (concreteTensorContract I M r s T m n)) x₀
  change _ = (c * (concreteTensorContract I M r s T m n)) x₀
  change _ = (c x₀ : ℝ) * (concreteTensorContract I M r s T m n) x₀
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- Goal: ∑ i, ((c • T) (Fin.cons σ_i m) (Fin.cons θ_i n)) x₀ =
  --        c x₀ * ∑ i, (T (...) (...)) x₀.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Apply MultilinearMap.smul_apply twice.
  rw [show ((c • T) (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M) =
      c • (T (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M) from
    by rw [MultilinearMap.smul_apply]; rfl]
  -- In R_ I M (which is C^∞(M, ℝ) ≅ its module over itself), c • f = c * f.
  change (c * (T (Fin.cons ((chooseLocalFrames I M x₀).1 k) m)
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 k)) n) : R_ I M)) x₀ = _
  rfl

/-- **Dual basis identification.** Given a biorthogonal pair `(σ, θ)` at `x₀`, the coord
functional of the basis made from `σ` agrees with the linear functional
`v ↦ toModel(θ i x₀)(fun _ => v)` on all of `TangentSpace I x₀`.

This is the reusable core of the argument at Chunk 7 lines 1283-1327 — two linear maps
agreeing on a basis extend uniquely. -/
private lemma basis_coord_eq_toModel_θ
    (σ : Fin (Module.finrank ℝ E) → V_ I M)
    (θ : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (x₀ : M)
    (h_biorth : ∀ i j, (Tensor0SSpace.toModel (θ i x₀))
      (fun _ : Fin 1 => (σ j x₀ : TangentSpace I x₀)) = if i = j then 1 else 0)
    (h_basis : LinearIndependent ℝ (fun i => (σ i x₀ : TangentSpace I x₀)) ∧
      Submodule.span ℝ (Set.range (fun i => (σ i x₀ : TangentSpace I x₀))) = ⊤)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x₀) :
    (Module.Basis.mk h_basis.1 (le_of_eq h_basis.2.symm)).coord i v =
      (Tensor0SSpace.toModel (θ i x₀)) (fun _ : Fin 1 => v) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis.1 (le_of_eq h_basis.2.symm) with hbasis_def
  have hb_apply : ∀ j, basis j = (σ j) x₀ := fun j => Module.Basis.mk_apply _ _ _
  -- Two linear maps agreeing on a basis: `basis.coord i` and `v ↦ toModel(θ i x₀)(fun _ => v)`.
  have h_on_basis : ∀ j,
      (basis.coord i) (basis j) =
        (Tensor0SSpace.toModel ((θ i) x₀)) (fun _ : Fin 1 => basis j) := by
    intro j
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb_apply]
    rw [h_biorth i j]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  -- Extend from basis-equality to all v.
  have h1 := basis.sum_repr v
  rw [← h1, map_sum]
  set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
    (Tensor0SSpace.toModel ((θ i) x₀)).toMultilinearMap
  change _ = tm (fun _ : Fin 1 => ∑ j, basis.repr v j • basis j)
  rw [show (fun _ : Fin 1 => ∑ j, basis.repr v j • basis j) =
    Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
      (∑ j, basis.repr v j • basis j) from by
      funext k; fin_cases k; rfl]
  rw [tm.map_update_sum (t := Finset.univ)
    (g := fun j => basis.repr v j • basis j)
    (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
  simp_rw [map_smul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tm.map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
    (basis.repr v j) (basis j)]
  rw [smul_eq_mul]
  change basis.repr v j • basis.coord i (basis j) = _
  rw [smul_eq_mul, h_on_basis j]
  have h_upd_const : Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0 (basis j) =
      (fun _ : Fin 1 => basis j) := by
    funext k; fin_cases k; rfl
  rw [h_upd_const, smul_eq_mul]
  rfl

/-- **Endo-trace identity.** The `(1,1)` contraction of the tensor representation of an
endomorphism equals the `concreteTr` trace. This is the axiom
`AbstractTrace.tensor_contract_endo` for the concrete instantiation. -/
theorem concreteTensorContract_endo (L : V_ I M →ₗ[R_ I M] V_ I M) :
    (concreteTensorContract I M 0 0 (endo_to_tensor L)) ![] ![] = concreteTr I M L := by
  apply ContMDiffMap.ext
  intro x₀
  -- Unfold LHS: concreteTensorContract_fun value at x₀.
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- Set up local frames.
  set σ_x₀ := (chooseLocalFrames I M x₀).1 with hσ_def
  set θ_x₀ := (chooseLocalFrames I M x₀).2 with hθ_def
  -- Biorthogonality at x₀ (from Filter.Eventually.self_of_nhds).
  have hbiorth : ∀ i j,
      (Tensor0SSpace.toModel ((θ_x₀ i) x₀))
        (fun _ : Fin 1 => ((σ_x₀ j) x₀ : TangentSpace I x₀)) = if i = j then 1 else 0 :=
    Filter.Eventually.self_of_nhds (chooseLocalFrames_biorth_eventually I M x₀)
  -- Basis from σ_x₀.
  have hbase_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have h_basis_σ : LinearIndependent ℝ
      (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_x₀ i) x₀ :
        Fin (Module.finrank ℝ E) → TangentSpace I x₀)) = ⊤ := by
    have hσ_x₀_eq := Filter.Eventually.self_of_nhds (chooseLocalFrames_σ_eqOn I M x₀)
    let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_x₀ i) x₀ = le.symm (b i) := fun i => by
      rw [hσ_x₀_eq i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hbase_tan)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis_σ.1 (le_of_eq h_basis_σ.2.symm) with hbasis_def
  have hb_apply : ∀ i, basis i = (σ_x₀ i) x₀ := fun i => Module.Basis.mk_apply _ _ _
  -- Rewrite LHS: each summand = toModel(θ_x₀ i x₀)(fun _ => (L (σ_x₀ i)) x₀).
  have h_summand_eq : ∀ i,
      (endo_to_tensor L (Fin.cons (σ_x₀ i) ![])
        (Fin.cons (covectorToFunctional I M (θ_x₀ i)) ![])) x₀ =
      (Tensor0SSpace.toModel ((θ_x₀ i) x₀))
        (fun _ : Fin 1 => (vbcFiber I M L x₀) ((σ_x₀ i) x₀ : TangentSpace I x₀)) := by
    intro i
    -- Fin.cons σ ![] = ![σ] and Fin.cons θ_f ![] = ![θ_f].
    have h_cons_v : (Fin.cons (σ_x₀ i) ![] : Fin 1 → V_ I M) = ![σ_x₀ i] := by
      funext k; fin_cases k; rfl
    have h_cons_c : (Fin.cons (covectorToFunctional I M (θ_x₀ i)) ![] : Fin 1 →
        V_ I M →ₗ[R_ I M] R_ I M) = ![covectorToFunctional I M (θ_x₀ i)] := by
      funext k; fin_cases k; rfl
    rw [h_cons_v, h_cons_c]
    rw [endo_to_tensor_eval]
    -- Now: covectorToFunctional (θ_x₀ i) (L (σ_x₀ i)) x₀.
    rw [covectorToFunctional_apply]
    -- Now: (toModel (θ_x₀ i x₀)) (fun _ => (L (σ_x₀ i)) x₀).
    congr 1
    funext k
    fin_cases k
    -- (L (σ_x₀ i)) x₀ = vbcFiber L x₀ (σ_x₀ i x₀).
    exact (vbcFiber_spec I M L (σ_x₀ i) x₀).symm
  rw [show (∑ i, (endo_to_tensor L (Fin.cons ((chooseLocalFrames I M x₀).1 i) ![])
        (Fin.cons (covectorToFunctional I M ((chooseLocalFrames I M x₀).2 i)) ![])) x₀) =
      ∑ i, (Tensor0SSpace.toModel ((θ_x₀ i) x₀))
        (fun _ : Fin 1 => (vbcFiber I M L x₀) ((σ_x₀ i) x₀ : TangentSpace I x₀)) from
    Finset.sum_congr rfl (fun i _ => h_summand_eq i)]
  -- RHS: concreteTr L x₀ = LinearMap.trace ℝ (TangentSpace I x₀) (vbcFiber L x₀).
  change _ = concreteTr_fun I M L x₀
  change _ = LinearMap.trace ℝ (TangentSpace I x₀) (vbcFiber I M L x₀)
  -- Match via matrix-trace formula in basis.
  rw [LinearMap.trace_eq_matrix_trace ℝ basis]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Matrix diag entry (i,i) = basis.coord i (vbcFiber L x₀ (basis i)).
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hb_apply]
  -- Goal: toModel (θ_x₀ i x₀) (fun _ => vbcFiber L x₀ (σ_x₀ i x₀)) =
  --       basis.coord i (vbcFiber L x₀ (σ_x₀ i x₀)).
  rw [basis_coord_eq_toModel_θ I M σ_x₀ θ_x₀ x₀ hbiorth h_basis_σ i
    ((vbcFiber I M L x₀) ((σ_x₀ i) x₀ : TangentSpace I x₀))]

end Chunk12

/-! ### Chunk 13 — `data_eval_single_contract` axiom

The `AbstractTrace.data_eval_single_contract` field: contraction of
`tensor_prod (vectorToData v) D` equals `D` evaluated with `v` plugged into the first
covariant slot.

The axiom uses a cast from `TensorData (1+r) (0+(s+1))` to `TensorData (r+1) (s+1)` to
reconcile the index algebra. -/

section Chunk13

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Pointwise action of a single-cast TensorData after transporting the lower index. -/
private lemma cast_lower_apply {a b : ℕ} (r : ℕ) (h : a = b)
    (T : TensorData (R_ I M) (V_ I M) r a)
    (m : Fin b → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    (h ▸ T) m n = T (m ∘ Fin.cast h) n := by
  subst h
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Pointwise action of a single-cast TensorData after transporting the upper index. -/
private lemma cast_upper_apply {a b : ℕ} (s : ℕ) (h : a = b)
    (T : TensorData (R_ I M) (V_ I M) a s)
    (m : Fin s → V_ I M)
    (n : Fin b → V_ I M →ₗ[R_ I M] R_ I M) :
    (h ▸ T) m n = T m (n ∘ Fin.cast h) := by
  subst h
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Unfold the cast-wrapped `tensor_prod (vectorToData v) D` at concrete inputs. -/
private lemma cast_vectorToData_tensor_prod_apply (r s : ℕ)
    (D : TensorData (R_ I M) (V_ I M) r (s + 1)) (v : V_ I M)
    (m : Fin (s + 1) → V_ I M)
    (n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) :
    ((show 1 + r = r + 1 from by omega) ▸
     (show 0 + (s + 1) = s + 1 from by omega) ▸
     tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
       (vectorToData (R := R_ I M) v) D) m n =
    (tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
        (vectorToData (R := R_ I M) v) D)
      (m ∘ Fin.cast (by omega)) (n ∘ Fin.cast (by omega)) := by
  rw [cast_upper_apply I M (s + 1) (by omega)]
  rw [cast_lower_apply I M (1 + r) (by omega)]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Compute the value of `tensor_prod (vectorToData v) D` at `Fin.cons σ m'` and
`Fin.cons α n'`, via the `tensor_prod_eval` unfolding. The result factors as
`α(v) * D(m')(n')`. -/
private lemma tensor_prod_vectorToData_cons_eval (r s : ℕ)
    (D : TensorData (R_ I M) (V_ I M) r (s + 1)) (v : V_ I M)
    (σ : V_ I M) (m' : Fin s → V_ I M)
    (α : V_ I M →ₗ[R_ I M] R_ I M) (n' : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    ((tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
        (vectorToData (R := R_ I M) v) D)
      ((Fin.cons σ m' : Fin (s + 1) → V_ I M) ∘ Fin.cast (by omega : 0 + (s + 1) = s + 1))
      ((Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
        ∘ Fin.cast (by omega : 1 + r = r + 1))) =
    α v * D (Fin.cons σ m') n' := by
  -- Unfold tensor_prod at the given arguments.
  rw [tensor_prod_eval]
  -- The vectorToData factor, with no lower slots and one upper slot at position 0.
  have h_vec :
      (vectorToData (R := R_ I M) v)
          (((Fin.cons σ m') ∘ Fin.cast (by omega : 0 + (s + 1) = s + 1)) ∘
              Fin.castAdd (s + 1))
          (((Fin.cons α n') ∘ Fin.cast (by omega : 1 + r = r + 1)) ∘ Fin.castAdd r) =
        α v := by
    -- `vectorToData v` ignores its 0-lower-slot argument (Fin 0 is empty); evaluates the
    -- single upper slot at `v`.
    -- Fin.castAdd r 0 : Fin (1 + r). Its value is 0. Fin.cast maps it to (0 : Fin (r+1)).
    -- Fin.cons α n' at position 0 is α.
    change (evalLinear v)
      ((((Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
        Fin.cast (by omega : 1 + r = r + 1)) ∘ Fin.castAdd r) 0) = α v
    have h0 : (((Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
        Fin.cast (by omega : 1 + r = r + 1)) ∘ Fin.castAdd r) 0 = α := by
      change (Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
        (Fin.cast (by omega : 1 + r = r + 1) (Fin.castAdd r (0 : Fin 1))) = α
      have hcast_zero : Fin.cast (by omega : 1 + r = r + 1) (Fin.castAdd r (0 : Fin 1))
          = (0 : Fin (r + 1)) := by
        apply Fin.ext
        rfl
      rw [hcast_zero, Fin.cons_zero]
    rw [h0]
    rfl
  have h_D :
      D (((Fin.cons σ m') ∘ Fin.cast (by omega : 0 + (s + 1) = s + 1)) ∘ Fin.natAdd 0)
          (((Fin.cons α n') ∘ Fin.cast (by omega : 1 + r = r + 1)) ∘ Fin.natAdd 1) =
        D (Fin.cons σ m') n' := by
    -- The m-argument: `Fin.natAdd 0 = id` (plus Fin.cast).
    have hm_eq :
        ((Fin.cons σ m' : Fin (s + 1) → V_ I M) ∘
          Fin.cast (by omega : 0 + (s + 1) = s + 1)) ∘ Fin.natAdd 0 =
          Fin.cons σ m' := by
      funext k
      change (Fin.cons σ m' : Fin (s + 1) → V_ I M)
        (Fin.cast (by omega : 0 + (s + 1) = s + 1) (Fin.natAdd 0 k)) =
        (Fin.cons σ m' : Fin (s + 1) → V_ I M) k
      congr 1
      apply Fin.ext
      change 0 + k.val = k.val
      omega
    -- The n-argument: `Fin.natAdd 1 k = k.succ` via the cast.
    have hn_eq :
        ((Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
          Fin.cast (by omega : 1 + r = r + 1)) ∘ Fin.natAdd 1 = n' := by
      funext k
      change (Fin.cons α n' : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
        (Fin.cast (by omega : 1 + r = r + 1) (Fin.natAdd 1 k)) = n' k
      have hcast : Fin.cast (by omega : 1 + r = r + 1) (Fin.natAdd 1 k) = k.succ := by
        apply Fin.ext
        change 1 + k.val = k.val + 1
        omega
      rw [hcast, Fin.cons_succ]
    rw [hm_eq, hn_eq]
  rw [h_vec, h_D]

/-- `data_eval_single_contract` axiom as a concrete theorem.

Mathematical content: if we build the tensor product `vectorToData(v) ⊗ D` and contract the
first covariant/contravariant pair (after transporting the indices), the result evaluated at
`(m, n)` equals `D (Fin.cons v m) n`. -/
theorem concreteTensorContract_data_eval_single_contract (r s : ℕ)
    (D : TensorData (R_ I M) (V_ I M) r (s + 1)) (v : V_ I M)
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    (concreteTensorContract I M r s
      ((show 1 + r = r + 1 from by omega) ▸
       (show 0 + (s + 1) = s + 1 from by omega) ▸
       tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
         (vectorToData (R := R_ I M) v) D)) m n =
    D (Fin.cons v m) n := by
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- Set up local frames at x₀.
  set σ_x₀ := (chooseLocalFrames I M x₀).1 with hσ_def
  set θ_x₀ := (chooseLocalFrames I M x₀).2 with hθ_def
  -- Biorthogonality and basis property at x₀.
  have hbiorth : ∀ i j,
      (Tensor0SSpace.toModel ((θ_x₀ i) x₀))
        (fun _ : Fin 1 => ((σ_x₀ j) x₀ : TangentSpace I x₀)) = if i = j then 1 else 0 :=
    Filter.Eventually.self_of_nhds (chooseLocalFrames_biorth_eventually I M x₀)
  have hbase_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have h_basis_σ : LinearIndependent ℝ
      (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_x₀ i) x₀ :
        Fin (Module.finrank ℝ E) → TangentSpace I x₀)) = ⊤ := by
    have hσ_x₀_eq := Filter.Eventually.self_of_nhds (chooseLocalFrames_σ_eqOn I M x₀)
    let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_x₀ i) x₀ = le.symm (b i) := fun i => by
      rw [hσ_x₀_eq i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hbase_tan)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis_σ.1 (le_of_eq h_basis_σ.2.symm) with hbasis_def
  have hb_apply : ∀ i, basis i = (σ_x₀ i) x₀ := fun i => Module.Basis.mk_apply _ _ _
  -- Simplify each summand using `cast_vectorToData_tensor_prod_apply` and the tensor_prod formula.
  have h_summand_eq : ∀ i,
      (((show 1 + r = r + 1 from by omega) ▸
        (show 0 + (s + 1) = s + 1 from by omega) ▸
        tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
          (vectorToData (R := R_ I M) v) D)
          (Fin.cons (σ_x₀ i) m) (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)) x₀ =
      (covectorToFunctional I M (θ_x₀ i) v) x₀ * (D (Fin.cons (σ_x₀ i) m) n) x₀ := by
    intro i
    rw [cast_vectorToData_tensor_prod_apply I M r s D v
      (Fin.cons (σ_x₀ i) m) (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)]
    rw [tensor_prod_vectorToData_cons_eval I M r s D v
      (σ_x₀ i) m (covectorToFunctional I M (θ_x₀ i)) n]
    rfl
  -- Rewrite each summand. Note: the LHS sum evaluation at x₀ unfolds through R_evalAt_sum.
  rw [Finset.sum_congr rfl (fun i _ => h_summand_eq i)]
  -- Each coefficient `(ctf θ_i v) x₀ = toModel(θ_x₀ i x₀)(fun _ => v x₀)`.
  -- Use R_-linearity of D in the first lower slot: define c_i := ctf(θ_i)(v) : R_ I M.
  let c : Fin (Module.finrank ℝ E) → R_ I M :=
    fun i => covectorToFunctional I M (θ_x₀ i) v
  -- Build the R_-linear combination Z := ∑_i c_i • σ_x₀_i : V_ I M.
  let Z : V_ I M := ∑ i, c i • σ_x₀ i
  -- Key fact 1: `Z x₀ = v x₀`, via the dual-basis expansion + biorthogonality.
  have hZ_at_x₀ : Z x₀ = v x₀ := by
    change (∑ i, c i • σ_x₀ i) x₀ = v x₀
    simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
    -- ∑_i (c_i x₀) • (σ_x₀_i x₀) = v x₀.
    -- c_i x₀ = toModel(θ_x₀ i x₀)(fun _ => v x₀) = basis.coord i (v x₀).
    have h_coord_c : ∀ i, (c i) x₀ = basis.coord i (v x₀) := by
      intro i
      change (covectorToFunctional I M (θ_x₀ i) v) x₀ = _
      rw [covectorToFunctional_apply]
      symm
      exact basis_coord_eq_toModel_θ I M σ_x₀ θ_x₀ x₀ hbiorth h_basis_σ i (v x₀)
    have h_sum : (∑ i, ((c i) x₀ : ℝ) • ((σ_x₀ i) x₀ : TangentSpace I x₀)) = v x₀ := by
      have h_expand : v x₀ = ∑ i, (basis.coord i) (v x₀) • basis i := by
        conv_lhs => rw [← basis.sum_repr (v x₀)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [basis.coord_apply]
      rw [h_expand]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_coord_c, hb_apply]
    exact h_sum
  -- Key fact 2: R_-linearity of D in the first lower slot gives
  --     D(Fin.cons Z m)(n) = ∑_i c_i * D(Fin.cons σ_x₀_i m)(n).
  have h_D_lin : D (Fin.cons Z m) n = ∑ i, c i * D (Fin.cons (σ_x₀ i) m) n := by
    -- Use D.curryLeft for R_-linearity in the first lower slot.
    change (D.curryLeft Z m) n = _
    change (D.curryLeft (∑ i, c i • σ_x₀ i) m) n = _
    rw [map_sum D.curryLeft]
    rw [MultilinearMap.sum_apply, MultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.map_smul]
    rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply]
    rfl
  -- Connect: ∑_i (c_i x₀) * (D (Fin.cons σ_x₀_i m) n) x₀ = (D (Fin.cons Z m) n) x₀.
  have h_sum_eq_DZ :
      (∑ i, (c i) x₀ * (D (Fin.cons (σ_x₀ i) m) n) x₀) = (D (Fin.cons Z m) n) x₀ := by
    rw [h_D_lin]
    rw [R_evalAt_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rfl
  rw [h_sum_eq_DZ]
  -- Use `tensorData_eval_pointwise` at x₀: Z x₀ = v x₀, so the values match.
  apply tensorData_eval_pointwise I M r (s + 1) D
    (Fin.cons Z m) (Fin.cons v m) n n x₀
  · intro i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; exact hZ_at_x₀
    | succ i => simp only [Fin.cons_succ]
  · intro j X
    rfl

end Chunk13

/-! ### Chunk 14 — `data_eval_single_contract_dual` axiom

The `AbstractTrace.data_eval_single_contract_dual` field: contracting `tensor_prod A B`
with `A : TensorData R V 0 (s₁+1)` and `B : TensorData R V (r+1) s₂` (after transporting
the indices) pairs A's first covariant slot with B's first contravariant slot. The result
plugs the covector `v ↦ A (Fin.cons v m') ![]` (i.e. `covector_from_tensor A m' ![]`) into
B's first contravariant slot.

The proof mirrors Chunk 13 but handles the dual direction: the contracted slot sits on
A's vector side (with its unique covector partner from the contraction) and B's covector
side (at position 0). -/

section Chunk14

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Unfold the double-cast tensor_prod A B at concrete `Fin.cons`-shaped inputs. Analogous to
`cast_vectorToData_tensor_prod_apply` in Chunk 13, but for A on the left (s₁+1 vector
slots, no covector slots) and B on the right (s₂ vectors, r+1 covectors). -/
private lemma cast_A_tensor_prod_apply (r s₁ s₂ : ℕ)
    (A : TensorData (R_ I M) (V_ I M) 0 (s₁ + 1))
    (B : TensorData (R_ I M) (V_ I M) (r + 1) s₂)
    (m_in : Fin ((s₁ + s₂) + 1) → V_ I M)
    (n_in : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) :
    ((show 0 + (r + 1) = r + 1 from by omega) ▸
     (show (s₁ + 1) + s₂ = (s₁ + s₂) + 1 from by omega) ▸
     tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B) m_in n_in =
    (tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)
      (m_in ∘ Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1))
      (n_in ∘ Fin.cast (by omega : 0 + (r + 1) = r + 1)) := by
  rw [cast_upper_apply I M ((s₁ + s₂) + 1) (by omega : 0 + (r + 1) = r + 1)]
  rw [cast_lower_apply I M (0 + (r + 1)) (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [FiniteDimensional ℝ E] in
/-- Compute `tensor_prod A B` at `Fin.cons`-shaped vector and covector inputs (after the
cast). The result factors as `A (Fin.cons σ (m ∘ Fin.castAdd s₂)) ![] * B (m ∘ Fin.natAdd s₁)
(Fin.cons β n)`. -/
private lemma tensor_prod_A_B_cons_eval (r s₁ s₂ : ℕ)
    (A : TensorData (R_ I M) (V_ I M) 0 (s₁ + 1))
    (B : TensorData (R_ I M) (V_ I M) (r + 1) s₂)
    (σ : V_ I M) (m : Fin (s₁ + s₂) → V_ I M)
    (β : V_ I M →ₗ[R_ I M] R_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    ((tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)
        ((Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M) ∘
          Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1))
        ((Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
          ∘ Fin.cast (by omega : 0 + (r + 1) = r + 1))) =
    A (Fin.cons σ (m ∘ Fin.castAdd s₂)) ![] * B (m ∘ Fin.natAdd s₁) (Fin.cons β n) := by
  -- Unfold tensor_prod at the given arguments.
  rw [tensor_prod_eval]
  -- The A factor: s₁+1 vector slots from the castAdd-projected m-input, 0 covector slots.
  have h_A :
      A (((Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M) ∘
            Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)) ∘ Fin.castAdd s₂)
          (((Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
            Fin.cast (by omega : 0 + (r + 1) = r + 1)) ∘ Fin.castAdd (r + 1)) =
        A (Fin.cons σ (m ∘ Fin.castAdd s₂)) ![] := by
    -- The m-argument: show (Fin.cons σ m ∘ Fin.cast h_inner) ∘ Fin.castAdd s₂
    --               = Fin.cons σ (m ∘ Fin.castAdd s₂).
    have hm_A :
        ((Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M) ∘
          Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)) ∘ Fin.castAdd s₂ =
          Fin.cons σ (m ∘ Fin.castAdd s₂) := by
      funext i
      induction i using Fin.cases with
      | zero =>
        change (Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M)
          (Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)
            (Fin.castAdd s₂ (0 : Fin (s₁ + 1)))) = σ
        have hcast_zero :
            Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)
              (Fin.castAdd s₂ (0 : Fin (s₁ + 1))) = (0 : Fin ((s₁ + s₂) + 1)) := by
          apply Fin.ext
          rfl
        rw [hcast_zero, Fin.cons_zero]
      | succ i =>
        change (Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M)
          (Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)
            (Fin.castAdd s₂ i.succ)) =
          (m ∘ Fin.castAdd s₂) i
        have hcast_succ :
            Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)
              (Fin.castAdd s₂ i.succ) =
            (⟨i.val, by omega⟩ : Fin (s₁ + s₂)).succ := by
          apply Fin.ext
          change i.val + 1 = i.val + 1
          rfl
        rw [hcast_succ, Fin.cons_succ]
        change m (⟨i.val, by omega⟩ : Fin (s₁ + s₂)) = m (Fin.castAdd s₂ i)
        rfl
    -- The n-argument: Fin 0 is empty, so any function is `![]`.
    have hn_A : (((Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
          Fin.cast (by omega : 0 + (r + 1) = r + 1)) ∘ Fin.castAdd (r + 1) :
          Fin 0 → V_ I M →ₗ[R_ I M] R_ I M) =
        ![] := by
      funext k; exact k.elim0
    rw [hm_A, hn_A]
  have h_B :
      B (((Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M) ∘
            Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)) ∘ Fin.natAdd (s₁ + 1))
          (((Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
            Fin.cast (by omega : 0 + (r + 1) = r + 1)) ∘ Fin.natAdd 0) =
        B (m ∘ Fin.natAdd s₁) (Fin.cons β n) := by
    have hm_B :
        ((Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M) ∘
          Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1)) ∘ Fin.natAdd (s₁ + 1) =
          m ∘ Fin.natAdd s₁ := by
      funext k
      change (Fin.cons σ m : Fin ((s₁ + s₂) + 1) → V_ I M)
        (Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1) (Fin.natAdd (s₁ + 1) k)) =
          m (Fin.natAdd s₁ k)
      -- Fin.natAdd (s₁+1) k has val = s₁ + 1 + k.val > 0, so Fin.cons σ m gives m at some index.
      have hcast_eq :
          Fin.cast (by omega : (s₁ + 1) + s₂ = (s₁ + s₂) + 1) (Fin.natAdd (s₁ + 1) k) =
          (⟨s₁ + k.val, by omega⟩ : Fin (s₁ + s₂)).succ := by
        apply Fin.ext
        change (s₁ + 1) + k.val = s₁ + k.val + 1
        omega
      rw [hcast_eq, Fin.cons_succ]
      change m (⟨s₁ + k.val, by omega⟩ : Fin (s₁ + s₂)) = m (Fin.natAdd s₁ k)
      rfl
    have hn_B :
        ((Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) ∘
          Fin.cast (by omega : 0 + (r + 1) = r + 1)) ∘ Fin.natAdd 0 = Fin.cons β n := by
      funext k
      change (Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
        (Fin.cast (by omega : 0 + (r + 1) = r + 1) (Fin.natAdd 0 k)) =
          (Fin.cons β n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) k
      congr 1
      apply Fin.ext
      change 0 + k.val = k.val
      omega
    rw [hm_B, hn_B]
  rw [h_A, h_B]

/-- `data_eval_single_contract_dual` axiom as a concrete theorem.

Mathematical content: contracting `tensor_prod A B` (with A : (0, s₁+1) and B : (r+1, s₂))
after the cast reconciling `TensorData ((s₁+1)+s₂) (0+(r+1))` with
`TensorData ((s₁+s₂)+1) (r+1)` equals `B` evaluated with the covector
`covector_from_tensor A (m ∘ Fin.castAdd s₂) ![]` plugged into B's first covector slot. -/
theorem concreteTensorContract_data_eval_single_contract_dual (r s₁ s₂ : ℕ)
    (A : TensorData (R_ I M) (V_ I M) 0 (s₁ + 1))
    (B : TensorData (R_ I M) (V_ I M) (r + 1) s₂)
    (m : Fin (s₁ + s₂) → V_ I M)
    (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) :
    (concreteTensorContract I M r (s₁ + s₂)
      ((show 0 + (r + 1) = r + 1 from by omega) ▸
       (show (s₁ + 1) + s₂ = (s₁ + s₂) + 1 from by omega) ▸
       tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)) m n =
    B (m ∘ Fin.natAdd s₁) (Fin.cons (covector_from_tensor A (m ∘ Fin.castAdd s₂) ![]) n) := by
  apply ContMDiffMap.ext
  intro x₀
  rw [concreteTensorContract_apply, concreteTensorContract_fun_apply]
  -- Set up local frames at x₀.
  set σ_x₀ := (chooseLocalFrames I M x₀).1 with hσ_def
  set θ_x₀ := (chooseLocalFrames I M x₀).2 with hθ_def
  set α := covector_from_tensor A (m ∘ Fin.castAdd s₂) ![] with hα_def
  -- Biorthogonality and basis at x₀ (reuse from Chunk 12/13 boilerplate).
  have hbiorth : ∀ i j,
      (Tensor0SSpace.toModel ((θ_x₀ i) x₀))
        (fun _ : Fin 1 => ((σ_x₀ j) x₀ : TangentSpace I x₀)) = if i = j then 1 else 0 :=
    Filter.Eventually.self_of_nhds (chooseLocalFrames_biorth_eventually I M x₀)
  have hbase_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt _ _ x₀
  have h_basis_σ : LinearIndependent ℝ
      (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) ∧
      Submodule.span ℝ (Set.range (fun i => (σ_x₀ i) x₀ :
        Fin (Module.finrank ℝ E) → TangentSpace I x₀)) = ⊤ := by
    have hσ_x₀_eq := Filter.Eventually.self_of_nhds (chooseLocalFrames_σ_eqOn I M x₀)
    let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, (σ_x₀ i) x₀ = le.symm (b i) := fun i => by
      rw [hσ_x₀_eq i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hbase_tan)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => (σ_x₀ i) x₀ : Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀) :=
    Module.Basis.mk h_basis_σ.1 (le_of_eq h_basis_σ.2.symm) with hbasis_def
  have hb_apply : ∀ i, basis i = (σ_x₀ i) x₀ := fun i => Module.Basis.mk_apply _ _ _
  -- Per-summand simplification via cast_A_tensor_prod_apply + tensor_prod_A_B_cons_eval.
  have h_summand_eq : ∀ i,
      (((show 0 + (r + 1) = r + 1 from by omega) ▸
        (show (s₁ + 1) + s₂ = (s₁ + s₂) + 1 from by omega) ▸
        tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)
          (Fin.cons (σ_x₀ i) m) (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)) x₀ =
      (α (σ_x₀ i) : R_ I M) x₀ *
        (B (m ∘ Fin.natAdd s₁)
          (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)) x₀ := by
    intro i
    rw [cast_A_tensor_prod_apply I M r s₁ s₂ A B (Fin.cons (σ_x₀ i) m)
      (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)]
    rw [tensor_prod_A_B_cons_eval I M r s₁ s₂ A B (σ_x₀ i) m
      (covectorToFunctional I M (θ_x₀ i)) n]
    -- LHS at x₀ = A(Fin.cons σ_i (m∘castAdd s₂)) ![] * B(m∘natAdd s₁)(Fin.cons θ_i n).
    -- α (σ_x₀ i) = A (Fin.cons (σ_x₀ i) (m∘castAdd s₂)) ![] by definition of covector_from_tensor.
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h_summand_eq i)]
  -- Now: ∑_i (α (σ_x₀ i)) x₀ * (B(m∘natAdd s₁)(Fin.cons (ctf θ_i) n)) x₀.
  -- Use R_-linearity of B in its first covector slot. Let c_i := α (σ_x₀ i) : R_ I M.
  -- Define Y := ∑_i c_i • ctf(θ_x₀ i) : V_ →ₗ[R_] R_.
  let c : Fin (Module.finrank ℝ E) → R_ I M := fun i => α (σ_x₀ i)
  let Y : V_ I M →ₗ[R_ I M] R_ I M := ∑ i, c i • covectorToFunctional I M (θ_x₀ i)
  -- Key fact 1: Y X x₀ = α X x₀ for all X : V_ I M.
  have hY_eq_α_at_x₀ : ∀ X : V_ I M, (Y X) x₀ = (α X) x₀ := by
    intro X
    -- Y X = ∑_i c_i * (ctf θ_i) X, so (Y X) x₀ = ∑_i (c_i x₀) * ((ctf θ_i) X) x₀.
    have hY_unfold : (Y X) x₀ =
        ∑ i, (c i) x₀ * ((covectorToFunctional I M (θ_x₀ i)) X) x₀ := by
      change ((∑ i, c i • covectorToFunctional I M (θ_x₀ i)) X) x₀ = _
      rw [LinearMap.sum_apply]
      rw [R_evalAt_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change ((c i) • (covectorToFunctional I M (θ_x₀ i) X)) x₀ =
        (c i) x₀ * ((covectorToFunctional I M (θ_x₀ i)) X) x₀
      rfl
    rw [hY_unfold]
    -- Each (ctf θ_i) X x₀ = toModel (θ_x₀ i x₀) (fun _ => X x₀) = basis.coord i (X x₀).
    have h_coord : ∀ i, ((covectorToFunctional I M (θ_x₀ i)) X) x₀ = basis.coord i (X x₀) := by
      intro i
      rw [covectorToFunctional_apply]
      symm
      exact basis_coord_eq_toModel_θ I M σ_x₀ θ_x₀ x₀ hbiorth h_basis_σ i (X x₀)
    -- Rewrite the sum using h_coord.
    rw [show (∑ i, (c i) x₀ * ((covectorToFunctional I M (θ_x₀ i)) X) x₀) =
        ∑ i, (c i) x₀ * basis.coord i (X x₀) from
      Finset.sum_congr rfl (fun i _ => by rw [h_coord i])]
    -- Now: ∑_i (α (σ_x₀ i)) x₀ * basis.coord i (X x₀) = (α X) x₀.
    -- Build a test section Z = ∑_i (basis.coord i (X x₀) : R_) • σ_x₀ i : V_.
    -- At x₀, Z x₀ = X x₀; by VBC on α (smoothLinearMap_acts_pointwise), α X x₀ = α Z x₀.
    let coord_const : Fin (Module.finrank ℝ E) → R_ I M := fun i =>
      ⟨fun _ => basis.coord i (X x₀), contMDiff_const⟩
    let Z : V_ I M := ∑ i, coord_const i • σ_x₀ i
    have hZ_at_x₀ : Z x₀ = X x₀ := by
      change (∑ i, coord_const i • σ_x₀ i) x₀ = X x₀
      simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      have h_expand : X x₀ = ∑ i, basis.coord i (X x₀) • basis i := by
        conv_lhs => rw [← basis.sum_repr (X x₀)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [basis.coord_apply]
      rw [h_expand]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hb_apply]
      rfl
    -- α acts pointwise: (α X) x₀ = (α Z) x₀.
    have hα_XZ : (α X) x₀ = (α Z) x₀ :=
      smoothLinearMap_acts_pointwise I M α X Z x₀ hZ_at_x₀.symm
    rw [hα_XZ]
    -- α Z = ∑_i coord_const i • (α (σ_x₀ i)) = ∑_i coord_const i * c_i (by R_-linearity of α).
    have hα_Z : α Z = ∑ i, coord_const i * c i := by
      change α (∑ i, coord_const i • σ_x₀ i) = _
      rw [map_sum α]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change α (coord_const i • σ_x₀ i) = coord_const i * c i
      rw [LinearMap.map_smul]
      change coord_const i • α (σ_x₀ i) = coord_const i * c i
      rfl
    rw [hα_Z, R_evalAt_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (c i) x₀ * basis.coord i (X x₀) = (coord_const i * c i) x₀
    change (c i) x₀ * basis.coord i (X x₀) = (coord_const i) x₀ * (c i) x₀
    change (c i) x₀ * basis.coord i (X x₀) = basis.coord i (X x₀) * (c i) x₀
    ring
  -- Key fact 2: R_-linearity of B in the first covector slot.
  -- ∑_i (c_i x₀) * (B (m ∘ natAdd s₁) (Fin.cons (ctf θ_i) n)) x₀ = (B (m ∘ natAdd s₁) (Fin.cons Y n)) x₀.
  have h_B_lin : B (m ∘ Fin.natAdd s₁) (Fin.cons Y n) =
      ∑ i, c i * B (m ∘ Fin.natAdd s₁) (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n) := by
    -- B m curryLeft on the first covector slot via currying.
    -- Use MultilinearMap.map_update_sum / map_update_smul on Fin.cons's 0-slot.
    let T : TensorData (R_ I M) (V_ I M) (r + 1) s₂ := B
    -- For fixed m-arg, (T (m ∘ natAdd s₁) : MultilinearMap _ (fun _ : Fin (r+1) => V_ →ₗ R_) R_)
    -- applied at Fin.cons Y n = (∑_i c_i • ctf θ_i) in slot 0.
    have h_expand :
        (Fin.cons Y n : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) =
          Function.update (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) n) 0 Y := by
      funext j
      induction j using Fin.cases with
      | zero => simp [Function.update]
      | succ j =>
          simp only [Fin.cons_succ, Function.update]
          split_ifs with h
          · exfalso; exact Fin.succ_ne_zero j h
          · rfl
    rw [h_expand]
    -- Expand Y as ∑_i c_i • ctf θ_i via map_update_sum.
    rw [show Y = ∑ i, c i • covectorToFunctional I M (θ_x₀ i) from rfl]
    rw [(B (m ∘ Fin.natAdd s₁)).map_update_sum (t := Finset.univ)
      (g := fun i => c i • covectorToFunctional I M (θ_x₀ i))
      (m := Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) n) (i := 0)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(B (m ∘ Fin.natAdd s₁)).map_update_smul
      (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) n) 0
      (c i) (covectorToFunctional I M (θ_x₀ i))]
    rw [smul_eq_mul]
    -- Now: update (Fin.cons 0 n) 0 (ctf θ_i) = Fin.cons (ctf θ_i) n.
    have h_upd :
        Function.update (Fin.cons (0 : V_ I M →ₗ[R_ I M] R_ I M) n) 0
          (covectorToFunctional I M (θ_x₀ i)) =
        (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n :
          Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) := by
      funext j
      induction j using Fin.cases with
      | zero => simp [Function.update]
      | succ j =>
          simp only [Function.update, Fin.cons_succ]
          split_ifs with h
          · exfalso; exact Fin.succ_ne_zero j h
          · rfl
    rw [h_upd]
  have h_sum_eq_BY :
      (∑ i, (c i) x₀ *
        (B (m ∘ Fin.natAdd s₁) (Fin.cons (covectorToFunctional I M (θ_x₀ i)) n)) x₀) =
      (B (m ∘ Fin.natAdd s₁) (Fin.cons Y n)) x₀ := by
    rw [h_B_lin, R_evalAt_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rfl
  rw [h_sum_eq_BY]
  -- Apply tensorData_eval_pointwise on B: vectors match trivially; covector at slot 0
  -- matches via hY_eq_α_at_x₀.
  apply tensorData_eval_pointwise I M (r + 1) s₂ B
    (m ∘ Fin.natAdd s₁) (m ∘ Fin.natAdd s₁) (Fin.cons Y n) (Fin.cons α n) x₀
  · intro i; rfl
  · intro j X
    induction j using Fin.cases with
    | zero => simp only [Fin.cons_zero]; exact hY_eq_α_at_x₀ X
    | succ j => simp only [Fin.cons_succ]

end Chunk14

/-! ### Chunk 15 — Final assembly: `concreteAbstractTrace`

The capstone of P27: package `concreteTr` (from `Trace.lean`) together with
`concreteTensorContract` and its companion axioms into a single
`SyntheticTensor.AbstractTrace` instance.

All 9 fields of `AbstractTrace` are `rfl` wrappers around theorems already proved
in `Trace.lean` and Chunks 10–14 of this file. Since the concrete theorems have
`(r s : ℕ)` explicit while `AbstractTrace` expects them implicit, we eta-expand
with `fun {r s} => ...` at each of the six contraction fields. -/

section Chunk15

/-- **Final assembly**: the concrete `AbstractTrace` instance for the Synthetic
layer, instantiated with `R := C^∞(M, ℝ)` and `V := Γ(TM)`.

All 9 axiom fields are discharged from Mathlib + the realization infrastructure
in this file (Chunks 10–14) and `Trace.lean`, with no axioms, sorries, or new
classes introduced. -/
noncomputable def concreteAbstractTrace : AbstractTrace (R_ I M) (V_ I M) where
  tr := concreteTr I M
  trace_outer := concreteTr_outer I M
  trace_comm := concreteTr_comm I M
  tensor_contract := fun {r s} => concreteTensorContract I M r s
  tensor_contract_add := fun {r s} T₁ T₂ =>
    concreteTensorContract_add I M r s T₁ T₂
  tensor_contract_smul := fun {r s} c T =>
    concreteTensorContract_smul I M r s c T
  data_eval_single_contract := fun {r s} D v m n =>
    concreteTensorContract_data_eval_single_contract I M r s D v m n
  data_eval_single_contract_dual := fun {r s₁ s₂} A B m n =>
    concreteTensorContract_data_eval_single_contract_dual I M r s₁ s₂ A B m n
  tensor_contract_endo := concreteTensorContract_endo I M

/-- `concreteAbstractTrace.tr` unfolds to `concreteTr`. -/
@[simp] theorem concreteAbstractTrace_tr :
    (concreteAbstractTrace I M).tr = concreteTr I M := rfl

/-- `concreteAbstractTrace.tensor_contract` unfolds to `concreteTensorContract`. -/
@[simp] theorem concreteAbstractTrace_tensor_contract (r s : ℕ)
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1)) :
    (concreteAbstractTrace I M).tensor_contract T =
      concreteTensorContract I M r s T := rfl

end Chunk15

end TensorContractRealization

end
