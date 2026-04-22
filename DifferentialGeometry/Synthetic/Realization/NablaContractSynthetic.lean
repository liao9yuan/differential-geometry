import DifferentialGeometry.Synthetic.Realization.TensorContract
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors

/-!
# SmoothRicciFlow: helpers for `∇` commuting with tensor contraction (P29.3a)

This file develops helper infrastructure used by the realization of the Synthetic
axiom `NablaTensorContractComm`. All helpers are fiberwise/pointwise lemmas about
the interaction between the concrete connection `concreteConn`, the concrete
contraction `concreteTensorContract` and the `nabla_dual` operator.

## Main helpers

* `ncsFrames x₀` : a public version of the private `chooseLocalFrames` used in
  `TensorContract.lean`. Produces a tangent frame `σ'` and dual frame `θ'` agreeing
  with `trivializationAt x₀`'s local frames on a neighborhood of `x₀`.

* `ncsFrames_sigma_eqOn_nhd`, `ncsFrames_theta_eqOn_nhd` : their spec lemmas.

* `ncsFrames_biorth_eventually` : biorthogonality on a neighborhood of `x₀`.

* `ncsFrames_sigma_basis_at` : at `x₀`, `σ'` forms a basis of `TangentSpace I x₀`.

* `T_slot0_vector_pointwise` : fiber-tensoriality in the 0-th vector slot.

* `T_slot0_covector_pointwise` : fiber-tensoriality in the 0-th covector slot.

* `T_fiber_expansion_vector` : local-frame expansion at `x₀` in the vector slot.

* `T_fiber_expansion_covector` : local-frame expansion at `x₀` in the covector slot.

* `nabla_dual_frame_at_x₀` : value of `(nabla_dual θ'ᵏ)(σ'ᵢ)(x₀)` using biorthogonality.

* `christoffel_cancellation` : the core cancellation identity.

These are combined downstream to prove the main theorem
`concrete_nabla_tensor_contract_comm`.
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
open SyntheticTensor
open TensorContractRealization

namespace NablaContractSynthetic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Shorthand: the `C^∞(M, ℝ)` algebra (the scalar ring `R` in the Synthetic layer). -/
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-- Shorthand: the `C^∞(M, ℝ)`-module of smooth tangent sections. -/
private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯

/-! ## Helper 1 — Frame pair at `x₀` (public reproduction of `chooseLocalFrames`).

We reproduce the private `chooseLocalFrames` of `TensorContract.lean` as a public
definition so downstream code can refer to the pair uniformly. -/

section Frames

/-- Pick smooth tangent and dual frames near `x₀` agreeing with the trivialization's
local frames for `finBasis ℝ E` (tangent) and `dualCovectorBasis'` (dual).

Public wrapper for the private `chooseLocalFrames` used in `TensorContract.lean`. -/
noncomputable def ncsFrames (x₀ : M) :
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

/-- The tangent frame `ncsFrames x₀).1` agrees with `trivializationAt x₀`'s
local frame for `finBasis ℝ E` on a neighborhood of `x₀`. -/
theorem ncsFrames_sigma_eqOn_nhd (x₀ : M) :
    ∀ᶠ x in nhds x₀, ∀ i, ((ncsFrames I M x₀).1 i) x =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
        (Module.finBasis ℝ E) i x := by
  let e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis (R := ℝ) (M := E)
  let hframe_tan := e_tan.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  exact Classical.choose_spec (hframe_tan.exists_contMDiffSection_eqOn_nhd
    e_tan.open_baseSet (mem_baseSet_trivializationAt _ _ x₀))

/-- The dual frame `(ncsFrames x₀).2` agrees with the `(0,1)`-bundle's local frame
for `dualCovectorBasis'` on a neighborhood of `x₀`. -/
theorem ncsFrames_theta_eqOn_nhd (x₀ : M) :
    ∀ᶠ x in nhds x₀, ∀ i, ((ncsFrames I M x₀).2 i) x =
      (trivializationAt (Tensor0SModel 1 ℝ E)
        (fun x => Tensor0SSpace 1 I x) x₀).localFrame
        (dualCovectorBasis' (E := E)) i x := by
  let e_1 := trivializationAt (Tensor0SModel 1 ℝ E) (fun x => Tensor0SSpace 1 I x) x₀
  let hframe_1 := e_1.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞))
    (dualCovectorBasis' (E := E))
  exact Classical.choose_spec (hframe_1.exists_contMDiffSection_eqOn_nhd
    e_1.open_baseSet (mem_baseSet_trivializationAt _ _ x₀))

end Frames

/-! ## Helper 2 — Biorthogonality on a neighborhood.

On a neighborhood of `x₀`, the pair `(σ', θ')` satisfies the biorthogonality identity
`toModel(θ'ⱼ y)(fun _ => σ'ᵢ y) = δⱼᵢ`. This is a direct consequence of the
Mathlib trivialization's dual-pair identity on the intersection of base sets. -/

section Biorth

/-- On a neighborhood of `x₀`, the chosen local frames `(σ', θ')` are biorthogonal:
for every `y` in that neighborhood, `θ'ⱼ y (σ'ᵢ y) = δⱼᵢ` (as real numbers at `y`). -/
theorem ncsFrames_biorth_eventually (x₀ : M) :
    ∀ᶠ y in nhds x₀, ∀ i j : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel ((ncsFrames I M x₀).2 i y))
        (fun _ : Fin 1 => (((ncsFrames I M x₀).1 j) y : TangentSpace I y)) =
        (if i = j then (1 : ℝ) else 0) := by
  -- Mirrors `chooseLocalFrames_biorth_eventually` in `TensorContract.lean`.
  have hσ := ncsFrames_sigma_eqOn_nhd I M x₀
  have hθ := ncsFrames_theta_eqOn_nhd I M x₀
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
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
  have h_toModel_symm : ∀ (N : Tensor0SModel 1 ℝ E) (v : Fin 1 → TangentSpace I y),
      (Tensor0SSpace.toModel
        ((e_1.linearEquivAt ℝ y hy_1).symm N) : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ)
        v =
      N (fun i => e_tan.continuousLinearMapAt ℝ y (v i)) := by
    intro N v
    have h_symm_eq : ((e_1.linearEquivAt ℝ y hy_1).symm N : Tensor0SSpace 1 I y) =
        e_1.symmL ℝ y N := by rfl
    rw [h_symm_eq]
    rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ y hy_tan]
    rfl
  rw [h_toModel_symm (dualCovectorBasis' i)
    (fun _ : Fin 1 => (e_tan.linearEquivAt ℝ y hy_tan).symm (b j))]
  have h_round : e_tan.continuousLinearMapAt ℝ y
      ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) = b j := by
    change e_tan.linearMapAt ℝ y ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) = b j
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hy_tan]
    change (e_tan.linearEquivAt ℝ y hy_tan) ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j)) = b j
    rw [LinearEquiv.apply_symm_apply]
  have h_funext : (fun _k : Fin 1 => e_tan.continuousLinearMapAt ℝ y
        ((e_tan.linearEquivAt ℝ y hy_tan).symm (b j))) =
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

/-- At `x₀` itself, biorthogonality of `(σ', θ')` holds: a specialization of the
`Eventually` statement by `Filter.Eventually.self_of_nhds`. -/
theorem ncsFrames_biorth_at (x₀ : M) :
    ∀ i j : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel ((ncsFrames I M x₀).2 i x₀))
        (fun _ : Fin 1 => (((ncsFrames I M x₀).1 j) x₀ : TangentSpace I x₀)) =
        (if i = j then (1 : ℝ) else 0) :=
  Filter.Eventually.self_of_nhds (ncsFrames_biorth_eventually I M x₀)

end Biorth

/-! ## Helper 3 — `σ'` at `x₀` forms a basis.

Since `σ'` at `x₀` equals the trivialization's local frame, and the trivialization's
fiber map is a linear equivalence on its base set, the family of values at `x₀` is
the image of the standard basis of `E` under `(linearEquivAt x₀).symm`, hence a basis. -/

section SigmaBasis

/-- The tangent frame `σ' = (ncsFrames x₀).1` evaluated at `x₀` is linearly independent
and spans `TangentSpace I x₀`. -/
theorem ncsFrames_sigma_basis_at_data (x₀ : M) :
    LinearIndependent ℝ (fun i => ((ncsFrames I M x₀).1 i) x₀ :
        Fin (Module.finrank ℝ E) → TangentSpace I x₀) ∧
    Submodule.span ℝ (Set.range (fun i => ((ncsFrames I M x₀).1 i) x₀ :
        Fin (Module.finrank ℝ E) → TangentSpace I x₀)) = ⊤ := by
  have hσ_x₀ := Filter.Eventually.self_of_nhds (ncsFrames_sigma_eqOn_nhd I M x₀)
  have hbase_tan : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt E _ x₀
  let le : TangentSpace I x₀ ≃ₗ[ℝ] E :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ x₀ hbase_tan
  let b := Module.finBasis (R := ℝ) (M := E)
  have hσ_eq : ∀ i, ((ncsFrames I M x₀).1 i) x₀ = le.symm (b i) := fun i => by
    rw [hσ_x₀ i]
    change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i x₀ =
      le.symm (b i)
    rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
      (hx := hbase_tan)]
    simp [Trivialization.basisAt, le]
  have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
    b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
  have h2 : (fun i => ((ncsFrames I M x₀).1 i) x₀ :
      Fin (Module.finrank ℝ E) → TangentSpace I x₀) =
      (fun i => le.symm (b i)) := funext hσ_eq
  refine ⟨?_, ?_⟩
  · rw [h2]; exact h1
  · rw [h2]
    rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I x₀)) =
        le.symm.toLinearMap '' Set.range b by
      ext w; simp [Set.mem_range, Set.mem_image]]
    rw [Submodule.span_image, b.span_eq]
    simp

/-- Packaged basis version of Helper 3. -/
theorem ncsFrames_sigma_basis_at (x₀ : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x₀),
      ∀ i, basis i = ((ncsFrames I M x₀).1 i) x₀ := by
  have h := ncsFrames_sigma_basis_at_data I M x₀
  refine ⟨Module.Basis.mk h.1 (le_of_eq h.2.symm), ?_⟩
  intro i
  exact Module.Basis.mk_apply _ _ _

end SigmaBasis

/-! ## Helper 4 — Fiber tensoriality in vector slot 0.

For `T : TensorData R V (r+1) (s+1)` and two sections `Y, Y'` with `Y x₀ = Y' x₀`,
the value `T (cons Y vs) αs x₀` depends only on the fiber value at `x₀`. We build
the `R`-linear functional `S : V →ₗ[R] R` by `S(Z) := T (cons Z vs) αs`, then apply
`smoothLinearMap_acts_pointwise`. -/

section Slot0Vector

/-- Fiber tensoriality in the 0-th vector slot: the value
`T (cons Y vs) αs x₀` depends only on `Y x₀`. -/
theorem T_slot0_vector_pointwise {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (vs : Fin s → V_ I M)
    (αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
    (Y Y' : V_ I M) (x₀ : M) (h : Y x₀ = Y' x₀) :
    (T (Fin.cons Y vs) αs) x₀ = (T (Fin.cons Y' vs) αs) x₀ := by
  -- Define the `R_`-linear functional S via `T.curryLeft`.
  -- `T.curryLeft Z` has type `TensorData R V r s`, with `T.curryLeft Z m = T (Fin.cons Z m)`.
  let S : V_ I M →ₗ[R_ I M] R_ I M :=
    { toFun := fun Z => T.curryLeft Z vs αs
      map_add' := fun Z₁ Z₂ => by
        rw [map_add T.curryLeft]
        rfl
      map_smul' := fun c Z => by
        simp only [RingHom.id_apply]
        rw [map_smul T.curryLeft]
        rfl }
  have hS : ∀ Z, S Z = T (Fin.cons Z vs) αs := fun Z => rfl
  rw [show (T (Fin.cons Y vs) αs : R_ I M) = S Y from (hS Y).symm,
      show (T (Fin.cons Y' vs) αs : R_ I M) = S Y' from (hS Y').symm]
  exact smoothLinearMap_acts_pointwise I M S Y Y' x₀ h

end Slot0Vector

/-! ## Helper 5 — Fiber tensoriality in covector slot 0.

For `T : TensorData R V (r+1) (s+1)` and two covectors `β, β'` with `β X x₀ = β' X x₀`
for every smooth vector field `X`, the value `T vs (cons β αs) x₀` is invariant. We
build the `R`-linear functional `F : (V →ₗ[R] R) →ₗ[R] R` by
`F(γ) := T vs (cons γ αs)` and apply `smoothLinearMap_acts_pointwise_covector`. -/

section Slot0Covector

/-- Fiber tensoriality in the 0-th covector slot. -/
theorem T_slot0_covector_pointwise {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (vs : Fin (s + 1) → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (β β' : V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M)
    (h : ∀ X : V_ I M, (β X) x₀ = (β' X) x₀) :
    (T vs (Fin.cons β αs)) x₀ = (T vs (Fin.cons β' αs)) x₀ := by
  -- Define the `R_`-linear functional `F : (V_ →ₗ[R_] R_) →ₗ[R_] R_`
  -- via `MultilinearMap.curryLeft` on the covector factor.
  -- `(T vs).curryLeft γ ntail = T vs (Fin.cons γ ntail)`
  let F : (V_ I M →ₗ[R_ I M] R_ I M) →ₗ[R_ I M] R_ I M :=
    { toFun := fun γ => (T vs).curryLeft γ αs
      map_add' := fun γ₁ γ₂ => by
        rw [map_add (T vs).curryLeft]
        rfl
      map_smul' := fun c γ => by
        simp only [RingHom.id_apply]
        rw [map_smul (T vs).curryLeft]
        rfl }
  have hF : ∀ γ, F γ = T vs (Fin.cons γ αs) := fun γ => rfl
  rw [show (T vs (Fin.cons β αs) : R_ I M) = F β from (hF β).symm,
      show (T vs (Fin.cons β' αs) : R_ I M) = F β' from (hF β').symm]
  exact smoothLinearMap_acts_pointwise_covector I M F β β' x₀ h

end Slot0Covector

/-! ## Helper 6 — Fiber expansion in the vector slot.

At `x₀`, any tangent vector `Y x₀` can be expanded in the basis `σ'(x₀)` with
coefficients given by the dual basis action: `Y x₀ = ∑ⱼ θ'(j)(x₀)(Y x₀) • σ'(j)(x₀)`.
Combined with Helper 4, this produces the expansion
```
T (cons Y vs) αs x₀ = ∑ⱼ θ'(j)(Y)(x₀) · T(cons σ'(j) vs) αs x₀
```
for any `Y : V_`.

This is stated for an arbitrary `Y`; downstream we instantiate `Y := concreteConn X σ'(k)`. -/

section VectorExpansion

/-- Expand a section `Y` in the local frame at `x₀`, using biorthogonality at `x₀`.

For any `T : TensorData R V (r+1) (s+1)` and any vector field `Y`, the value
`T (cons Y vs) αs x₀` equals the finite sum `∑ⱼ θ'(j)(Y)(x₀) · T(cons σ'(j) vs) αs x₀`. -/
theorem T_fiber_expansion_vector_generic {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (Y : V_ I M) (vs : Fin s → V_ I M)
    (αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    (T (Fin.cons Y vs) αs) x₀ =
      ∑ j, (covectorToFunctional I M ((ncsFrames I M x₀).2 j) Y) x₀ *
        (T (Fin.cons ((ncsFrames I M x₀).1 j) vs) αs) x₀ := by
  classical
  -- Get the basis at x₀.
  obtain ⟨basis, hb_apply⟩ := ncsFrames_sigma_basis_at I M x₀
  set σ' := (ncsFrames I M x₀).1 with hσ_def
  set θ' := (ncsFrames I M x₀).2 with hθ_def
  have h_biorth_at := ncsFrames_biorth_at I M x₀
  -- Step 1: express Y x₀ as a linear combination of σ'(j)(x₀).
  -- The coefficient of σ'(j)(x₀) equals θ'(j)(Y)(x₀) by biorthogonality.
  have h_Y_expand : Y x₀ = ∑ j, (covectorToFunctional I M (θ' j) Y) x₀ •
      ((σ' j) x₀ : TangentSpace I x₀) := by
    -- Use basis.sum_repr: Y x₀ = ∑ j, basis.repr (Y x₀) j • basis j.
    -- And identify basis.repr (Y x₀) j = θ'(j)(Y)(x₀) via the coord functional identity.
    have h_sum := basis.sum_repr (Y x₀)
    rw [← h_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hb_apply j]
    congr 1
    rw [covectorToFunctional_apply]
    -- Goal: basis.repr (Y x₀) j = toModel(θ'(j) x₀) (fun _ => Y x₀)
    -- Rewrite LHS as basis.coord j (Y x₀).
    change (basis.coord j) (Y x₀) = _
    -- Use the identification from TensorContract.lean (inline its proof).
    -- basis.coord j and (v ↦ toModel(θ'(j) x₀)(fun _ => v)) agree on basis elements
    -- (by h_biorth_at), hence agree everywhere by linearity.
    have h_on_basis : ∀ i,
        (basis.coord j) (basis i) =
          (Tensor0SSpace.toModel ((θ' j) x₀)) (fun _ : Fin 1 => basis i) := by
      intro i
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb_apply]
      rw [h_biorth_at j i]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]
    -- Now extend via basis.sum_repr.
    have h1 := basis.sum_repr (Y x₀)
    rw [← h1, map_sum]
    set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
      (Tensor0SSpace.toModel ((θ' j) x₀)).toMultilinearMap
    change _ = tm (fun _ : Fin 1 => ∑ i, basis.repr (Y x₀) i • basis i)
    rw [show (fun _ : Fin 1 => ∑ i, basis.repr (Y x₀) i • basis i) =
      Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
        (∑ i, basis.repr (Y x₀) i • basis i) from by
        funext k; fin_cases k; rfl]
    rw [tm.map_update_sum (t := Finset.univ)
      (g := fun i => basis.repr (Y x₀) i • basis i)
      (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
    simp_rw [map_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [tm.map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
      (basis.repr (Y x₀) i) (basis i)]
    rw [smul_eq_mul]
    change basis.repr (Y x₀) i • basis.coord j (basis i) = _
    rw [smul_eq_mul, h_on_basis i]
    have h_upd_const : Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0 (basis i) =
        (fun _ : Fin 1 => basis i) := by
      funext k; fin_cases k; rfl
    rw [h_upd_const, smul_eq_mul]
    rfl
  -- Step 2: Build a smooth section ψ whose fiber at x₀ equals Y x₀, as ∑ⱼ aⱼ • σ'(j),
  -- where aⱼ ∈ R_ is a smooth function with (aⱼ) x₀ = (θ'(j)(Y)) x₀.
  -- For each j, let aⱼ := covectorToFunctional I M (θ' j) Y : R_.
  let a : Fin (Module.finrank ℝ E) → R_ I M :=
    fun j => covectorToFunctional I M (θ' j) Y
  let ψ : V_ I M := ∑ j, (a j) • σ' j
  have hψ_x₀ : ψ x₀ = Y x₀ := by
    change (∑ j, (a j) • σ' j) x₀ = Y x₀
    simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
    change ∑ j, (a j x₀ : ℝ) • ((σ' j) x₀ : TangentSpace I x₀) = Y x₀
    exact h_Y_expand.symm
  -- Step 3: apply Helper 4 to replace Y with ψ in slot 0.
  rw [T_slot0_vector_pointwise I M T vs αs Y ψ x₀ hψ_x₀.symm]
  -- Step 4: ψ = ∑ⱼ aⱼ • σ'(j), so by R_-multilinearity of T in slot 0, the sum distributes.
  -- T (cons ψ vs) αs = T.curryLeft ψ vs αs = (∑ⱼ aⱼ • T.curryLeft (σ'(j))) vs αs.
  have h_distribute : T.curryLeft ψ = ∑ j, (a j) • T.curryLeft (σ' j) := by
    change T.curryLeft (∑ j, (a j) • σ' j) = _
    rw [map_sum T.curryLeft]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul T.curryLeft]
  have h_eval : T.curryLeft ψ vs αs =
      ∑ j, (a j) * (T.curryLeft (σ' j) vs αs) := by
    rw [h_distribute]
    -- LHS is now: ((∑ j, (a j) • T.curryLeft (σ' j)) vs) αs.
    -- Unfold the outer sum on the MultilinearMap layer.
    rw [MultilinearMap.sum_apply _ vs]
    -- Now: (∑ j, ((a j) • T.curryLeft (σ' j)) vs) αs.
    rw [MultilinearMap.sum_apply _ αs]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Goal: ((a j • T.curryLeft (σ' j)) vs) αs = (a j) * ((T.curryLeft (σ' j)) vs) αs
    rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply]
    rfl
  -- Evaluate at x₀.
  have : (T.curryLeft ψ vs αs) x₀ =
      ∑ j, ((a j) * (T.curryLeft (σ' j) vs αs)) x₀ := by
    rw [h_eval]
    -- Use R_evalAt_sum-style: evaluation at x₀ is a RingHom.
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    change evalAt (∑ j, (a j) * (T.curryLeft (σ' j) vs αs)) = _
    rw [map_sum]
    rfl
  -- Rewrite LHS and RHS using T.curryLeft.
  change (T.curryLeft ψ vs αs) x₀ = _
  rw [this]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Goal: ((a j) * (T.curryLeft (σ' j) vs αs)) x₀ =
  --   (covectorToFunctional I M (θ' j) Y) x₀ * (T (Fin.cons (σ' j) vs) αs) x₀
  change ((a j) x₀) * ((T.curryLeft (σ' j) vs αs) x₀) = _
  rfl

/-- Specialization of Helper 6 from the prompt: apply with `Y := concreteConn X σ'(k)`,
using the fixed covector-slot shape `Fin.cons (covectorToFunctional θ'(k)) αs`. -/
theorem T_fiber_expansion_vector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (X : V_ I M) (vs : Fin s → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (k : Fin (Module.finrank ℝ E)) :
    (T (Fin.cons (concreteConn I M cov X ((ncsFrames I M x₀).1 k)) vs)
      (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 k)) αs)) x₀ =
    ∑ j, (covectorToFunctional I M ((ncsFrames I M x₀).2 j)
      (concreteConn I M cov X ((ncsFrames I M x₀).1 k))) x₀ *
      (T (Fin.cons ((ncsFrames I M x₀).1 j) vs)
        (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 k)) αs)) x₀ :=
  T_fiber_expansion_vector_generic I M T
    (concreteConn I M cov X ((ncsFrames I M x₀).1 k)) vs
    (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 k)) αs) x₀

end VectorExpansion

/-! ## Helper 7 — `nabla_dual` fiber evaluation at `x₀`.

At `x₀`, the value `(nabla_dual emb conn X α)(σ'(i))(x₀)` simplifies when `α` is
`covectorToFunctional θ'(k)` and `σ'(i)` is a member of our local frame, because
`α(σ'(i))` is locally constant near `x₀` (by biorthogonality). -/

section NablaDualFrame

/-- The pairing `covectorToFunctional θ'(k) σ'(i)` is locally constant near `x₀`:
it equals `δₖᵢ` on the neighborhood where biorthogonality holds. -/
private lemma covectorToFunctional_ncs_pair_eventually (x₀ : M)
    (k i : Fin (Module.finrank ℝ E)) :
    ∀ᶠ y in nhds x₀,
      (covectorToFunctional I M ((ncsFrames I M x₀).2 k) ((ncsFrames I M x₀).1 i)) y =
        (if k = i then (1 : ℝ) else 0) := by
  filter_upwards [ncsFrames_biorth_eventually I M x₀] with y h
  rw [covectorToFunctional_apply]
  exact h k i

/-- A smooth function locally equal to a constant on a neighborhood of `x₀` has zero
`vectorFieldAction` at `x₀` for any smooth vector field. -/
private lemma vectorFieldAction_zero_of_locally_const
    (X : V_ I M) (f : R_ I M) (x₀ : M) (c : ℝ)
    (h : ∀ᶠ y in nhds x₀, (f : M → ℝ) y = c) :
    vectorFieldActionSmooth I M X f x₀ = 0 := by
  -- vectorFieldActionSmooth X f x₀ = extDerivFun f x₀ (X x₀) = mfderiv f x₀ (X x₀).
  -- Locally constant => mfderiv at x₀ is zero.
  change vectorFieldAction I M X f x₀ = 0
  unfold vectorFieldAction
  -- The function `f` agrees with the constant function `fun _ => c` near x₀.
  -- So mfderiv I 𝓘(ℝ, ℝ) f x₀ = mfderiv I 𝓘(ℝ, ℝ) (fun _ => c) x₀ = 0.
  have hconst : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ = 0 := by
    -- Filter.EventuallyEq.mfderiv_eq : f₁ =ᶠ[𝓝 x] f → mfderiv f₁ x = mfderiv f x.
    -- We have ⇑f =ᶠ[𝓝 x₀] fun _ => c, so we need the reverse: fun _ => c =ᶠ[𝓝 x₀] ⇑f.
    have heq_rev : (fun _ : M => c) =ᶠ[nhds x₀] (f : M → ℝ) := by
      filter_upwards [h] with y hy
      exact hy.symm
    have := Filter.EventuallyEq.mfderiv_eq (f := (f : M → ℝ)) (f₁ := fun _ : M => c)
      (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x₀) heq_rev
    rw [← this, mfderiv_const]
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hconst,
    ContinuousLinearMap.zero_apply]
  rfl

/-- Helper 7: nabla_dual fiber evaluation at `x₀`.

Unfolding `nabla_dual` gives `(emb X)(αᵏ σ'ᵢ)(x₀) − αᵏ(conn X σ'ᵢ)(x₀)`.
Using biorthogonality-eventually, `αᵏ(σ'ᵢ)` is locally constant near `x₀`, so the
first term vanishes. The second term is the non-trivial Christoffel-like residual. -/
theorem nabla_dual_frame_at_x₀
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : V_ I M) (x₀ : M) (k i : Fin (Module.finrank ℝ E)) :
    (nabla_dual (concreteDerivationEmbedding I M) (concreteConn I M cov)
      (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov)
      X (covectorToFunctional I M ((ncsFrames I M x₀).2 k)))
      ((ncsFrames I M x₀).1 i) x₀ =
    -(covectorToFunctional I M ((ncsFrames I M x₀).2 k)
      (concreteConn I M cov X ((ncsFrames I M x₀).1 i))) x₀ := by
  -- Unfold nabla_dual.
  change ((concreteDerivationEmbedding I M).embed X)
      ((covectorToFunctional I M ((ncsFrames I M x₀).2 k)) ((ncsFrames I M x₀).1 i)) x₀ -
    ((covectorToFunctional I M ((ncsFrames I M x₀).2 k))
      (concreteConn I M cov X ((ncsFrames I M x₀).1 i))) x₀ =
    -(covectorToFunctional I M ((ncsFrames I M x₀).2 k)
      (concreteConn I M cov X ((ncsFrames I M x₀).1 i))) x₀
  -- First term: (emb X)(pair)(x₀) = vectorFieldActionSmooth X pair x₀ = 0 (pair locally const).
  have h_pair_const := covectorToFunctional_ncs_pair_eventually I M x₀ k i
  have h_first_zero :
      ((concreteDerivationEmbedding I M).embed X)
        ((covectorToFunctional I M ((ncsFrames I M x₀).2 k)) ((ncsFrames I M x₀).1 i)) x₀ = 0 := by
    change (embedLinearMap I M X : Derivation ℝ (R_ I M) (R_ I M))
        ((covectorToFunctional I M ((ncsFrames I M x₀).2 k)) ((ncsFrames I M x₀).1 i)) x₀ = 0
    change (embedDeriv I M X : Derivation ℝ (R_ I M) (R_ I M))
        ((covectorToFunctional I M ((ncsFrames I M x₀).2 k)) ((ncsFrames I M x₀).1 i)) x₀ = 0
    change (vectorFieldActionSmooth I M X
        ((covectorToFunctional I M ((ncsFrames I M x₀).2 k)) ((ncsFrames I M x₀).1 i))) x₀ = 0
    exact vectorFieldAction_zero_of_locally_const I M X _ x₀ _ h_pair_const
  rw [h_first_zero]
  ring

end NablaDualFrame

/-! ## Helper 8 — Fiber expansion in the covector slot.

At `x₀`, a smooth covector `β : V_ →ₗ[R_] R_` admits a fiber decomposition:
```
(β Y)(x₀) = ∑ⱼ (β σ'(j))(x₀) · (θ'(j)(Y))(x₀).
```
Combined with Helper 5, this expansion yields
```
T vs (cons β αs) x₀ = ∑ⱼ (β σ'(j)) x₀ · T vs (cons (covectorToFunctional θ'(j)) αs) x₀.
``` -/

section CovectorExpansion

/-- Fiberwise decomposition of a smooth covector in the local dual frame at `x₀`:
for any smooth `Y`, `(β Y) x₀ = ∑ⱼ (β σ'(j)) x₀ * (θ'(j)(Y)) x₀`. -/
theorem covector_fiber_expansion_at_x₀ (β : V_ I M →ₗ[R_ I M] R_ I M)
    (Y : V_ I M) (x₀ : M) :
    (β Y) x₀ =
      ∑ j, (β ((ncsFrames I M x₀).1 j)) x₀ *
        (covectorToFunctional I M ((ncsFrames I M x₀).2 j) Y) x₀ := by
  -- Reduce to a fiber statement at x₀: both sides depend only on Y x₀.
  -- Strategy: show that at x₀, Y admits a section decomposition via ψ (from Helper 6 proof),
  -- which equals ∑ⱼ (θ'(j)(Y)) • σ'(j) at x₀. Apply β R_-linearly.
  classical
  obtain ⟨basis, hb_apply⟩ := ncsFrames_sigma_basis_at I M x₀
  set σ' := (ncsFrames I M x₀).1 with hσ_def
  set θ' := (ncsFrames I M x₀).2 with hθ_def
  have h_biorth_at := ncsFrames_biorth_at I M x₀
  -- Decompose Y x₀ in basis; coefficient of basis j is (θ' j Y)(x₀).
  have h_Y_expand : Y x₀ = ∑ j, (covectorToFunctional I M (θ' j) Y) x₀ •
      ((σ' j) x₀ : TangentSpace I x₀) := by
    have h_sum := basis.sum_repr (Y x₀)
    rw [← h_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hb_apply j]
    congr 1
    rw [covectorToFunctional_apply]
    change (basis.coord j) (Y x₀) = _
    have h_on_basis : ∀ i,
        (basis.coord j) (basis i) =
          (Tensor0SSpace.toModel ((θ' j) x₀)) (fun _ : Fin 1 => basis i) := by
      intro i
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb_apply]
      rw [h_biorth_at j i]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]
    have h1 := basis.sum_repr (Y x₀)
    rw [← h1, map_sum]
    set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x₀) ℝ :=
      (Tensor0SSpace.toModel ((θ' j) x₀)).toMultilinearMap
    change _ = tm (fun _ : Fin 1 => ∑ i, basis.repr (Y x₀) i • basis i)
    rw [show (fun _ : Fin 1 => ∑ i, basis.repr (Y x₀) i • basis i) =
      Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
        (∑ i, basis.repr (Y x₀) i • basis i) from by
        funext k; fin_cases k; rfl]
    rw [tm.map_update_sum (t := Finset.univ)
      (g := fun i => basis.repr (Y x₀) i • basis i)
      (m := fun _ : Fin 1 => (0 : TangentSpace I x₀)) (i := 0)]
    simp_rw [map_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [tm.map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0
      (basis.repr (Y x₀) i) (basis i)]
    rw [smul_eq_mul]
    change basis.repr (Y x₀) i • basis.coord j (basis i) = _
    rw [smul_eq_mul, h_on_basis i]
    have h_upd_const : Function.update (fun _ : Fin 1 => (0 : TangentSpace I x₀)) 0 (basis i) =
        (fun _ : Fin 1 => basis i) := by
      funext k; fin_cases k; rfl
    rw [h_upd_const, smul_eq_mul]
    rfl
  -- Build the section ψ whose fiber is Y x₀.
  let a : Fin (Module.finrank ℝ E) → R_ I M :=
    fun j => covectorToFunctional I M (θ' j) Y
  let ψ : V_ I M := ∑ j, (a j) • σ' j
  have hψ_x₀ : ψ x₀ = Y x₀ := by
    change (∑ j, (a j) • σ' j) x₀ = Y x₀
    simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
    change ∑ j, (a j x₀ : ℝ) • ((σ' j) x₀ : TangentSpace I x₀) = Y x₀
    exact h_Y_expand.symm
  -- Apply smoothLinearMap_acts_pointwise to replace Y with ψ:
  have h_ptwise : (β Y) x₀ = (β ψ) x₀ :=
    smoothLinearMap_acts_pointwise I M β Y ψ x₀ hψ_x₀.symm
  rw [h_ptwise]
  -- β ψ = ∑ⱼ aⱼ • β(σ' j), evaluate at x₀.
  have h_bψ : β ψ = ∑ j, (a j) • β (σ' j) := by
    change β (∑ j, (a j) • σ' j) = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
  rw [h_bψ]
  -- Evaluate at x₀ via ring hom.
  let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
  change evalAt (∑ j, (a j) • β (σ' j)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change ((a j) • β (σ' j) : R_ I M) x₀ = (β (σ' j)) x₀ * ((a j) x₀ : ℝ)
  change ((a j) * β (σ' j) : R_ I M) x₀ = (β (σ' j)) x₀ * ((a j) x₀ : ℝ)
  change ((a j) x₀ : ℝ) * (β (σ' j)) x₀ = (β (σ' j)) x₀ * ((a j) x₀ : ℝ)
  ring

/-- Helper 8 (generic covector expansion of a tensor evaluation): -/
theorem T_fiber_expansion_covector_generic {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (β : V_ I M →ₗ[R_ I M] R_ I M)
    (vs : Fin (s + 1) → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    (T vs (Fin.cons β αs)) x₀ =
      ∑ j, (β ((ncsFrames I M x₀).1 j)) x₀ *
        (T vs (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 j)) αs)) x₀ := by
  classical
  set σ' := (ncsFrames I M x₀).1 with hσ_def
  set θ' := (ncsFrames I M x₀).2 with hθ_def
  -- Build a smooth substitute covector β' for β satisfying β' Y x₀ = β Y x₀ pointwise.
  -- Specifically: β' := ∑ⱼ (β σ'(j)) • covectorToFunctional θ'(j).
  let a : Fin (Module.finrank ℝ E) → R_ I M := fun j => β (σ' j)
  let θf : Fin (Module.finrank ℝ E) → (V_ I M →ₗ[R_ I M] R_ I M) :=
    fun j => covectorToFunctional I M (θ' j)
  let β' : V_ I M →ₗ[R_ I M] R_ I M := ∑ j, (a j) • θf j
  -- β Y x₀ = β' Y x₀, for every Y, by `covector_fiber_expansion_at_x₀`.
  have h_agree : ∀ Y : V_ I M, (β Y) x₀ = (β' Y) x₀ := fun Y => by
    rw [covector_fiber_expansion_at_x₀ I M β Y x₀]
    -- RHS: (β' Y) x₀.
    change _ = ((∑ j, (a j) • θf j) Y : R_ I M) x₀
    rw [LinearMap.sum_apply]
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    change _ = evalAt (∑ j, ((a j) • θf j) Y)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change (β (σ' j)) x₀ * (covectorToFunctional I M (θ' j) Y) x₀ =
        (((a j) • θf j) Y : R_ I M) x₀
    change _ = ((a j) • θf j Y : R_ I M) x₀
    change _ = ((a j) * θf j Y : R_ I M) x₀
    rfl
  -- Apply Helper 5 (fiber tensoriality in covector slot 0):
  rw [T_slot0_covector_pointwise I M T vs αs β β' x₀ h_agree]
  -- Now expand T vs (Fin.cons β' αs) using that β' = ∑ⱼ (β σ'(j)) • covectorToFunctional (θ'(j)).
  -- Use curryLeft on covector slot 0.
  have h_curry : (T vs).curryLeft β' = ∑ j, (a j) • (T vs).curryLeft (θf j) := by
    change (T vs).curryLeft (∑ j, (a j) • θf j) = _
    rw [map_sum (T vs).curryLeft]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
  have h_eval :
      ((T vs).curryLeft β' αs) x₀ =
      ∑ j, ((a j) * ((T vs).curryLeft (θf j) αs)) x₀ := by
    rw [h_curry]
    rw [MultilinearMap.sum_apply _ αs]
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    change evalAt (∑ j, ((a j) • (T vs).curryLeft (θf j)) αs) = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MultilinearMap.smul_apply]
    rfl
  change ((T vs).curryLeft β' αs) x₀ = _
  rw [h_eval]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change ((a j) x₀ : ℝ) * ((T vs).curryLeft (θf j) αs) x₀ = _
  rfl

/-- Specialization of Helper 8 with `β := nabla_dual ... (covectorToFunctional θ'(k))`. -/
theorem T_fiber_expansion_covector_nabla_dual
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (X : V_ I M) (vs : Fin (s + 1) → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) (k : Fin (Module.finrank ℝ E)) :
    (T vs (Fin.cons
        (nabla_dual (concreteDerivationEmbedding I M) (concreteConn I M cov)
          (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov)
          X (covectorToFunctional I M ((ncsFrames I M x₀).2 k))) αs)) x₀ =
    ∑ j, (nabla_dual (concreteDerivationEmbedding I M) (concreteConn I M cov)
        (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov)
        X (covectorToFunctional I M ((ncsFrames I M x₀).2 k))
        ((ncsFrames I M x₀).1 j)) x₀ *
      (T vs (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 j)) αs)) x₀ :=
  T_fiber_expansion_covector_generic I M T
    (nabla_dual (concreteDerivationEmbedding I M) (concreteConn I M cov)
      (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov)
      X (covectorToFunctional I M ((ncsFrames I M x₀).2 k)))
    vs αs x₀

end CovectorExpansion

/-! ## Helper 9 — Christoffel cancellation (CORE).

The sum of the two diagonal "residual" terms arising when expanding
`nabla_tensor X (concreteTensorContract T)` vs. `concreteTensorContract (nabla_tensor X T)`
via the local-frame formula vanishes at `x₀`. Below, we abbreviate:
* `Γⱼₖ = (covectorToFunctional θ'(j) (concreteConn X σ'(k)))(x₀)` — the j,k Christoffel entry;
* `Tⱼₖ = T (cons σ'(j) vs) (cons (covectorToFunctional θ'(k)) αs) x₀` — the j,k tensor value.

By Helper 6, the first sum equals `∑ⱼ,ₖ Γⱼₖ · Tⱼₖ`; by Helpers 7+8, the second sum equals
`-∑ⱼ,ₖ Γⱼₖ · Tⱼₖ` (after reindexing). Their sum is therefore zero. -/

section ChristoffelCancellation

/-- **Christoffel cancellation.** At `x₀`, the sum of the first "diagonal" residual
(vector-slot contraction) and the second "diagonal" residual (covector-slot contraction)
vanishes. -/
theorem christoffel_cancellation
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : V_ I M) {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (vs : Fin s → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    (∑ k, (T (Fin.cons (concreteConn I M cov X ((ncsFrames I M x₀).1 k)) vs)
        (Fin.cons (covectorToFunctional I M ((ncsFrames I M x₀).2 k)) αs)) x₀) +
    (∑ k, (T (Fin.cons ((ncsFrames I M x₀).1 k) vs)
        (Fin.cons (nabla_dual (concreteDerivationEmbedding I M)
          (concreteConn I M cov) (concreteConn_add_right I M cov)
          (concreteConn_leibniz I M cov) X
          (covectorToFunctional I M ((ncsFrames I M x₀).2 k))) αs)) x₀) = 0 := by
  classical
  set σ' := (ncsFrames I M x₀).1 with hσ_def
  set θ' := (ncsFrames I M x₀).2 with hθ_def
  -- Abbreviations for the generic building blocks.
  -- Γⱼₖ := (covectorToFunctional θ'(j) (concreteConn X σ'(k))) x₀.
  let Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j k => (covectorToFunctional I M (θ' j) (concreteConn I M cov X (σ' k))) x₀
  -- Tⱼₖ := T (cons σ'(j) vs) (cons (covectorToFunctional θ'(k)) αs) x₀.
  let Tjk : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j k => (T (Fin.cons (σ' j) vs)
      (Fin.cons (covectorToFunctional I M (θ' k)) αs)) x₀
  -- Step 1: rewrite the first sum.
  have h_first : (∑ k, (T (Fin.cons (concreteConn I M cov X (σ' k)) vs)
        (Fin.cons (covectorToFunctional I M (θ' k)) αs)) x₀) =
      ∑ k, ∑ j, Γ j k * Tjk j k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact T_fiber_expansion_vector I M cov T X vs αs x₀ k
  -- Step 2: rewrite the second sum via Helpers 7 and 8.
  have h_second : (∑ k, (T (Fin.cons (σ' k) vs)
        (Fin.cons (nabla_dual (concreteDerivationEmbedding I M)
          (concreteConn I M cov) (concreteConn_add_right I M cov)
          (concreteConn_leibniz I M cov) X
          (covectorToFunctional I M (θ' k))) αs)) x₀) =
      ∑ k, ∑ j, (-Γ k j) * Tjk k j := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- Apply Helper 8:
    rw [T_fiber_expansion_covector_nabla_dual I M cov T X (Fin.cons (σ' k) vs) αs x₀ k]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Substitute nabla_dual_frame_at_x₀:
    rw [nabla_dual_frame_at_x₀ I M cov X x₀ k j]
  -- Step 3: rewrite the outer goal.
  rw [h_first, h_second]
  -- Combine the two iterated sums into a difference.
  rw [show (∑ k, ∑ j, (-Γ k j) * Tjk k j) = - ∑ k, ∑ j, Γ k j * Tjk k j by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_mul]]
  -- Use Finset.sum_comm to swap outer/inner sums in the second term.
  rw [show (∑ k, ∑ j, Γ k j * Tjk k j) = ∑ j, ∑ k, Γ j k * Tjk j k from by
    rw [Finset.sum_comm]]
  -- Final cancellation: `∑ k ∑ j a - ∑ j ∑ k a = 0` (after re-associating outer).
  rw [show (∑ k, ∑ j, Γ j k * Tjk j k) = ∑ j, ∑ k, Γ j k * Tjk j k from by
    rw [Finset.sum_comm]]
  ring

end ChristoffelCancellation

/-! ## Helper 10 — Eventual equality of `concreteTensorContract` and the local-frame sum.

The smooth function `(concreteTensorContract T m n : R_ I M)` agrees, on a neighborhood of
`x₀`, with the smooth local-frame sum using the fixed frames `(ncsFrames I M x₀)`. This is
the `TensorData`-level analogue of `concreteTr_fun_local_formula` and the key input for
handling the term `(emb X)(ct T vs αs) x₀` in the main theorem via `Filter.EventuallyEq`. -/

section ContractLocalFormula

/-- Fiber-level bilinear form: given `T, m, n, x₀` and fiber data `(v, α)` at `x₀`, the
scalar `T (cons v_ext m) (cons (cf α_ext) n) x₀` is independent of the choice of smooth
extensions `v_ext, α_ext` of `v, α`. -/
private theorem tensorContract_fiber_bilinForm_well_def {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (v : TangentSpace I y) (α : Tensor0SSpace 1 I y)
    (v_ext₁ v_ext₂ : V_ I M)
    (α_ext₁ α_ext₂ : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hv₁ : v_ext₁ y = v) (hv₂ : v_ext₂ y = v)
    (hα₁ : α_ext₁ y = α) (hα₂ : α_ext₂ y = α) :
    (T (Fin.cons v_ext₁ m) (Fin.cons (covectorToFunctional I M α_ext₁) n)) y =
      (T (Fin.cons v_ext₂ m) (Fin.cons (covectorToFunctional I M α_ext₂) n)) y := by
  refine tensorData_eval_pointwise I M (r + 1) (s + 1) T _ _ _ _ y ?_ ?_
  · intro i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; rw [hv₁, hv₂]
    | succ i => simp only [Fin.cons_succ]
  · intro j X
    induction j using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [covectorToFunctional_apply, covectorToFunctional_apply, hα₁, hα₂]
    | succ j => simp only [Fin.cons_succ]

/-- A choice of fiber-level bilinear form representative: a specific value of
`T (cons v_ext m)(cons (cf α_ext) n)` at `y`, where `v_ext, α_ext` are the smooth
extensions provided by `ContMDiffSection.exists_eq_at`. -/
private noncomputable def ncsBilinForm {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (v : TangentSpace I y) (α : Tensor0SSpace 1 I y) : ℝ :=
  let v_ext := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y v).choose
  let α_ext := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) y α).choose
  (T (Fin.cons v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) y

/-- Evaluation lemma: `ncsBilinForm T m n y v α` equals any `T (cons v_ext m)(cons (cf α_ext) n) y`
where `v_ext, α_ext` are any smooth extensions. -/
private theorem ncsBilinForm_eval {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (v : TangentSpace I y) (α : Tensor0SSpace 1 I y)
    (v_ext : V_ I M)
    (α_ext : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (hv : v_ext y = v) (hα : α_ext y = α) :
    ncsBilinForm I M T m n y v α =
      (T (Fin.cons v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) y := by
  classical
  unfold ncsBilinForm
  set v₀ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y v).choose with hv₀_def
  have hv₀ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y v).choose_spec
  set α₀ := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) y α).choose with hα₀_def
  have hα₀ := (ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) y α).choose_spec
  exact tensorContract_fiber_bilinForm_well_def I M T m n y v α v₀ v_ext α₀ α_ext hv₀ hv hα₀ hα

/-- Linearity in `v`: `ncsBilinForm T m n y (v + w) α = ncsBilinForm y v α + ncsBilinForm y w α`. -/
private theorem ncsBilinForm_add_left {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (v w : TangentSpace I y) (α : Tensor0SSpace 1 I y) :
    ncsBilinForm I M T m n y (v + w) α =
      ncsBilinForm I M T m n y v α + ncsBilinForm I M T m n y w α := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y v
  obtain ⟨w_ext, hw⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y w
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) y α
  have hvw : (v_ext + w_ext) y = v + w := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, hv, hw]
  rw [ncsBilinForm_eval I M T m n y v α v_ext α_ext hv hα,
      ncsBilinForm_eval I M T m n y w α w_ext α_ext hw hα,
      ncsBilinForm_eval I M T m n y (v + w) α (v_ext + w_ext) α_ext hvw hα]
  change ((T.curryLeft (v_ext + w_ext) m) (Fin.cons (covectorToFunctional I M α_ext) n)) y =
      ((T.curryLeft v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) y +
      ((T.curryLeft w_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) y
  rw [map_add]
  rfl

/-- ℝ-homogeneity in `v`: `ncsBilinForm T m n y (c • v) α = c * ncsBilinForm T m n y v α`. -/
private theorem ncsBilinForm_smul_left {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (c : ℝ) (v : TangentSpace I y) (α : Tensor0SSpace 1 I y) :
    ncsBilinForm I M T m n y (c • v) α = c * ncsBilinForm I M T m n y v α := by
  obtain ⟨v_ext, hv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) y v
  obtain ⟨α_ext, hα⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E)
    (V := (fun x => Tensor0SSpace 1 I x))
    (n := (⊤ : ℕ∞)) y α
  let c' : R_ I M := ⟨fun _ => c, contMDiff_const⟩
  have hcv : (c' • v_ext) y = c • v := by
    rw [ContMDiffSection.coe_smulContMDiffMap]
    change c • v_ext y = c • v
    rw [hv]
  rw [ncsBilinForm_eval I M T m n y v α v_ext α_ext hv hα,
      ncsBilinForm_eval I M T m n y (c • v) α (c' • v_ext) α_ext hcv hα]
  change ((T.curryLeft (c' • v_ext) m) (Fin.cons (covectorToFunctional I M α_ext) n)) y =
      c * ((T.curryLeft v_ext m) (Fin.cons (covectorToFunctional I M α_ext) n)) y
  rw [map_smul]
  rfl

/-- The bilinear form packaged as an `ℝ`-linear map in its first argument. -/
private noncomputable def ncsBilinFormLin {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (y : M) (α : Tensor0SSpace 1 I y) :
    TangentSpace I y →ₗ[ℝ] ℝ where
  toFun v := ncsBilinForm I M T m n y v α
  map_add' v w := ncsBilinForm_add_left I M T m n y v w α
  map_smul' c v := by
    rw [RingHom.id_apply]
    exact ncsBilinForm_smul_left I M T m n y c v α

/-- Frame-independence at a point: given two biorth + basis pairs at `y`, the
local-frame sums coincide.

This is a cut-down version of `concreteTensorContract_localSum_frame_indep`
(which is private in `TensorContract.lean`) reproved locally from the public
`tensorData_eval_pointwise` lemma, using the bilinear-form reformulation
`ncsBilinForm`. -/
private theorem localSum_frame_indep {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (σ'₁ σ'₂ : Fin (Module.finrank ℝ E) → V_ I M)
    (θ'₁ θ'₂ : Fin (Module.finrank ℝ E) →
      Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (y : M)
    (h_biorth₁ : ∀ i j, (Tensor0SSpace.toModel ((θ'₁ i) y))
      (fun _ : Fin 1 => ((σ'₁ j) y : TangentSpace I y)) = if i = j then 1 else 0)
    (h_biorth₂ : ∀ i j, (Tensor0SSpace.toModel ((θ'₂ i) y))
      (fun _ : Fin 1 => ((σ'₂ j) y : TangentSpace I y)) = if i = j then 1 else 0)
    (h_basis₁ : LinearIndependent ℝ (fun i => (σ'₁ i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y) ∧
      Submodule.span ℝ (Set.range (fun i => (σ'₁ i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y)) = ⊤)
    (h_basis₂ : LinearIndependent ℝ (fun i => (σ'₂ i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y) ∧
      Submodule.span ℝ (Set.range (fun i => (σ'₂ i) y : Fin (Module.finrank ℝ E) →
        TangentSpace I y)) = ⊤) :
    (concreteTensorContract_localSum I M r s T σ'₁ θ'₁ m n) y =
      (concreteTensorContract_localSum I M r s T σ'₂ θ'₂ m n) y := by
  classical
  rw [concreteTensorContract_localSum_apply, concreteTensorContract_localSum_apply]
  -- Rewrite each summand via ncsBilinForm (value at y depends only on fiber).
  have h_summand₁ : ∀ i,
      (T (Fin.cons (σ'₁ i) m) (Fin.cons (covectorToFunctional I M (θ'₁ i)) n)) y =
        ncsBilinForm I M T m n y ((σ'₁ i) y) ((θ'₁ i) y) := fun i => by
    rw [ncsBilinForm_eval I M T m n y ((σ'₁ i) y) ((θ'₁ i) y) (σ'₁ i) (θ'₁ i) rfl rfl]
  have h_summand₂ : ∀ i,
      (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M (θ'₂ i)) n)) y =
        ncsBilinForm I M T m n y ((σ'₂ i) y) ((θ'₂ i) y) := fun i => by
    rw [ncsBilinForm_eval I M T m n y ((σ'₂ i) y) ((θ'₂ i) y) (σ'₂ i) (θ'₂ i) rfl rfl]
  simp_rw [h_summand₁, h_summand₂]
  -- Construct bases.
  let basis₁ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    Module.Basis.mk h_basis₁.1 (le_of_eq h_basis₁.2.symm)
  let basis₂ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    Module.Basis.mk h_basis₂.1 (le_of_eq h_basis₂.2.symm)
  have hb₁_apply : ∀ i, basis₁ i = (σ'₁ i) y := fun i => Module.Basis.mk_apply _ _ _
  have hb₂_apply : ∀ i, basis₂ i = (σ'₂ i) y := fun i => Module.Basis.mk_apply _ _ _
  -- Define an auxiliary endomorphism Φ : TangentSpace I y → TangentSpace I y
  -- independent of which basis we pick. We use basis₁ + θ'₁ as the explicit construction,
  -- and show both sums equal trace(Φ).
  let Φ : TangentSpace I y →ₗ[ℝ] TangentSpace I y :=
    ∑ k, (ncsBilinFormLin I M T m n y ((θ'₁ k) y)).smulRight ((σ'₁ k) y : TangentSpace I y)
  -- Trace in basis₁ equals ∑ i, ncsBilinForm y (σ'₁_i y) (θ'₁_i y).
  have h_trace_basis₁ : LinearMap.trace ℝ (TangentSpace I y) Φ =
      ∑ i, ncsBilinForm I M T m n y ((σ'₁ i) y) ((θ'₁ i) y) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ basis₁, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hb₁_apply]
    have hΦ_apply : Φ ((σ'₁ i) y) =
        ∑ k, (ncsBilinForm I M T m n y ((σ'₁ i) y) ((θ'₁ k) y)) •
          (((σ'₁ k) y) : TangentSpace I y) := by
      change (∑ k, (ncsBilinFormLin I M T m n y ((θ'₁ k) y)).smulRight
          ((σ'₁ k) y : TangentSpace I y)) ((σ'₁ i) y) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.smulRight_apply]
      rfl
    rw [hΦ_apply, map_sum]
    have h_coord_σ : ∀ k, (basis₁.coord i) ((σ'₁ k) y : TangentSpace I y) =
        if i = k then 1 else 0 := by
      intro k
      rw [← hb₁_apply k]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hik : k = i
      · rw [if_pos hik, if_pos hik.symm]
      · rw [if_neg hik, if_neg (fun h => hik h.symm)]
    simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_coord_σ]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]
    · intro k _ hki; rw [if_neg (fun h => hki h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Trace in basis₂ equals ∑ i, ncsBilinForm y (σ'₂_i y) (θ'₂_i y).
  -- The dual expansion is analogous but requires expanding θ'₂_i in terms of θ'₁_k.
  have h_coord_eq : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I y),
      (basis₂.coord i) v = (Tensor0SSpace.toModel ((θ'₂ i) y)) (fun _ : Fin 1 => v) := by
    intro i v
    have h_on_basis : ∀ j,
        (basis₂.coord i) (basis₂ j) =
          (Tensor0SSpace.toModel ((θ'₂ i) y)) (fun _ : Fin 1 => basis₂ j) := by
      intro j
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb₂_apply]
      rw [h_biorth₂ i j]
      by_cases hij : j = i
      · rw [if_pos hij, if_pos hij.symm]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]
    have h1 := basis₂.sum_repr v
    rw [← h1, map_sum]
    set tm : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I y) ℝ :=
      (Tensor0SSpace.toModel ((θ'₂ i) y)).toMultilinearMap
    change _ = tm (fun _ : Fin 1 => ∑ j, basis₂.repr v j • basis₂ j)
    rw [show (fun _ : Fin 1 => ∑ j, basis₂.repr v j • basis₂ j) =
      Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
        (∑ j, basis₂.repr v j • basis₂ j) from by
        funext k; fin_cases k; rfl]
    rw [tm.map_update_sum (t := Finset.univ)
      (g := fun j => basis₂.repr v j • basis₂ j)
      (m := fun _ : Fin 1 => (0 : TangentSpace I y)) (i := 0)]
    simp_rw [map_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [tm.map_update_smul (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
      (basis₂.repr v j) (basis₂ j)]
    rw [smul_eq_mul]
    change basis₂.repr v j • basis₂.coord i (basis₂ j) = _
    rw [smul_eq_mul, h_on_basis j]
    have h_upd_const :
        Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 (basis₂ j) =
        (fun _ : Fin 1 => basis₂ j) := by
      funext k; fin_cases k; rfl
    rw [h_upd_const, smul_eq_mul]
    rfl
  have h_trace_basis₂ : LinearMap.trace ℝ (TangentSpace I y) Φ =
      ∑ i, ncsBilinForm I M T m n y ((σ'₂ i) y) ((θ'₂ i) y) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ basis₂, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hb₂_apply]
    -- Φ (σ'₂_i y) = ∑ k, ncsBilinForm y (σ'₂_i y) (θ'₁_k y) • (σ'₁_k y).
    have hΦ_apply : Φ ((σ'₂ i) y) =
        ∑ k, (ncsBilinForm I M T m n y ((σ'₂ i) y) ((θ'₁ k) y)) •
          (((σ'₁ k) y) : TangentSpace I y) := by
      change (∑ k, (ncsBilinFormLin I M T m n y ((θ'₁ k) y)).smulRight
          ((σ'₁ k) y : TangentSpace I y)) ((σ'₂ i) y) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.smulRight_apply]
      rfl
    change (basis₂.coord i) (Φ ((σ'₂ i) y)) = _
    rw [hΦ_apply, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_coord_eq]
    -- Goal: ∑ k, ncsBilinForm y (σ'₂_i y) (θ'₁_k y) * toModel(θ'₂_i y)(fun _ => σ'₁_k y) =
    --       ncsBilinForm y (σ'₂_i y) (θ'₂_i y).
    -- Use linearity of ncsBilinForm in α (at fixed v).
    -- First: ncsBilinFormLin is R-linear in α via left argument; but α-linearity goes
    -- through `map_smul`/`map_add` on covectors which we haven't proven.
    -- We only need the specific identity: ∑ k toModel(θ'₂_i y)(σ'₁_k y) • θ'₁_k y = θ'₂_i y.
    -- Then using multilinearity of T in the covector slot, transform the sum.
    have h_dual_expand :
        ∑ k, (Tensor0SSpace.toModel ((θ'₂ i) y)
            (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) • ((θ'₁ k) y) =
        (θ'₂ i) y := by
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      change (Tensor0SSpace.toModel (∑ k, (Tensor0SSpace.toModel ((θ'₂ i) y)
          (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) • ((θ'₁ k) y))) v =
        (Tensor0SSpace.toModel ((θ'₂ i) y)) v
      rw [show (Tensor0SSpace.toModel
          (∑ k, (Tensor0SSpace.toModel ((θ'₂ i) y)
            (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) • ((θ'₁ k) y)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I y) ℝ) =
        ∑ k, Tensor0SSpace.toModel (
          (Tensor0SSpace.toModel ((θ'₂ i) y)
            (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) • ((θ'₁ k) y)) from by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 y) _ = _
        rw [map_sum]; rfl]
      rw [ContinuousMultilinearMap.sum_apply]
      simp_rw [show ∀ k,
          (Tensor0SSpace.toModel
            ((Tensor0SSpace.toModel ((θ'₂ i) y)
              (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) • ((θ'₁ k) y))) =
          (Tensor0SSpace.toModel ((θ'₂ i) y)
            (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y))) •
            Tensor0SSpace.toModel ((θ'₁ k) y) from fun k => by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 y) _ = _
        rw [map_smul]; rfl]
      simp_rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      set w := v 0 with hw
      have hv : v = fun _ : Fin 1 => w := by funext k; fin_cases k; rfl
      rw [hv]
      set tm₂ : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I y) ℝ :=
        (Tensor0SSpace.toModel ((θ'₂ i) y)).toMultilinearMap
      have h_tm₂_eq : ∀ u : TangentSpace I y,
          (Tensor0SSpace.toModel ((θ'₂ i) y)) (fun _ : Fin 1 => u) =
            tm₂ (fun _ : Fin 1 => u) := fun _ => rfl
      simp_rw [h_tm₂_eq]
      have hw_expand : w = ∑ k, basis₁.repr w k • basis₁ k := (basis₁.sum_repr w).symm
      conv_rhs => rw [show (fun _ : Fin 1 => w) =
          Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0 w from by
            funext k; fin_cases k; rfl, hw_expand]
      rw [tm₂.map_update_sum (t := Finset.univ) (g := fun k => basis₁.repr w k • basis₁ k)
        (m := fun _ : Fin 1 => (0 : TangentSpace I y)) (i := 0)]
      have h_upd_smul : ∀ k, tm₂ (Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
              (basis₁.repr w k • basis₁ k)) =
            basis₁.repr w k * tm₂ (fun _ : Fin 1 => basis₁ k) := fun k => by
        rw [tm₂.map_update_smul]
        rw [show Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
            (basis₁ k) = (fun _ : Fin 1 => basis₁ k) from by funext m; fin_cases m; rfl]
        rw [smul_eq_mul]
      simp_rw [h_upd_smul]
      have h_θ₁_eval : ∀ k,
          (Tensor0SSpace.toModel ((θ'₁ k) y)) (fun _ : Fin 1 => w) = basis₁.repr w k := by
        intro k
        set tm₁ : MultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I y) ℝ :=
          (Tensor0SSpace.toModel ((θ'₁ k) y)).toMultilinearMap
        have h_eq : (Tensor0SSpace.toModel ((θ'₁ k) y)) (fun _ : Fin 1 => w) =
            tm₁ (fun _ : Fin 1 => w) := rfl
        rw [h_eq, hw_expand]
        rw [show (fun _ : Fin 1 => ∑ l, basis₁.repr w l • basis₁ l) =
          Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
            (∑ l, basis₁.repr w l • basis₁ l) from by
            funext m; fin_cases m; rfl]
        rw [tm₁.map_update_sum (t := Finset.univ) (g := fun l => basis₁.repr w l • basis₁ l)
          (m := fun _ : Fin 1 => (0 : TangentSpace I y)) (i := 0)]
        have h_upd_smul₁ : ∀ l,
            tm₁ (Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
              (basis₁.repr w l • basis₁ l)) =
              basis₁.repr w l * tm₁ (fun _ : Fin 1 => basis₁ l) := fun l => by
          rw [tm₁.map_update_smul]
          rw [show Function.update (fun _ : Fin 1 => (0 : TangentSpace I y)) 0
              (basis₁ l) = (fun _ : Fin 1 => basis₁ l) from by funext m; fin_cases m; rfl]
          rw [smul_eq_mul]
        simp_rw [h_upd_smul₁]
        have h_tm₁_basis : ∀ l, tm₁ (fun _ : Fin 1 => basis₁ l) =
            (if k = l then (1 : ℝ) else 0) := by
          intro l
          change (Tensor0SSpace.toModel ((θ'₁ k) y)) (fun _ : Fin 1 => basis₁ l) = _
          rw [hb₁_apply]
          exact h_biorth₁ k l
        simp_rw [h_tm₁_basis]
        rw [basis₁.sum_repr]
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl, mul_one]
        · intro l _ hlk; rw [if_neg (fun h => hlk h.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ k) h
      simp_rw [h_θ₁_eval]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hb₁_apply]
      rw [mul_comm]
    -- Now, having `∑ k toModel(θ'₂_i y)(σ'₁_k y) • θ'₁_k y = θ'₂_i y`,
    -- use ℝ-linearity of `ncsBilinForm T m n y (σ'₂_i y) (·)` as Tensor0SSpace → ℝ.
    -- This α-linearity is NOT axiomatized here. Instead, we re-derive it directly
    -- by picking smooth extensions.
    -- Pick extensions u := σ'₂_i, β_k := θ'₁_k. Then ncsBilinForm y (σ'₂_i y) (θ'₁_k y) =
    -- T (cons σ'₂_i m) (cons (cf θ'₁_k) n) y.
    -- So ∑_k ncsBilinForm(σ'₂_i y, θ'₁_k y) * toModel(θ'₂_i y)(σ'₁_k y) =
    --     ∑_k T (cons σ'₂_i m) (cons (cf θ'₁_k) n) y * toModel(θ'₂_i y)(σ'₁_k y).
    -- RHS: ncsBilinForm(σ'₂_i y, θ'₂_i y) = T (cons σ'₂_i m) (cons (cf θ'₂_i) n) y.
    -- We use the fact: cf is `R_`-linear in its argument (linear map), so
    -- cf (∑_k c_k • β_k) = ∑_k c_k • cf β_k.
    -- Equivalently, define β_total := ∑_k c_k • θ'₁_k with c_k := (cTs ... σ'₁_k),
    -- then cf β_total = ∑_k c_k • cf β_k (as smooth functionals on V_).
    -- And T (cons σ'₂_i m) (cons ... n) is R_-multilinear in the cons-ed covector (slot 0),
    -- so ∑_k c_k • T (cons _ (cons (cf θ'₁_k) n)) = T (cons _ (cons (cf β_total) n)).
    -- At y, β_total y = θ'₂_i y, so by ncsBilinForm_well_def it equals
    -- T (cons σ'₂_i m) (cons (cf θ'₂_i) n) y.
    let h_c : Fin (Module.finrank ℝ E) → R_ I M := fun k =>
      ⟨fun _ => (Tensor0SSpace.toModel ((θ'₂ i) y))
          (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y)),
        contMDiff_const⟩
    let β_total : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1 :=
      ∑ k, h_c k • θ'₁ k
    have h_hc_eval : ∀ k, (h_c k : R_ I M) y =
        ((θ'₂ i) y).toModel (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y)) := by
      intro k
      rfl
    have h_β_total_y : β_total y = (θ'₂ i) y := by
      change (∑ k, h_c k • θ'₁ k) y = (θ'₂ i) y
      rw [← h_dual_expand]
      simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [h_hc_eval k]
    -- Express T (cons σ'₂_i m) (cons (cf β_total) n) via R_-linearity in the 0-th covector slot.
    have h_cf_lin :
        covectorToFunctional I M β_total =
          ∑ k, h_c k • covectorToFunctional I M (θ'₁ k) := by
      refine LinearMap.ext (fun X => ?_)
      apply ContMDiffMap.ext; intro x
      change (Tensor0SSpace.toModel (β_total x)) (fun _ : Fin 1 => X x) =
        ((∑ k, h_c k • covectorToFunctional I M (θ'₁ k)) X) x
      rw [LinearMap.sum_apply]
      let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x
      change _ = evalAt (∑ k, (h_c k • covectorToFunctional I M (θ'₁ k)) X)
      rw [map_sum]
      change (Tensor0SSpace.toModel ((∑ k, h_c k • θ'₁ k) x)) (fun _ : Fin 1 => X x) = _
      simp only [ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      rw [show (∑ k, (h_c k x : ℝ) • ((θ'₁ k) x) : Tensor0SSpace 1 I x) =
        ∑ k, (h_c k x : ℝ) • ((θ'₁ k) x) from rfl]
      rw [show (Tensor0SSpace.toModel (∑ k, (h_c k x : ℝ) • ((θ'₁ k) x)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) =
          ∑ k, Tensor0SSpace.toModel ((h_c k x : ℝ) • ((θ'₁ k) x)) from by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 x) _ = _
        rw [map_sum]; rfl]
      rw [ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show (Tensor0SSpace.toModel ((h_c k x : ℝ) • ((θ'₁ k) x)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ) =
          (h_c k x : ℝ) • Tensor0SSpace.toModel ((θ'₁ k) x) from by
        change (Tensor0SSpace.toModelL (𝕜 := ℝ) 1 x) _ = _
        rw [map_smul]; rfl]
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      change (h_c k x : ℝ) * _ = (((h_c k : R_ I M) • (covectorToFunctional I M (θ'₁ k)) X) : R_ I M) x
      change (h_c k x : ℝ) * _ = (((h_c k : R_ I M) * (covectorToFunctional I M (θ'₁ k)) X) : R_ I M) x
      rfl
    have h_T_lin :
        (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M β_total) n)) y =
        ∑ k, (h_c k y : ℝ) *
          (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M (θ'₁ k)) n)) y := by
      rw [h_cf_lin]
      -- LHS: T (cons σ'₂_i m) (cons (∑ k hk • cf θ'₁_k) n) y.
      -- Use (T (cons σ'₂_i m)).curryLeft for linearity in slot 0 of covectors.
      change ((T (Fin.cons (σ'₂ i) m)).curryLeft
          (∑ k, h_c k • covectorToFunctional I M (θ'₁ k)) n) y = _
      rw [map_sum (T (Fin.cons (σ'₂ i) m)).curryLeft]
      rw [MultilinearMap.sum_apply]
      -- Goal: (∑ k, (T (cons σ'₂_i m)).curryLeft (h_c k • cf θ'₁_k) n) y = RHS
      -- Use `map_smul (T.curryLeft)` to pull `h_c k •` out of each summand.
      have h_each : ∀ k,
          ((T (Fin.cons (σ'₂ i) m)).curryLeft (h_c k • covectorToFunctional I M (θ'₁ k))) n =
          (h_c k : R_ I M) •
            ((T (Fin.cons (σ'₂ i) m)).curryLeft (covectorToFunctional I M (θ'₁ k))) n := by
        intro k
        rw [map_smul (T (Fin.cons (σ'₂ i) m)).curryLeft]
        rw [MultilinearMap.smul_apply]
      simp_rw [h_each]
      -- Now: (∑ k, h_c k • (T.curryLeft (cf θ'₁_k)) n) y = ∑ k, (h_c k y) * T y.
      let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom y
      change evalAt (∑ k, (h_c k : R_ I M) •
          ((T (Fin.cons (σ'₂ i) m)).curryLeft (covectorToFunctional I M (θ'₁ k))) n) = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      change ((h_c k : R_ I M) •
          (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M (θ'₁ k)) n))) y = _
      change ((h_c k : R_ I M) *
          (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M (θ'₁ k)) n))) y = _
      rfl
    -- Use ncsBilinForm_well_def and h_β_total_y to rewrite the RHS of h_T_lin.
    have h_rhs : (T (Fin.cons (σ'₂ i) m) (Fin.cons (covectorToFunctional I M β_total) n)) y =
        ncsBilinForm I M T m n y ((σ'₂ i) y) ((θ'₂ i) y) := by
      rw [ncsBilinForm_eval I M T m n y ((σ'₂ i) y) ((θ'₂ i) y) (σ'₂ i) β_total rfl h_β_total_y]
    rw [h_rhs] at h_T_lin
    -- Now `h_T_lin : ncsBilinForm y (σ'₂_i y) (θ'₂_i y) = ∑ k, (h_c k y) * T(...)`.
    -- We want: ∑ k, ncsBilinForm y (σ'₂_i y) (θ'₁_k y) * toModel(θ'₂_i y)(fun _ => σ'₁_k y)
    --       = ncsBilinForm y (σ'₂_i y) (θ'₂_i y).
    -- Use: ncsBilinForm y (σ'₂_i y) (θ'₁_k y) = T (cons σ'₂_i m)(cons (cf θ'₁_k) n) y
    --                                         (from ncsBilinForm_eval with v_ext = σ'₂_i, α_ext = θ'₁_k).
    rw [h_T_lin]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ncsBilinForm_eval I M T m n y ((σ'₂ i) y) ((θ'₁ k) y) (σ'₂ i) (θ'₁ k) rfl rfl]
    -- Goal: T(cons σ'₂_i m)(cons (cf θ'₁_k) n) y * toModel(θ'₂_i y)(fun _ => σ'₁_k y) =
    --       (h_c k) y * T(cons σ'₂_i m)(cons (cf θ'₁_k) n) y.
    -- By definition of h_c, (h_c k) y = toModel(θ'₂_i y)(fun _ => σ'₁_k y).
    have h_hc : (h_c k) y = ((θ'₂ i) y).toModel (fun _ : Fin 1 => ((σ'₁ k) y : TangentSpace I y)) :=
      rfl
    rw [h_hc]
    ring
  -- Combine:
  rw [← h_trace_basis₁, h_trace_basis₂]

/-- Eventual equality of `concreteTensorContract T m n` and the local-frame sum using
fixed frames `(ncsFrames I M x₀)` on a neighborhood of `x₀`. -/
theorem concreteTensorContract_eventuallyEq_ncsLocalSum {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (m : Fin s → V_ I M) (n : Fin r → V_ I M →ₗ[R_ I M] R_ I M) (x₀ : M) :
    ∀ᶠ y in nhds x₀,
      ((concreteTensorContract I M r s T m n : R_ I M) : M → ℝ) y =
      ((concreteTensorContract_localSum I M r s T
          (ncsFrames I M x₀).1 (ncsFrames I M x₀).2 m n : R_ I M) : M → ℝ) y := by
  classical
  -- Prepare eventual hypotheses.
  have hσ_x₀ := ncsFrames_sigma_eqOn_nhd I M x₀
  have hθ_x₀ := ncsFrames_theta_eqOn_nhd I M x₀
  have hbiorth_x₀ := ncsFrames_biorth_eventually I M x₀
  have hbase_x₀_nhds :
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ nhds x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbiorth_x₀, hσ_x₀, hbase_x₀_nhds] with y hbiorth_y hσ_y hy_base
  -- Apply concreteTensorContract_eq_localSum at y with ncsFrames y (which satisfies specs at y).
  have hσ_y_spec := ncsFrames_sigma_eqOn_nhd I M y
  have hθ_y_spec := ncsFrames_theta_eqOn_nhd I M y
  have h_ct_y : (concreteTensorContract I M r s T m n) y =
      (concreteTensorContract_localSum I M r s T
        (ncsFrames I M y).1 (ncsFrames I M y).2 m n) y :=
    concreteTensorContract_eq_localSum I M r s T m n y
      (ncsFrames I M y).1 (ncsFrames I M y).2 hσ_y_spec hθ_y_spec
  -- Biorth of (ncsFrames y) at y itself.
  have hbiorth_y_at_y := Filter.Eventually.self_of_nhds (ncsFrames_biorth_eventually I M y)
  -- Basis of (ncsFrames y).1 at y.
  have h_basis_σy := ncsFrames_sigma_basis_at_data I M y
  -- Basis of (ncsFrames x₀).1 at y.
  have h_basis_σx₀_at_y : LinearIndependent ℝ (fun i => ((ncsFrames I M x₀).1 i) y :
      Fin (Module.finrank ℝ E) → TangentSpace I y) ∧
      Submodule.span ℝ (Set.range (fun i => ((ncsFrames I M x₀).1 i) y :
        Fin (Module.finrank ℝ E) → TangentSpace I y)) = ⊤ := by
    let le : TangentSpace I y ≃ₗ[ℝ] E :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).linearEquivAt ℝ y hy_base
    let b := Module.finBasis (R := ℝ) (M := E)
    have hσ_eq : ∀ i, ((ncsFrames I M x₀).1 i) y = le.symm (b i) := fun i => by
      rw [hσ_y i]
      change (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i y =
        le.symm (b i)
      rw [(trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
        (hx := hy_base)]
      simp [Trivialization.basisAt, le]
    have h1 : LinearIndependent ℝ (fun i => le.symm (b i)) :=
      b.linearIndependent.map' le.symm.toLinearMap le.symm.ker
    have h2 : (fun i => ((ncsFrames I M x₀).1 i) y :
          Fin (Module.finrank ℝ E) → TangentSpace I y) =
        (fun i => le.symm (b i)) := funext hσ_eq
    refine ⟨?_, ?_⟩
    · rw [h2]; exact h1
    · rw [h2]
      rw [show (Set.range (fun i => le.symm (b i)) : Set (TangentSpace I y)) =
          le.symm.toLinearMap '' Set.range b by
        ext w; simp [Set.mem_range, Set.mem_image]]
      rw [Submodule.span_image, b.span_eq]
      simp
  -- Apply frame-indep at y.
  have h_frame_indep :
      (concreteTensorContract_localSum I M r s T
        (ncsFrames I M y).1 (ncsFrames I M y).2 m n) y =
      (concreteTensorContract_localSum I M r s T
        (ncsFrames I M x₀).1 (ncsFrames I M x₀).2 m n) y :=
    localSum_frame_indep I M T (ncsFrames I M y).1 (ncsFrames I M x₀).1
      (ncsFrames I M y).2 (ncsFrames I M x₀).2 m n y
      hbiorth_y_at_y hbiorth_y h_basis_σy h_basis_σx₀_at_y
  rw [h_ct_y, h_frame_indep]

end ContractLocalFormula

/-! ## Main theorem — `concrete_nabla_tensor_contract_comm_at_point`.

The pointwise identity: at every `x₀ : M`, `(nabla_tensor X (concreteTensorContract T))(vs, αs)` and
`(concreteTensorContract (nabla_tensor X T))(vs, αs)` agree at `x₀`. This is the
TensorData-level analogue of the bundle-level `concrete_nabla_contract_comm`. -/

section MainTheorem

/-- **Pointwise `NablaTensorContractComm` identity.** At every `x₀ : M`, the value of
`nabla_tensor X (concreteTensorContract T)` agrees with the value of
`concreteTensorContract (nabla_tensor X T)`. This is the SYNTHETIC TensorData-level
commutation of `∇_X` with tensor contraction, the direct analogue at the TensorData
level of the bundle-level theorem `concrete_nabla_contract_comm`. -/
theorem concrete_nabla_tensor_contract_comm_at_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : V_ I M) {r s : ℕ}
    (T : TensorData (R_ I M) (V_ I M) (r + 1) (s + 1))
    (vs : Fin s → V_ I M)
    (αs : Fin r → V_ I M →ₗ[R_ I M] R_ I M)
    (x₀ : M) :
    (nabla_tensor (concreteDerivationEmbedding I M) (concreteConn I M cov)
      (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov) X
      ((concreteAbstractTrace I M).tensor_contract T) vs αs) x₀ =
    ((concreteAbstractTrace I M).tensor_contract
      (nabla_tensor (concreteDerivationEmbedding I M) (concreteConn I M cov)
        (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov) X T) vs αs) x₀ := by
  classical
  -- Unfold the `AbstractTrace.tensor_contract` field to `concreteTensorContract`.
  rw [concreteAbstractTrace_tensor_contract, concreteAbstractTrace_tensor_contract]
  -- Unfold `nabla_tensor` via `nabla_tensor_eval` on both sides.
  set emb := concreteDerivationEmbedding I M with hemb_def
  set conn := concreteConn I M cov with hconn_def
  set ha := concreteConn_add_right I M cov with hha_def
  set hl := concreteConn_leibniz I M cov with hhl_def
  set σ' := (ncsFrames I M x₀).1 with hσ_def
  set θ' := (ncsFrames I M x₀).2 with hθ_def
  set cf : (Fin (Module.finrank ℝ E) → V_ I M →ₗ[R_ I M] R_ I M) :=
    fun k => covectorToFunctional I M (θ' k) with hcf_def
  -- LHS expansion via nabla_tensor_eval.
  rw [nabla_tensor_eval]
  -- Distribute (·) x₀ through the LHS top-level sub/sum.
  have h_LHS_distribute :
      ((emb.embed X) (concreteTensorContract I M r s T vs αs)
        - ∑ i : Fin s, concreteTensorContract I M r s T
            (Function.update vs i (conn X (vs i))) αs
        - ∑ j : Fin r, concreteTensorContract I M r s T vs
            (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀ =
      ((emb.embed X) (concreteTensorContract I M r s T vs αs)) x₀
        - ∑ i : Fin s, (concreteTensorContract I M r s T
            (Function.update vs i (conn X (vs i))) αs) x₀
        - ∑ j : Fin r, (concreteTensorContract I M r s T vs
            (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀ := by
    simp only [ContMDiffMap.coe_sub, Pi.sub_apply]
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    have h1 :
        ((∑ i : Fin s, concreteTensorContract I M r s T
            (Function.update vs i (conn X (vs i))) αs : R_ I M)) x₀ =
        ∑ i : Fin s, (concreteTensorContract I M r s T
          (Function.update vs i (conn X (vs i))) αs) x₀ := by
      change evalAt _ = _; rw [map_sum]; rfl
    have h2 :
        ((∑ j : Fin r, concreteTensorContract I M r s T vs
            (Function.update αs j (nabla_dual emb conn ha hl X (αs j))) : R_ I M)) x₀ =
        ∑ j : Fin r, (concreteTensorContract I M r s T vs
          (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀ := by
      change evalAt _ = _; rw [map_sum]; rfl
    rw [h1, h2]
  rw [h_LHS_distribute]
  -- LHS is now:
  -- (emb X)(ct T vs αs) x₀
  -- - Σ i, (ct T (update vs i (conn X (vs i))) αs) x₀
  -- - Σ j, (ct T vs (update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀
  -- RHS expansion: ct (nabla_tensor ... X T) vs αs x₀, expand ct via localSum at x₀.
  have hσ_x₀_spec := ncsFrames_sigma_eqOn_nhd I M x₀
  have hθ_x₀_spec := ncsFrames_theta_eqOn_nhd I M x₀
  rw [show ((concreteTensorContract I M r s
      (nabla_tensor emb conn ha hl X T)) vs αs) x₀ =
      (concreteTensorContract_localSum I M r s
        (nabla_tensor emb conn ha hl X T) σ' θ' vs αs) x₀ from
    concreteTensorContract_eq_localSum I M r s _ vs αs x₀ σ' θ' hσ_x₀_spec hθ_x₀_spec]
  rw [concreteTensorContract_localSum_apply]
  -- RHS is now: Σ k, (nabla_tensor emb conn ha hl X T)(cons σ'_k vs)(cons (cf θ'_k) αs) x₀.
  -- Expand the inner nabla_tensor at each summand via nabla_tensor_eval.
  -- Define abbreviations vcs_k, ccs_k to stabilize typeclass inference.
  have h_rhs_inner : ∀ k,
      ((nabla_tensor emb conn ha hl X T)
        (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
        (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)) x₀ =
        (emb.embed X) (T
          (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
          (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)) x₀
        - ∑ i : Fin (s + 1),
            T (Function.update (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i
              (conn X ((Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i)))
              (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀
        - ∑ j : Fin (r + 1),
            T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
              (Function.update
                (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j
                (nabla_dual emb conn ha hl X
                  ((Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
                    j))) x₀ := fun k => by
    have h_eq : (nabla_tensor emb conn ha hl X T)
        (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
        (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) =
      (emb.embed X) (T
        (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
        (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M))
      - ∑ i : Fin (s + 1),
          T (Function.update (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i
            (conn X ((Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i)))
            (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
      - ∑ j : Fin (r + 1),
          T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
            (Function.update
              (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j
              (nabla_dual emb conn ha hl X
                ((Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
                  j))) :=
      nabla_tensor_eval emb conn ha hl X T
        (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
        (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
    rw [h_eq]
    -- Distribute (·) x₀ over the sub and sums.
    simp only [ContMDiffMap.coe_sub, Pi.sub_apply]
    -- Goal shape: A x₀ - B x₀ - C x₀ = A x₀ - ∑ i, B_i x₀ - ∑ j, C_j x₀
    -- where B = ∑ i, B_i and C = ∑ j, C_j. Rewrite B x₀ and C x₀ using evalRingHom.
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    have hB :
        ((∑ i : Fin (s + 1),
          T (Function.update (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i
            (conn X ((Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i)))
            (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
            : R_ I M)) x₀ =
        ∑ i : Fin (s + 1),
          (T (Function.update (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i
              (conn X ((Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i)))
            (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)) x₀ := by
      change evalAt _ = _
      rw [map_sum]; rfl
    have hC :
        ((∑ j : Fin (r + 1),
          T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
            (Function.update
              (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j
              (nabla_dual emb conn ha hl X
                ((Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
                  j))) : R_ I M)) x₀ =
        ∑ j : Fin (r + 1),
          (T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
            (Function.update
              (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j
              (nabla_dual emb conn ha hl X
                ((Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M)
                  j)))) x₀ := by
      change evalAt _ = _
      rw [map_sum]; rfl
    rw [hB, hC]
  rw [Finset.sum_congr rfl (fun k _ => h_rhs_inner k)]
  -- Split the i, j sums via Fin.sum_univ_succ.
  have h_rhs_vec_split : ∀ k,
      ∑ i : Fin (s + 1), T (Function.update (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i
          (conn X ((Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i)))
          (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀ =
        T (Fin.cons (conn X (σ' k)) vs : Fin (s + 1) → V_ I M)
          (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀ +
        ∑ i : Fin s, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i)))
          : Fin (s + 1) → V_ I M)
          (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀ := by
    intro k
    rw [Fin.sum_univ_succ]
    congr 1
    · -- i = 0 case
      rw [show (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) 0 = σ' k from rfl,
          Fin.update_cons_zero]
    · -- i = .succ case
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M) i.succ = vs i from rfl,
          ← Fin.cons_update]
  have h_rhs_cov_split : ∀ k,
      ∑ j : Fin (r + 1), T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
          (Function.update (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j
            (nabla_dual emb conn ha hl X
              ((Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j))) x₀ =
        T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
          (Fin.cons (nabla_dual emb conn ha hl X (cf k)) αs :
            Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀ +
        ∑ j : Fin r, T (Fin.cons (σ' k) vs : Fin (s + 1) → V_ I M)
          (Fin.cons (cf k) (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))
            : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) x₀ := by
    intro k
    rw [Fin.sum_univ_succ]
    congr 1
    · -- j = 0 case
      rw [show (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) 0 = cf k from rfl,
          Fin.update_cons_zero]
    · -- j = .succ case
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show (Fin.cons (cf k) αs : Fin (r + 1) → V_ I M →ₗ[R_ I M] R_ I M) j.succ = αs j
          from rfl,
        ← Fin.cons_update]
  simp_rw [h_rhs_vec_split, h_rhs_cov_split]
  -- At this point, the RHS is
  -- ∑ k, ((emb X)(T(cons σ'_k vs)(cons (cf θ'_k) αs)) x₀
  --         - (T(cons (conn X σ'_k) vs)(cons (cf θ'_k) αs) x₀ +
  --            ∑ i, T(cons σ'_k (update vs i ..))(cons (cf θ'_k) αs) x₀)
  --         - (T(cons σ'_k vs)(cons (nabla_dual X (cf θ'_k)) αs) x₀ +
  --            ∑ j, T(cons σ'_k vs)(cons (cf θ'_k) (update αs j ..)) x₀))
  -- We distribute Σ over subtraction/addition using Finset.sum_sub_distrib and
  -- Finset.sum_add_distrib on the outer Σ k.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ((emb.embed X) (T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs)) x₀
        - (T (Fin.cons (conn X (σ' k)) vs) (Fin.cons (cf k) αs) x₀ +
           ∑ i : Fin s, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i))))
             (Fin.cons (cf k) αs) x₀)
        - (T (Fin.cons (σ' k) vs)
             (Fin.cons (nabla_dual emb conn ha hl X (cf k)) αs) x₀ +
           ∑ j : Fin r, T (Fin.cons (σ' k) vs) (Fin.cons (cf k)
             (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀))) =
      (∑ k, (emb.embed X) (T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs)) x₀)
      - (∑ k, T (Fin.cons (conn X (σ' k)) vs) (Fin.cons (cf k) αs) x₀)
      - (∑ k, ∑ i : Fin s, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i))))
          (Fin.cons (cf k) αs) x₀)
      - (∑ k, T (Fin.cons (σ' k) vs)
          (Fin.cons (nabla_dual emb conn ha hl X (cf k)) αs) x₀)
      - (∑ k, ∑ j : Fin r, T (Fin.cons (σ' k) vs) (Fin.cons (cf k)
          (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀) from by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring]
  -- Now expand LHS.
  -- LHS first term: (emb X)(ct T vs αs) x₀ = Σ_k (emb X)(T(cons σ'_k vs)(cons (cf θ'_k) αs)) x₀.
  -- Use the eventual equality + derivation linearity.
  have h_LHS_first : ((emb.embed X) (concreteTensorContract I M r s T vs αs)) x₀ =
      ∑ k, ((emb.embed X) (T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs))) x₀ := by
    -- Set up the smooth finite sum.
    set S : R_ I M := ∑ k, T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs) with hS_def
    -- Show ct T vs αs =ᶠ S near x₀ (as M → ℝ functions).
    have h_ev : ((concreteTensorContract I M r s T vs αs : R_ I M) : M → ℝ) =ᶠ[nhds x₀]
        ((S : R_ I M) : M → ℝ) := by
      have hev := concreteTensorContract_eventuallyEq_ncsLocalSum I M T vs αs x₀
      filter_upwards [hev] with y hy
      rw [hy]
      change (concreteTensorContract_localSum I M r s T σ' θ' vs αs : R_ I M) y = _
      rw [concreteTensorContract_localSum_apply]
      let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom y
      change _ = evalAt (∑ k, T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs))
      rw [map_sum]
      rfl
    -- Use Filter.EventuallyEq.mfderiv_eq.
    have hmfd : mfderiv I 𝓘(ℝ, ℝ)
        ((concreteTensorContract I M r s T vs αs : R_ I M) : M → ℝ) x₀ =
      mfderiv I 𝓘(ℝ, ℝ) ((S : R_ I M) : M → ℝ) x₀ :=
      Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) h_ev
    -- Also ct T vs αs x₀ = S x₀.
    have hval : ((concreteTensorContract I M r s T vs αs : R_ I M) : M → ℝ) x₀ =
        ((S : R_ I M) : M → ℝ) x₀ := h_ev.self_of_nhds
    -- Now: (emb X)(ct T vs αs) x₀ = vectorFieldAction X (ct T vs αs) x₀ =
    --                              extDerivFun (ct T vs αs) x₀ (X x₀)
    --                            = extDerivFun S x₀ (X x₀) via hmfd
    --                            = vectorFieldAction X S x₀
    --                            = (emb X) S x₀.
    change (embedLinearMap I M X : Derivation ℝ (R_ I M) (R_ I M))
        (concreteTensorContract I M r s T vs αs) x₀ = _
    change (embedDeriv I M X : Derivation ℝ (R_ I M) (R_ I M))
        (concreteTensorContract I M r s T vs αs) x₀ = _
    change (vectorFieldActionSmooth I M X
        (concreteTensorContract I M r s T vs αs)) x₀ = _
    have h_emb_eq : (vectorFieldActionSmooth I M X
          (concreteTensorContract I M r s T vs αs)) x₀ =
        (vectorFieldActionSmooth I M X S) x₀ := by
      change vectorFieldAction I M X (concreteTensorContract I M r s T vs αs) x₀ =
        vectorFieldAction I M X S x₀
      unfold vectorFieldAction
      simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [hmfd, hval]
    rw [h_emb_eq]
    -- Now (emb X) S x₀ = Σ_k (emb X)(T(...)) x₀ by linearity of derivation over finite sum.
    change (embedDeriv I M X : Derivation ℝ (R_ I M) (R_ I M)) S x₀ = _
    rw [show (S : R_ I M) = ∑ k, T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs) from rfl]
    rw [map_sum (embedDeriv I M X : Derivation ℝ (R_ I M) (R_ I M))]
    let evalAt : R_ I M →+* ℝ := ContMDiffMap.evalRingHom x₀
    change evalAt (∑ k, (embedDeriv I M X : Derivation ℝ (R_ I M) (R_ I M))
        (T (Fin.cons (σ' k) vs) (Fin.cons (cf k) αs))) = _
    rw [map_sum]
    rfl
  rw [h_LHS_first]
  -- LHS second term: -Σ i, (ct T (update vs i (conn X (vs i))) αs) x₀.
  -- Apply concreteTensorContract_eq_localSum at x₀.
  have h_LHS_second : ∀ i,
      (concreteTensorContract I M r s T (Function.update vs i (conn X (vs i))) αs) x₀ =
        ∑ k, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i))))
          (Fin.cons (cf k) αs) x₀ := by
    intro i
    rw [concreteTensorContract_eq_localSum I M r s T
      (Function.update vs i (conn X (vs i))) αs x₀ σ' θ' hσ_x₀_spec hθ_x₀_spec]
    rw [concreteTensorContract_localSum_apply]
  -- LHS third term: -Σ j, (ct T vs (update αs j (nabla_dual X αs_j))) x₀.
  have h_LHS_third : ∀ j,
      (concreteTensorContract I M r s T vs
        (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀ =
        ∑ k, T (Fin.cons (σ' k) vs) (Fin.cons (cf k)
          (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀ := by
    intro j
    rw [concreteTensorContract_eq_localSum I M r s T vs
      (Function.update αs j (nabla_dual emb conn ha hl X (αs j))) x₀ σ' θ' hσ_x₀_spec hθ_x₀_spec]
    rw [concreteTensorContract_localSum_apply]
  -- Substitute.
  simp_rw [h_LHS_second, h_LHS_third]
  -- LHS is now:
  -- Σ_k (emb X)(T(cons σ'_k vs)(cons (cf θ'_k) αs)) x₀
  -- - Σ i, Σ_k T(cons σ'_k (update vs i (conn X vs i)))(cons (cf θ'_k) αs) x₀
  -- - Σ j, Σ_k T(cons σ'_k vs)(cons (cf θ'_k) (update αs j (nabla_dual X αs_j))) x₀
  -- Compare with RHS (after regrouping):
  -- Σ_k (emb X)(T(cons σ'_k vs)(cons (cf θ'_k) αs)) x₀       -- matches LHS first term
  -- - Σ_k T(cons (conn X σ'_k) vs)(cons (cf θ'_k) αs) x₀     -- residual A (christoffel)
  -- - Σ_k Σ_i T(cons σ'_k (update vs i ...))(cons (cf θ'_k) αs) x₀   -- matches LHS second (after swap)
  -- - Σ_k T(cons σ'_k vs)(cons (nabla_dual X (cf θ'_k)) αs) x₀      -- residual B (christoffel)
  -- - Σ_k Σ_j T(cons σ'_k vs)(cons (cf θ'_k) (update αs j ...)) x₀  -- matches LHS third (after swap)
  -- Rearrange so that LHS - RHS = A + B = 0 (by christoffel_cancellation).
  rw [show (∑ i, ∑ k, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i))))
          (Fin.cons (cf k) αs) x₀) =
        (∑ k, ∑ i, T (Fin.cons (σ' k) (Function.update vs i (conn X (vs i))))
          (Fin.cons (cf k) αs) x₀) from by rw [Finset.sum_comm]]
  rw [show (∑ j, ∑ k, T (Fin.cons (σ' k) vs) (Fin.cons (cf k)
          (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀) =
        (∑ k, ∑ j, T (Fin.cons (σ' k) vs) (Fin.cons (cf k)
          (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) x₀) from by
    rw [Finset.sum_comm]]
  -- Now LHS has the same "matching" sums. Introduce the Christoffel residuals.
  -- Use christoffel_cancellation to show:
  --   Σ_k T(cons (conn X σ'_k) vs)(cons (cf θ'_k) αs) x₀
  -- + Σ_k T(cons σ'_k vs)(cons (nabla_dual X (cf θ'_k)) αs) x₀ = 0.
  have h_cancel := christoffel_cancellation I M cov X T vs αs x₀
  -- Rearrange h_cancel to match our term shape.
  -- h_cancel : Σ_k T(cons (conn X σ'_k) vs)(cons (cf θ'_k) αs) x₀
  --          + Σ_k T(cons σ'_k vs)(cons (nabla_dual X (cf θ'_k)) αs) x₀ = 0.
  linarith [h_cancel]

/-- **Synthetic `NablaTensorContractComm` for `concreteConn cov`**.
The covariant derivative `nabla_tensor` induced by the Mathlib `CovariantDerivative cov`
on the tangent bundle commutes with the abstract tensor contraction at the Synthetic
TensorData level. Immediate consequence of the pointwise identity
`concrete_nabla_tensor_contract_comm_at_point` via `MultilinearMap.ext` and
`ContMDiffMap.ext`. -/
theorem concrete_NablaTensorContractComm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    NablaTensorContractComm
      (concreteDerivationEmbedding I M)
      (concreteAbstractTrace I M)
      (concreteConn I M cov)
      (concreteConn_add_right I M cov) (concreteConn_leibniz I M cov) := by
  intro X r s T
  refine MultilinearMap.ext fun vs => ?_
  refine MultilinearMap.ext fun αs => ?_
  refine ContMDiffMap.ext fun x₀ => ?_
  exact concrete_nabla_tensor_contract_comm_at_point I M cov X T vs αs x₀

end MainTheorem

end NablaContractSynthetic

end







