/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Dual.Basis
/-!
# Dual of the multilinear bundle as multilinear maps on the dual

This file establishes the canonical (model-fiber-level) linear equivalence between
the continuous dual of `MLF r = ContinuousMultilinearMap 𝕜 (Fin r → F) 𝕜`
and the space of `r`-multilinear maps on the dual `F →L[𝕜] 𝕜`:

  `(MLF r) →L[𝕜] 𝕜  ≃ₗ[𝕜]  ContinuousMultilinearMap 𝕜 (Fin r → (F →L[𝕜] 𝕜)) 𝕜`

The forward map sends a linear functional `φ` on `MLF r` to the multilinear map
`(α₁,…,αᵣ) ↦ φ((v₁,…,vᵣ) ↦ ∏ αᵢ(vᵢ))`. The construction relies on the `mkPiAlgebra`
"product" multilinear map and `compContinuousLinearMapLRight` to package the tensor
product of dual elements as a multilinear map.

The equivalence is built explicitly: we construct the inverse map via `Basis.constr`
on the explicit basis of `MLF r` from `Multilinear/Basis.lean`, then verify that
the round trips are identities. Both round trips reduce to checking equality on
basis elements / multilinear inputs.

This is the model-fiber-level iso that will later be used to identify the dual of the
multilinear bundle (`Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`) with the
multilinear bundle of the dual (`Bundle.continuousMultilinearMap 𝕜 r F* E*`).

## Main Definitions

* `ContinuousMultilinearMap.tensorOfDualLinearForms` : the multilinear "tensor of duals"
  map, sending `(α₁,…,αᵣ) ∈ (F →L[𝕜] 𝕜)^r` to the multilinear map
  `(v₁,…,vᵣ) ↦ ∏ αᵢ(vᵢ)`.
* `ContinuousMultilinearMap.dualMultilinearLinearMap` : the forward linear map from
  `(MLF r)*` to `MLF r over F*`.
* `ContinuousMultilinearMap.dualMultilinearInverseMap` : the explicit inverse, built
  via `Basis.constr` on the basis of `MLF r`.
* `ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual` : the linear
  equivalence assembled via `LinearEquiv.ofLinear` from the two maps and the
  round-trip identities.

## Tags

multilinear map, dual, finite-dimensional, tensor of duals
-/

noncomputable section

open Module

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ## The "tensor of duals" multilinear map -/

/-- The "tensor of dual linear forms as a multilinear map" continuous multilinear map at
the model-fiber level: sends `(α₁,…,αᵣ) ∈ (F →L[𝕜] 𝕜)^r` to the `r`-multilinear map
`(v₁,…,vᵣ) ↦ ∏ αᵢ(vᵢ) ∈ 𝕜`.

Built by composing the "product" multilinear map `mkPiAlgebra 𝕜 (Fin r) 𝕜` with linear
maps in each slot, packaged as a multilinear map in those linear maps via
`compContinuousLinearMapLRight`. -/
noncomputable def tensorOfDualLinearForms (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
  ContinuousMultilinearMap.compContinuousLinearMapLRight (E := fun _ : Fin r => F)
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin r) 𝕜)

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem tensorOfDualLinearForms_apply (r : ℕ) (α : Fin r → (F →L[𝕜] 𝕜))
    (v : Fin r → F) :
    tensorOfDualLinearForms 𝕜 F r α v = ∏ i, α i (v i) := by
  simp [tensorOfDualLinearForms,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-! ## The forward linear map -/

variable (𝕜 F)

/-- The linear map from `(MLF r)*` (continuous dual of `r`-multilinear maps on `F`) to
the space of `r`-multilinear maps on the dual `F →L[𝕜] 𝕜`, sending a linear functional
`φ` to `(α₁,…,αᵣ) ↦ φ((v₁,…,vᵣ) ↦ ∏ αᵢ(vᵢ))`. -/
noncomputable def dualMultilinearLinearMap (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 where
  toFun φ := φ.compContinuousMultilinearMap (tensorOfDualLinearForms 𝕜 F r)
  map_add' φ ψ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      Function.comp_apply]
  map_smul' c φ := by
    ext α
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
      Function.comp_apply, RingHom.id_apply]

variable {𝕜 F}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem dualMultilinearLinearMap_apply (r : ℕ)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (F →L[𝕜] 𝕜)) :
    dualMultilinearLinearMap 𝕜 F r φ α =
      φ ((tensorOfDualLinearForms 𝕜 F r) α) := rfl

/-! ## Basis identification of `tensorOfDualLinearForms` -/

variable (𝕜 F)

/-- The basis element `continuousMultilinearMap_basisElem b r σ` of `MLF r` (a tensor
product of coordinate functionals) coincides with `tensorOfDualLinearForms` applied to
the dual basis at the index `σ`. -/
theorem basisElem_eq_tensorOfDualLinearForms {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (r : ℕ) (σ : Fin r → Fin d) :
    continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) b r σ
      = tensorOfDualLinearForms 𝕜 F r
        (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i))) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorOfDualLinearForms_apply]
  simp [continuousMultilinearMap_basisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply]

/-! ## Dual basis decomposition for the continuous dual `F →L[𝕜] 𝕜` -/

variable {𝕜 F}

/-- The continuous-linear analogue of `Basis.sum_dual_apply_smul_coord`: any
continuous linear functional on `F` decomposes in the dual basis as
`α = ∑ k, α (b k) • LinearMap.toContinuousLinearMap (b.coord k)`. -/
theorem cdual_sum_repr {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F) (α : F →L[𝕜] 𝕜) :
    (∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)) = α := by
  -- Lift to the algebraic dual via `Basis.sum_dual_apply_smul_coord`.
  apply ContinuousLinearMap.coe_injective
  -- Goal (after coe): ∑ k, α (b k) • b.coord k = α
  rw [show ((∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)
        : F →L[𝕜] 𝕜) : F →ₗ[𝕜] 𝕜) =
      ∑ k, (α (b k)) • (b.coord k) by
    rw [ContinuousLinearMap.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.coe_smul, LinearMap.coe_toContinuousLinearMap]]
  exact b.sum_dual_apply_smul_coord (α : F →ₗ[𝕜] 𝕜)

/-! ## The explicit inverse map

We construct the inverse `dualMultilinearInverseMap` in two steps:

1. First, we build a `LinearMap` directly from `Basis.constr`. This uses
   `Basis.constr 𝕜 (data Ψ) : (MLF r) →ₗ[𝕜] 𝕜` for each `Ψ`, then promotes to a
   continuous linear map via `LinearMap.toContinuousLinearMap` (a `LinearEquiv` in
   finite dimensions).
2. Then, we prove `map_add'` and `map_smul'` by reducing each goal via
   `ContinuousLinearMap.coe_injective` and `Basis.ext` to verifying equality on basis
   elements, where everything reduces to `Basis.constr_basis`.
-/

variable (𝕜 F)

private noncomputable def dualMultilinearInverseAux (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  LinearMap.toContinuousLinearMap
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r).constr 𝕜
      (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i)))))

variable {𝕜 F}

private theorem dualMultilinearInverseAux_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverseAux 𝕜 F r Ψ
        (continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
  -- bMLF σ definitionally equals continuousMultilinearMap_basisElem b r σ.
  have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
      continuousMultilinearMap_basisElem b r σ :=
    congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
  -- Unfold the definition to expose the Basis.constr.
  change LinearMap.toContinuousLinearMap
      (bMLF.constr 𝕜 (fun σ => Ψ (fun i =>
        LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      (continuousMultilinearMap_basisElem b r σ) = _
  rw [LinearMap.coe_toContinuousLinearMap', ← hb_eq, Basis.constr_basis]

variable (𝕜 F)

/-- The explicit inverse of `dualMultilinearLinearMap`, built via `Basis.constr` on the
explicit basis of `MLF r`. Given a multilinear map `Ψ` on `(F →L[𝕜] 𝕜)^r`, produces the
continuous linear functional on `MLF r` whose value on the basis element
`continuousMultilinearMap_basisElem b r σ` is `Ψ (b.coord ∘ σ)`. -/
noncomputable def dualMultilinearInverseMap (r : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 →ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) where
  toFun := dualMultilinearInverseAux 𝕜 F r
  map_add' Ψ₁ Ψ₂ := by
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂) (bMLF σ) =
          (dualMultilinearInverseAux 𝕜 F r Ψ₁ + dualMultilinearInverseAux 𝕜 F r Ψ₂)
            (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMap_basisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, ContinuousLinearMap.add_apply,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂) x =
        (dualMultilinearInverseAux 𝕜 F r Ψ₁ + dualMultilinearInverseAux 𝕜 F r Ψ₂) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverseAux 𝕜 F r (Ψ₁ + Ψ₂)).toLinearMap)
        (f₂ := ((dualMultilinearInverseAux 𝕜 F r Ψ₁ +
          dualMultilinearInverseAux 𝕜 F r Ψ₂).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x
  map_smul' c Ψ := by
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
      continuousMultilinearMap_finiteDimensional r
    apply ContinuousLinearMap.ext
    intro x
    let b := Module.finBasis 𝕜 F
    let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
    have h_basis : ∀ σ,
        dualMultilinearInverseAux 𝕜 F r (c • Ψ) (bMLF σ) =
          (c • dualMultilinearInverseAux 𝕜 F r Ψ) (bMLF σ) := by
      intro σ
      have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
          continuousMultilinearMap_basisElem b r σ :=
        congr_fun (Module.Basis.coe_mk
          (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
      rw [hb_eq, ContinuousLinearMap.smul_apply,
        dualMultilinearInverseAux_basisElem,
        dualMultilinearInverseAux_basisElem]
      rfl
    have hLHS : ∀ x, dualMultilinearInverseAux 𝕜 F r (c • Ψ) x =
        (c • dualMultilinearInverseAux 𝕜 F r Ψ) x := by
      have := bMLF.ext (f₁ := (dualMultilinearInverseAux 𝕜 F r (c • Ψ)).toLinearMap)
        (f₂ := ((c • dualMultilinearInverseAux 𝕜 F r Ψ).toLinearMap)) h_basis
      intro x
      exact congrFun (congrArg DFunLike.coe this) x
    exact hLHS x

variable {𝕜 F}

/-- Defining property of `dualMultilinearInverseMap`: it sends `Ψ` to a functional whose
value on the basis element `continuousMultilinearMap_basisElem b r σ` is `Ψ (b.coord ∘ σ)`,
where `b = Module.finBasis 𝕜 F`. -/
theorem dualMultilinearInverseMap_basisElem (r : ℕ)
    (Ψ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (σ : Fin r → Fin (Module.finrank 𝕜 F)) :
    dualMultilinearInverseMap 𝕜 F r Ψ
        (continuousMultilinearMap_basisElem (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) r σ) =
      Ψ (fun i =>
        LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 F).coord (σ i))) :=
  dualMultilinearInverseAux_basisElem r Ψ σ

/-! ## Round-trip identities -/

variable (𝕜 F)

/-- Left inverse: `dualMultilinearInverseMap ∘ dualMultilinearLinearMap = id`. -/
theorem dualMultilinearInverseMap_dualMultilinearLinearMap (r : ℕ) :
    (dualMultilinearInverseMap 𝕜 F r).comp (dualMultilinearLinearMap 𝕜 F r) =
      LinearMap.id := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro φ
  change ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) : _ →L[𝕜] _)
    = φ
  apply ContinuousLinearMap.ext
  intro x
  let b := Module.finBasis 𝕜 F
  let bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
  have h_basis : ∀ σ,
      ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
          _ →L[𝕜] _) (bMLF σ) = φ (bMLF σ) := by
    intro σ
    have hb_eq : (bMLF σ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) =
        continuousMultilinearMap_basisElem b r σ :=
      congr_fun (Module.Basis.coe_mk
        (continuousMultilinearMap_basisElem_linearIndependent b r) _) σ
    rw [hb_eq, dualMultilinearInverseMap_basisElem,
      show (dualMultilinearLinearMap 𝕜 F r φ) (fun i =>
          LinearMap.toContinuousLinearMap (b.coord (σ i))) =
        φ ((tensorOfDualLinearForms 𝕜 F r) (fun i =>
            LinearMap.toContinuousLinearMap (b.coord (σ i)))) from rfl,
      ← basisElem_eq_tensorOfDualLinearForms]
  have hAll : ∀ x, ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ) :
        _ →L[𝕜] _) x = φ x := by
    have :=
      bMLF.ext (f₁ := ((dualMultilinearInverseMap 𝕜 F r) ((dualMultilinearLinearMap 𝕜 F r) φ)
          : _ →L[𝕜] _).toLinearMap)
        (f₂ := (φ : _ →L[𝕜] _).toLinearMap) h_basis
    intro y
    exact congrFun (congrArg DFunLike.coe this) y
  exact hAll x

/-- Right inverse: `dualMultilinearLinearMap ∘ dualMultilinearInverseMap = id`. -/
theorem dualMultilinearLinearMap_dualMultilinearInverseMap (r : ℕ) :
    (dualMultilinearLinearMap 𝕜 F r).comp (dualMultilinearInverseMap 𝕜 F r) =
      LinearMap.id := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  apply LinearMap.ext
  intro Ψ
  apply ContinuousMultilinearMap.ext
  intro α
  let b := Module.finBasis 𝕜 F
  have hα : ∀ i, α i = ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k) := fun i =>
    (cdual_sum_repr (𝕜 := 𝕜) (F := F) b (α i)).symm
  have hα_funext : α = (fun i => ∑ k, α i (b k) •
      LinearMap.toContinuousLinearMap (b.coord k)) := funext hα
  change ((dualMultilinearLinearMap 𝕜 F r) ((dualMultilinearInverseMap 𝕜 F r) Ψ)) α = Ψ α
  rw [dualMultilinearLinearMap_apply]
  change (dualMultilinearInverseAux 𝕜 F r Ψ : _ →L[𝕜] _)
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  change LinearMap.toContinuousLinearMap
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r).constr 𝕜
        (fun σ => Ψ (fun i => LinearMap.toContinuousLinearMap (b.coord (σ i)))))
      ((tensorOfDualLinearForms 𝕜 F r) α) = Ψ α
  rw [LinearMap.coe_toContinuousLinearMap',
    Basis.constr_apply_fintype]
  set bMLF := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := F) b r
  have hcoord : ∀ σ, bMLF.equivFun ((tensorOfDualLinearForms 𝕜 F r) α) σ
      = ∏ i, α i (b (σ i)) := by
    intro σ
    rw [Basis.equivFun_apply, continuousMultilinearMap_basis_repr,
      tensorOfDualLinearForms_apply]
  simp_rw [hcoord]
  conv_rhs => rw [hα_funext, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i => α i (b (σ i)) •
        LinearMap.toContinuousLinearMap (b.coord (σ i))) =
      (fun i => (α i (b (σ i))) •
        (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j))) i) from rfl,
    ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-! ## The linear equivalence -/

/-- The linear equivalence `(MLF r)* ≃ₗ MLF r over F*`, built explicitly via the
forward map `dualMultilinearLinearMap` and the inverse `dualMultilinearInverseMap`,
with the round-trip identities. -/
noncomputable def dualMultilinearEquivMultilinearOfDual (r : ℕ) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 :=
  LinearEquiv.ofLinear
    (dualMultilinearLinearMap 𝕜 F r)
    (dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearLinearMap_dualMultilinearInverseMap 𝕜 F r)
    (dualMultilinearInverseMap_dualMultilinearLinearMap 𝕜 F r)

end ContinuousMultilinearMap

end
