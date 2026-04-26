/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Fiber
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.Multilinear.Dual
import Mathlib.LinearAlgebra.Contraction
import DifferentialGeometry.Tensor.Product.Section
import DifferentialGeometry.Tensor.Product.HomEquiv

/-!
# The Tensor Product Decomposition of Mixed `(r, s)`-Tensors

For a `C^n` vector bundle `E` over `B` with model fiber `F`, the mixed `(r, s)`-tensor
bundle `Tʳₛ(E)` decomposes as a tensor product:

  `Tʳₛ(E) ≃ T⁰ᵣ(E*) ⊗ T⁰ₛ(E)`

i.e. the `r`-multilinear bundle on the dual tensored with the `s`-multilinear bundle,
as a `C^n` vector bundle equivalence (`ContMDiffVectorBundleEquiv`). Fiberwise, a CLM
`T : Tʳₛ(E)ₓ` is sent via `homEquivCDualTensor` (the tensor-hom iso `Hom(V, W) ≃ V* ⊗ W`)
composed with `dualMultilinearEquivMultilinearOfDual` on the first factor.

## Main Definitions

* `ContinuousMultilinearMap.homEquivCDualTensor` : the abstract tensor-hom iso
  `(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W`.
* `ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor` :
  model-fiber linear equivalence
  `(MLF r →L[𝕜] MLF s) ≃ₗ[𝕜] (MLF_dual r) ⊗[𝕜] (MLF s)`.
* `Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle` :
  fiberwise `LinearEquiv` between the mixed fiber and the tensor product fiber at each `x : B`.
* `ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor_naturality` :
  naturality of the model-level equivalence w.r.t. the base-bundle transition map `Φ`.
* `mixedBundle_tensorBundle_equiv` :
  the `C^n` vector bundle equivalence assembling the fiberwise equivs into a global smooth
  equivalence over `B`.
* `mixedSectionToTensorBundleSection` / `tensorBundleSectionToMixedSection` :
  section-level transport across the equivalence, with round-trip and linearity lemmas.
* `mixedBundle_tensorBundle_sectionEquiv` :
  the `C^n`-linear equivalence between mixed sections and tensor product bundle sections.

## Implementation Notes

The equivalence is built in four stages: (1) an explicit fiber-level `LinearEquiv` via
`homEquivCDualTensor` and `dualMultilinearEquivMultilinearOfDual`; (2) a naturality proof
(`multilinearHomEquivDualMultilinearTensor_naturality`) showing the model-level equiv
commutes with trivialization transitions, combining algebraic naturality of
`dualTensorHomEquiv` with `dualMultilinearEquivMultilinearOfDual_compCCLM`; (3) bundle
instances for the tensor product target; (4) total-space smoothness via trivialization
compatibility (`mixedToTensor_triv_eq_bundle`, `tensorToMixed_triv_eq_bundle`), assembled
by `ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv`.

## Tags

mixed tensor, dual, tensor product, vector bundle, fiberwise equivalence, section equivalence
-/

noncomputable section

open Bundle TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (W : Type*) [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- `(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W` for finite-dimensional normed spaces. -/
noncomputable def homEquivCDualTensor :
    (V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) := by
  let e1 : (V →L[𝕜] W) ≃ₗ[𝕜] (V →ₗ[𝕜] W) := LinearMap.toContinuousLinearMap.symm
  let e2 : (V →ₗ[𝕜] W) ≃ₗ[𝕜] (Module.Dual 𝕜 V ⊗[𝕜] W) :=
    (dualTensorHomEquiv 𝕜 V W).symm
  let cdualEquiv : (V →L[𝕜] 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 V :=
    LinearMap.toContinuousLinearMap.symm
  let e3 : (Module.Dual 𝕜 V ⊗[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) :=
    TensorProduct.congr cdualEquiv.symm (LinearEquiv.refl 𝕜 W)
  exact e1.trans (e2.trans e3)

/-- Model-level equivalence `(MLF r F →L[𝕜] MLF s F) ≃ₗ[𝕜] (MLF r (F →L[𝕜] 𝕜) ⊗[𝕜] MLF s F)`. -/
noncomputable def multilinearHomEquivDualMultilinearTensor
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  (homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)).trans
    (TensorProduct.congr
      (dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (LinearEquiv.refl 𝕜 _))

end ContinuousMultilinearMap

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Bundle-fiber-level equivalence between the mixed multilinear fiber at `x` and
`(MLF-of-dual r at x) ⊗ (MLF s at x)`, stated in the unfolded `ContinuousMultilinearMap`
form to avoid the topology diamond. -/
noncomputable def multilinearHomTensorEquivAt (r s : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  let e1 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
        ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    ContinuousMultilinearMap.homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
  let e2 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 ≃ₗ[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    TensorProduct.congr
      (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x)
      (LinearEquiv.refl 𝕜 _)
  exact e1.trans e2

/-- Untrivialize each factor of a model-fiber tensor product back to the bundle fiber at `x`. -/
noncomputable def dualTensorMultilinearUntrivializeAt (r s : ℕ) (x : B) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TensorProduct.congr
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
      (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Bundle-form analogue of `multilinearHomTensorEquivAt`: routes through the model fiber
via `mixedContinuousLinearEquivAt`, then `multilinearHomEquivDualMultilinearTensor`, then
`dualTensorMultilinearUntrivializeAt`. -/
noncomputable def multilinearHomTensorEquivAt_bundle (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) ≃ₗ[𝕜]
    ((Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  ((mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toLinearEquiv.trans
    (ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor 𝕜 F r s)).trans
    (dualTensorMultilinearUntrivializeAt (𝕜 := 𝕜) (F := F) (E := E) r s x)

end Bundle.continuousMultilinearMap

/-- `dualTensorHomEquiv.symm` intertwines hom-conjugation with `TensorProduct.map`. -/
theorem dualTensorHomEquiv_symm_naturality
    {𝕜 : Type*} [CommRing 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module.Free 𝕜 V] [Module.Finite 𝕜 V]
    {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    (φ : V ≃ₗ[𝕜] V) (ψ : W ≃ₗ[𝕜] W) (T : V →ₗ[𝕜] W) :
    (dualTensorHomEquiv 𝕜 V W).symm (ψ.toLinearMap.comp (T.comp φ.symm.toLinearMap)) =
      TensorProduct.map φ.symm.toLinearMap.dualMap ψ.toLinearMap
        ((dualTensorHomEquiv 𝕜 V W).symm T) := by
  apply (dualTensorHomEquiv 𝕜 V W).injective
  rw [LinearEquiv.apply_symm_apply]
  set t := (dualTensorHomEquiv 𝕜 V W).symm T
  rw [show T = dualTensorHomEquiv 𝕜 V W t from (LinearEquiv.apply_symm_apply _ T).symm]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | tmul f w =>
    ext v
    simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis, LinearEquiv.ofLinear_apply,
      dualTensorHom_apply, TensorProduct.map_tmul, LinearMap.dualMap_apply,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, map_smul]

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `homEquivCDualTensor.symm` on a pure tensor: `(η ⊗ w) ↦ (v ↦ η(v) • w)`. -/
theorem homEquivCDualTensor_symm_tmul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (η : V →L[𝕜] 𝕜) (w : W) (v : V) :
    (homEquivCDualTensor 𝕜 V W).symm (η ⊗ₜ[𝕜] w) v = η v • w := by
  simp only [homEquivCDualTensor, LinearEquiv.symm_trans_apply,
    TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  have h_inner : (dualTensorHomEquiv 𝕜 V W
        (LinearMap.toContinuousLinearMap.symm η ⊗ₜ[𝕜] w)) v = η v • w := by
    simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis, LinearEquiv.ofLinear_apply,
      dualTensorHom_apply]
    rfl
  exact h_inner

set_option maxHeartbeats 800000 in
-- Diamond on `AddCommMonoid` in the tensor fiber slows elaboration.
/-- `multilinearHomEquivDualMultilinearTensor` intertwines hom-conjugation by `Φ` with
`TensorProduct.map` of pre/post-composition on the tensor side. -/
theorem multilinearHomEquivDualMultilinearTensor_naturality
    (r s : ℕ) (Φ : F ≃L[𝕜] F)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    multilinearHomEquivDualMultilinearTensor 𝕜 F r s
        ((compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
          (f.comp (compContinuousLinearMapL
            (fun _ : Fin r => Φ.toContinuousLinearMap)))) =
      TensorProduct.map
        (compContinuousLinearMapL (fun _ : Fin r =>
          (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap
        (compContinuousLinearMapL
          (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).toLinearMap
        (multilinearHomEquivDualMultilinearTensor 𝕜 F r s f) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  set MHE := multilinearHomEquivDualMultilinearTensor 𝕜 F r s with hMHE_def
  set t := MHE f with ht_def
  have hf_eq : f = MHE.symm t := (LinearEquiv.symm_apply_apply _ _).symm
  suffices h : ∀ (u : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
                     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜),
      MHE ((compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
          ((MHE.symm u).comp (compContinuousLinearMapL
            (fun _ : Fin r => Φ.toContinuousLinearMap)))) =
        TensorProduct.map
          (compContinuousLinearMapL (fun _ : Fin r =>
            (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap
          (compContinuousLinearMapL
            (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).toLinearMap u by
    have := h t
    rw [ht_def] at this
    rw [LinearEquiv.symm_apply_apply] at this
    convert this using 2
  intro u
  induction u using TensorProduct.induction_on with
  | zero =>
    rw [LinearEquiv.map_zero MHE.symm, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, LinearEquiv.map_zero MHE,
      (TensorProduct.map _ _).map_zero]
  | add t₁ t₂ ih₁ ih₂ =>
    rw [LinearEquiv.map_add MHE.symm, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add, LinearEquiv.map_add MHE, ih₁, ih₂,
      (TensorProduct.map _ _).map_add]
  | tmul α β =>
    set η := (dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm α with hη_def
    have hMHE_symm_tmul : MHE.symm (α ⊗ₜ[𝕜] β) =
        (homEquivCDualTensor 𝕜
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)).symm (η ⊗ₜ[𝕜] β) := by
      change ((homEquivCDualTensor 𝕜 _ _).trans (TensorProduct.congr
          (dualMultilinearEquivMultilinearOfDual 𝕜 F r) (LinearEquiv.refl 𝕜 _))).symm
            (α ⊗ₜ[𝕜] β) = _
      simp only [LinearEquiv.symm_trans_apply, TensorProduct.congr_symm_tmul,
        LinearEquiv.refl_symm, LinearEquiv.refl_apply]
      rfl
    rw [hMHE_symm_tmul]
    have hconj :
        (compContinuousLinearMapL (fun _ : Fin s => Φ.symm.toContinuousLinearMap)).comp
            (((homEquivCDualTensor 𝕜 _ _).symm (η ⊗ₜ[𝕜] β)).comp
              (compContinuousLinearMapL (fun _ : Fin r => Φ.toContinuousLinearMap))) =
          (homEquivCDualTensor 𝕜 _ _).symm
            ((η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
              ((compContinuousLinearMapL
                (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β)) := by
      ext M'
      simp only [ContinuousLinearMap.comp_apply, homEquivCDualTensor_symm_tmul, map_smul]
    rw [hconj]
    have hMHE_apply_h_symm :
        MHE ((homEquivCDualTensor 𝕜 _ _).symm
            ((η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
              ((compContinuousLinearMapL
                (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β))) =
          dualMultilinearEquivMultilinearOfDual 𝕜 F r
              (η.comp (compContinuousLinearMapL
                (fun _ : Fin r => Φ.toContinuousLinearMap))) ⊗ₜ[𝕜]
            ((compContinuousLinearMapL
              (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) β) := by
      change ((homEquivCDualTensor 𝕜 _ _).trans (TensorProduct.congr
          (dualMultilinearEquivMultilinearOfDual 𝕜 F r) (LinearEquiv.refl 𝕜 _))) _ = _
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [hMHE_apply_h_symm,
      dualMultilinearEquivMultilinearOfDual_compCCLM_ext r Φ.toContinuousLinearMap η,
      hη_def, LinearEquiv.apply_symm_apply]
    rfl

end ContinuousMultilinearMap

section SectionTensorEquiv

open Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

set_option backward.isDefEq.respectTransparency false

local instance (r : ℕ) : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
  continuousMultilinearMap_finiteDimensional r
local instance (s : ℕ) : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  continuousMultilinearMap_finiteDimensional s
local instance (r : ℕ) : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  continuousMultilinearMap_finiteDimensional r

local instance (r : ℕ) : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance
local instance (r : ℕ) : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

local instance (r s : ℕ) : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  instNormedAddCommGroup_tensor 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
local instance (r s : ℕ) : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  instNormedSpace_tensor 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)

local instance instDTTop (r s : ℕ) (x : B) :
    TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                      Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  Bundle.TensorProduct.tensorFiberTopology (𝕜:=𝕜) (B:=B)
    (F₁:=ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (F₂:=ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x

local instance instDTAddCommGroup (r s : ℕ) (x : B) :
    AddCommGroup (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TensorProduct.addCommGroup

local instance instDTTotalTop (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x)) :=
  Bundle.TensorProduct.tensorTotalSpaceTop (𝕜:=𝕜) (B:=B)
    (F₁:=ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (F₂:=ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

local instance instDTFB (r s : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  Bundle.TensorProduct.fiberBundle (𝕜:=𝕜) (B:=B)
    (F₁:=ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (F₂:=ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

local instance instDTVB (r s : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  Bundle.TensorProduct.vectorBundle (𝕜:=𝕜) (B:=B)
    (F₁:=ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (F₂:=ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

local instance instDTCMDVB (r s : ℕ) :
    ContMDiffVectorBundle n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x) IB :=
  (Bundle.TensorProduct.vectorPrebundle (𝕜:=𝕜) (B:=B)
    (F₁:=ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (F₂:=ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)).contMDiffVectorBundle IB

abbrev DualTensorMultilinearSection (r s : ℕ) :=
  ContMDiffSection IB
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) n
    (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x)

/-- Model-level forward CLM: `Hom(MLF r, MLF s) → (MLF-of-dual r) ⊗ (MLF s)`. -/
noncomputable def Bundle.continuousMultilinearMap.modelMixedToTensorCLM
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (F := F →L[𝕜] 𝕜) r
  let e1 := ContinuousMultilinearMap.homEquivCDualTensor 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
  let e2 := TensorProduct.congr
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
    (LinearEquiv.refl 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
  (e1.trans e2).toContinuousLinearMap

/-- Model-level inverse CLM: `(MLF-of-dual r) ⊗ (MLF s) → Hom(MLF r, MLF s)`. -/
noncomputable def Bundle.continuousMultilinearMap.modelTensorToMixedCLM
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  letI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (F := F →L[𝕜] 𝕜) r
  let e1 := ContinuousMultilinearMap.homEquivCDualTensor 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
  let e2 := TensorProduct.congr
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
    (LinearEquiv.refl 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
  (e1.trans e2).symm.toContinuousLinearMap

set_option maxHeartbeats 800000 in
-- Nested trivialization unfolding for hom and tensor product bundles.
/-- Trivialization compatibility for the forward direction: the tensor-product bundle
trivialization of the fiberwise equiv equals the model-level CLM on the trivialized input. -/
theorem mixedToTensor_triv_eq_bundle {r s : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
              (𝕜 := 𝕜) (F := F) (E := E) r s x) T⟩).2 =
    Bundle.continuousMultilinearMap.modelMixedToTensorCLM 𝕜 F r s
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, T⟩).2) := by
  set Φ : F ≃L[𝕜] F :=
    ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F E x)).symm.trans
      ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx) with hΦ_def
  have hLHS : (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
              (𝕜 := 𝕜) (F := F) (E := E) r s x) T⟩).2 =
      TensorProduct.map
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜) (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
          (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin s => F) (E₁ := fun _ : Fin s => F) (F := 𝕜)
          (fun _ => Φ.symm.toContinuousLinearMap)).toLinearMap
        ((ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor 𝕜 F r s)
          ((Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt
              (𝕜 := 𝕜) (F := F) (E := E) r s x) T)) := by
    set u := (ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor 𝕜 F r s)
      ((Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt
        (𝕜 := 𝕜) (F := F) (E := E) r s x) T) with hu_def
    have hf_eq : (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
        (𝕜 := 𝕜) (F := F) (E := E) r s x) T =
        (Bundle.continuousMultilinearMap.dualTensorMultilinearUntrivializeAt
          (𝕜 := 𝕜) (F := F) (E := E) r s x) u := by
      unfold Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
      simp only [LinearEquiv.trans_apply, hu_def,
        ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [hf_eq]
    rw [show (Bundle.continuousMultilinearMap.dualTensorMultilinearUntrivializeAt
          (𝕜 := 𝕜) (F := F) (E := E) r s x) u =
        TensorProduct.map
          (Bundle.continuousMultilinearMap.continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
            (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv.toLinearMap
          (Bundle.continuousMultilinearMap.continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv.toLinearMap
          u from rfl]
    rw [show (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀) =
        ((trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀).tensorProduct
          (𝕜 := 𝕜)
          (trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀)) from
      Bundle.TensorProduct.tensorProduct_trivializationAt x₀]
    rw [Trivialization.tensorProduct_apply]
    simp only [TensorProduct.map_map]
    have h_r : (((trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
            x₀).continuousLinearMapAt 𝕜 x).toLinearMap ∘ₗ
          (Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv.toLinearMap) =
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜) (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
          (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)).toLinearMap := by
      apply LinearMap.ext; intro M
      simp only [LinearMap.coe_comp, Function.comp_apply]
      have hx_dmr : x ∈ (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀).baseSet := by
        have : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).baseSet := by
          change x ∈ (trivializationAt F E x₀).baseSet ∩ Set.univ
          exact ⟨hx, trivial⟩
        exact this
      apply ContinuousMultilinearMap.ext; intro w
      set T : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 :=
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜) (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
          (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip Φ.toContinuousLinearMap)) M with hT_def
      have key : (Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm M =
          (trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
            x₀).symmL 𝕜 x T := by
        apply ContinuousMultilinearMap.ext; intro v
        have hx_dual : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).baseSet := by
          change x ∈ (trivializationAt F E x₀).baseSet ∩ Set.univ
          exact ⟨hx, trivial⟩
        rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
          (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) x₀ x hx_dual]
        simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
        change M (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt 𝕜 x (v i)) =
          T (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).continuousLinearMapAt 𝕜 x (v i))
        rw [hT_def]
        rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
            ContinuousMultilinearMap.compContinuousLinearMap_apply]
        congr 1
        funext i
        apply ContinuousLinearMap.ext
        intro a
        simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
        have hxx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
        have hxx_dual : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).baseSet :=
          mem_baseSet_trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x
        have hLHS : (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt 𝕜 x
            (v i) a = (v i) (((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a) := by
          have := Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp
            (𝕜 := 𝕜) (F := F) (E := E) x x hxx
            ((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).continuousLinearMapAt 𝕜 x (v i))
            (((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a)
          rw [Trivialization.symmL_continuousLinearMapAt _ hxx_dual] at this
          have h_symm_eq : ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a
              = (trivializationAt F E x).symmL 𝕜 x a := rfl
          rw [h_symm_eq, Trivialization.continuousLinearMapAt_symmL _ hxx] at this
          exact this.symm
        have hx_dual_x₀ : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).baseSet :=
          hx_dual
        have hRHS : (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).continuousLinearMapAt 𝕜 x
            (v i) (Φ a) = (v i)
              (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm (Φ a)) := by
          have := Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp
            (𝕜 := 𝕜) (F := F) (E := E) x₀ x hx
            ((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).continuousLinearMapAt 𝕜 x (v i))
            (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm (Φ a))
          rw [Trivialization.symmL_continuousLinearMapAt _ hx_dual_x₀] at this
          have h_symm_eq : ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm (Φ a)
              = (trivializationAt F E x₀).symmL 𝕜 x (Φ a) := rfl
          rw [h_symm_eq, Trivialization.continuousLinearMapAt_symmL _ hx] at this
          exact this.symm
        rw [hLHS]
        change _ = (((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).continuousLinearMapAt 𝕜 x
            (v i)) (Φ a))
        rw [hRHS]
        congr 1
        rw [hΦ_def]
        simp only [ContinuousLinearEquiv.trans_apply,
          ContinuousLinearEquiv.symm_apply_apply]
      change ((trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀).continuousLinearMapAt 𝕜 x
          ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm M)) w = _
      rw [key]
      exact DFunLike.congr_fun
        ((trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀).continuousLinearMapAt_symmL hx_dmr T) w
    have h_s : (((trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)
            x₀).continuousLinearMapAt 𝕜 x).toLinearMap ∘ₗ
          (Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv.toLinearMap) =
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin s => F) (E₁ := fun _ : Fin s => F) (F := 𝕜)
          (fun _ => Φ.symm.toContinuousLinearMap)).toLinearMap := by
      apply LinearMap.ext; intro M
      simp only [LinearMap.coe_comp, Function.comp_apply]
      have hx_ms : x ∈ (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).baseSet := hx
      apply ContinuousMultilinearMap.ext; intro w
      set T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin s => F) (E₁ := fun _ : Fin s => F) (F := 𝕜)
          (fun _ => Φ.symm.toContinuousLinearMap)) M with hT_def
      have key : (Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) s x).symm M =
          (trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).symmL 𝕜 x T := by
        apply ContinuousMultilinearMap.ext; intro v
        rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx]
        simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
        change M (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (v i)) =
          T (fun i => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x (v i))
        rw [hT_def]
        change M (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (v i)) =
          ((ContinuousMultilinearMap.compContinuousLinearMapL
            (fun _ : Fin s => Φ.symm.toContinuousLinearMap)) M)
            (fun i => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x (v i))
        rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
            ContinuousMultilinearMap.compContinuousLinearMap_apply]
        congr 1
        funext i
        rw [hΦ_def]
        simp only [ContinuousLinearEquiv.symm_trans_apply,
          ContinuousLinearEquiv.symm_symm,
          ContinuousLinearEquiv.coe_coe,
          Trivialization.coe_continuousLinearEquivAt_eq _ (mem_baseSet_trivializationAt F E x)]
        congr 1
        rw [← Trivialization.coe_continuousLinearEquivAt_eq _ hx]
        exact (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm_apply_apply (v i)).symm
      change ((trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).continuousLinearMapAt 𝕜 x
          ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F) (E := E) s x).symm M)) w = _
      rw [key]
      exact DFunLike.congr_fun
        ((trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).continuousLinearMapAt_symmL hx_ms T) w
    rw [h_r, h_s]
  have hx_ms : x ∈ (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).baseSet := hx
  have hRHS : (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, T⟩).2 =
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (𝕜 := 𝕜) (E := fun _ : Fin s => F) (E₁ := fun _ : Fin s => F) (F := 𝕜)
        (fun _ => Φ.symm.toContinuousLinearMap)).comp
        (((Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt
            (𝕜 := 𝕜) (F := F) (E := E) r s x) T).comp
          (ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := 𝕜) (E := fun _ : Fin r => F) (E₁ := fun _ : Fin r => F) (F := 𝕜)
            (fun _ => Φ.toContinuousLinearMap))) := by
    change ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).continuousLinearMapAt 𝕜 x).comp
          (T.comp ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x) x₀).symmL 𝕜 x)) = _
    apply ContinuousLinearMap.ext; intro M
    apply ContinuousMultilinearMap.ext; intro v
    have hmlr_symmL : ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x) x₀).symmL 𝕜 x M :
          Bundle.continuousMultilinearMap 𝕜 r F E x) =
        M.compContinuousLinearMap
          (fun _ : Fin r => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x) :=
      Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
        (𝕜 := 𝕜) (F := F) (E := E) x₀ x hx M
    have hmls_cLMA : ∀ (N : Bundle.continuousMultilinearMap 𝕜 s F E x),
        ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).continuousLinearMapAt 𝕜 x N :
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) =
        N.compContinuousLinearMap
          (fun _ : Fin s => (trivializationAt F E x₀).symmL 𝕜 x) := by
      intro N
      change (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).linearMapAt 𝕜 x N = _
      rw [Trivialization.coe_linearMapAt_of_mem _ hx_ms]
      rfl
    simp only [ContinuousLinearMap.comp_apply]
    rw [hmlr_symmL, hmls_cLMA]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe]
    change _ =
      (Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) s x
        (T ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F) (E := E) r x).symm
          (M.compContinuousLinearMap (fun _ : Fin r => Φ.toContinuousLinearMap)))))
        (fun i => Φ.symm.toContinuousLinearMap (v i))
    change _ =
      (T ((M.compContinuousLinearMap (fun _ : Fin r => Φ.toContinuousLinearMap)
          ).compContinuousLinearMap
          (fun _ : Fin r => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
        )).compContinuousLinearMap
          (fun _ : Fin s => (trivializationAt F E x).symmL 𝕜 x) (fun i => Φ.symm (v i))
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have h_arg : M.compContinuousLinearMap
          (fun _ : Fin r => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x) =
        (M.compContinuousLinearMap (fun _ : Fin r => Φ.toContinuousLinearMap)).compContinuousLinearMap
          (fun _ : Fin r => (trivializationAt F E x).continuousLinearMapAt 𝕜 x) := by
      apply ContinuousMultilinearMap.ext; intro w
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      rw [hΦ_def]
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
        Trivialization.coe_continuousLinearEquivAt_eq _ hx]
      congr 1
      have h_sym_eq : ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
          (mem_baseSet_trivializationAt F E x)).symm
          ((trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) =
        (trivializationAt F E x).symmL 𝕜 x
          ((trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) := rfl
      rw [h_sym_eq, Trivialization.symmL_continuousLinearMapAt _
        (mem_baseSet_trivializationAt F E x)]
    have h_vec : (fun i : Fin s => (trivializationAt F E x₀).symmL 𝕜 x (v i)) =
        (fun i : Fin s => (trivializationAt F E x).symmL 𝕜 x (Φ.symm (v i))) := by
      funext i
      rw [hΦ_def]
      simp only [ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
        Trivialization.coe_continuousLinearEquivAt_eq _ (mem_baseSet_trivializationAt F E x)]
      rw [Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_trivializationAt F E x)]
      rfl
    rw [h_arg, h_vec]
  rw [hLHS, hRHS]
  exact (ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor_naturality
    r s Φ ((Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt
      (𝕜 := 𝕜) (F := F) (E := E) r s x) T)).symm

/-- Trivialization compatibility for the inverse direction. -/
theorem tensorToMixed_triv_eq_bundle {r s : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
              (𝕜 := 𝕜) (F := F) (E := E) r s x).symm T⟩).2 =
    Bundle.continuousMultilinearMap.modelTensorToMixedCLM 𝕜 F r s
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) x₀
        ⟨x, T⟩).2) := by
  have hfwd := mixedToTensor_triv_eq_bundle x₀ x hx
    ((Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
      (𝕜 := 𝕜) (F := F) (E := E) r s x).symm T)
  rw [LinearEquiv.apply_symm_apply] at hfwd
  rw [hfwd]
  exact (LinearEquiv.symm_apply_apply _ _).symm

set_option maxHeartbeats 400000 in
-- `ContMDiffWithinAtProp` on a hom/tensor total space exceeds default.
/-- The total-space map induced by `multilinearHomTensorEquivAt_bundle` is `C^n`. -/
theorem multilinearHomTensorEquivAt_bundle_smooth {r s : ℕ} :
    ContMDiff
      (IB.prod 𝓘(𝕜,
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
      (IB.prod 𝓘(𝕜,
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
      n
      (fun p : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 s F E x) =>
        (⟨p.1, (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
                  (𝕜 := 𝕜) (F := F) (E := E) r s p.1) p.2⟩ :
          TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
             ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                      Bundle.continuousMultilinearMap 𝕜 s F E x))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜,
          ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
        𝓘(𝕜,
          ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) n
        (fun p => (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 s F E x) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelMixedToTensorCLM 𝕜 F r s)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact mixedToTensor_triv_eq_bundle p₀.proj p.proj hp p.snd

set_option maxHeartbeats 400000 in
-- Same as `multilinearHomTensorEquivAt_bundle_smooth`.
/-- The total-space map induced by the inverse of `multilinearHomTensorEquivAt_bundle` is `C^n`. -/
theorem multilinearHomTensorEquivAt_bundle_symm_smooth {r s : ℕ} :
    ContMDiff
      (IB.prod 𝓘(𝕜,
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
      (IB.prod 𝓘(𝕜,
        ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
      n
      (fun p : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 s F E x) =>
        (⟨p.1, (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
                  (𝕜 := 𝕜) (F := F) (E := E) r s p.1).symm p.2⟩ :
          TotalSpace
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
             ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                      Bundle.continuousMultilinearMap 𝕜 s F E x))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜,
          ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜))
        𝓘(𝕜,
          ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) n
        (fun p => (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 s F E x) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelTensorToMixedCLM 𝕜 F r s)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact tensorToMixed_triv_eq_bundle p₀.proj p.proj hp p.snd

/-- The mixed `(r,s)`-multilinear bundle is `C^n`-equivalent to
`(r-multilinear-of-dual bundle) ⊗ (s-multilinear bundle)`. -/
noncomputable def mixedBundle_tensorBundle_equiv {r s : ℕ} :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
                (𝕜 := 𝕜) (F := F) (E := E) r s x)
    (multilinearHomTensorEquivAt_bundle_smooth n)
    (multilinearHomTensorEquivAt_bundle_symm_smooth n)

/-- Transport a mixed section to a section of the tensor product bundle. -/
noncomputable def mixedSectionToTensorBundleSection {r s : ℕ}
    (T : MixedSection 𝕜 F IB E n r s) :
    DualTensorMultilinearSection (𝕜 := 𝕜) (F := F) (IB := IB) (E := E) (n := n) r s :=
  ⟨fun x => (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
              (𝕜 := 𝕜) (F := F) (E := E) r s x) (T x),
   ((multilinearHomTensorEquivAt_bundle_smooth n).comp T.contMDiff).congr fun _ => rfl⟩

/-- Transport a section of the tensor product bundle to a mixed section. -/
noncomputable def tensorBundleSectionToMixedSection {r s : ℕ}
    (W : DualTensorMultilinearSection (𝕜 := 𝕜) (F := F) (IB := IB) (E := E) (n := n) r s) :
    MixedSection 𝕜 F IB E n r s :=
  ⟨fun x => (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
              (𝕜 := 𝕜) (F := F) (E := E) r s x).symm (W x),
   ((multilinearHomTensorEquivAt_bundle_symm_smooth n).comp W.contMDiff).congr fun _ => rfl⟩

@[simp]
theorem tensorBundleSectionToMixedSection_mixedSectionToTensorBundleSection {r s : ℕ}
    (T : MixedSection 𝕜 F IB E n r s) :
    tensorBundleSectionToMixedSection n (mixedSectionToTensorBundleSection n T) = T := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.symm_apply_apply _ _

@[simp]
theorem mixedSectionToTensorBundleSection_tensorBundleSectionToMixedSection {r s : ℕ}
    (W : DualTensorMultilinearSection (𝕜 := 𝕜) (F := F) (IB := IB) (E := E) (n := n) r s) :
    mixedSectionToTensorBundleSection n (tensorBundleSectionToMixedSection n W) = W := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.apply_symm_apply _ _

theorem mixedSectionToTensorBundleSection_add {r s : ℕ}
    (T₁ T₂ : MixedSection 𝕜 F IB E n r s) :
    mixedSectionToTensorBundleSection n (T₁ + T₂) =
    mixedSectionToTensorBundleSection n T₁ + mixedSectionToTensorBundleSection n T₂ := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
    (𝕜 := 𝕜) (F := F) (E := E) r s x).map_add (T₁ x) (T₂ x)

theorem mixedSectionToTensorBundleSection_smul {r s : ℕ}
    (φ : C^n⟮IB, B; 𝕜⟯) (T : MixedSection 𝕜 F IB E n r s) :
    mixedSectionToTensorBundleSection n (φ • T) =
    φ • mixedSectionToTensorBundleSection n T := by
  apply ContMDiffSection.ext; intro x
  exact (Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
    (𝕜 := 𝕜) (F := F) (E := E) r s x).map_smul (φ x) (T x)

/-- The `C^n`-linear equivalence between mixed sections and tensor product bundle sections. -/
noncomputable def mixedBundle_tensorBundle_sectionEquiv {r s : ℕ} :
    MixedSection 𝕜 F IB E n r s ≃ₗ[C^n⟮IB, B; 𝕜⟯]
    DualTensorMultilinearSection (𝕜 := 𝕜) (F := F) (IB := IB) (E := E) (n := n) r s where
  toFun := mixedSectionToTensorBundleSection n
  invFun := tensorBundleSectionToMixedSection n
  left_inv := tensorBundleSectionToMixedSection_mixedSectionToTensorBundleSection n
  right_inv := mixedSectionToTensorBundleSection_tensorBundleSectionToMixedSection n
  map_add' := mixedSectionToTensorBundleSection_add n
  map_smul' := mixedSectionToTensorBundleSection_smul n

end SectionTensorEquiv

end
