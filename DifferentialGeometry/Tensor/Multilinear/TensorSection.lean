/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Multilinear.TensorFiber
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.VectorBundle.Section
/-!
# Tensor product of smooth multilinear sections

This file defines tensor products at the section level for smooth multilinear sections,
and establishes a `C^n` vector bundle equivalence between the `(s+q)`-multilinear bundle
and the tensor product of the `s`- and `q`-multilinear bundles.

The key building blocks (defined fiberwise in `TensorFiber.lean`) are `fromTensor` (the
universal-property lift of `product_fun` to the abstract tensor product of multilinear
fibers) and its constructive inverse `modelFromTensorEquiv.symm`. Trivialization
compatibility lemmas (`triv_fromTensor_eq_modelFromTensor` and
`triv_toTensor_eq_modelFromTensorEquiv_symm`) are proved here because they require
`Product.Bundle` for the tensor product bundle trivialization, which would create a
cycle if placed in `TensorFiber.lean`.

## Main Definitions

* `MultilinearSection.product` : tensor product of two smooth multilinear sections.
* `MultilinearSection.fromTensorProduct` : promote a smooth section of the tensor product
  bundle to a smooth `(s+q)`-multilinear section via `fromTensor` fiberwise.
* `MultilinearSection.toTensorProduct` : decompose a smooth `(s+q)`-multilinear section into
  a smooth section of the tensor product bundle via `(modelFromTensorEquiv b s q).symm`
  fiberwise.
* `MultilinearSection.multilinearBundle_tensorProduct_equiv` : the `C^n` vector bundle
  equivalence between the `(s+q)`-multilinear bundle and the tensor product of the `s`-
  and `q`-multilinear bundles, via the section characterization lemma.

## Main Results

* `Bundle.continuousMultilinearMap.triv_fromTensor_eq_modelFromTensor` :
  trivializing `fromTensor(t)` equals `modelFromTensor` applied to the trivialized
  tensor product section.
* `Bundle.continuousMultilinearMap.triv_toTensor_eq_modelFromTensorEquiv_symm` :
  the reverse trivialization compatibility.
* `MultilinearSection.fromTensor_toTensorProduct` :
  `fromTensor ∘ toTensorProduct = id`.
* `MultilinearSection.toTensorProduct_fromTensorProduct` :
  `toTensorProduct ∘ fromTensorProduct = id`.
* `MultilinearSection.toTensorProduct_add`, `MultilinearSection.fromTensorProduct_add` :
  additivity.
* `MultilinearSection.toTensorProduct_smulByFun`, `MultilinearSection.fromTensorProduct_smul` :
  smooth-function linearity.

## Tags

multilinear section, tensor product, smooth section, vector bundle equivalence
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Abbreviation for the model fiber of the `s`-multilinear bundle. -/
local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

namespace Bundle.continuousMultilinearMap

/-!
## Trivialization compatibility for `fromTensor`
-/

/-- Trivializing `fromTensor s q x (t)` in the `(s+q)`-multilinear bundle at `x₀` equals
`modelFromTensor` applied to the trivialization of `t` in the tensor product bundle at `x₀`,
provided `x` lies in the base set of the base bundle trivialization at `x₀`.

Both sides are linear in `t`. On pure tensors `α ⊗ₜ β`, the LHS trivializes
`product_fun α β` by precomposing with `symmL`, while the RHS trivializes each factor
and applies `modelProduct`. Both yield `v ↦ α(symmL(v ∘ castAdd)) * β(symmL(v ∘ natAdd))`. -/
theorem triv_fromTensor_eq_modelFromTensor (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (trivializationAt (MLF (s + q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
      ⟨x, fromTensor s q x t⟩).2 =
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      ((trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                   Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
        ⟨x, t⟩).2) := by
  letI := Bundle.TensorProduct.tensorFiberTopology
    𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)
  letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  have hxs : x ∈ (trivializationAt (MLF s)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).baseSet := hx
  have hxq : x ∈ (trivializationAt (MLF q)
      (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀).baseSet := hx
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change (trivializationAt _ _ x₀
      ⟨x, (0 : Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)⟩).2 = 0
    ext w; rfl
  | add t₁ t₂ ih₁ ih₂ =>
    have hlin : ∀ (a b : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x),
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x (a + b)⟩).2 =
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x a⟩).2 +
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x b⟩).2 := by
      intro a b; ext w; simp [map_add]; rfl
    rw [hlin, ih₁, ih₂]
    simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
      Trivialization.tensorProduct_apply, map_add]
  | tmul α β =>
    ext w
    change (product_fun α β) (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) = _
    rw [product_fun_apply]
    simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
      Trivialization.tensorProduct_apply, TensorProduct.map_tmul, modelFromTensor,
      TensorProduct.lift.tmul, LinearMap.mk₂_apply, modelProduct_apply]
    have hs : ⇑((trivializationAt (MLF s)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).continuousLinearMapAt 𝕜 x) =
        fun y => (trivializationAt (MLF s)
          (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, y⟩).2 := by
      change ⇑((trivializationAt (MLF s) _ x₀).linearMapAt 𝕜 x) = _
      exact (trivializationAt (MLF s) _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hxs
    have hq' : ⇑((trivializationAt (MLF q)
        (Bundle.continuousMultilinearMap 𝕜 q F E) x₀).continuousLinearMapAt 𝕜 x) =
        fun y => (trivializationAt (MLF q)
          (Bundle.continuousMultilinearMap 𝕜 q F E) x₀ ⟨x, y⟩).2 := by
      change ⇑((trivializationAt (MLF q) _ x₀).linearMapAt 𝕜 x) = _
      exact (trivializationAt (MLF q) _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hxq
    change _ = (⇑((trivializationAt (MLF s) (Bundle.continuousMultilinearMap 𝕜 s F E) x₀
        ).continuousLinearMapAt 𝕜 x) α) (w ∘ Fin.castAdd q) *
      (⇑((trivializationAt (MLF q) (Bundle.continuousMultilinearMap 𝕜 q F E) x₀
        ).continuousLinearMapAt 𝕜 x) β) (w ∘ Fin.natAdd s)
    rw [hs, hq']; rfl

/-- The reverse trivialization compatibility: trivializing `fromTensor.symm(α)` in the
tensor product bundle equals `modelFromTensorEquiv.symm` of the trivialized `(s+q)`-section.

Proved by writing `α = fromTensor(equiv.symm α)`, applying `triv_fromTensor_eq_modelFromTensor`,
and using that `modelFromTensorEquiv` extends `modelFromTensor`. -/
theorem triv_toTensor_eq_modelFromTensorEquiv_symm {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm
      ((trivializationAt (MLF (s + q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, fromTensor s q x t⟩).2) =
    (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
      ⟨x, t⟩).2 := by
  letI := Bundle.TensorProduct.tensorFiberTopology
    𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)
  letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  rw [triv_fromTensor_eq_modelFromTensor s q x₀ x hx t]
  exact (modelFromTensorEquiv b s q).symm_apply_apply _

end Bundle.continuousMultilinearMap

namespace MultilinearSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

/-!
## Tensor product of multilinear sections

The tensor product of a `C^n` `s`-multilinear section `α` and a `C^n` `q`-multilinear section
`β` is a `C^n` `(s+q)`-multilinear section, defined pointwise by
`Bundle.continuousMultilinearMap.product_fun`.
-/

section Product

variable {s q : ℕ}

/-- The tensor product of a `C^n` `s`-multilinear section `α` and a `C^n` `q`-multilinear
section `β` is a `C^n` `(s+q)`-multilinear section, defined pointwise by `product_fun`.

Smoothness is proved by reducing to basis coordinates via
`contMDiff_multilinearSection_iff_coord`: the trivialized coordinate of `α ⊗ β` at
`σ : Fin (s+q) → Fin d` equals the product of the coordinate of `α` at `σ ∘ Fin.castAdd q`
and the coordinate of `β` at `σ ∘ Fin.natAdd s`, both of which are smooth. -/
noncomputable def product
    (α : MultilinearSection 𝕜 F IB E n s)
    (β : MultilinearSection 𝕜 F IB E n q) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (α x).product_fun (β x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro σ x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (β x : Bundle.continuousMultilinearMap 𝕜 q F E x))).mp β.contMDiff)
    -- The trivialized coordinate of the product decomposes as a product of coordinates
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

end Product

/-!
## From tensor product sections to multilinear sections

A `C^n` section of the tensor product bundle
`(MultilinearBundle s) ⊗ (MultilinearBundle q)` determines a `C^n` section of
`MultilinearBundle (s + q)`, by applying the fiberwise linear map `fromTensor`
(the lift of `product_fun` via the universal property of `⊗`).

Smoothness is proved by reducing to local trivializations. The trivialized
`(s+q)`-section equals `modelFromTensor` composed with the trivialized tensor
product section, where `modelFromTensor` is the model-fiber lift of the product
(a fixed linear map, hence continuous by finite-dimensionality).
-/

section FromTensorProduct

open Bundle.continuousMultilinearMap

variable {s q : ℕ}

/-- Construct a `C^n` `(s+q)`-multilinear section from a `C^n` section of the tensor product
bundle of the `s`- and `q`-multilinear bundles, by applying `fromTensor` fiberwise.

Smoothness is proved via local trivializations: the trivialized `(s+q)`-section equals
`modelFromTensor` (a fixed CLM) composed with the trivialized tensor product section. -/
noncomputable def fromTensorProduct
    (γ : letI := Bundle.TensorProduct.tensorFiberTopology
            𝕜 (MLF s) (MLF q)
            (Bundle.continuousMultilinearMap 𝕜 s F E)
            (Bundle.continuousMultilinearMap 𝕜 q F E)
         letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
            (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
            (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
            (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
         letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
            (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
            (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
            (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
         ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => fromTensor s q x (γ x), by
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    letI : ChartedSpace (ModelProd HB ((MLF s) ⊗[𝕜] (MLF q)))
        (TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
      FiberBundle.chartedSpace
    intro x₀
    rw [contMDiffAt_section x₀]
    have hγ_triv := (contMDiffAt_section x₀).mp (γ.contMDiff x₀)
    refine ((modelFromTensor (𝕜 := 𝕜) (F := F) s q).toContinuousLinearMap.contMDiffAt.comp
      x₀ hγ_triv).congr_of_eventuallyEq ?_
    exact (Filter.Eventually.mono
      ((trivializationAt F E x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x₀))
      fun x hx => triv_fromTensor_eq_modelFromTensor s q x₀ x hx (γ x))⟩

end FromTensorProduct

/-!
## From multilinear sections to tensor product sections

A `C^n` section of `MultilinearBundle (s + q)` determines a `C^n` section of the
tensor product bundle `(MultilinearBundle s) ⊗ (MultilinearBundle q)`.

The fiberwise map is `(modelFromTensorEquiv b s q).symm`, which is a constructive
inverse of `fromTensor` (via `modelFromTensor` and `ofBijective`). Since
`fromTensor (modelFromTensorEquiv.symm α) = α`, the section
`fun x => (modelFromTensorEquiv b).symm (α x)` lives in the tensor product fiber
and maps back to `α x` under `fromTensor`.

Smoothness follows from `triv_toTensor_eq_modelFromTensorEquiv_symm`.
-/

section ToTensorProduct

open Bundle.continuousMultilinearMap

variable {s q : ℕ}

/-- Decompose a `C^n` `(s+q)`-multilinear section into a `C^n` section of the tensor product
bundle of the `s`- and `q`-multilinear bundles, by applying `(modelFromTensorEquiv b s q).symm`
fiberwise (a constructive inverse of `fromTensor`).

Smoothness is proved via local trivializations: the trivialized tensor product section
equals `(modelFromTensorEquiv b s q).symm` (a CLE) composed with the trivialized
`(s+q)`-section, by `triv_toTensor_eq_modelFromTensorEquiv_symm`. -/
noncomputable def toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  let d := Module.finrank 𝕜 F
  let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
  letI := Bundle.TensorProduct.tensorFiberTopology
    𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)
  letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  letI : ContMDiffVectorBundle n ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) IB :=
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)).contMDiffVectorBundle IB
  letI : ChartedSpace (ModelProd HB ((MLF s) ⊗[𝕜] (MLF q)))
      (TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                   Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    FiberBundle.chartedSpace
  -- The fiberwise map: trivialize to MLF(s+q) at x, apply modelFromTensorEquiv.symm,
  -- then un-trivialize back to cmm(s) ⊗ cmm(q) using the tensor product CLE at x.
  -- This is well-defined globally (uses trivialization at x, not a fixed x₀).
  ⟨fun x =>
    TensorProduct.map
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
        (MLF s) →ₗ[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x)
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
        (MLF q) →ₗ[𝕜] Bundle.continuousMultilinearMap 𝕜 q F E x)
      ((modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x))),
   by
    intro x₀
    rw [contMDiffAt_section x₀]
    have hα_triv := (contMDiffAt_section x₀).mp (α.contMDiff x₀)
    -- The trivialized tensor section at x₀ is:
    -- triv_⊗(x₀)(section(x)) = TensorProduct.map(cle_s(x₀), cle_q(x₀))(section(x))
    -- = TensorProduct.map(cle_s(x₀), cle_q(x₀))
    --     (TensorProduct.map(cle_s(x).symm, cle_q(x).symm)
    --       (modelFromTensorEquiv.symm(cle_{s+q}(x)(α x))))
    -- Near x₀ (on the base set), cle(x₀) ∘ cle(x).symm = id on each factor.
    -- So the trivialized section ≈ modelFromTensorEquiv.symm(cle_{s+q}(x₀)(α x₀))
    -- = modelFromTensorEquiv.symm ∘ trivialized (s+q)-section.
    -- This is a CLE composed with a smooth section, hence smooth.
    set e := (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm.toContinuousLinearEquiv
    -- For the trivialization compatibility, we use fromTensor as a bridge:
    -- fromTensor(section(x)) = α x, and triv_fromTensor_eq_modelFromTensor gives
    -- the forward identity. Then triv_toTensor_eq_modelFromTensorEquiv_symm gives
    -- the reverse.
    refine (e.toContinuousLinearMap.contMDiffAt.comp x₀ hα_triv).congr_of_eventuallyEq ?_
    exact (Filter.Eventually.mono
      ((trivializationAt F E x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x₀)) fun x hx => by
      -- fromTensor(section(x)) = α x
      have hfrom := fromTensor_map_ofModel
        (𝕜 := 𝕜) (F := F) (E := E) (s := s) (q := q) (x := x)
        ((modelFromTensorEquiv b s q).symm
          (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x)))
      -- modelFromTensor(e.symm(m)) = m
      have happly := (modelFromTensorEquiv b s q).apply_symm_apply
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x))
      -- Let u be the model-fiber element
      set u := (modelFromTensorEquiv b s q).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x))
      -- fromTensor(map(cle.symm)(u)) = ofModel(modelFromTensor(u))
      -- = ofModel(cle(α x)) = α x
      have hid : fromTensor s q x (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
            (MLF s) →ₗ[𝕜] _)
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
            (MLF q) →ₗ[𝕜] _) u) = α x :=
        hfrom.trans (congrArg (ofModel (F := F) (E := E)) happly |>.trans (ofModel_toModel _))
      -- Combine: triv_toTensor + rewrite fromTensor(...) = α x via simp
      have h1 := triv_toTensor_eq_modelFromTensorEquiv_symm b s q x₀ x hx
        (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
            (MLF s) →ₗ[𝕜] _)
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
            (MLF q) →ₗ[𝕜] _) u)
      simp only [hid] at h1
      exact h1.symm)⟩

end ToTensorProduct

/-!
## Round-trip identities
-/

section RoundTrip

open Bundle.continuousMultilinearMap

variable {s q : ℕ}

/-- `fromTensor ∘ toTensorProduct = id` pointwise:
decomposing into a tensor product and then reassembling via `fromTensor` gives back
the original section value. -/
theorem fromTensor_toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    fromTensor s q x ((toTensorProduct n α).1 x) = α x := by
  change fromTensor s q x (TensorProduct.map
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
      (MLF s) →ₗ[𝕜] _)
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
      (MLF q) →ₗ[𝕜] _)
    ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x)))) = α x
  rw [fromTensor_map_ofModel]
  -- Goal: ofModel(modelFromTensor(e.symm(cle(α x)))) = α x
  -- modelFromTensor = modelFromTensorEquiv, so modelFromTensor(e.symm(m)) = e(e.symm(m)) = m
  change ofModel (F := F) (E := E)
    ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q)
      ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x)))) = α x
  rw [LinearEquiv.apply_symm_apply]
  exact ofModel_toModel _

/-- `toTensorProduct ∘ fromTensorProduct = id` pointwise:
reassembling from a tensor product section via `fromTensor` and then decomposing gives
back the original tensor product fiber element. -/
theorem toTensorProduct_fromTensorProduct
    (γ : letI := Bundle.TensorProduct.tensorFiberTopology
            𝕜 (MLF s) (MLF q)
            (Bundle.continuousMultilinearMap 𝕜 s F E)
            (Bundle.continuousMultilinearMap 𝕜 q F E)
         letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
            (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
            (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
            (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
         letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
            (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
            (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
            (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
         ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x))
    (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (toTensorProduct n (fromTensorProduct n γ)).1 x = γ x := by
  set b := Module.finBasis 𝕜 F
  -- Goal: map(cle.symm)(modelFromTensorEquiv.symm(cle(fromTensor(γ x)))) = γ x
  -- Chain: fromTensor(γ x) = ofModel(modelFromTensor(map(cle)(γ x)))  [key]
  --   cle(ofModel(m)) = m   [apply_symm_apply]
  --   modelFromTensorEquiv.symm(modelFromTensor(t)) = t  [symm_apply_apply]
  --   map(cle.symm)(map(cle)(γ x)) = γ x  [CLE round-trip]
  -- Helper: fromTensor = ofModel ∘ modelFromTensor ∘ map(cle)
  have key : ∀ (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
      Bundle.continuousMultilinearMap 𝕜 q F E x),
      fromTensor s q x t = ofModel (F := F) (E := E) (modelFromTensor s q
        (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x :
            _ →ₗ[𝕜] MLF s))
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x :
            _ →ₗ[𝕜] MLF q)) t)) := by
    intro t
    -- Write t = map(cle.symm)(map(cle)(t)) and use fromTensor_map_ofModel
    have hrt : ∀ (u : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x),
        TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
            (MLF s) →ₗ[𝕜] _)
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
            (MLF q) →ₗ[𝕜] _)
          (TensorProduct.map
            ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x : _ →ₗ[𝕜] MLF s))
            ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x : _ →ₗ[𝕜] MLF q))
            u) = u := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp [map_zero]
      | add _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
      | tmul a b =>
        change ofModel (toModel a) ⊗ₜ[𝕜] ofModel (toModel b) = a ⊗ₜ[𝕜] b
        rw [ofModel_toModel, ofModel_toModel]
    conv_lhs => rw [← hrt t]
    exact fromTensor_map_ofModel _
  change TensorProduct.map
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm : (MLF s) →ₗ[𝕜] _)
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm : (MLF q) →ₗ[𝕜] _)
    ((modelFromTensorEquiv b s q).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
        (fromTensor s q x (γ x)))) = γ x
  rw [key (γ x)]
  simp only [ofModel, ContinuousLinearEquiv.apply_symm_apply]
  -- Goal: map(cle.symm)(e.symm(modelFromTensor(map(cle)(γ x)))) = γ x
  -- Change modelFromTensor to modelFromTensorEquiv, then symm_apply_apply simplifies
  change TensorProduct.map _ _
    ((modelFromTensorEquiv b s q).symm
      ((modelFromTensorEquiv b s q)
        (TensorProduct.map _ _ (γ x)))) = γ x
  rw [LinearEquiv.symm_apply_apply]
  -- Goal: map(cle.symm)(map(cle)(γ x)) = γ x
  induction (γ x) using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | add _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | tmul a c =>
    change ofModel (toModel a) ⊗ₜ[𝕜] ofModel (toModel c) = a ⊗ₜ[𝕜] c
    rw [ofModel_toModel, ofModel_toModel]

end RoundTrip

/-!
## Linearity properties
-/

section Linearity

open Bundle.continuousMultilinearMap

variable {s q : ℕ}

/-- `toTensorProduct` is additive. -/
theorem toTensorProduct_add
    (α β : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (toTensorProduct n (α + β)).1 x =
    (toTensorProduct n α).1 x + (toTensorProduct n β).1 x := by
  show TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
    (continuousLinearEquivAt (s + q) x ((α + β) x))) =
    TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
      (continuousLinearEquivAt (s + q) x (α x))) +
    TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
      (continuousLinearEquivAt (s + q) x (β x)))
  simp [map_add]

/-- `toTensorProduct` commutes with scalar multiplication by a smooth function. -/
theorem toTensorProduct_smulByFun
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (toTensorProduct n (smulByFun n φ hφ α)).1 x =
    φ x • (toTensorProduct n α).1 x := by
  show TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
    (continuousLinearEquivAt (s + q) x ((smulByFun n φ hφ α) x))) =
    φ x • TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
      (continuousLinearEquivAt (s + q) x (α x)))
  simp [smulByFun_apply, map_smul]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- `fromTensorProduct` is additive (pointwise):
`fromTensor(γ₁ x + γ₂ x) = fromTensor(γ₁ x) + fromTensor(γ₂ x)`. -/
theorem fromTensorProduct_add
    (γ₁ γ₂ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                        Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (γ₁ x + γ₂ x) = fromTensor s q x (γ₁ x) + fromTensor s q x (γ₂ x) :=
  map_add _ _ _

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- `fromTensorProduct` commutes with scalar multiplication (pointwise):
`fromTensor(c • γ x) = c • fromTensor(γ x)`. -/
theorem fromTensorProduct_smul
    (c : 𝕜) (γ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (c • γ x) = c • fromTensor s q x (γ x) :=
  (fromTensor s q x).map_smul c (γ x)

end Linearity

/-!
## Bundle equivalence via the section characterization lemma

The `toTensorProduct`/`fromTensorProduct` maps define a fiberwise linear equivalence
between the `(s+q)`-multilinear bundle and the tensor product of the `s`- and
`q`-multilinear bundles. By the vector bundle section characterization lemma
(`ContMDiffVectorBundleEquiv.ofLinearEquivSection`), this gives a `C^n` vector bundle
equivalence.

The key ingredients (all proved above) are:
* `fromTensor_toTensorProduct` : left inverse
* `toTensorProduct_fromTensorProduct` : right inverse
* `toTensorProduct_add`, `fromTensorProduct_add` : additivity
* `toTensorProduct_smulByFun`, `fromTensorProduct_smul` : smooth-function linearity
-/

section BundleEquiv

open Bundle.continuousMultilinearMap

variable {s q : ℕ}

/-- The `(s+q)`-multilinear bundle is `C^n`-equivalent to the tensor product of the
`s`- and `q`-multilinear bundles, as a consequence of the vector bundle section
characterization lemma applied to `toTensorProduct`/`fromTensorProduct`.

This specializes to `𝕜 = ℝ` and requires `IsManifold`, `SigmaCompactSpace`, `T2Space`,
and `FiniteDimensional` to apply the section characterization lemma. -/
noncomputable def multilinearBundle_tensorProduct_equiv
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {FM : Type*} [NormedAddCommGroup FM] [NormedSpace ℝ FM] [FiniteDimensional ℝ FM]
    [CompleteSpace ℝ]
    {EM' : M → Type*} [∀ x, NormedAddCommGroup (EM' x)] [∀ x, NormedSpace ℝ (EM' x)]
    [TopologicalSpace (TotalSpace FM EM')]
    [FiberBundle FM EM'] [VectorBundle ℝ FM EM']
    {nm : ℕ∞} [h1nm : Fact (1 ≤ nm)] [ContMDiffVectorBundle nm FM EM' IM]
    [IsManifold IM ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ EM]
    [∀ x, ContinuousAdd (Bundle.continuousMultilinearMap ℝ s FM EM' x)]
    [∀ x, ContinuousSMul ℝ (Bundle.continuousMultilinearMap ℝ s FM EM' x)]
    [∀ x, ContinuousAdd (Bundle.continuousMultilinearMap ℝ q FM EM' x)]
    [∀ x, ContinuousSMul ℝ (Bundle.continuousMultilinearMap ℝ q FM EM' x)] :
    letI := Bundle.TensorProduct.tensorFiberTopology
      ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
        (ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (Bundle.continuousMultilinearMap ℝ s FM EM')
      (Bundle.continuousMultilinearMap ℝ q FM EM')
    letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := ℝ) (B := M)
      (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (E₁ := Bundle.continuousMultilinearMap ℝ s FM EM')
      (E₂ := Bundle.continuousMultilinearMap ℝ q FM EM')
    letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
      (𝕜 := ℝ) (B := M)
      (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (E₁ := Bundle.continuousMultilinearMap ℝ s FM EM')
      (E₂ := Bundle.continuousMultilinearMap ℝ q FM EM')
    ContMDiffVectorBundleEquiv ℝ IM nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin (s + q) => FM) ℝ)
      (Bundle.continuousMultilinearMap ℝ (s + q) FM EM')
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
       ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                 Bundle.continuousMultilinearMap ℝ q FM EM' x) := by
  letI := Bundle.TensorProduct.tensorFiberTopology
    ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
    (Bundle.continuousMultilinearMap ℝ s FM EM')
    (Bundle.continuousMultilinearMap ℝ q FM EM')
  letI := Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
    (𝕜 := ℝ) (B := M)
    (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
    (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
    (E₁ := Bundle.continuousMultilinearMap ℝ s FM EM')
    (E₂ := Bundle.continuousMultilinearMap ℝ q FM EM')
  letI := Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
    (𝕜 := ℝ) (B := M)
    (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
    (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
    (E₁ := Bundle.continuousMultilinearMap ℝ s FM EM')
    (E₂ := Bundle.continuousMultilinearMap ℝ q FM EM')
  letI : ContMDiffVectorBundle nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
       ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                 Bundle.continuousMultilinearMap ℝ q FM EM' x) IM :=
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := ℝ) (B := M)
      (F₁ := ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ)
      (F₂ := ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (E₁ := Bundle.continuousMultilinearMap ℝ s FM EM')
      (E₂ := Bundle.continuousMultilinearMap ℝ q FM EM')).contMDiffVectorBundle IM
  -- Construct the section-level C^nm(M,ℝ)-linear equivalence
  let Fequiv : Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin (s + q) => FM) ℝ,
        Bundle.continuousMultilinearMap ℝ (s + q) FM EM'⟯
      ≃ₗ[C^nm⟮IM, M; ℝ⟯]
      Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ,
        fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                  Bundle.continuousMultilinearMap ℝ q FM EM' x⟯ :=
    { toFun := fun α => toTensorProduct nm α
      invFun := fun γ => fromTensorProduct nm γ
      map_add' := fun α β => by
        apply ContMDiffSection.ext; intro x
        exact toTensorProduct_add nm α β x
      map_smul' := fun φ α => by
        apply ContMDiffSection.ext; intro x
        exact toTensorProduct_smulByFun nm φ φ.contMDiff α x
      left_inv := fun α => by
        apply ContMDiffSection.ext; intro x
        exact fromTensor_toTensorProduct (n := nm) α x
      right_inv := fun γ => by
        apply ContMDiffSection.ext; intro x
        exact toTensorProduct_fromTensorProduct (n := nm) γ x }
  -- Apply the section characterization lemma
  exact ContMDiffVectorBundleEquiv.ofLinearEquivSection Fequiv

end BundleEquiv

end MultilinearSection

end
