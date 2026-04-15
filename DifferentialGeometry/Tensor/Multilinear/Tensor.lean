/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.VectorBundle.Section
import Mathlib.RingTheory.TensorProduct.Finite
/-!
# Tensor product of multilinear bundle fibers

This file defines the pointwise tensor product of two multilinear bundle fiber elements,
yielding an `(s+q)`-multilinear element by concatenating inputs. The construction works by
mapping to the model fiber via `toModel`, forming the product there using
`smulRight`/`uncurrySum`/`domDomCongr`, and mapping back via `ofModel`.

The model-fiber analogues `modelProduct` and `modelFromTensor` are also provided,
along with `modelFromTensorEquiv`: a constructive linear equivalence from the tensor
product of model fibers to `MLF (s+q)`, obtained via `LinearEquiv.ofBijective` from
the surjectivity of `modelFromTensor` together with matching dimensions.

These are the fiber-level building blocks for the section-level constructions in
`TensorSection.lean`.

## Main Definitions

* `Bundle.continuousMultilinearMap.product_fun` : pointwise tensor product of multilinear
  bundle fiber elements.
* `Bundle.continuousMultilinearMap.fromTensor` : tensor product map lifted to the abstract
  tensor product via the universal property.
* `Bundle.continuousMultilinearMap.modelProduct` : model-fiber analogue of `product_fun`.
* `Bundle.continuousMultilinearMap.modelFromTensor` : model-fiber analogue of `fromTensor`.
* `Bundle.continuousMultilinearMap.modelFromTensorEquiv` : `modelFromTensor` as a linear
  equivalence (via dimension counting).
* `Bundle.continuousMultilinearMap.equiv` : the abstract linear equivalence between the
  `(s+q)`-multilinear bundle fiber and the tensor product of the `s`- and `q`-multilinear
  bundle fibers, obtained by dimension counting.

## Main Results

* `product_fun_apply` : evaluation of `product_fun α β`.
* `triv_coord_product` : the trivialized basis coordinate of `product_fun α β` decomposes
  as a product of the trivialized basis coordinates of `α` and `β`.
* `modelFromTensor_basisElem` : `modelFromTensor` maps tensor products of basis elements
  to basis elements.
* `modelFromTensor_surjective` : `modelFromTensor` is surjective.
* `product_fun_ofModel`, `fromTensor_map_ofModel` : compatibility of `product_fun`/`fromTensor`
  with `ofModel` and the model-fiber operations.

## Tags

multilinear map, vector bundle, tensor product, fiber
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-!
## Tensor product of multilinear bundle fibers

The pointwise tensor product of an `s`-multilinear and a `q`-multilinear bundle fiber element
yields an `(s+q)`-multilinear element by concatenating inputs. The construction works by
mapping to the model fiber via `toModel`, forming the product there using
`smulRight`/`uncurrySum`/`domDomCongr`, and mapping back via `ofModel`.
-/

/-- The pointwise tensor product of two multilinear bundle fiber elements,
yielding an `(s+q)`-multilinear map by concatenating their inputs. -/
noncomputable def product_fun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => product_fun

set_option linter.unusedSimpArgs false in
omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- `product_fun α β` applied to arguments `v : Fin (s+q) → E x` equals
`α (v ∘ Fin.castAdd q) * β (v ∘ Fin.natAdd s)`.

The `toModel`/`ofModel` roundtrip cancels because both use the trivialization at `x`,
so `symmL ∘ continuousLinearMapAt = id` on each argument. -/
theorem product_fun_apply {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x)
    (v : Fin (s + q) → E x) :
    product_fun α β v = α (v ∘ Fin.castAdd q) * β (v ∘ Fin.natAdd s) := by
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  change (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv) v = _
  have hsymm : ∀ (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
      (w : Fin (s + q) → E x),
      (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm f w =
      f (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) := by
    intro f w; rfl
  rw [hsymm]
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  conv_lhs =>
    rw [show ∀ (c : 𝕜) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (w : Fin q → F), (c • f) w = c * f w
      from fun c f w => by simp [ContinuousMultilinearMap.smul_apply, smul_eq_mul]]
  simp_rw [show ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F), toModel T w =
      T (fun i => (trivializationAt F E x).symmL 𝕜 x (w i)) from fun _ _ _ => rfl,
    Function.comp, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  congr 1
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _

/-- The trivialized basis coordinate of a pointwise tensor product of multilinear bundle
fiber elements decomposes as a product of the trivialized basis coordinates of the factors.

Specifically, the `σ`-coordinate of `product_fun α β` (trivialized at `x₀`)
equals the `(σ ∘ Fin.castAdd q)`-coordinate of `α` times the `(σ ∘ Fin.natAdd s)`-coordinate
of `β`. -/
theorem triv_coord_product {s q d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (σ : Fin (s + q) → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    (continuousMultilinearMap_basis b (s + q)).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, product_fun α β⟩).2 σ =
    (continuousMultilinearMap_basis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (σ ∘ Fin.castAdd q) *
    (continuousMultilinearMap_basis b q).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀ ⟨x, β⟩).2
        (σ ∘ Fin.natAdd s) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 n F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro n T w; rfl
  simp_rw [htriv, product_fun_apply]
  rfl

/-- The tensor product of multilinear bundle fiber elements is bilinear. -/
noncomputable def product_bilinear (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 q F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  LinearMap.mk₂ 𝕜 product_fun
    (fun α₁ α₂ β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.add_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.add_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)

/-- The tensor product map lifted to the abstract tensor product via the universal property. -/
noncomputable def fromTensor (s q : ℕ) (x : B) :
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  TensorProduct.lift (product_bilinear (F := F) (E := E) s q x)

/-!
## Model-fiber product and tensor lift

The model-fiber analogues of `product_fun` and `fromTensor`, operating on
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜` rather than on bundle fibers.
-/

/-- The model-fiber product: given `f : MLF s` and `g : MLF q`, produce an element of
`MLF (s+q)` by `v ↦ f (v ∘ castAdd q) * g (v ∘ natAdd s)`. This is the model-fiber
analogue of `product_fun` (which works on bundle fibers). -/
noncomputable def modelProduct (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  (f.smulRight g).uncurrySum.domDomCongr finSumFinEquiv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem modelProduct_apply (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (v : Fin (s + q) → F) :
    modelProduct s q f g v = f (v ∘ Fin.castAdd q) * g (v ∘ Fin.natAdd s) := by
  simp only [modelProduct, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  congr 1

/-- The model-fiber bilinear product lifted to the tensor product. -/
noncomputable def modelFromTensor (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  TensorProduct.lift (LinearMap.mk₂ 𝕜 (modelProduct (𝕜 := 𝕜) (F := F) s q)
    (fun f₁ f₂ g => by ext v; simp [modelProduct_apply, add_mul])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)
    (fun f g₁ g₂ => by ext v; simp [modelProduct_apply, mul_add])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring))

/-- `modelFromTensor` maps tensor products of basis elements to basis elements:
`modelFromTensor (basisElem_s(σ ∘ castAdd) ⊗ₜ basisElem_q(σ ∘ natAdd)) = basisElem_{s+q}(σ)`.

This is because the product of coordinate functionals splits over `Fin s` and `Fin q`
via `Fin.prod_univ_add`. -/
theorem modelFromTensor_basisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) (σ : Fin (s + q) → Fin d) :
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      (continuousMultilinearMap_basisElem b s (σ ∘ Fin.castAdd q) ⊗ₜ[𝕜]
       continuousMultilinearMap_basisElem b q (σ ∘ Fin.natAdd s)) =
    continuousMultilinearMap_basisElem b (s + q) σ := by
  ext v
  simp only [modelFromTensor, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
    modelProduct_apply]
  simp only [continuousMultilinearMap_basisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Function.comp]
  rw [← Fin.prod_univ_add (fun i => (b.coord (σ i)) (v i))]

/-- `modelFromTensor` is surjective: every `(s+q)`-multilinear basis element is in its range,
since it equals `modelFromTensor` applied to the tensor product of the corresponding
`s`- and `q`-basis elements. -/
theorem modelFromTensor_surjective {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    Function.Surjective (modelFromTensor (𝕜 := 𝕜) (F := F) s q) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff]
  intro f _
  rw [← (continuousMultilinearMap_basis b (s + q)).sum_repr f]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  rw [show (continuousMultilinearMap_basis b (s + q)) σ =
    continuousMultilinearMap_basisElem b (s + q) σ from
    congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b (s + q)) _) σ]
  rw [← modelFromTensor_basisElem b s q σ]
  exact LinearMap.mem_range_self _ _

/-- `modelFromTensor` as a linear equivalence, obtained from surjectivity and
matching dimensions. -/
noncomputable def modelFromTensorEquiv {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional q
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofBijective (modelFromTensor s q)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Module.finrank_tensorProduct,
          finrank_continuousMultilinearMap s,
          finrank_continuousMultilinearMap q,
          finrank_continuousMultilinearMap (s + q), pow_add])).mpr
      (modelFromTensor_surjective b s q),
     modelFromTensor_surjective b s q⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- `product_fun` on un-trivialized elements equals un-trivialization of `modelProduct`:
`product_fun (ofModel f) (ofModel g) = ofModel (modelProduct f g)`. -/
theorem product_fun_ofModel {s q : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    product_fun (ofModel (F := F) (E := E) (x := x) f)
                (ofModel (F := F) (E := E) (x := x) g) =
    ofModel (modelProduct s q f g) := by
  simp only [product_fun, modelProduct, toModel_ofModel]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- `fromTensor` on un-trivialized tensor elements equals un-trivialization of
`modelFromTensor`:
`fromTensor(TensorProduct.map cle_s.symm cle_q.symm t) = ofModel(modelFromTensor t)`. -/
theorem fromTensor_map_ofModel {s q : ℕ} {x : B}
    (t : TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :
    fromTensor s q x (TensorProduct.map
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 s F E x)
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) t) =
    ofModel (F := F) (E := E) (x := x) (modelFromTensor s q t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [fromTensor, modelFromTensor, ofModel]
  | add t₁ t₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂, ofModel]
  | tmul f g =>
    simp only [TensorProduct.map_tmul, fromTensor, TensorProduct.lift.tmul,
      product_bilinear, LinearMap.mk₂_apply, modelFromTensor]
    exact product_fun_ofModel f g

set_option backward.isDefEq.respectTransparency false in
/-- Linear equivalence between the `(s+q)`-multilinear bundle fiber and the tensor product
of the `s`- and `q`-multilinear bundle fibers, obtained by dimension counting. -/
noncomputable def equiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) s x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) q x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) s x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) q x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) (s + q) x, pow_add])

end Bundle.continuousMultilinearMap

end

/-!
## Tensor product of smooth multilinear sections

This section defines tensor products at the section level for smooth multilinear sections,
and establishes a `C^n` vector bundle equivalence between the `(s+q)`-multilinear bundle
and the tensor product of the `s`- and `q`-multilinear bundles.

The key building blocks (defined fiberwise earlier in this file) are `fromTensor` (the
universal-property lift of `product_fun` to the abstract tensor product of multilinear
fibers) and its constructive inverse `modelFromTensorEquiv.symm`. Trivialization
compatibility lemmas (`triv_fromTensor_eq_modelFromTensor` and
`triv_toTensor_eq_modelFromTensorEquiv_symm`) are proved here because they require
`Product.Bundle` for the tensor product bundle trivialization.
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
    letI := Bundle.TensorProduct.fiberBundle
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
  letI := Bundle.TensorProduct.fiberBundle
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
    letI := Bundle.TensorProduct.fiberBundle
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
  letI := Bundle.TensorProduct.fiberBundle
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
## Tensor product instances

To avoid threading `letI` throughout the module, we declare local instances for the
topological space and bundle structures on the tensor product of two multilinear bundles.
This section wraps all tensor-product-related definitions and theorems.
-/

section TensorProductInstances

variable {s q : ℕ}

local instance multilinearTensorFiberTopology {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    ∀ x : B, TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                                Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.tensorFiberTopology 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorFiberBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorVectorBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

/-!
## From tensor product sections to multilinear sections
-/

section FromTensorProduct

open Bundle.continuousMultilinearMap

/-- Construct a `C^n` `(s+q)`-multilinear section from a `C^n` section of the tensor product
bundle of the `s`- and `q`-multilinear bundles, by applying `fromTensor` fiberwise.

Smoothness is proved via local trivializations: the trivialized `(s+q)`-section equals
`modelFromTensor` (a fixed CLM) composed with the trivialized tensor product section. -/
noncomputable def fromTensorProduct
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => fromTensor s q x (γ x), by
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
-/

section ToTensorProduct

open Bundle.continuousMultilinearMap

/-- Decompose a `C^n` `(s+q)`-multilinear section into a `C^n` section of the tensor product
bundle of the `s`- and `q`-multilinear bundles. -/
noncomputable def toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) :
    ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  let d := Module.finrank 𝕜 F
  let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
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
    set e := (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm.toContinuousLinearEquiv
    refine (e.toContinuousLinearMap.contMDiffAt.comp x₀ hα_triv).congr_of_eventuallyEq ?_
    exact (Filter.Eventually.mono
      ((trivializationAt F E x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x₀)) fun x hx => by
      have hfrom := fromTensor_map_ofModel
        (𝕜 := 𝕜) (F := F) (E := E) (s := s) (q := q) (x := x)
        ((modelFromTensorEquiv b s q).symm
          (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x)))
      have happly := (modelFromTensorEquiv b s q).apply_symm_apply
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x))
      set u := (modelFromTensorEquiv b s q).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x))
      have hid : fromTensor s q x (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
            (MLF s) →ₗ[𝕜] _)
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
            (MLF q) →ₗ[𝕜] _)
          u) = α x :=
        hfrom.trans (congrArg (ofModel (F := F) (E := E)) happly |>.trans (ofModel_toModel _))
      have h1 := triv_toTensor_eq_modelFromTensorEquiv_symm b s q x₀ x hx
        (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
            (MLF s) →ₗ[𝕜] _)
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
            (MLF q) →ₗ[𝕜] _)
          u)
      simp only [hid] at h1
      exact h1.symm)⟩

end ToTensorProduct

/-!
## Round-trip identities
-/

section RoundTrip

open Bundle.continuousMultilinearMap

/-- `fromTensor ∘ toTensorProduct = id` pointwise:
decomposing into a tensor product and then reassembling via `fromTensor` gives back
the original section value. -/
theorem fromTensor_toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    fromTensor s q x ((toTensorProduct n α).1 x) = α x := by
  change fromTensor s q x (TensorProduct.map
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
      (MLF s) →ₗ[𝕜] _)
    ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
      (MLF q) →ₗ[𝕜] _)
    ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x (α x)))) = α x
  rw [fromTensor_map_ofModel]
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
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x))
    (x : B) :
    (toTensorProduct n (fromTensorProduct n γ)).1 x = γ x := by
  set b := Module.finBasis 𝕜 F
  have key : ∀ (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
      Bundle.continuousMultilinearMap 𝕜 q F E x),
      fromTensor s q x t = ofModel (F := F) (E := E) (modelFromTensor s q
        (TensorProduct.map
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x :
            _ →ₗ[𝕜] MLF s))
          ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x :
            _ →ₗ[𝕜] MLF q)) t)) := by
    intro t
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
  change TensorProduct.map _ _
    ((modelFromTensorEquiv b s q).symm
      ((modelFromTensorEquiv b s q)
        (TensorProduct.map _ _ (γ x)))) = γ x
  rw [LinearEquiv.symm_apply_apply]
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

/-- `toTensorProduct` is additive. -/
theorem toTensorProduct_add
    (α β : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (toTensorProduct n (α + β)).1 x =
    (toTensorProduct n α).1 x + (toTensorProduct n β).1 x := by
  change TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
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
    (toTensorProduct n (smulByFun n φ hφ α)).1 x =
    φ x • (toTensorProduct n α).1 x := by
  change TensorProduct.map _ _ ((modelFromTensorEquiv _ s q).symm
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

/-- The section-level equivalence underlying `multilinearBundle_tensorProduct_equiv`. -/
noncomputable def multilinearBundle_tensorProduct_sectionEquiv
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {FM : Type*} [NormedAddCommGroup FM] [NormedSpace ℝ FM] [FiniteDimensional ℝ FM]
    [CompleteSpace ℝ]
    {EM' : M → Type*} [∀ x, NormedAddCommGroup (EM' x)] [∀ x, NormedSpace ℝ (EM' x)]
    [TopologicalSpace (TotalSpace FM EM')]
    [FiberBundle FM EM'] [VectorBundle ℝ FM EM']
    {nm : ℕ∞} [Fact (1 ≤ nm)] [ContMDiffVectorBundle nm FM EM' IM]
    [IsManifold IM ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ EM] :
    Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin (s + q) => FM) ℝ,
      Bundle.continuousMultilinearMap ℝ (s + q) FM EM'⟯
    ≃ₗ[C^nm⟮IM, M; ℝ⟯]
    Cₛ^nm⟮IM; ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ,
      fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                Bundle.continuousMultilinearMap ℝ q FM EM' x⟯ := by
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
  exact { toFun := fun α => toTensorProduct nm α
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
    [FiniteDimensional ℝ EM] :
    ContMDiffVectorBundleEquiv ℝ IM nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin (s + q) => FM) ℝ)
      (Bundle.continuousMultilinearMap ℝ (s + q) FM EM')
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
       ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                 Bundle.continuousMultilinearMap ℝ q FM EM' x) := by
  letI : ContMDiffVectorBundle nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => FM) ℝ ⊗[ℝ]
       ContinuousMultilinearMap ℝ (fun _ : Fin q => FM) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ s FM EM' x ⊗[ℝ]
                 Bundle.continuousMultilinearMap ℝ q FM EM' x) IM :=
    inferInstance
  exact ContMDiffVectorBundleEquiv.ofLinearEquivSection multilinearBundle_tensorProduct_sectionEquiv

end BundleEquiv

end TensorProductInstances

end MultilinearSection

end

