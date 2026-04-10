/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
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
  -- Unfold product_fun; ofModel = (continuousLinearEquivAt).symm
  change (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv) v = _
  have hsymm : ∀ (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
      (w : Fin (s + q) → E x),
      (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm f w =
      f (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) := by
    intro f w; rfl
  rw [hsymm]
  -- Now simplify the model-level combinators
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  conv_lhs =>
    rw [show ∀ (c : 𝕜) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (w : Fin q → F), (c • f) w = c * f w
      from fun c f w => by simp [ContinuousMultilinearMap.smul_apply, smul_eq_mul]]
  -- Now both sides have toModel fully applied
  simp_rw [show ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F), toModel T w =
      T (fun i => (trivializationAt F E x).symmL 𝕜 x (w i)) from fun _ _ _ => rfl,
    Function.comp, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  -- Cancel symmL ∘ continuousLinearMapAt = id on each factor
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
