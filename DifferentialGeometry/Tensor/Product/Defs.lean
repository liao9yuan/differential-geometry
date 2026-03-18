/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Product.HomEquiv
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.Alternating.Curry
/-!
# TensorProduct.mapL and its properties

The continuous bilinear map `TensorProduct.mapL` and related properties.

## Main Definitions

* `TensorProduct.mapL L₁ L₂` : the continuous linear map `F₁ ⊗ F₂ →L G₁ ⊗ G₂` induced
  by continuous linear maps `L₁ : F₁ →L G₁` and `L₂ : F₂ →L G₂`.
* `TensorProduct.mapLBilinear` : the bilinear map `(F₁ →L G₁) →L (F₂ →L G₂) →L (F₁⊗F₂ →L G₁⊗G₂)`.

## Main Results

* `TensorProduct.mapL_tmul` : `mapL L₁ L₂ (v ⊗ₜ w) = L₁ v ⊗ₜ L₂ w`.

## Tags

tensor product, continuous linear map
-/

open scoped Topology TensorProduct

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

/-! ## TensorProduct.mapL and its properties -/

section MapL

variable {G₁ G₂ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]

/-- `TensorProduct.map` as a continuous linear map in finite dimensions. -/
noncomputable def TensorProduct.mapL (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    (F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂) :=
  (TensorProduct.map L₁.toLinearMap L₂.toLinearMap).toContinuousLinearMap

omit [FiniteDimensional 𝕜 G₂] in
/-- `mapL` acts on pure tensors by applying each factor: `(L₁ ⊗ L₂)(v ⊗ w) = L₁ v ⊗ L₂ w`. -/
@[simp]
theorem TensorProduct.mapL_tmul (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) (v : F₁) (w : F₂) :
    TensorProduct.mapL L₁ L₂ (v ⊗ₜ w) = L₁ v ⊗ₜ L₂ w := by
  simp [TensorProduct.mapL, TensorProduct.map_tmul]

omit [FiniteDimensional 𝕜 G₂] in
/-- `mapL` is additive in the left factor: `(L₁ + L₁') ⊗ L₂ = L₁ ⊗ L₂ + L₁' ⊗ L₂`. -/
theorem TensorProduct.mapL_add_left (L₁ L₁' : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL (L₁ + L₁') L₂ = TensorProduct.mapL L₁ L₂ + TensorProduct.mapL L₁' L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_add_left]

omit [FiniteDimensional 𝕜 G₂] in
/-- `mapL` is additive in the right factor: `L₁ ⊗ (L₂ + L₂') = L₁ ⊗ L₂ + L₁ ⊗ L₂'`. -/
theorem TensorProduct.mapL_add_right (L₁ : F₁ →L[𝕜] G₁) (L₂ L₂' : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL L₁ (L₂ + L₂') = TensorProduct.mapL L₁ L₂ + TensorProduct.mapL L₁ L₂' := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_add_right]

omit [FiniteDimensional 𝕜 G₂] in
/-- `mapL` is homogeneous in the left factor: `(c • L₁) ⊗ L₂ = c • (L₁ ⊗ L₂)`. -/
theorem TensorProduct.mapL_smul_left (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL (c • L₁) L₂ = c • TensorProduct.mapL L₁ L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_smul_left]

omit [FiniteDimensional 𝕜 G₂] in
/-- `mapL` is homogeneous in the right factor: `L₁ ⊗ (c • L₂) = c • (L₁ ⊗ L₂)`. -/
theorem TensorProduct.mapL_smul_right (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL L₁ (c • L₂) = c • TensorProduct.mapL L₁ L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_smul_right]


/-- The bilinear map (L₁, L₂) ↦ TensorProduct.mapL L₁ L₂. -/
noncomputable def TensorProduct.mapLBilinear :
    (F₁ →L[𝕜] G₁) →L[𝕜] (F₂ →L[𝕜] G₂) →L[𝕜]
      ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) := by
  classical
  -- continuity will be obtained from finite-dimensionality of the domains
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] G₁) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F₂ →L[𝕜] G₂) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F₂ →L[𝕜] G₂) →L[𝕜] F₁ ⊗[𝕜] F₂ →L[𝕜] G₁ ⊗[𝕜] G₂)
    := ContinuousLinearMap.finiteDimensional
  -- inner: linear in L₂
  let innerLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →ₗ[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    { toFun := fun L₂ => TensorProduct.mapL (𝕜 := 𝕜) L₁ L₂
      map_add' := TensorProduct.mapL_add_right (𝕜 := 𝕜) (L₁ := L₁)
      map_smul' := fun c L₂ =>
        TensorProduct.mapL_smul_right (𝕜 := 𝕜) (L₁ := L₁) (L₂ := L₂) c }
  let innerCLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    (innerLM (L₁ := L₁)).toContinuousLinearMap
  -- outer: linear in L₁, valued in continuous linear maps (in L₂)
  let outerLM :
      (F₁ →L[𝕜] G₁) →ₗ[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    { toFun := fun L₁ => innerCLM (L₁ := L₁)
      map_add' := by
        intro L₁ L₁'
        ext L₂ x
        -- evaluate in the codomain to reduce to your previously proved lemma
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapL_add_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) (L₁' := L₁'))
      map_smul' := by
        intro c L₁
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapL_smul_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) c) }
  have h : Continuous outerLM := @LinearMap.continuous_of_finiteDimensional
    _ _ (F₁ →L[𝕜] G₁) _ _ _ _ _ ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)))
    _ _ _ _ _ _ _ _ outerLM
  let f : (F₁ →L[𝕜] G₁) →L[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    ContinuousLinearMap.mk outerLM h
  exact f

end MapL

/-! ## Tensor products of (r,s)-tensors -/

namespace Tensor0SBundle

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The pointwise tensor product of a (0,s)-tensor `α` and a (0,q)-tensor `β`,
yielding a (0,s+q)-tensor by concatenating their inputs. -/
noncomputable def tensor0S_product_fun (s q : ℕ)
    (x : M) (α : Tensor0SSpace s I x) (β : Tensor0SSpace q I x) :
    Tensor0SSpace (s + q) I x :=
  (α.smulRight β).uncurrySum.domDomCongr finSumFinEquiv

/-- The tensor product of (0,s)- and (0,q)-tensors is bilinear in both factors,
giving a bilinear map `Tensor0SSpace s ⊗ Tensor0SSpace q →ₗ Tensor0SSpace (s+q)`.

Equivalently, this is `(tensor0S_equiv s q x).symm ∘ₗ TensorProduct.mk 𝕜 _ _`: the
abstract bilinear map from the universal property of tensor products, transported
back to the concrete (0,s+q)-tensor space via `tensor0S_equiv`. -/
noncomputable def tensor0S_product_bilinear (s q : ℕ) (x : M) :
    Tensor0SSpace s I x →ₗ[𝕜] Tensor0SSpace q I x →ₗ[𝕜] Tensor0SSpace (s + q) I x :=
  LinearMap.mk₂ 𝕜 (tensor0S_product_fun s q x)
    (fun α₁ α₂ β => by unfold tensor0S_product_fun; ext m; simp [add_smul])
    (fun c α β => by
      unfold tensor0S_product_fun; ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by unfold tensor0S_product_fun; ext m; simp [smul_add])
    (fun c α β => by
      unfold tensor0S_product_fun; ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)

/-- The tensor product map lifted to the abstract tensor product via the universal property:
`Tensor0SSpace s ⊗[𝕜] Tensor0SSpace q →ₗ Tensor0SSpace (s+q)`. -/
noncomputable def tensor0S_fromTensor (s q : ℕ) (x : M) :
    TensorProduct 𝕜 (Tensor0SSpace s I x) (Tensor0SSpace q I x) →ₗ[𝕜]
    Tensor0SSpace (s + q) I x :=
  TensorProduct.lift (tensor0S_product_bilinear s q x)

/-- Linear equivalence `Tensor0SSpace (r+r') ≃ₗ[𝕜] Tensor0SSpace r ⊗[𝕜] Tensor0SSpace r'`
at each point, obtained by dimension counting:
both sides have dimension `(finrank 𝕜 E)^r · (finrank 𝕜 E)^r'`. -/
noncomputable def tensor0S_equiv (r r' : ℕ) (x : M) :
    Tensor0SSpace (r + r') I x ≃ₗ[𝕜]
      TensorProduct 𝕜 (Tensor0SSpace r I x) (Tensor0SSpace r' I x) := by
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace r I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) r x
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace r' I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) r' x
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace (r + r') I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) (r + r') x
  haveI : Module.Free 𝕜 (Tensor0SSpace r I x) := inferInstance
  haveI : Module.Free 𝕜 (Tensor0SSpace r' I x) := inferInstance
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜 (Tensor0SSpace r I x) (Tensor0SSpace r' I x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r x,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r' x,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) (r + r') x,
        pow_add])

/-- Given T : (r,s) and T' : (r',s'), we define T ⊗ T' : (r+r',s+s').

Concretely, via `tensor0S_equiv`, the (0,r+r')-tensor space is identified with
`(0,r) ⊗[𝕜] (0,r')`, and we transport `TensorProduct.mapL T T'` (from
`DifferentialGeometry.Tensor.Product`) along these isomorphisms:

  `tensorRS_product T T' =
    (tensor0S_equiv s s').symm ∘ₗ TensorProduct.map T T' ∘ₗ tensor0S_equiv r r'`

We use the algebraic `TensorProduct.map` with a single outer `LinearMap.toContinuousLinearMap`,
since composing algebraic linear maps avoids synthesizing `TopologicalSpace` instances on the
intermediate tensor products `(0,r) ⊗[𝕜] (0,r')` and `(0,s) ⊗[𝕜] (0,s')`.
-/
-- TODO: Add notation for tensor product of tensors using ⊗ symbol
-- TODO: Define tensor product on sections/bundles, not just pointwise
-- TODO: Show that the product of smooth tensor fields is again smooth
noncomputable def tensorRS_product (r s r' s' : ℕ) (x : M)
    (T : TensorRSSpace r s I x) (T' : TensorRSSpace r' s' I x) :
    TensorRSSpace (r + r') (s + s') I x :=
  LinearMap.toContinuousLinearMap
    ((tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s s' x).symm.toLinearMap ∘ₗ
     TensorProduct.map T.toLinearMap T'.toLinearMap ∘ₗ
     (tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r r' x).toLinearMap)

end Tensor0SBundle

/-! ## Tensor product of alternating maps -/

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

/-- The tensor product of `g` and `h` with respect to a bilinear map `f`, as a continuous
multilinear map on `Fin (m + n)`. Generalizes `tensor0S_product_fun`: the curried product
`f.compContinuousAlternatingMap₂ g h` is uncurried via `ContinuousMultilinearMap.uncurrySum`
and relabeled to `Fin (m + n)` via `finSumFinEquiv`. -/
def tensorProductMap (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + n) => M) N'' :=
  (ContinuousMultilinearMap.uncurrySum
    ((f.compContinuousAlternatingMap₂ g h).toContinuousMultilinearMap
      |>.flipAlternating.toContinuousMultilinearMap.flipMultilinear))
  |>.domDomCongr finSumFinEquiv

end ContinuousAlternatingMap
