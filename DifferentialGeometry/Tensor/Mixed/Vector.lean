/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Fiber
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.Multilinear.Covector
import DifferentialGeometry.Tensor.Multilinear.Scalar
import DifferentialGeometry.VectorBundle.Equiv
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Vector Equivalence `T¹₀(E) ≃ E`

The mixed `(1,0)`-multilinear bundle `T¹₀(E)` is `C^n`-equivalent to the original vector
bundle `E` as a `ContMDiffVectorBundleEquiv`. Fiberwise, a `(1,0)`-mixed tensor
`T⁰₁(E)ₓ →L[𝕜] T⁰₀(E)ₓ` is identified with a vector `v : E x` via the double dual:
a mixed tensor `T` sends a covector `ω` to the scalar `ω(v)`.

## Main Definitions

* `Bundle.continuousMultilinearMap.vectorEquivAt` : fiber-level `LinearEquiv`
  between `T¹₀(E)ₓ` and `E x`.
* `Bundle.continuousMultilinearMap.vectorBundle_equiv` : the `C^n` vector bundle equivalence.
* `MixedSection.toVectorSection` / `fromVectorSection` : section-level transport with
  round-trip lemmas.

## Tags

multilinear map, vector, double dual, vector bundle, fiberwise equivalence
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-!
## Continuous double dual equivalence in finite dimensions
-/

/-- The continuous double dual equivalence in finite dimensions: the evaluation map
`v ↦ (f ↦ f v)` is a `LinearEquiv` from `V` to `(V →L[𝕜] 𝕜) →L[𝕜] 𝕜`. -/
noncomputable def continuousDoubleDualEquiv
    [CompleteSpace 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] :
    V ≃ₗ[𝕜] (V →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (V →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := V) (F' := 𝕜)).finiteDimensional
  { toFun := fun v => LinearMap.toContinuousLinearMap
      { toFun := fun f => f v
        map_add' := fun f g => ContinuousLinearMap.add_apply f g v
        map_smul' := fun c f => ContinuousLinearMap.smul_apply c f v }
    invFun := fun Φ =>
      (Module.evalEquiv 𝕜 V).symm
        { toFun := fun g => Φ (LinearMap.toContinuousLinearMap g)
          map_add' := fun g₁ g₂ => by simp [map_add]
          map_smul' := fun c g => by simp [map_smul] }
    left_inv := fun v => by
      change (Module.evalEquiv 𝕜 V).symm _ = v
      rw [LinearEquiv.symm_apply_eq]
      ext g
      simp [Module.evalEquiv_apply, Module.Dual.eval_apply]
    right_inv := fun Φ => by
      ext f
      change (f : V →ₗ[𝕜] 𝕜) ((Module.evalEquiv 𝕜 V).symm _) = Φ f
      rw [Module.apply_evalEquiv_symm_apply]
      change Φ (LinearMap.toContinuousLinearMap (f : V →ₗ[𝕜] 𝕜)) = Φ f
      congr 1
    map_add' := fun v w => by
      ext f; simp [map_add]
    map_smul' := fun c v => by
      ext f; simp [map_smul] }

/-!
## Fiber-level equivalence
-/

/-- Fiber-level `LinearEquiv` between the `(1,0)`-mixed tensor bundle fiber at `x` and
`E x`. A mixed tensor `T` is identified with the unique vector `v` such that
`T(ω) = ω(v)` for all covectors `ω`. -/
noncomputable def vectorEquivAt [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 0 F E x) ≃ₗ[𝕜] E x := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  let covCLE := (covectorEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).toContinuousLinearEquiv
  let scaCLE := (scalarEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).toContinuousLinearEquiv
  let e_hom := covCLE.arrowCongr scaCLE
  exact e_hom.toLinearEquiv.trans (continuousDoubleDualEquiv (𝕜 := 𝕜)).symm

/-!
## Model-level continuous linear maps

The model-level CLMs use explicit `𝕜` and `F` parameters. We expand the `MLF` notation
explicitly since `variable (𝕜 F) in` introduces fresh type variables that shadow the
ones used by the local notation.
-/

variable (𝕜 F) in
/-- Model-level forward CLM: extract a model vector from a (1,0)-mixed tensor on `F`. -/
noncomputable def modelVectorFwdCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) →L[𝕜] F := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 1
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 0
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F →L[𝕜] 𝕜) (F' := 𝕜)).finiteDimensional
  let covInv := modelCovectorInvCLM 𝕜 F
  let scaFwd := modelScalarFwdCLM 𝕜 F
  let dd := continuousDoubleDualEquiv (𝕜 := 𝕜) (V := F)
  exact LinearMap.toContinuousLinearMap
    { toFun := fun T => dd.symm (scaFwd.comp (T.comp covInv))
      map_add' := fun T₁ T₂ => by
        simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, map_add]
      map_smul' := fun c T => by
        simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, map_smul,
          RingHom.id_apply] }

variable (𝕜 F) in
/-- Model-level inverse CLM: embed a model vector as a (1,0)-mixed tensor on `F`. -/
noncomputable def modelVectorInvCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    F →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 1
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 0
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  let covFwd := modelCovectorFwdCLM 𝕜 F
  let scaInv := modelScalarInvCLM 𝕜 F
  let dd := continuousDoubleDualEquiv (𝕜 := 𝕜) (V := F)
  exact LinearMap.toContinuousLinearMap
    { toFun := fun v => scaInv.comp ((dd v).comp covFwd)
      map_add' := fun v w => by
        simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' := fun c v => by
        simp only [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
          RingHom.id_apply] }

/-!
## Trivialization compatibility
-/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Trivialization compatibility for the forward direction. -/
theorem vector_triv_fwd_eq (x₀ x : B)
    (_hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    (trivializationAt F E x₀
      ⟨x, vectorEquivAt (F := F) (E := E) x T⟩).2 =
    modelVectorFwdCLM 𝕜 F
      ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀ ⟨x, T⟩).2) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 1
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 0
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F →L[𝕜] 𝕜) (F' := 𝕜)).finiteDimensional
  haveI : FiniteDimensional 𝕜 (E x →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := E x) (F' := 𝕜)).finiteDimensional
  -- Both sides are in `F`. Apply `continuousDoubleDualEquiv` to both sides (injective),
  -- then show the resulting double-dual functionals agree on every `g : F →L[𝕜] 𝕜`.
  let dd_F := continuousDoubleDualEquiv (𝕜 := 𝕜) (V := F)
  let dd_E := continuousDoubleDualEquiv (𝕜 := 𝕜) (V := E x)
  apply dd_F.injective
  apply ContinuousLinearMap.ext; intro g
  -- RHS: modelVectorFwdCLM applies dd_F.symm, so dd_F ∘ dd_F.symm = id.
  have hRHS : (dd_F (modelVectorFwdCLM 𝕜 F
      ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀ ⟨x, T⟩).2)) g =
      (modelScalarFwdCLM 𝕜 F)
        ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀ ⟨x, T⟩).2
          (modelCovectorInvCLM 𝕜 F g))) := by
    change dd_F (dd_F.symm _) g = _
    rw [LinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearMap.comp_apply]
  rw [hRHS]; clear hRHS
  -- LHS: dd_F w g = g w by definition of dd_F.
  change g ((trivializationAt F E x₀ ⟨x, vectorEquivAt (F := F) (E := E) x T⟩).2) = _
  -- Unfold vectorEquivAt x T = dd_E.symm (e_hom T).
  -- The trivialization sends v ∈ E x to (trivAt F E x₀).continuousLinearMapAt 𝕜 x v.
  -- So LHS = g ((trivAt F E x₀).cLMA x (dd_E.symm (e_hom T))).
  -- By the double dual property, for f : E x →L 𝕜:
  --   f (dd_E.symm Φ) = Φ f.
  -- Setting f = g.comp ((trivAt F E x₀).cLMA x):
  --   (g.comp cLMA x) (dd_E.symm Φ) = Φ (g.comp cLMA x)
  -- i.e. g (cLMA x (dd_E.symm Φ)) = Φ (g.comp cLMA x).
  -- Step 1: Show LHS = scaCLE (T (covCLE.symm (g.comp (trivAt F E x₀).cLMA x)))
  -- by the double dual evaluation.
  let covCLE := (covectorEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).toContinuousLinearEquiv
  let scaCLE := (scalarEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).toContinuousLinearEquiv
  -- vectorEquivAt x T = (covCLE.arrowCongr scaCLE).toLinearEquiv.trans dd_E.symm applied to T
  have hvec : vectorEquivAt (F := F) (E := E) x T =
      dd_E.symm (scaCLE.toContinuousLinearMap.comp
        (T.comp covCLE.symm.toContinuousLinearMap)) := by
    change ((covCLE.arrowCongr scaCLE).toLinearEquiv.trans
      (continuousDoubleDualEquiv (𝕜 := 𝕜)).symm) T = _
    simp only [LinearEquiv.trans_apply]
    congr 1
  rw [hvec]
  -- Now LHS = g (cLMA x (dd_E.symm Φ)) where Φ = scaCLE.toCLM.comp (T.comp covCLE.symm.toCLM).
  -- Use: f (dd_E.symm Φ) = Φ f, so g (cLMA x (dd_E.symm Φ)) = Φ (g.comp (cLMA x)) when
  -- we view g.comp(cLMA x) as an element of (E x →L[𝕜] 𝕜).
  -- The trivialization on the base set: (trivAt F E x₀ ⟨x, v⟩).2 = (trivAt F E x₀).cLMA x v.
  -- So g ((trivAt F E x₀ ⟨x, dd_E.symm Φ⟩).2) = g ((trivAt F E x₀).cLMA x (dd_E.symm Φ))
  --   = (g.comp (cLMA x)) (dd_E.symm Φ) = Φ (g.comp (cLMA x))
  --   = scaCLE (T (covCLE.symm (g.comp (cLMA x))))
  -- Step 1a: Rewrite (trivAt ⟨x, v⟩).2 = (trivAt).continuousLinearMapAt 𝕜 x v on the base set.
  have h_triv_eq : ∀ (v : E x), (trivializationAt F E x₀ ⟨x, v⟩).2 =
      (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v := by
    intro v
    rw [Trivialization.continuousLinearMapAt_apply]
    exact (congrFun ((trivializationAt F E x₀).coe_linearMapAt_of_mem _hx) v).symm
  rw [h_triv_eq]
  -- Step 1b: g (L v) = (g.comp L) v (definitional)
  rw [show g ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x
    (dd_E.symm (scaCLE.toContinuousLinearMap.comp
      (T.comp covCLE.symm.toContinuousLinearMap)))) =
    (g.comp ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x))
      (dd_E.symm (scaCLE.toContinuousLinearMap.comp
        (T.comp covCLE.symm.toContinuousLinearMap))) from rfl]
  -- Step 1c: f (dd_E.symm Φ) = Φ f by the double dual property.
  -- dd_E v is the eval-at-v functional; dd_E.symm Φ is the vector v s.t. ∀ f, f v = Φ f.
  -- Specifically dd_E.symm Φ = (Module.evalEquiv).symm (Φ restricted to linear maps),
  -- and (Module.evalEquiv).symm satisfies f ((Module.evalEquiv).symm φ) = φ f.
  -- The right approach: dd_E v f = f v, so dd_E (dd_E.symm Φ) = Φ, so Φ f = dd_E (dd_E.symm Φ) f = f (dd_E.symm Φ).
  -- i.e., f (dd_E.symm Φ) = Φ f.
  have hdd_eval : ∀ (Φ : (E x →L[𝕜] 𝕜) →L[𝕜] 𝕜) (f : E x →L[𝕜] 𝕜),
      f (dd_E.symm Φ) = Φ f := by
    intro Φ f
    -- dd_E v is the CLM f ↦ f v, so (dd_E v) f = f v by definition.
    -- Therefore f (dd_E.symm Φ) = (dd_E (dd_E.symm Φ)) f = Φ f.
    change (dd_E (dd_E.symm Φ)) f = Φ f
    rw [dd_E.apply_symm_apply]
  rw [hdd_eval]
  -- Now LHS = scaCLE (T (covCLE.symm (g.comp (cLMA x)))).
  -- RHS = modelScalarFwdCLM (trivAt_mixed(T).2 (modelCovectorInvCLM g)).
  -- Step 2: Unfold the hom trivialization.
  -- (trivAt_mixed ⟨x, T⟩).2 = inCoordinates ... T
  --   = (trivAt_0.cLMA x).comp (T.comp (trivAt_1.symmL x))   [by hom_trivializationAt_apply]
  -- So (trivAt_mixed(T).2) (covInv g) = (trivAt_0.cLMA x) (T ((trivAt_1.symmL x) (covInv g))).
  -- Step 2a: Show (trivAt_1.symmL x)(covInv g) = covCLE.symm(g.comp(cLMA x)).
  -- Both sides are 1-multilinear maps on E x.
  -- By triv_symmL_eq_compContinuousLinearMap:
  --   (trivAt_1.symmL x)(covInv g) = (covInv g).compCCLM(fun _ => cLMA x)
  -- And covCLE.symm(g.comp(cLMA x)) = ofSubsingleton 0 (g.comp(cLMA x)).
  -- These agree: both send v to g(cLMA x (v 0)).
  have h_cov_eq : ∀ (g' : F →L[𝕜] 𝕜),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 1 F E) x₀).symmL 𝕜 x
        (modelCovectorInvCLM 𝕜 F g') =
      (covectorEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).symm
        (g'.comp ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x)) := by
    intro g'
    rw [triv_symmL_eq_compContinuousLinearMap x₀ x _hx]
    apply Bundle.continuousMultilinearMap.ext; intro v
    rfl
  -- Step 2b: Show scaCLE(S) = scaFwd(trivAt_0.cLMA x S) for any S in 0-ML fiber at x.
  -- scaCLE S = scalarEquivAt x S = S Fin.elim0.
  -- (trivAt_0.cLMA x S) w = S (fun i : Fin 0 => symmL x (w i)) = S Fin.elim0 (by Subsingleton).
  -- scaFwd((trivAt_0.cLMA x S)) = (trivAt_0.cLMA x S) 0 = S Fin.elim0.
  have h_sca_eq : ∀ (S : Bundle.continuousMultilinearMap 𝕜 0 F E x),
      scaCLE S = (modelScalarFwdCLM 𝕜 F)
        ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ ⟨x, S⟩).2) := by
    intro S
    change S Fin.elim0 = _
    exact (triv_zero_apply_eq x₀ x S 0).symm
  -- Step 3: Unfold CLM composition, then rewrite using h_sca_eq and h_cov_eq.
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  -- Goal: scaCLE (T (covCLE.symm (g.comp (cLMA x)))) = scaFwd (trivAt_mixed(T).2 (covInv g))
  -- Use h_sca_eq to rewrite LHS: scaCLE S = scaFwd (trivAt_0 ⟨x, S⟩).2
  rw [h_sca_eq]
  -- Goal: scaFwd (trivAt_0 ⟨x, T(covCLE.symm(g.comp(cLMA x)))⟩).2
  --     = scaFwd (trivAt_mixed(T).2 (covInv g))
  -- Rewrite covCLE.symm(g.comp(cLMA x)) = (trivAt_1.symmL x)(covInv g) using h_cov_eq.
  -- Rewrite using h_cov_eq: covCLE.symm = (covectorEquivAt x).symm as let binding.
  conv_lhs => rw [show (covCLE.symm : Bundle.dual 𝕜 E x → _) = (covectorEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).symm from rfl]
  rw [← h_cov_eq g]
  -- Goal: scaFwd (trivAt_0 ⟨x, T((trivAt_1.symmL x)(covInv g))⟩).2
  --     = scaFwd (trivAt_mixed(T).2 (covInv g))
  -- The hom trivialization: (trivAt_mixed ⟨x, T⟩).2 M = (trivAt_0.cLMA x)(T((trivAt_1.symmL x) M))
  -- and (trivAt_0 ⟨x, S⟩).2 = (trivAt_0.cLMA x) S  [on the base set, but also definitionally
  -- as the multilinear triv sends S to S.compCCLM(fun _ => symmL)].
  -- So both sides reduce to scaFwd applied to the 0-multilinear trivialization of T(symmL(covInv g)).
  -- The RHS is definitionally: (trivAt_0 ⟨x, T((trivAt_1.symmL x)(covInv g))⟩).2
  -- after unfolding inCoordinates for the hom bundle.
  -- Both LHS and RHS apply scaFwd to a 0-multilinear map; show the args are equal.
  congr 1
  -- Need: (trivAt_0 ⟨x, T(symmL(covInv g))⟩).2 = (trivAt_mixed ⟨x, T⟩).2 (covInv g)
  -- Unfold the hom trivialization via hom_trivializationAt_apply.
  rw [hom_trivializationAt_apply]
  -- After rewriting, RHS becomes inCoordinates applied to T at (covInv g).
  -- inCoordinates ... T (covInv g) = (trivAt_0.cLMA x)(T((trivAt_1.symmL x)(covInv g)))
  simp only [ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Goal: (trivAt_0 ⟨x, S⟩).2 = (trivAt_0).continuousLinearMapAt 𝕜 x S
  -- Use coe_linearMapAt_of_mem to rewrite (e ⟨x, y⟩).2 = e.linearMapAt x y on base set.
  rw [Trivialization.continuousLinearMapAt_apply]
  exact (congrFun ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀).coe_linearMapAt_of_mem
    (show x ∈ _ from _hx)) _).symm

variable (𝕜 F) in
/-- Model-level round-trip: `modelVectorInvCLM ∘ modelVectorFwdCLM = id`.
This is the model fiber version of `vectorEquivAt.symm ∘ vectorEquivAt = id`. -/
private theorem modelVector_inv_fwd [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (M : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :
    modelVectorInvCLM 𝕜 F (modelVectorFwdCLM 𝕜 F M) = M := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 1
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional 0
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :=
    ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F →L[𝕜] 𝕜) (F' := 𝕜)).finiteDimensional
  -- The model CLMs factor through vectorEquivAt on the trivial F-bundle.
  -- Use the actual vectorEquivAt on B = Unit, E = fun _ => F.
  -- Instead, prove directly by ext and unfolding definitions.
  -- modelVectorFwdCLM M = dd.symm (scaFwd ∘ M ∘ covInv)
  -- modelVectorInvCLM v = scaInv ∘ (dd v) ∘ covFwd
  -- Composition: scaInv ∘ (dd(dd.symm(scaFwd ∘ M ∘ covInv))) ∘ covFwd
  --            = scaInv ∘ (scaFwd ∘ M ∘ covInv) ∘ covFwd
  --            = scaInv ∘ scaFwd ∘ M ∘ covInv ∘ covFwd
  -- The ofSubsingleton round-trips give covInv ∘ covFwd = id and scaInv ∘ scaFwd = id.
  let dd := continuousDoubleDualEquiv (𝕜 := 𝕜) (V := F)
  -- The model CLMs factor through vectorEquivAt on the trivial bundle.
  -- Observe: modelVectorFwdCLM and modelVectorInvCLM are precisely the two directions
  -- of vectorEquivAt on the trivial F-bundle (B = PUnit, E = fun _ => F).
  -- We prove the round-trip by reducing to (vectorEquivAt).symm ∘ (vectorEquivAt) = id.
  -- Direct approach: unfold, cancel dd, cancel ofSubsingleton and constOfIsEmpty round-trips.
  -- Prove pointwise equality by unfolding all definitions.
  -- modelVectorFwdCLM M = dd.symm (scaFwd ∘ M ∘ covInv)
  -- modelVectorInvCLM v = scaInv ∘ (dd v) ∘ covFwd
  -- After cancelling dd ∘ dd.symm and ofSubsingleton round-trips, reduces to M.
  -- Step 1: Cancel dd ∘ dd.symm to get:
  -- modelVectorInvCLM (modelVectorFwdCLM M) = scaInv ∘ (scaFwd ∘ M ∘ covInv) ∘ covFwd
  have h1 : modelVectorInvCLM 𝕜 F (modelVectorFwdCLM 𝕜 F M) =
    (modelScalarInvCLM 𝕜 F).comp
      (((modelScalarFwdCLM 𝕜 F).comp (M.comp (modelCovectorInvCLM 𝕜 F))).comp
        (modelCovectorFwdCLM 𝕜 F)) := by
    change (modelScalarInvCLM 𝕜 F).comp
      ((dd (dd.symm ((modelScalarFwdCLM 𝕜 F).comp (M.comp (modelCovectorInvCLM 𝕜 F))))).comp
        (modelCovectorFwdCLM 𝕜 F)) = _
    rw [dd.apply_symm_apply]
  rw [h1]
  -- Step 2: ext and simplify compositions.
  apply ContinuousLinearMap.ext; intro m
  simp only [ContinuousLinearMap.comp_apply]
  -- Goal: scaInv(scaFwd(M(covInv(covFwd m)))) = M m
  -- The covector round-trip: covInv(covFwd m) = ofSubsingleton(ofSubsingleton.symm m) = m.
  -- ofSubsingleton.symm extracts the CLM from a 1-multilinear map, ofSubsingleton wraps it back.
  -- The scalar round-trip: scaInv(scaFwd S) = constOfIsEmpty(S Fin.elim0) which equals S
  -- since any Fin-0-multilinear map is determined by its value at the unique empty input.
  -- Goal: (modelScalarInvCLM 𝕜 F) ((modelScalarFwdCLM 𝕜 F) (M ((modelCovectorInvCLM 𝕜 F)
  --        ((modelCovectorFwdCLM 𝕜 F) m)))) = M m
  -- Prove by unfolding step by step. Each model CLM is toCLM of a LinearMap.
  -- First unfold the outer applications.
  -- Covector round-trip: covInv ∘ covFwd = id
  -- modelCovectorFwdCLM maps T ↦ ofSubsingleton.symm T, modelCovectorInvCLM maps f ↦ ofSubsingleton f
  -- So composition = ofSubsingleton ∘ ofSubsingleton.symm = id.
  -- Covector round-trip: covInv(covFwd m) = ofSubsingleton(ofSubsingleton.symm m) = m
  have h1 : (modelCovectorInvCLM 𝕜 F) ((modelCovectorFwdCLM 𝕜 F) m) = m := by
    simp only [modelCovectorInvCLM, modelCovectorFwdCLM]
    -- Goal has toCLM wrappers. They are transparent for function application.
    change (ContinuousMultilinearMap.ofSubsingleton (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0)
      ((ContinuousMultilinearMap.ofSubsingleton (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0).symm m) = m
    exact (ContinuousMultilinearMap.ofSubsingleton (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0).apply_symm_apply m
  -- Scalar round-trip: scaInv(scaFwd S) = constOfIsEmpty(S 0) = S
  have h2 : ∀ (S : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜),
      (modelScalarInvCLM 𝕜 F) ((modelScalarFwdCLM 𝕜 F) S) = S := by
    intro S
    simp only [modelScalarInvCLM, modelScalarFwdCLM]
    -- Goal: (toCLM constOfIsEmpty) ((toCLM (fun M => M 0)) S) = S
    -- This is constOfIsEmpty (S 0) = S. But 0 : Fin 0 → F, not Fin.elim0.
    -- constOfIsEmpty (S 0) w = S 0 for all w : Fin 0 → F.
    -- S 0 = S w by Subsingleton for Fin 0 → F.
    ext w
    change ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => F) (S 0) w = S w
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact congrArg S (Subsingleton.elim _ _)
  simp only [h1, h2]

/-- Trivialization compatibility for the inverse direction. -/
theorem vector_triv_inv_eq (x₀ x : B)
    (_hx : x ∈ (trivializationAt F E x₀).baseSet)
    (v : E x) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀
      ⟨x, (vectorEquivAt (F := F) (E := E) x).symm v⟩).2 =
    modelVectorInvCLM 𝕜 F
      ((trivializationAt F E x₀ ⟨x, v⟩).2) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  have hfwd := vector_triv_fwd_eq x₀ x _hx
    ((vectorEquivAt (𝕜 := 𝕜) (F := F) (E := E) x).symm v)
  rw [LinearEquiv.apply_symm_apply] at hfwd
  rw [hfwd]
  exact (modelVector_inv_fwd 𝕜 F _).symm

/-!
## Total-space smoothness
-/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable [ChartedSpace HB B]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

/-- The forward total-space map induced by `vectorEquivAt` is `C^n`. -/
theorem vectorEquivAt_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (IB.prod 𝓘(𝕜, F))
      n
      (fun p : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
          (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 0 F E x) =>
        (⟨p.1, vectorEquivAt (F := F) (E := E) p.1 p.2⟩ :
          TotalSpace F E)) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) n
      (fun p => (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 0 F E x) p₀.proj p).2)
      p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := modelVectorFwdCLM 𝕜 F)).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F E p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F E p₀.proj)
  ] with p hp
  exact vector_triv_fwd_eq p₀.proj p.proj hp p.snd

/-- The inverse total-space map induced by `vectorEquivAt` is `C^n`. -/
theorem vectorEquivAt_symm_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, F))
      (IB.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      n
      (fun p : TotalSpace F E =>
        (⟨p.1, (vectorEquivAt (F := F) (E := E) p.1).symm p.2⟩ :
          TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
            (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                      Bundle.continuousMultilinearMap 𝕜 0 F E x))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
      (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun p => (trivializationAt F E p₀.proj p).2) p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := modelVectorInvCLM 𝕜 F)).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F E p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F E p₀.proj)
  ] with p hp
  exact vector_triv_inv_eq p₀.proj p.proj hp p.snd

/-!
## The bundle equivalence
-/

/-- The `C^n` vector bundle equivalence `T¹₀(E) ≃ E`. -/
noncomputable def vectorBundle_equiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 0 F E x)
      F
      E :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => vectorEquivAt (F := F) (E := E) x)
    vectorEquivAt_smooth
    vectorEquivAt_symm_smooth

end Bundle.continuousMultilinearMap

/-!
## Section-level transport
-/

namespace MixedSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-- Transport a `C^n` mixed `(1,0)`-section to a `C^n` section of `E`
via `vectorBundle_equiv`. -/
noncomputable def toVectorSection
    (T : MixedSection 𝕜 F IB E n 1 0) :
    ContMDiffSection IB F n E :=
  let e := Bundle.continuousMultilinearMap.vectorBundle_equiv
    (𝕜 := 𝕜) (IB := IB) (n := n) (F := F) (E := E)
  ⟨fun x => e.fiberLinearEquiv x (T x),
   (e.toDiffeomorph.contMDiff.comp T.contMDiff).congr fun _ => (e.fiber_compat _ _).symm⟩

/-- Transport a `C^n` section of `E` to a `C^n` mixed `(1,0)`-section
via `vectorBundle_equiv.symm`. -/
noncomputable def fromVectorSection
    (σ : ContMDiffSection IB F n E) :
    MixedSection 𝕜 F IB E n 1 0 :=
  let e := (Bundle.continuousMultilinearMap.vectorBundle_equiv
    (𝕜 := 𝕜) (IB := IB) (n := n) (F := F) (E := E)).symm
  ⟨fun x => e.fiberLinearEquiv x (σ x),
   (e.toDiffeomorph.contMDiff.comp σ.contMDiff).congr fun _ => (e.fiber_compat _ _).symm⟩

@[simp]
theorem fromVectorSection_toVectorSection
    (T : MixedSection 𝕜 F IB E n 1 0) :
    fromVectorSection n (toVectorSection n T) = T := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.symm_apply_apply _ (T x)

@[simp]
theorem toVectorSection_fromVectorSection
    (σ : ContMDiffSection IB F n E) :
    toVectorSection n (fromVectorSection n σ) = σ := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.apply_symm_apply _ (σ x)

end MixedSection

end
