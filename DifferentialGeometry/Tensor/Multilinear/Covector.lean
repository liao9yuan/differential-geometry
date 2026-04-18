/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.VectorBundle.Dual
import DifferentialGeometry.VectorBundle.Equiv

/-!
# The Covector Equivalence `T⁰₁(E) ≃ E*`

The 1-multilinear bundle `T⁰₁(E)` is `C^n`-equivalent to the dual bundle `E*`
as a `ContMDiffVectorBundleEquiv`. Fiberwise, a 1-multilinear map
`(Fin 1 → E x) → 𝕜` is identified with the corresponding linear functional
`E x →L[𝕜] 𝕜` via `ContinuousMultilinearMap.ofSubsingleton`.

## Main Definitions

* `Bundle.continuousMultilinearMap.covectorEquivAt` : fiber-level `LinearEquiv`
  between `T⁰₁(E)ₓ` and `E*ₓ`.
* `Bundle.continuousMultilinearMap.covectorBundle_equiv` : the `C^n` vector bundle
  equivalence.
* `MultilinearSection.toCovectorSection` / `fromCovectorSection` : section-level
  transport with round-trip and algebraic lemmas.

## Tags

multilinear map, covector, dual bundle, vector bundle, fiberwise equivalence
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
## Fiber-level equivalence
-/

/-- Fiber-level `LinearEquiv` between the 1-multilinear bundle fiber at `x` and the
dual fiber `E x →L[𝕜] 𝕜`. Forward: extract the CLM. Backward: `ofSubsingleton`. -/
noncomputable def covectorEquivAt (x : B) :
    Bundle.continuousMultilinearMap 𝕜 1 F E x ≃ₗ[𝕜] Bundle.dual 𝕜 E x where
  toFun T := (ContinuousMultilinearMap.ofSubsingleton
      (ι := Fin 1) (R := 𝕜) (M₂ := E x) (M₃ := 𝕜) 0).symm T
  invFun f := (ContinuousMultilinearMap.ofSubsingleton
      (ι := Fin 1) (R := 𝕜) (M₂ := E x) (M₃ := 𝕜) 0) f
  left_inv T := (ContinuousMultilinearMap.ofSubsingleton
      (ι := Fin 1) (R := 𝕜) (M₂ := E x) (M₃ := 𝕜) 0).right_inv T
  right_inv f := (ContinuousMultilinearMap.ofSubsingleton
      (ι := Fin 1) (R := 𝕜) (M₂ := E x) (M₃ := 𝕜) 0).left_inv f
  map_add' T₁ T₂ := by
    ext v; exact ContinuousMultilinearMap.add_apply T₁ T₂ _
  map_smul' c T := by
    ext v; exact ContinuousMultilinearMap.smul_apply T c _

/-!
## Model-level continuous linear maps
-/

variable (𝕜 F) in
/-- Model-level forward CLM: extract a covector from a 1-multilinear map on `F`. -/
noncomputable def modelCovectorFwdCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    (MLF 1) →L[𝕜] (F →L[𝕜] 𝕜) :=
  haveI : FiniteDimensional 𝕜 (MLF 1) := continuousMultilinearMap_finiteDimensional 1
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (ContinuousMultilinearMap.ofSubsingleton
        (ι := Fin 1) (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0).symm M
      map_add' := fun M₁ M₂ => by ext; exact ContinuousMultilinearMap.add_apply M₁ M₂ _
      map_smul' := fun c M => by ext; exact ContinuousMultilinearMap.smul_apply M c _ }

variable (𝕜 F) in
/-- Model-level inverse CLM: wrap a covector as a 1-multilinear map on `F`. -/
noncomputable def modelCovectorInvCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    (F →L[𝕜] 𝕜) →L[𝕜] (MLF 1) :=
  haveI : FiniteDimensional 𝕜 (MLF 1) := continuousMultilinearMap_finiteDimensional 1
  LinearMap.toContinuousLinearMap
    { toFun := fun f => (ContinuousMultilinearMap.ofSubsingleton
        (ι := Fin 1) (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0) f
      map_add' := fun f₁ f₂ => by
        ext v; exact ContinuousLinearMap.add_apply f₁ f₂ _
      map_smul' := fun c f => by
        ext v; exact ContinuousLinearMap.smul_apply c f _ }

/-!
## Trivialization compatibility
-/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Trivialization compatibility for the forward direction. -/
theorem covector_triv_fwd_eq (x₀ x : B)
    (_hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 1 F E x) :
    (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀
      ⟨x, covectorEquivAt (F := F) (E := E) x T⟩).2 =
    modelCovectorFwdCLM 𝕜 F
      ((trivializationAt (MLF 1)
        (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x) x₀ ⟨x, T⟩).2) := by
  -- The dual triv = hom triv with trivial codomain. By `hom_trivializationAt` (rfl) and
  -- `Trivialization.continuousLinearMap_apply` (rfl), `.2 a` definitionally equals
  -- `(trivAt_𝕜.cLMA x) (f (trivAt_F.symmL x a))`.
  -- The trivial 𝕜-bundle cLMA is propositionally `id`.
  ext a
  change (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).continuousLinearMapAt 𝕜 x
      ((covectorEquivAt (F := F) (E := E) x T) ((trivializationAt F E x₀).symmL 𝕜 x a)) = _
  have hmem_triv : x ∈ (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).baseSet := by
    simp [trivializationAt, FiberBundle.trivializationAt']
  change (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).linearMapAt 𝕜 x
      ((covectorEquivAt (F := F) (E := E) x T) ((trivializationAt F E x₀).symmL 𝕜 x a)) = _
  rw [Trivialization.coe_linearMapAt_of_mem _ hmem_triv]
  -- Now LHS = (trivAt_𝕜 ⟨x, covectorEquivAt T (symmL a)⟩).2 = covectorEquivAt T (symmL a) by rfl
  -- RHS = (ofSubsingleton).symm (T.compCCLM(fun _ => symmL)) a = T (fun _ => symmL a) by rfl
  rfl

/-- Trivialization compatibility for the inverse direction. -/
theorem covector_triv_inv_eq (x₀ x : B)
    (_hx : x ∈ (trivializationAt F E x₀).baseSet)
    (f : Bundle.dual 𝕜 E x) :
    (trivializationAt (MLF 1)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x) x₀
      ⟨x, (covectorEquivAt (F := F) (E := E) x).symm f⟩).2 =
    modelCovectorInvCLM 𝕜 F
      ((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀ ⟨x, f⟩).2) := by
  -- Multilinear triv: T.compCCLM(fun _ => symmL). With T = (ofSubsingleton 0) f:
  -- LHS w = ((ofSubsingleton 0 f).compCCLM(fun _ => symmL)) w = f (symmL (w 0))
  -- Dual triv (hom triv with trivial codomain): f.comp(symmL), by the same rfl chain.
  -- RHS w = (ofSubsingleton 0 (f.comp(symmL))) w = f (symmL (w 0))
  -- Multilinear triv precomposes with symmL on each (single) Fin 1 argument.
  -- Dual triv (hom triv) gives (trivAt_𝕜.cLMA).comp(f.comp(symmL)), and trivAt_𝕜.cLMA = id.
  -- Both sides evaluate to f(symmL(w 0)) on input w.
  ext w
  change ((ContinuousMultilinearMap.ofSubsingleton (ι := Fin 1) (R := 𝕜) (M₂ := E x) (M₃ := 𝕜) 0) f).compContinuousLinearMap
      (fun _ : Fin 1 => (trivializationAt F E x₀).symmL 𝕜 x) w =
    (ContinuousMultilinearMap.ofSubsingleton (ι := Fin 1) (R := 𝕜) (M₂ := F) (M₃ := 𝕜) 0)
      (((trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).continuousLinearMapAt 𝕜 x).comp
        (f.comp ((trivializationAt F E x₀).symmL 𝕜 x))) w
  have hmem_triv : x ∈ (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).baseSet := by
    simp [trivializationAt, FiberBundle.trivializationAt']
  have h_triv_id : (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).continuousLinearMapAt 𝕜 x =
      ContinuousLinearMap.id 𝕜 𝕜 := by
    apply ContinuousLinearMap.ext; intro c
    change (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀).linearMapAt 𝕜 x c = c
    rw [Trivialization.coe_linearMapAt_of_mem _ hmem_triv]; rfl
  simp only [ContinuousMultilinearMap.ofSubsingleton,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, h_triv_id]
  rfl

/-!
## Total-space smoothness
-/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable [ChartedSpace HB B]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

/-- The forward total-space map induced by `covectorEquivAt` is `C^n`. -/
theorem covectorEquivAt_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, MLF 1))
      (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      n
      (fun p : TotalSpace (MLF 1)
          (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x) =>
        (⟨p.1, covectorEquivAt (F := F) (E := E) p.1 p.2⟩ :
          TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
      (IB.prod 𝓘(𝕜, MLF 1)) 𝓘(𝕜, MLF 1) n
      (fun p => (trivializationAt (MLF 1)
        (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x) p₀.proj p).2)
      p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := modelCovectorFwdCLM 𝕜 F)).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F E p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F E p₀.proj)
  ] with p hp
  exact covector_triv_fwd_eq p₀.proj p.proj hp p.snd

/-- The inverse total-space map induced by `covectorEquivAt` is `C^n`. -/
theorem covectorEquivAt_symm_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜))
      (IB.prod 𝓘(𝕜, MLF 1))
      n
      (fun p : TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) =>
        (⟨p.1, (covectorEquivAt (F := F) (E := E) p.1).symm p.2⟩ :
          TotalSpace (MLF 1)
            (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
      (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) 𝓘(𝕜, F →L[𝕜] 𝕜) n
      (fun p => (trivializationAt (F →L[𝕜] 𝕜)
        (Bundle.dual 𝕜 E) p₀.proj p).2) p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := modelCovectorInvCLM 𝕜 F)).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F E p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F E p₀.proj)
  ] with p hp
  exact covector_triv_inv_eq p₀.proj p.proj hp p.snd

/-!
## The bundle equivalence
-/

/-- The `C^n` vector bundle equivalence `T⁰₁(E) ≃ E*`. -/
noncomputable def covectorBundle_equiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF 1)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x)
      (F →L[𝕜] 𝕜)
      (Bundle.dual 𝕜 E) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => covectorEquivAt (F := F) (E := E) x)
    covectorEquivAt_smooth
    covectorEquivAt_symm_smooth

end Bundle.continuousMultilinearMap

/-!
## Section-level transport
-/

namespace MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

/-- Transport a `C^n` 1-multilinear section to a `C^n` dual bundle section
via `covectorBundle_equiv`. -/
noncomputable def toCovectorSection
    (α : MultilinearSection 𝕜 F IB E n 1) :
    ContMDiffSection IB (F →L[𝕜] 𝕜) n (Bundle.dual 𝕜 E) :=
  let e := Bundle.continuousMultilinearMap.covectorBundle_equiv
    (𝕜 := 𝕜) (F := F) (E := E) (IB := IB) (n := n)
  ⟨fun x => e.fiberLinearEquiv x (α x),
   (e.toDiffeomorph.contMDiff.comp α.contMDiff).congr fun _ => (e.fiber_compat _ _).symm⟩

/-- Transport a `C^n` dual bundle section to a `C^n` 1-multilinear section
via `covectorBundle_equiv.symm`. -/
noncomputable def fromCovectorSection
    (w : ContMDiffSection IB (F →L[𝕜] 𝕜) n (Bundle.dual 𝕜 E)) :
    MultilinearSection 𝕜 F IB E n 1 :=
  let e := (Bundle.continuousMultilinearMap.covectorBundle_equiv
    (𝕜 := 𝕜) (F := F) (E := E) (IB := IB) (n := n)).symm
  ⟨fun x => e.fiberLinearEquiv x (w x),
   (e.toDiffeomorph.contMDiff.comp w.contMDiff).congr fun _ => (e.fiber_compat _ _).symm⟩

@[simp]
theorem fromCovectorSection_toCovectorSection
    (α : MultilinearSection 𝕜 F IB E n 1) :
    fromCovectorSection n (toCovectorSection n α) = α := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.symm_apply_apply _ (α x)

@[simp]
theorem toCovectorSection_fromCovectorSection
    (w : ContMDiffSection IB (F →L[𝕜] 𝕜) n (Bundle.dual 𝕜 E)) :
    toCovectorSection n (fromCovectorSection n w) = w := by
  apply ContMDiffSection.ext; intro x
  exact LinearEquiv.apply_symm_apply _ (w x)

end MultilinearSection

end
