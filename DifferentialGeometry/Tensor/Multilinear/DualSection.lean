/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.DualBundle
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.VectorBundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.Hom
/-!
# Section-level dual lift of the multilinear-of-dual iso

This file lifts the bundle-fiber-level continuous linear equivalence
`Bundle.continuousMultilinearMap.dualMultilinearLinearEquivAt` from `DualFiber.lean`
to a canonical mapping between section spaces, eventually building a `C^n` vector bundle
equivalence between the dual of the `r`-multilinear bundle and the `r`-multilinear bundle
of the dual:

  `Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`  ≃
  `Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)`.

This file mirrors the pattern of `Tensor/Multilinear/TensorSection.lean` and
`Tensor/Mixed/Field.lean`.

## Construction strategy

The lift uses the model-fiber-level inverse iso `dualMultilinearEquivMultilinearOfDual 𝕜 F r`
applied locally via the bundle's trivialization. The key technical lemma is the
trivialization compatibility:

  `(triv (Bundle.dual (mlb r F E)) x₀ ⟨x, ψ x⟩).2`
    `= (model_inv) ((triv (mlb r (F →L[𝕜] 𝕜) (dual E)) x₀ ⟨x, α x⟩).2)`

where `ψ x` is defined via the fiber CLE at point `x`. This lemma is proved by applying
the forward direction `dualMultilinearLinearMap 𝕜 F r` (injective, being part of a
`LinearEquiv`) to both sides and reducing to the same expression
`α x (fun i => (β i).comp ((trivAt F E x₀).continuousLinearMapAt 𝕜 x))` via the round-trip
identity and the naturality of `tensorOfDualLinearForms` under composition.

## Main Definitions

* `DualBundleSection` : `C^n` sections of the dual of the multilinear bundle
  `Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`.
* `Bundle.continuousMultilinearMap.dualLiftFiber` : the pointwise lifted fiber value.
* `MultilinearSection.toDualBundleSection` : convert a smooth section of the multilinear
  bundle of the dual to a smooth section of the dual of the multilinear bundle.

## Main Results

* `Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality` :
  naturality of `tensorOfDualLinearForms` under composition with a CLM.
* `MultilinearSection.dualLiftFiber_triv_eq` : the trivialization compatibility lemma
  identifying the trivialized lifted section with `modelDualInvCLM` applied to the
  trivialized input section.

## TODO

* `MultilinearSection.fromDualBundleSection` : the inverse direction.
* Round-trip, additivity, and smul-by-fun properties.
* `dualBundle_multilinearOfDual_equiv` : the `C^n` vector bundle equivalence, via
  `ContMDiffVectorBundleEquiv.ofLinearEquivSection` (following the pattern of
  `multilinearBundle_tensorProduct_equiv` and `multilinearBundle_mixedBundle_equiv`).

## Tags

multilinear bundle, dual bundle, section, lift
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Abbreviation for the model fiber of the `r`-multilinear bundle on `F`. -/
local notation "MLF" => fun r => ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜

/-- Abbreviation for the model fiber of the `r`-multilinear bundle on `F →L[𝕜] 𝕜`. -/
local notation "MLF_dual" => fun r =>
  ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜

/-! ## Naturality of `tensorOfDualLinearForms` -/

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- Naturality of `tensorOfDualLinearForms` with respect to composition with a continuous
linear map. For any `L : G →L[𝕜] F` and `β : Fin r → (F →L[𝕜] 𝕜)`,
`(tensorOfDualLinearForms 𝕜 F r β).compContinuousLinearMap (fun _ => L)` equals
`tensorOfDualLinearForms 𝕜 G r (fun i => (β i).comp L)`. -/
theorem tensorOfDualLinearForms_compContinuousLinearMap_naturality
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (r : ℕ) (L : G →L[𝕜] F)
    (β : Fin r → (F →L[𝕜] 𝕜)) :
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β).compContinuousLinearMap
        (fun _ : Fin r => L) =
      ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 G r (fun i => (β i).comp L) := by
  apply ContinuousMultilinearMap.ext
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply,
      ContinuousMultilinearMap.tensorOfDualLinearForms_apply]
  rfl

/-! ## Pointwise lift via the model-fiber-level inverse iso

We define the pointwise value of the lifted section by transporting through the
multilinear bundle's fiber-level CLE (`continuousLinearEquivAt`) on each side of the
model-level inverse iso `dualMultilinearEquivMultilinearOfDual 𝕜 F r`. -/

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

/-- The pointwise lifted section value at `x`: given an element `a` of the
multilinear-of-dual bundle fiber `Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x`,
trivialize via `continuousLinearEquivAt` (for the dual bundle of `E`), apply the model-level
inverse iso, then untrivialize via the dual of `continuousLinearEquivAt` (for the multilinear
bundle of `E`). -/
noncomputable def dualLiftFiber (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜 :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
      (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a))

/-- Pointwise formula for `dualLiftFiber a`: it equals the model-level inverse iso applied
to the trivialized `a`, postcomposed with `cleBundle r x` (via `arrowCongr.symm`).
Spelled out: `dualLiftFiber r x a T = (model_inv (cle_dual a)) (cle_bundle T)`. -/
theorem dualLiftFiber_apply (r : ℕ) (x : B)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x)
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x) :
    dualLiftFiber (F := F) r x a T =
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x T) := by
  rfl

end Bundle.continuousMultilinearMap

/-! ## The dual bundle section type -/

/-- A `C^n` section of the dual of the `r`-multilinear bundle over a vector bundle `E`.
The fiber at `x` is `Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜`, i.e., continuous
linear functionals on the `r`-multilinear forms on the fiber `E x`. -/
abbrev DualBundleSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) (r : ℕ) :=
  @ContMDiffSection 𝕜 _ EB _ _ HB _ IB B _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
    _ _ n
    (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
    (Bundle.continuousMultilinearMap.dualBundleTopology r)
    (fun _ => inferInstance)
    (Bundle.continuousMultilinearMap.dualBundleFiberBundle r)

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

/-- The model-level inverse iso `(dualMME 𝕜 F r).symm`, packaged as a continuous linear map
between the model fibers. -/
noncomputable def Bundle.continuousMultilinearMap.modelDualInvCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.toLinearMap

/-- Trivialization compatibility lemma for `dualLiftFiber`. -/
theorem dualLiftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (a : Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a⟩).2 =
    Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, a⟩).2) := by
  haveI : FiniteDimensional 𝕜 (E x) :=
    Bundle.continuousMultilinearMap.fiberFiniteDimensional 𝕜 F E x
  apply (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).injective
  rw [show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual (𝕜 := 𝕜) (F := F) r)
        ((Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r) _) = _ from
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
        (𝕜 := 𝕜) (F := F) r).apply_symm_apply _]
  apply ContinuousMultilinearMap.ext
  intro β
  show (ContinuousMultilinearMap.dualMultilinearLinearMap 𝕜 F r
    (_ : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)) β = _
  rw [ContinuousMultilinearMap.dualMultilinearLinearMap_apply]
  rw [hom_trivializationAt_apply]
  have hxTriv : x ∈ (trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    show x ∈ Set.univ; trivial
  have hxMlb : x ∈ (trivializationAt
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x) x₀).baseSet := hx
  rw [ContinuousLinearMap.inCoordinates_eq hxMlb hxTriv]
  show ((Trivialization.continuousLinearEquivAt 𝕜
      (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜).comp
    ((Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a).comp
      ((Trivialization.continuousLinearEquivAt 𝕜
        (trivializationAt
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 r F E) x₀) x hxMlb).symm : _ →L[𝕜] _)))
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β) =
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
      ⟨x, a⟩).2 β
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h_cle_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜
        (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by
    intro z; rfl
  rw [h_cle_triv]
  show (Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x a)
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 r F E) x₀).symmL 𝕜 x
      (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r β)) = _
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap x₀ x hx]
  rw [Bundle.continuousMultilinearMap.dualLiftFiber_apply]
  conv_lhs =>
    rw [show Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x
          (((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
            (fun _ => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x)) =
        ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r) β).compContinuousLinearMap
          (fun _ => ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
            ((trivializationAt F E x).symmL 𝕜 x)) from rfl]
  rw [Bundle.continuousMultilinearMap.tensorOfDualLinearForms_compContinuousLinearMap_naturality]
  show (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
    (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r
      (fun i => (β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
        ((trivializationAt F E x).symmL 𝕜 x)))) = _
  have h_rt : ∀ (m : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (γ : Fin r → (F →L[𝕜] 𝕜)),
      (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm m
        (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 F r γ) = m γ := by
    intro m γ
    have := (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).apply_symm_apply m
    have h2 := congr_fun (congr_arg DFunLike.coe this) γ
    exact h2
  rw [h_rt]
  show (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x a)
    (fun i => (β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x))) = _
  show a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x)))) = _
  change a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x).symmL 𝕜 x
    ((β i).comp (((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x).comp
      ((trivializationAt F E x).symmL 𝕜 x)))) =
    a (fun i => (trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x (β i))
  congr 1
  funext i
  apply ContinuousLinearMap.ext
  intro v
  rw [Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x₀ x hx,
    Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp x x
      (mem_baseSet_trivializationAt F E x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [(trivializationAt F E x).symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt F E x)]

/-- Convert a smooth section of the multilinear bundle of the dual to a smooth section of
the dual of the multilinear bundle, via the pointwise fiber-level inverse iso `dualLiftFiber`.

Smoothness is proved by the trivialization compatibility lemma `dualLiftFiber_triv_eq`. -/
noncomputable def toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    DualBundleSection 𝕜 F IB E n r :=
  ⟨fun x => Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x (α x), by
    intro x₀
    rw [contMDiffAt_section x₀]
    have hα := (contMDiffAt_section x₀).mp α.contMDiff.contMDiffAt
    letI : NormedAddCommGroup
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
    letI : NormedSpace 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
    letI : NormedAddCommGroup
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
    letI : NormedSpace 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualInvCLM 𝕜 F r)).clm_apply
      hα).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E x₀)] with x hx
    exact dualLiftFiber_triv_eq x₀ x hx (α x)⟩

end MultilinearSection

end
