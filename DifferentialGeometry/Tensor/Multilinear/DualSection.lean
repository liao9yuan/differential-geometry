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

* `Bundle.continuousMultilinearMap.dualUnliftFiber` : the pointwise inverse of `dualLiftFiber`.
* `MultilinearSection.fromDualBundleSection` : convert a smooth section of the dual of the
  multilinear bundle to a smooth section of the multilinear bundle of the dual.
* `dualBundle_multilinearOfDual_equiv` : the `C^n` vector bundle equivalence (over `ℝ`).

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

/-- The pointwise inverse of `dualLiftFiber`: given `ψ : mlb r F E x →L[𝕜] 𝕜`,
trivialize via `dualBundleContinuousLinearEquivAt`, apply the model-level FORWARD iso
`dualMultilinearEquivMultilinearOfDual`, then untrivialize via `continuousLinearEquivAt`
for the multilinear-of-dual bundle. -/
noncomputable def dualUnliftFiber (r : ℕ) (x : B)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x ψ))

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

/-! ## The inverse direction: from dual bundle sections to multilinear sections -/

/-- The model-level forward iso `dualMME 𝕜 F r`, packaged as a continuous linear map
between the model fibers. Analogous to `modelDualInvCLM` but for the forward direction. -/
noncomputable def Bundle.continuousMultilinearMap.modelDualFwdCLM (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
  haveI : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := by
    haveI : FiniteDimensional 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
      continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) r
    exact (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).symm.finiteDimensional
  LinearMap.toContinuousLinearMap
    (ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
      (𝕜 := 𝕜) (F := F) r).toLinearMap

/-- Trivialization compatibility lemma for `dualUnliftFiber`. For `x` in the base set of
`trivializationAt F E x₀`, trivializing `dualUnliftFiber r x ψ` at `x₀` (in the bundle
`Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)`) equals
`modelDualFwdCLM 𝕜 F r` applied to the trivialization of `ψ` at `x₀` (in the bundle
`Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`). -/
theorem dualUnliftFiber_triv_eq {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ψ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
        ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2 =
    Bundle.continuousMultilinearMap.modelDualFwdCLM 𝕜 F r
      ((trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) x₀
        ⟨x, ψ⟩).2) := by
  -- Use the existing `dualLiftFiber_triv_eq` and the fiber-level round-trip
  -- `dualLiftFiber (dualUnliftFiber ψ) = ψ`.
  have h_rt_fiber : Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x
      (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ) = ψ := by
    show (Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x).symm
        ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
          ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
              (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x)
            ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
                (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
              ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
                ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
                    (𝕜 := 𝕜) (F := F) (E := E) r x) ψ))))) = ψ
    simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  -- Apply `dualLiftFiber_triv_eq` to `a = dualUnliftFiber ψ`:
  have h_triv := dualLiftFiber_triv_eq x₀ x hx
    (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ)
  -- h_triv: triv_dual ⟨x, dualLiftFiber (dualUnliftFiber ψ)⟩.2
  --       = modelDualInvCLM (triv_mlbdual ⟨x, dualUnliftFiber ψ⟩.2)
  rw [h_rt_fiber] at h_triv
  -- h_triv: (triv_dual ⟨x, ψ⟩).2 = modelDualInvCLM (triv_mlbdual ⟨x, dualUnliftFiber ψ⟩.2)
  -- Goal: (triv_mlbdual ...).2 = modelDualFwdCLM ((triv_dual ⟨x, ψ⟩).2)
  -- From h_triv: modelDualFwdCLM ((triv_dual).2) = modelDualFwdCLM (modelDualInvCLM (triv_mlbdual).2)
  --            = (triv_mlbdual).2   (by apply_symm_apply).
  -- h_triv says: (triv_dual ⟨x, ψ⟩).2 = modelDualInvCLM (triv_mlbdual ⟨x, dualUnliftFiber ψ⟩.2)
  -- Goal: (triv_mlbdual ⟨x, dualUnliftFiber ψ⟩).2 = modelDualFwdCLM ((triv_dual ⟨x, ψ⟩).2)
  -- Since modelDualInvCLM = (dualMME).symm as a CLM, and modelDualFwdCLM = dualMME as a CLM,
  -- from h_triv we get: dualMME ((triv_dual).2) = dualMME (dualMME.symm ((triv_mlbdual).2))
  --                                             = (triv_mlbdual).2.
  -- So the goal follows by applying dualMME to h_triv and using `apply_symm_apply`.
  set triv_mlbdual := (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) x₀
    ⟨x, Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ψ⟩).2
  -- h_triv: (triv_dual ⟨x, ψ⟩).2 = modelDualInvCLM triv_mlbdual
  -- Goal: triv_mlbdual = modelDualFwdCLM ((triv_dual ⟨x, ψ⟩).2)
  rw [h_triv]
  -- Goal: triv_mlbdual = modelDualFwdCLM (modelDualInvCLM triv_mlbdual)
  -- = dualMME (dualMME.symm triv_mlbdual) = triv_mlbdual.  ✓
  exact ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual
    (𝕜 := 𝕜) (F := F) r).apply_symm_apply triv_mlbdual).symm

/-- Convert a smooth section of the dual of the multilinear bundle to a smooth section of
the multilinear bundle of the dual, via the pointwise fiber-level forward iso `dualUnliftFiber`.

Smoothness is proved by the trivialization compatibility lemma `dualUnliftFiber_triv_eq`. -/
noncomputable def fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r :=
  ⟨fun x => Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x (ψ x), by
    intro x₀
    rw [contMDiffAt_section x₀]
    have hψ := (contMDiffAt_section x₀).mp ψ.contMDiff.contMDiffAt
    letI : NormedAddCommGroup
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
    letI : NormedSpace 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := inferInstance
    letI : NormedAddCommGroup
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
    letI : NormedSpace 𝕜
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) := inferInstance
    refine ((contMDiffAt_const
      (c := Bundle.continuousMultilinearMap.modelDualFwdCLM 𝕜 F r)).clm_apply
      hψ).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E x₀)] with x hx
    exact dualUnliftFiber_triv_eq x₀ x hx (ψ x)⟩

/-! ## Round-trip identities -/

@[simp]
theorem toDualBundleSection_fromDualBundleSection {r : ℕ}
    (ψ : DualBundleSection 𝕜 F IB E n r) :
    toDualBundleSection n (fromDualBundleSection n ψ) = ψ := by
  apply ContMDiffSection.ext; intro x
  change Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x
    (Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x (ψ x)) = ψ x
  show (Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
      (𝕜 := 𝕜) (F := F) (E := E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
      ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x)
        ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
            (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
          ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
            ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
                (𝕜 := 𝕜) (F := F) (E := E) r x) (ψ x)))))) = ψ x
  simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem fromDualBundleSection_toDualBundleSection {r : ℕ}
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) :
    fromDualBundleSection n (toDualBundleSection n α) = α := by
  apply ContMDiffSection.ext; intro x
  change Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x
    (Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x (α x)) = α x
  show (Bundle.continuousMultilinearMap.continuousLinearEquivAt
      (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x).symm
    ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
          (𝕜 := 𝕜) (F := F) (E := E) r x)
        ((Bundle.continuousMultilinearMap.dualBundleContinuousLinearEquivAt
            (𝕜 := 𝕜) (F := F) (E := E) r x).symm
          ((ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 F r).symm
            ((Bundle.continuousMultilinearMap.continuousLinearEquivAt
                (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E) r x) (α x)))))) = α x
  simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-! ## Algebraic properties -/

theorem toDualBundleSection_add {r : ℕ}
    (α β : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (α + β)).1 x =
    (toDualBundleSection n α).1 x + (toDualBundleSection n β).1 x := by
  show Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x ((α + β) x) =
    Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x (α x) +
    Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x (β x)
  simp only [Bundle.continuousMultilinearMap.dualLiftFiber, ContMDiffSection.coe_add,
    Pi.add_apply, map_add]

theorem toDualBundleSection_smulByFun {r : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 (F →L[𝕜] 𝕜) IB (Bundle.dual 𝕜 E) n r) (x : B) :
    (toDualBundleSection n (MultilinearSection.smulByFun n φ hφ α)).1 x =
    φ x • (toDualBundleSection n α).1 x := by
  show Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x
      (MultilinearSection.smulByFun n φ hφ α x) =
    φ x • Bundle.continuousMultilinearMap.dualLiftFiber (F := F) r x (α x)
  simp only [Bundle.continuousMultilinearMap.dualLiftFiber,
    MultilinearSection.smulByFun_apply, map_smul]

theorem fromDualBundleSection_add {r : ℕ}
    (ψ₁ ψ₂ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (ψ₁ + ψ₂)).1 x =
    (fromDualBundleSection n ψ₁).1 x + (fromDualBundleSection n ψ₂).1 x := by
  show Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ((ψ₁ + ψ₂) x) =
    Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x (ψ₁ x) +
    Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x (ψ₂ x)
  simp only [Bundle.continuousMultilinearMap.dualUnliftFiber, ContMDiffSection.coe_add,
    Pi.add_apply, map_add]

theorem fromDualBundleSection_smul {r : ℕ}
    (c : 𝕜) (ψ : DualBundleSection 𝕜 F IB E n r) (x : B) :
    (fromDualBundleSection n (c • ψ)).1 x =
    c • (fromDualBundleSection n ψ).1 x := by
  show Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x ((c • ψ) x) =
    c • Bundle.continuousMultilinearMap.dualUnliftFiber (F := F) r x (ψ x)
  simp only [Bundle.continuousMultilinearMap.dualUnliftFiber, ContMDiffSection.coe_smul,
    Pi.smul_apply, map_smul]

end MultilinearSection

/-! ## Bundle equivalence -/

section BundleEquiv

open MultilinearSection

variable {r : ℕ}

/-- The dual of the `r`-multilinear bundle is `C^n`-equivalent to the `r`-multilinear bundle
of the dual, as a consequence of the section characterization lemma applied to
`toDualBundleSection`/`fromDualBundleSection`.

This specializes to `𝕜 = ℝ` and requires `IsManifold`, `SigmaCompactSpace`, `T2Space`,
and `FiniteDimensional` to apply the section characterization lemma. -/
noncomputable def dualBundle_multilinearOfDual_equiv
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
    letI := Bundle.continuousMultilinearMap.dualBundleTopology
      (𝕜 := ℝ) (F := FM) (E := EM') (r := r)
    letI := Bundle.continuousMultilinearMap.dualBundleFiberBundle
      (𝕜 := ℝ) (F := FM) (E := EM') (r := r)
    letI := Bundle.continuousMultilinearMap.dualBundleVectorBundle
      (𝕜 := ℝ) (F := FM) (E := EM') (r := r)
    ContMDiffVectorBundleEquiv ℝ IM nm
      (ContinuousMultilinearMap ℝ (fun _ : Fin r => FM) ℝ →L[ℝ] ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ r FM EM' x →L[ℝ] ℝ)
      (ContinuousMultilinearMap ℝ (fun _ : Fin r => FM →L[ℝ] ℝ) ℝ)
      (fun x => Bundle.continuousMultilinearMap ℝ r (FM →L[ℝ] ℝ) (Bundle.dual ℝ EM') x) := by
  -- Construct the section-level C^nm(M,ℝ)-linear equivalence, then apply the section
  -- characterization lemma.
  let Fequiv :
      DualBundleSection ℝ FM IM EM' nm r
      ≃ₗ[C^nm⟮IM, M; ℝ⟯]
      MultilinearSection ℝ (FM →L[ℝ] ℝ) IM (Bundle.dual ℝ EM') nm r :=
    { toFun := fun ψ => fromDualBundleSection nm ψ
      invFun := fun α => toDualBundleSection nm α
      map_add' := fun ψ₁ ψ₂ => by
        apply ContMDiffSection.ext; intro x
        exact fromDualBundleSection_add nm ψ₁ ψ₂ x
      map_smul' := fun φ ψ => by
        apply ContMDiffSection.ext; intro x
        exact fromDualBundleSection_smul nm (φ x) ψ x
      left_inv := fun ψ => toDualBundleSection_fromDualBundleSection nm ψ
      right_inv := fun α => fromDualBundleSection_toDualBundleSection nm α }
  exact ContMDiffVectorBundleEquiv.ofLinearEquivSection Fequiv

end BundleEquiv

end
