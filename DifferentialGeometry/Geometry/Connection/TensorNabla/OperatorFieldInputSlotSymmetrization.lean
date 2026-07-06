import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS

/-!
# Input-slot symmetrization of rank-`(2,2)` operator coefficient fields

The input-slot swap `D ↦ D ∘ swap` of rank-two tensor data, as a smooth `(2,2)`-coefficient
field, and the induced input-slot symmetrization `C ↦ (1/2) • (C + C ∘ swap)` of `(2,2)`
coefficient fields (precomposition via `appCcRS`).

A `(2,2)` coefficient field acts fibrewise as a continuous linear map from rank-two tensor data
to rank-two values (`appCc`). Its input-slot symmetrization agrees with the original coefficient
on symmetric data — in particular on every datum the realized Ricci linearization feeds its
arm-0 coefficients (`ccTensorBilinSymm` symmetrizes the perturbation directions), so the
symmetrized coefficient is the honest carrier of symmetric-sector estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option linter.unusedSectionVars false in
private lemma ofModel_add {s : ℕ} {x : M}
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x) (f + g) : Tensor0SSpace s I x) =
      Tensor0SSpace.ofModel f + Tensor0SSpace.ofModel g :=
  map_add (tensor0SSpace_continuousLinearEquiv s x).symm f g

set_option linter.unusedSectionVars false in
private lemma ofModel_smul {s : ℕ} {x : M} (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x) (c • f) : Tensor0SSpace s I x) =
      c • Tensor0SSpace.ofModel f :=
  map_smul (tensor0SSpace_continuousLinearEquiv s x).symm c f

set_option linter.unusedSectionVars false in
private lemma domDomCongr_swap_add
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) (f + g) =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) f +
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) g := by
  ext m
  simp [ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
private lemma domDomCongr_swap_smul (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) (c • f) =
      c • ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) f := by
  ext m
  simp [ContinuousMultilinearMap.domDomCongr_apply]

/-- The input-slot swap on rank-two tensor fibres: `D ↦ D ∘ (swap of the two slots)`,
as a continuous linear endomorphism of `Tensor0SSpace 2 I x`. -/
def slotSwapFib (x : M) : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel (𝕜 := ℝ) D))
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, domDomCongr_swap_add, ofModel_add]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, domDomCongr_swap_smul, ofModel_smul]
        rfl }

set_option linter.unusedSectionVars false in
@[simp] lemma slotSwapFib_apply (x : M) (D : Tensor0SSpace 2 I x) :
    slotSwapFib (I := I) (M := M) x D =
      Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel (𝕜 := ℝ) D)) := rfl

/-- The input-slot swap as a `(2,2)`-coefficient fibre value. -/
def ccSlotSwapFib (x : M) : TensorRSSpace 2 2 I x :=
  slotSwapFib (I := I) (M := M) x

set_option linter.unusedSectionVars false in
theorem ccSlotSwapFib_contMDiff :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (ccSlotSwapFib (I := I) (M := M) x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => slotSwapFib (I := I) (M := M) x)
  intro Y
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  classical
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) x
      (slotSwapFib (I := I) (M := M) x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x))) : Tensor0SSpace 2 I x))) := by
    funext x; rfl
  rw [heq]
  have hYfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)))) := by
    simpa only [Tensor0SSpace.ofModel_toModel] using Y.contMDiff
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x))) :
          Tensor0SSpace 2 I x))).mpr ?_
  have hY := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)) :
      Tensor0SSpace 2 I x))).mp hYfield
  intro τ x₀
  refine (hY (τ ∘ (Equiv.swap (0 : Fin 2) 1)) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

/-- The input-slot swap of rank-two data, as a smooth `(2,2)`-coefficient field: composing a
`(2,2)` coefficient with it (via `appCcRS`) precomposes the coefficient with the swap of its two
data slots. -/
def ccSlotSwapField (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 2 where
  toSection :=
    { toFun := fun x : M => ccSlotSwapFib (I := I) (M := M) x
      contMDiff_toFun := ccSlotSwapFib_contMDiff (I := I) (M := M) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] lemma ccSlotSwapField_toSection (g : SmoothRiemannianMetric I M) (x : M) :
    (ccSlotSwapField (I := I) (M := M) g).toSection x =
      ccSlotSwapFib (I := I) (M := M) x := rfl

/-- Input-slot symmetrization of a `(2,2)` coefficient field: the average of the coefficient
with its precomposition by the data-slot swap. On symmetric data (the only data the realized
Ricci linearization applies its arm-0 coefficients to — `ccTensorBilinSymm` kills the
antisymmetric part) it acts exactly as the original coefficient. -/
def ccInputSymm (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2) :
    SmoothCcTensor g 2 2 :=
  (1 / 2 : ℝ) • (C + appCcRS (I := I) (M := M) g 2 2 2 C (ccSlotSwapField (I := I) (M := M) g))

set_option linter.unusedSectionVars false in
lemma ccInputSymm_toSection (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (x : M) :
    (ccInputSymm (I := I) (M := M) g C).toSection x =
      (1 / 2 : ℝ) • (C.toSection x +
        (show TensorRSSpace 2 2 I x from
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x).comp
            (slotSwapFib (I := I) (M := M) x))) := rfl

set_option linter.unusedSectionVars false in
/-- Input-slot symmetrization is additive in the coefficient. -/
theorem ccInputSymm_add (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2) :
    ccInputSymm (I := I) (M := M) g (C + D) =
      ccInputSymm (I := I) (M := M) g C + ccInputSymm (I := I) (M := M) g D := by
  simp only [ccInputSymm]
  rw [appCcRS_add_left]
  rw [show C + D + (appCcRS (I := I) (M := M) g 2 2 2 C (ccSlotSwapField (I := I) (M := M) g)
      + appCcRS (I := I) (M := M) g 2 2 2 D (ccSlotSwapField (I := I) (M := M) g)) =
      (C + appCcRS (I := I) (M := M) g 2 2 2 C (ccSlotSwapField (I := I) (M := M) g))
        + (D + appCcRS (I := I) (M := M) g 2 2 2 D (ccSlotSwapField (I := I) (M := M) g)) from by
    abel]
  rw [smul_add]

end Connection
end Integral
end DifferentialGeometry

end
