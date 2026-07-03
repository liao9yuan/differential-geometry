import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieArm2DivSlotPermA : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

def deTurckLieArm2DivSlotPermAT : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

theorem deTurckLieArm2DivSlotPermA_apply :
    deTurckLieArm2DivSlotPermA 0 = 2 ∧ deTurckLieArm2DivSlotPermA 1 = 0 ∧
      deTurckLieArm2DivSlotPermA 2 = 3 ∧ deTurckLieArm2DivSlotPermA 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem deTurckLieArm2DivSlotPermAT_apply :
    deTurckLieArm2DivSlotPermAT 0 = 3 ∧ deTurckLieArm2DivSlotPermAT 1 = 0 ∧
      deTurckLieArm2DivSlotPermAT 2 = 2 ∧ deTurckLieArm2DivSlotPermAT 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def domDomCongrFibPerm (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFibPerm_apply (σ : Equiv.Perm (Fin 4)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFibPerm (I := I) σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibPerm]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def deTurckLieTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFibPerm (I := I) σ x)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem domDomCongr_section_contMDiff_local {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem deTurckLieTraceFib_contMDiff (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (deTurckLieTraceFib (I := I) g₁ σ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => deTurckLieTraceFib (I := I) g₁ σ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff_local (I := I) σ (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]
  rfl

noncomputable def deTurckLieTraceCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x)
      contMDiff_toFun := deTurckLieTraceFib_contMDiff (I := I) g₁ σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem deTurckLieTraceCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x) := rfl

theorem deTurckLieTraceCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieTraceCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => deTurckLieTraceFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hYρ := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hCDT := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYρ
  refine hCDT.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  change deTurckLieTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1 (Y p.1) = _
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option linter.unusedVariables false in

def deTurckLieArm2PrincipalCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA
    + deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT
    - traceHessianCoeff (I := I) (M := M) g₀ g₁

theorem deTurckLieArm2PrincipalCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hA := deTurckLieTraceCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermA
  have hAT := deTurckLieTraceCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    deTurckLieArm2DivSlotPermAT
  have hH := traceHessianCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add_local (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1)
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    hA hAT
  have hsub := jointTotalSpaceRS_sub_local (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieTraceCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermA).toSection p.1
        + (deTurckLieTraceCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) deTurckLieArm2DivSlotPermAT).toSection p.1)
    (fun p : M × ℝ => (traceHessianCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hadd hH
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckLieArm2PrincipalCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

theorem deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckLieArm2PrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieArm2PrincipalCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

noncomputable def domDomCongrFibRank (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFibRank_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    domDomCongrFibRank (I := I) d σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibRank]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

private noncomputable def modelProdCLM (p q : ℕ) :
    Tensor0SBundle.Tensor0SModel p ℝ E →L[ℝ]
      Tensor0SBundle.Tensor0SModel q ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel (p + q) ℝ E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun B =>
              Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B
            map_add' := fun B B' => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [ContinuousMultilinearMap.add_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.add_apply]
              ring
            map_smul' := fun c B => by
              apply ContinuousMultilinearMap.ext
              intro v
              rw [RingHom.id_apply, ContinuousMultilinearMap.smul_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.smul_apply]
              simp only [smul_eq_mul]
              ring }
      map_add' := fun A A' => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply]
        ring
      map_smul' := fun c A => by
        apply ContinuousLinearMap.ext
        intro B
        apply ContinuousMultilinearMap.ext
        intro v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
        rw [Bundle.continuousMultilinearMap.modelProduct_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply]
        simp only [smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in

private theorem modelProdCLM_apply (p q : ℕ)
    (A : Tensor0SBundle.Tensor0SModel p ℝ E) (B : Tensor0SBundle.Tensor0SModel q ℝ E) :
    modelProdCLM (E := E) p q A B =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q A B := by
  rw [modelProdCLM]
  rfl

noncomputable def tensor0SProdKappaFib {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) :
    Tensor0SBundle.Tensor0SSpace p I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + q) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (p + q)
      x).symm.toContinuousLinearMap.comp
    (((modelProdCLM (E := E) p q).flip
        (Tensor0SBundle.Tensor0SSpace.toModel κ)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) p x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem tensor0SProdKappaFib_apply {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) (D : Tensor0SBundle.Tensor0SSpace p I x) :
    tensor0SProdKappaFib (I := I) x κ D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel D) (Tensor0SBundle.Tensor0SSpace.toModel κ)) := by
  rw [tensor0SProdKappaFib]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.flip_apply]
  rw [modelProdCLM_apply]
  rfl

private noncomputable def trilinFormToModel (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (bilinFormToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.toLinearEquiv

private theorem trilinFormToModel_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    trilinFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (bilinFormToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [show ((bilinFormToModelₗᵢ F) (B (v 0)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
      = bilinFormToModel F (B (v 0)) from rfl]
  rw [bilinFormToModel_apply]
  rfl

noncomputable def metricConnDiffLoweredTrilin (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (gm.inner x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)

set_option linter.unusedSectionVars false in

theorem metricConnDiffLoweredTrilin_apply (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    metricConnDiffLoweredTrilin (I := I) gm gA gB x a b c =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [metricConnDiffLoweredTrilin]
  rfl

noncomputable def metricConnDiffLoweredFib (gm gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (metricConnDiffLoweredTrilin (I := I) gm gA gB x))

set_option linter.unusedSectionVars false in

theorem metricConnDiffLoweredFib_toModel (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) gm gA gB x) v =
      gm.inner x (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [metricConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (metricConnDiffLoweredTrilin (I := I) gm gA gB x) v = _
  rw [trilinFormToModel_apply, metricConnDiffLoweredTrilin_apply]

noncomputable def ccBilinConnDiffLoweredTrilin (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (ccTensorBilinSymm (I := I) g₀ V x)).comp
    (PDE.DeTurck.connDiff (I := I) gA gB x)

set_option linter.unusedSectionVars false in

theorem ccBilinConnDiffLoweredTrilin_apply (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x a b c =
      ccTensorBilinSymm (I := I) g₀ V x (PDE.DeTurck.connDiff (I := I) gA gB x a b) c := by
  rw [ccBilinConnDiffLoweredTrilin]
  rfl

noncomputable def ccBilinConnDiffLoweredFib (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (trilinFormToModel (TangentSpace I x) (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x))

set_option linter.unusedSectionVars false in

theorem ccBilinConnDiffLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x) v =
      ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (v 0) (v 1)) (v 2) := by
  rw [ccBilinConnDiffLoweredFib, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  change (trilinFormToModel (TangentSpace I x))
      (ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) v = _
  rw [trilinFormToModel_apply, ccBilinConnDiffLoweredTrilin_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem trilinKernel_section_contMDiff
    (K : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hK : ∀ (Y0 Y1 Y2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M => K x (Y0 x) (Y1 x) (Y2 x)) x₀) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (trilinFormToModel (TangentSpace I x) (K x)))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x : M => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (trilinFormToModel (TangentSpace I x) (K x)) :
          Tensor0SBundle.Tensor0SSpace 3 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  refine (hK (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) x₀).congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
    rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  have hframe2 : e₁.symmL ℝ x (b (σ 2)) = (Y (σ 2)) x := by
    rw [hYx (σ 2), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (trilinFormToModel (TangentSpace I x) (K x))
      (fun j : Fin 3 => e₁.symmL ℝ x (b (σ j))) = _
  rw [trilinFormToModel_apply]
  rw [hframe0, hframe1, hframe2]

theorem metricConnDiffLoweredFib_contMDiff (gm gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (metricConnDiffLoweredFib (I := I) gm gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => metricConnDiffLoweredTrilin (I := I) gm gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) gm
      ⟨fun x => PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x), hconn⟩ Y2
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [metricConnDiffLoweredTrilin_apply]

theorem ccBilinConnDiffLoweredFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (ccBilinConnDiffLoweredFib (I := I) g₀ V gA gB x)) := by
  refine trilinKernel_section_contMDiff (I := I)
    (K := fun x => ccBilinConnDiffLoweredTrilin (I := I) g₀ V gA gB x) ?_
  intro Y0 Y1 Y2 x₀
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gA gB Y0.contMDiff Y1.contMDiff
  have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, ccTensorBilinSymm (I := I) g₀ V x
        (PDE.DeTurck.connDiff (I := I) gA gB x (Y0 x) (Y1 x)) (Y2 x)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
    (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      (ccTensorBilinSymm_contMDiff (I := I) g₀ V).contMDiffOn hconn.contMDiffOn
      Y2.contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
  rw [Bundle.contMDiffAt_totalSpace] at h_total
  refine (h_total.2).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [ccBilinConnDiffLoweredTrilin_apply]
  rfl

def deTurckLieArm1PairPermCorr : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 1, 3, 5], ![1, 3, 2, 4, 0, 5], by decide, by decide⟩

def deTurckLieArm1PairPermOuterZero : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermOuterTwo : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 1, 3], ![0, 4, 2, 5, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermInnerTwo : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 5, 1, 3], ![1, 4, 2, 5, 0, 3], by decide, by decide⟩

def deTurckLieArm1VecSlotPerm : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

def deTurckLieArm1KoszulMidPerm : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def deTurckLieArm1KoszulZeroPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

noncomputable def deTurckLiePairTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (κ : Tensor0SBundle.Tensor0SSpace 3 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp
      ((cometricDoubleTraceFib (I := I) g₁ 4 x).comp
        (domDomCongrFibRank (I := I) 6 σ x))).comp
    (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x κ)

noncomputable def deTurckLieKoszulTraceFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x).comp
    ((cometricDoubleTraceFib (I := I) g₁ 1 x).comp
      (domDomCongrFibRank (I := I) 3 σ x))

noncomputable def deTurckLieArm1CoreFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermInnerTwo x
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermCorr x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    - (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)).comp
        (domDomCongrFibRank (I := I) 3 deTurckLieArm1VecSlotPerm x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterZero x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulMidPerm x
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)

noncomputable def deTurckLieArm1Fib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    + deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x
    + (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x).comp
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x)
    + deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulZeroPerm x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem tensor0SProd_section_contMDiff {p q : ℕ}
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace p I x)
    (K : ∀ x : M, Tensor0SBundle.Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
            (Tensor0SBundle.Tensor0SSpace.toModel (K x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
          (Tensor0SBundle.Tensor0SSpace.toModel (K x))) :
          Tensor0SBundle.Tensor0SSpace (p + q) I x))).mpr ?_
  have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Y x)).mp hY
  have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => K x)).mp hK
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
        (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)) (Tensor0SBundle.Tensor0SSpace.toModel (K x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLiePairTraceFib_apply_section_contMDiff
    (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6))
    (κ : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (κ x)))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLiePairTraceFib (I := I) g₁ σ x (κ x) (Y x))) := by
  classical
  have hprod := tensor0SProd_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => Y x) κ Y.contMDiff hκ
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 6) σ
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
        (Tensor0SBundle.Tensor0SSpace.toModel (κ x)))) hprod
  have htr4 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 4) hperm
  have htr2 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) htr4
  refine htr2.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLieKoszulTraceFib_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x (Y x))) := by
  classical
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 3) σ
    (fun x => Y x) Y.contMDiff
  have htr1 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) hperm
  have hkos := ContMDiff.clm_bundle_apply (b := id)
    (connDiffFib_contMDiff (I := I) g₁ g₀) htr1
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply]
  rfl

set_option linter.unusedSectionVars false in

private theorem deTurckLieArm1CoreFib_apply_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hS2 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermInnerTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hB := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermCorr
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg) Y
  have hpermY := domDomCongr_section_contMDiff_local (I := I) (d := 3)
    deTurckLieArm1VecSlotPerm (fun x => Y x) Y.contMDiff
  have hT2 := interiorProductField_contMDiff (I := I) 2
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))) hpermY
    (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)
  have hT3 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterZero
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hT4 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hsum := ((((hS2.sub_section hB).sub_section hT2).sub_section hT3).sub_section
    hT4).sub_section hT5
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

theorem deTurckLieArm1Fib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hW := interiorProductField_contMDiff (I := I) 2 (fun x => Y x) Y.contMDiff
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg)
  have hcore := deTurckLieArm1CoreFib_apply_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hcoreswap := domDomCongr_section_contMDiff_local (I := I) (d := 2)
    (Equiv.swap (0 : Fin 2) 1)
    (fun x => deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x)) hcore
  have hS3 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulZeroPerm Y
  have hsum := ((hW.add_section hcore).add_section hcoreswap).add_section hS3
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

noncomputable def deTurckLieArm1Coeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
      contMDiff_toFun := deTurckLieArm1Fib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem deTurckLieArm1Coeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x) := rfl

private theorem jointTotalSpace0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

private theorem jointTotalSpace0S_sub_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem jointTotalSpace0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

private theorem jointTensor0SProd_local {p q : ℕ} {S : Set ℝ}
    (A : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace p I pp.1)
    (B : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace q I pp.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) pp.1 (A pp))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) pp.1 (B pp))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) pp.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := pp.1)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
            (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) p
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) q
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + q)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel q ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z)).mp (hB p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E) ∞
      (fun pp : M × ℝ => modelProdCLM (E := E) p q
        ((trivializationAt (Tensor0SBundle.Tensor0SModel p ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x₀ ⟨pp.1, A pp⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel q ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x₀ ⟨pp.1, B pp⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := modelProdCLM (E := E) p q)).clm_apply
      hA'.2).clm_apply hB'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Filter.univ_mem] with pp _
    apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  · apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl

private theorem realizedFam_chartDeTurckVFComp_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_chartDeTurckVFComp (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG g_bg k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

private theorem deTurckVFChartLocal_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1) •
            chartBasisVecFiber (I := I) α k p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hcoeff : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun k => realizedFam_chartDeTurckVFComp_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg α k
  set e := trivializationAt E (TangentSpace I) α with he
  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2 =
        ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            (chartModelBasis E) k := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [trivializationAt_chartBasisVec_snd (I := I) α k hqbase]
  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finset_sum (fun k _ => ?_)
    exact (hcoeff k).smul contMDiffOn_const
  haveI : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

theorem deTurckVF_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
          Π b : M, TangentSpace I b) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp
  have hlocal := deTurckVFChartLocal_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg p.1
  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (∑ k : Fin (Module.finrank ℝ E),
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
              chartBasisVecFiber (I := I) p.1 k q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg :
            Π b : M, TangentSpace I b) q.1) := by
    rintro q ⟨hqx, _⟩
    have hqgood : q.1 ∈ chartLeviCivitaGoodSet (I := I) p.1 := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I), extChartAt_source (I := I)]
      exact hqx
    rw [PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 hqgood]
  have hpmem : p ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') :=
    ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') ∈
      nhdsWithin p ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (chartAt H p.1).open_source.prod realizedSmallSet_isOpen, hpmem, fun q hq => hq.1⟩
  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
            chartBasisVecFiber (I := I) p.1 k q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd
  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

private def arm1LowerSwapPermA : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def arm1LowerSwapPermC : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

private noncomputable def covGradSymmSValue (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SBundle.Tensor0SSpace 3 I x :=
  (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ V)).toSection x)
    (unitTensor (I := I) (M := M) x)

set_option linter.unusedSectionVars false in

private theorem covGradSymmSValue_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (covGradSymmSValue (I := I) g₀ V x)) := by
  have h := ContMDiff.clm_bundle_apply (b := id)
    (covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ V)).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  refine h.congr (fun x => ?_)
  rfl

set_option linter.unusedSectionVars false in

private theorem covGradSymmSValue_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) :
    covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x =
      (1 - s) • covGradSymmSValue (I := I) g₀ T' x +
        s • covGradSymmSValue (I := I) g₀ T x := by
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2
      (symmS (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) =
      (1 - s) • covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T')
        + s • covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) := by
    rw [convexPerturbation, symmS_add, symmS_smul, symmS_smul, covGrad_add,
      covGrad_smul, covGrad_smul]
  rw [covGradSymmSValue, hsplit, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul]
  rfl

set_option linter.unusedVariables false in

private theorem covGradSymmSValueFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hP' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T' p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T').comp_contMDiffOn contMDiffOn_fst
  have hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T' p.1) hP'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T p.1) hP
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (1 - p.2) • covGradSymmSValue (I := I) g₀ T' p.1)
    (fun p : M × ℝ => p.2 • covGradSymmSValue (I := I) g₀ T p.1) h1 h2
  refine hsum.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [covGradSymmSValue_convexPerturbation]

private theorem connDiff_split_middle (gA gC gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v +
        PDE.DeTurck.connDiff (I := I) gC gB x u v := by
  classical
  set σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x u, smoothExtensionTangent_contMDiff (I := I) x u⟩ with hσdef
  have hσx : σ x = u := smoothExtensionTangent_eq (I := I) x u
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (σ y)) x :=
    (σ.contMDiff x).mdifferentiableAt (by simp)
  have h1 := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => σ y) hmd v
  have h2 := PDE.DeTurck.connDiff_apply (I := I) gA gC (σ := fun y => σ y) hmd v
  have h3 := PDE.DeTurck.connDiff_apply (I := I) gC gB (σ := fun y => σ y) hmd v
  rw [hσx] at h1 h2 h3
  rw [h1, h2, h3]
  exact (sub_add_sub_cancel _ _ _).symm

set_option linter.unusedSectionVars false in

private theorem metricConnDiffLoweredFib_split (gm gA gC gB : SmoothRiemannianMetric I M)
    (x : M) :
    metricConnDiffLoweredFib (I := I) gm gA gB x =
      metricConnDiffLoweredFib (I := I) gm gA gC x +
        metricConnDiffLoweredFib (I := I) gm gC gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, metricConnDiffLoweredFib_toModel,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    connDiff_split_middle (I := I) gA gC gB, map_add, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in

private theorem metricConnDiffLowered_fixedPair_affine (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gB : SmoothRiemannianMetric I M) {s : ℝ}
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) :
    metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ gB x =
      metricConnDiffLoweredFib (I := I) g₀ g₀ gB x
        + (1 - s) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ gB x
        + s • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    ccBilinConnDiffLoweredFib_toModel, ccBilinConnDiffLoweredFib_toModel]
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    ccTensorBilinSymm_convexPerturbation]
  simp only [smul_eq_mul]
  ring

private theorem metricConnDiffLowered_selfFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set Vfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1 :=
    fun p => covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1
    with hVfamdef
  have hV : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Vfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    covGradSymmSValueFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hU1 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hU3 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermC
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    Vfam hU1 hV
  have hsub := jointTotalSpace0S_sub_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
          (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p)
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsum hU3
  have hhalf := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const
    (fun p : M × ℝ =>
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p) -
        Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsub
  refine hhalf.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  apply ContinuousMultilinearMap.ext
  intro v
  rw [metricConnDiffLoweredFib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner b u w =
        g₀.inner b u w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) b u w :=
    fun b u w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hp.2 b u w
  have hid := connDiffInner_g1_eq_half_covGradSymmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (convexPerturbation (I := I) g₀ T T' p.2) hg₁ p.1 (v 0) (v 1) (v 2)
  rw [hid]
  have h1 : (fun j => v (arm1LowerSwapPermA j)) = ![v 1, v 0, v 2] := by
    funext j; fin_cases j <;> rfl
  have h3 : (fun j => v (arm1LowerSwapPermC j)) = ![v 2, v 1, v 0] := by
    funext j; fin_cases j <;> rfl
  rw [h1, h3]
  have huM : ∀ vv : Fin 3 → TangentSpace I p.1,
      unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2
          (symmS (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2))) p.1 vv =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) vv := fun vv => rfl
  rw [huM ![v 1, v 0, v 2], huM ![v 0, v 1, v 2], huM ![v 2, v 1, v 0]]
  have hv012 : Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) v =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) ![v 0, v 1, v 2] := by
    congr 1
    funext j; fin_cases j <;> rfl
  rw [hv012]
  simp only [smul_eq_mul]

private theorem metricConnDiffLowered_bgFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hself := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hfix0 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T' g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1) hfixT'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1) hfixT
  have hsum1 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1)
    (fun p : M × ℝ => (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    hfix0 h1
  have hsum2 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
      (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    (fun p : M × ℝ => p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hsum1 h2
  have hsum3 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
        (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1 +
      p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hself hsum2
  refine hsum3.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [metricConnDiffLoweredFib_split (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ g_bg p.1]
  congr 1
  exact metricConnDiffLowered_fixedPair_affine (I := I) g₀ T T' hδ hδ' g_bg hp.2 p.1

private theorem connDiffFib_comp_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SBundle.Tensor0SSpace 1 I x) :
    (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x) om =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x om)) := by
  rw [connDiffFib_apply, raisedKoszulFib_apply]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [connDiffPairing_apply, raisedKoszulPairing_apply]
  set D : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hD
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  have hLHS : om (fun _ : Fin 1 => D) = g₁.inner x u D := by
    rw [← cotangentToDual_apply (I := I) (x := x) om D]
    rw [show cotangentToDual (I := I) (x := x) om D
          = cotangentToDualLinear (I := I) (x := x) om D from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₁ x om D]
  rw [hLHS]
  set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hPdef
  rw [show (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u)
        (fun _ : Fin 1 => P)
      = cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x u) P from
      (cotangentToDual_apply (I := I) (x := x) _ P).symm]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₀ x u P]
  rw [g₀.symm x u P]
  have hPval : P = inverseMetricSharpFib (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) := by
    rw [hPdef, raisedKoszulVec_apply]
  have hPinner : g₀.inner x P u = cotangentToDual (I := I) (x := x)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u := by
    rw [hPval,
      show cotangentToDual (I := I) (x := x)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        = cotangentToDualLinear (I := I) (x := x)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u
        from rfl]
    rw [inverseMetricSharpFib_inner (I := I) g₀ x
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₁ x D) u]
  rw [hPinner, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g₁ x D u]
  rw [g₁.symm x D u, hu]

private theorem deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieKoszulTraceFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have htr1 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 1)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))))
    hperm
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') htr1
  have hflatfield : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ]
      Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) p.1
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (g0FlatField_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have hflat := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflatfield hsharp
  have hkos := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (corrField_raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hflat
  refine hkos.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply, connDiffFib_comp_eq]

private theorem deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (σ : Equiv.Perm (Fin 6))
    (κfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1)
    (hκ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (κfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLiePairTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) σ p.1
          (κfam p) (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hprod := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Y p.1) κfam hYjoint hκ
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
        (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))) hprod
  have htr4 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 4)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
              (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
              (Tensor0SBundle.Tensor0SSpace.toModel (κfam p)))))))
    hperm
  have htr2 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
    g₀ T T' hδ hδ'
    (fun p : M × ℝ => cometricDoubleTraceFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 4 p.1
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
              (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
                (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))
                (Tensor0SBundle.Tensor0SSpace.toModel (κfam p))))))))
    htr4
  refine htr2.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]

private theorem deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1CoreFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hκA := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hκB := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hS2 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermInnerTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hB := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermCorr
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    hκB Y
  have hpermY := domDomCongrField_jointContMDiffOn (I := I) deTurckLieArm1VecSlotPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hW0 := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hT2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ : Π b : M, TangentSpace I b) p.1) hW0
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hpermY
  have hT3 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterZero
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hT4 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTrace_realizedFam_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
    deTurckLieArm1PairPermOuterTwo
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    hκA Y
  have hs1 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hS2 hB
  have hs2 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs1 hT2
  have hs3 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs2 hT3
  have hs4 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs3 hT4
  have hs5 := jointTotalSpace0S_sub_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hs4 hT5
  refine hs5.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

private theorem deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hWbg := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hW := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg : Π b : M, TangentSpace I b) p.1) hWbg
    (fun p : M × ℝ => Y p.1) hYjoint
  have hcore := deTurckLieArm1CoreFib_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' g_bg Y
  have hcoreswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => deTurckLieArm1CoreFib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1)) hcore
  have hS3 := deTurckLieKoszulTrace_realizedFam_apply_jointContMDiffOn (I := I)
    g₀ T T' hδ hδ' deTurckLieArm1KoszulZeroPerm Y
  have ha1 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hW hcore
  have ha2 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha1 hcoreswap
  have ha3 := jointTotalSpace0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ ha2 hS3
  refine ha3.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]

theorem deTurckLieArm1Coeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        ((deTurckLieArm1Coeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      deTurckLieArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => deTurckLieArm1Fib_realizedFam_apply_jointContMDiffOn (I := I)
      g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
  rw [deTurckLieArm1Coeff_toSection]

theorem deTurckLieArm1Coeff_realizedFam_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => deTurckLieArm1Coeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  deTurckLieArm1Coeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ' g_bg

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
