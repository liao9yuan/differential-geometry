import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral

/-!
# Algebra of jointly smooth three-arm coefficient families

This module records the additive and scalar closure properties of
`linearizedRicciThreeArmHjoint`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- Jointly smooth three-arm coefficient families are closed under
fibrewise addition. -/
theorem threeArmJoint_add
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g r B
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA hB ⊢
  have h := joint_rs_add (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- Jointly smooth three-arm coefficient families are closed under
fibrewise subtraction. -/
theorem threeArmJoint_sub
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g r B
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA hB ⊢
  have h := joint_rs_sub (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- Jointly smooth three-arm coefficient families are closed under
constant scalar multiplication. -/
theorem threeArmJoint_smul
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (c : ℝ) (A : ℝ → SmoothCcTensor g r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g r A
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun s => c • A s) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint] at hA ⊢
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r 2
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r 2 ℝ E)
    (fun z : M => TensorRSSpace r 2 I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r 2 ℝ E)
    (E := fun z : M => TensorRSSpace r 2 I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ
          realizedSmallSet (δ := δ) (δ' := δ')),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))
        (p := p₀))
        (e.open_baseSet.mem_nhds
          (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hp
    exact (e.linear ℝ hp).map_smul c ((A p.2).toSection p.1)
  · exact (e.linear ℝ
      (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
        c ((A p₀.2).toSection p₀.1)

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end
