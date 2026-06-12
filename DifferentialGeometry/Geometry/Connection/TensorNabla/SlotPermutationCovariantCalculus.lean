import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovariantIntegrationByParts

/-! # Slot-permutation covariant calculus for `(0, s)`-tensor sections

For a closed smooth Riemannian manifold `(M, g)`, the generic covariant slot-permutation
`permuteCcTensor g σ W` (`LiftedSectionCovariantRealizeBridge`) reindexes the `Fin s` covariant
slots of a smooth compactly-supported `(0, s)`-tensor section `W` by a fixed permutation
`σ : Equiv.Perm (Fin s)`.  This file supplies the *calculus* of that operation — the pieces by
which a tail-slot coupling of an operator field to a tensor section is transported to the
leading slot, where the operator-field covariant calculus (`OperatorFieldCovariantCalculus`,
`RicciTraceCarrier`, `NablaRicciTraceCarrier`) lives:

* **Group laws** (`permuteCcTensor_permuteCcTensor`, `permuteCcTensor_refl`,
  `permuteCcTensor_symm_cancel`, `permuteCcTensor_cancel_symm`) — the slot reindexing is a
  group action on sections, proved through the unit-model extensionality
  `smoothCcTensor_ext_of_unitModel` (a `(0, s)`-tensor section is determined by its
  unit-evaluated model form).

* **Pairing invariance** (`tensorInnerPointwise_permuteCcTensor`,
  `tensorInnerScalar_permuteCcTensor`) — the simultaneous slot reindexing of both arguments
  leaves the pointwise `g`-fibre inner product of two `(0, s)`-tensor sections unchanged: the
  reindexing is a parallel fibre isometry.  This is the section-level transport of the model
  invariance `tensorInnerPointwise_0s_domDomCongr` (`PointwiseInner.SlotPermutation`) through
  the rank-`0` metric lowering (`lowerAllUpperIndices`).

* **Pairing adjunction** (`tensorInnerPointwise_permuteCcTensor_left`) — moving a slot
  reindexing from one argument of the pairing to the other inverts it:
  `⟨permute σ W, T⟩ = ⟨W, permute σ⁻¹ T⟩`.

* **Covariant-gradient commutation** (`covGrad_permuteCcTensor`,
  `tensorCovDerivAt_permuteCcTensor_unit_toModel`) — the covariant gradient of the
  slot-reindexed section is the reindexing of the covariant gradient, with the permutation
  extended by fixing the new leading (gradient) slot:
  `∇(permute σ W) = permute (decomposeFin.symm (0, σ)) (∇W)`.  The directional core is the
  proven slot-permutation naturality `tensorCovDerivAt_unit_toModel_domDomCongr_of_section`
  (`CovGradSlotPermutationNaturality`): a constant slot reindexing is a parallel bundle
  automorphism, so it commutes with the Levi-Civita covariant derivative.

* **Slot-`k`-to-front specialisation** (`covGrad_permuteCcTensor_cycleRange`,
  `permuteCcTensor_cycleRange_unitModel_apply`) — the instance `σ = Fin.cycleRange k` (the
  cycle sending `k ↦ 0`, `j ↦ j + 1` for `j < k`, fixing the slots beyond `k`) brings the
  distinguished covariant slot `k` to the front; this is the transpose `Ξ_k` by which the
  tail-slot couplings of the differentiated-curvature trace (`ParsevalSevenTermBochnerFold`)
  are reduced to the leading-slot operator-field calculus.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ### Unit-model extensionality and the group laws of the slot reindexing -/

set_option linter.unusedSectionVars false in
/-- **Unit-model extensionality for `(0, s)`-tensor sections.**  Two smooth compactly-supported
`(0, s)`-tensor sections with the same unit-evaluated model form at every point are equal: the
fibre value is a continuous linear map out of the one-dimensional `(0, 0)`-fibre, hence
determined by its value at the unit (`tensor0s_ext_unitZero`). -/
theorem smoothCcTensor_ext_of_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    {W Z : SmoothCcTensor g 0 s}
    (h : ∀ x : M, unitModel (I := I) (M := M) g s W x = unitModel (I := I) (M := M) g s Z x) :
    W = Z := by
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  have hCLM : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z.toSection x) := by
    refine tensor0s_ext_unitZero (I := I) (M := M) ?_
    apply Tensor0SSpace.toModel_injective
    exact h x
  exact hCLM

set_option linter.unusedSectionVars false in
/-- **Composition law of the slot reindexing.**  Reindexing by `ρ` and then by `σ` is the single
reindexing by `ρ.trans σ` (read the slots of the inner reindexing through the outer one). -/
theorem permuteCcTensor_permuteCcTensor (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ ρ : Equiv.Perm (Fin s)) (W : SmoothCcTensor g 0 s) :
    permuteCcTensor (I := I) g σ (permuteCcTensor (I := I) g ρ W) =
      permuteCcTensor (I := I) g (ρ.trans σ) W := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [permuteCcTensor_unitModel, permuteCcTensor_unitModel, permuteCcTensor_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
/-- **The identity slot reindexing is the identity.** -/
theorem permuteCcTensor_refl (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    permuteCcTensor (I := I) g (Equiv.refl (Fin s)) W = W := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [permuteCcTensor_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
/-- **Inverse cancellation (outer `σ`).**  `permute σ ∘ permute σ⁻¹ = id`. -/
theorem permuteCcTensor_symm_cancel (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : SmoothCcTensor g 0 s) :
    permuteCcTensor (I := I) g σ (permuteCcTensor (I := I) g σ.symm W) = W := by
  rw [permuteCcTensor_permuteCcTensor, Equiv.symm_trans_self, permuteCcTensor_refl]

set_option linter.unusedSectionVars false in
/-- **Inverse cancellation (outer `σ⁻¹`).**  `permute σ⁻¹ ∘ permute σ = id`. -/
theorem permuteCcTensor_cancel_symm (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : SmoothCcTensor g 0 s) :
    permuteCcTensor (I := I) g σ.symm (permuteCcTensor (I := I) g σ W) = W := by
  rw [permuteCcTensor_permuteCcTensor, Equiv.self_trans_symm, permuteCcTensor_refl]

/-! ### Pairing invariance and adjunction -/

set_option linter.unusedSectionVars false in
/-- **Rank-`0` metric lowering reads off the unit-evaluated model form.**  At rank `r = 0` the
separable lowering form is the unit `(0, 0)`-tensor (`separableFormAt_zero`), so the metric
lowering of the model `(0, s)`-tensor of a section value is its unit-evaluated model form
(re-derivation of the corresponding step of `CovGradSlotPermutationNaturality` from the public
ingredients). -/
private lemma lowerAllUpperIndices_zero_apply_unitModel'
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (u : Fin (0 + s) → TangentSpace I x) :
    (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))) u =
      (unitModel (I := I) (M := M) g s W x) (fun j => u (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [unitModel, unitTensor]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]
  rfl

set_option linter.unusedSectionVars false in
/-- **The slot reindexing reindexes the rank-`0` metric lowering.**  The metric lowering of the
slot-reindexed section is the slot reindexing (transported along `Fin s ≃ Fin (0 + s)`) of the
metric lowering of the original section. -/
private lemma lowerAllUpperIndices_zero_permuteCcTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) (x : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (permuteCcTensor (I := I) g σ W).toSection x)) =
      ContinuousMultilinearMap.domDomCongr
        ((finCongr (Nat.zero_add s)).permCongr.symm σ)
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))) := by
  apply ContinuousMultilinearMap.ext
  intro u
  rw [lowerAllUpperIndices_zero_apply_unitModel' (I := I) (M := M) g s
    (permuteCcTensor (I := I) g σ W) x u]
  rw [permuteCcTensor_unitModel (I := I) g σ W x, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [lowerAllUpperIndices_zero_apply_unitModel' (I := I) (M := M) g s W x]
  congr 1
  funext j
  congr 1
  rw [Equiv.permCongr_symm, Equiv.permCongr_apply]
  apply Fin.ext
  simp

set_option linter.unusedSectionVars false in
/-- **Slot-permutation invariance of the pointwise `(0, s)` pairing of sections.**  Reindexing
the covariant slots of *both* arguments by the same permutation `σ` leaves the pointwise
`g`-fibre inner product unchanged: the slot reindexing is a parallel fibre isometry.  This is
the section-level transport of `tensorInnerPointwise_0s_domDomCongr` through the rank-`0`
metric lowering. -/
theorem tensorInnerPointwise_permuteCcTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W T : SmoothCcTensor g 0 s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ W).toSection x))
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ T).toSection x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (T.toSection x)) := by
  change tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
      (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ W).toSection x)))
      (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ T).toSection x))) =
    tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
      (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)))
      (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (T.toSection x)))
  rw [lowerAllUpperIndices_zero_permuteCcTensor (I := I) (M := M) g s σ W x,
    lowerAllUpperIndices_zero_permuteCcTensor (I := I) (M := M) g s σ T x,
    tensorInnerPointwise_0s_domDomCongr]

set_option linter.unusedSectionVars false in
/-- **Pairing adjunction of the slot reindexing.**  Moving a slot reindexing from the left
argument of the pointwise pairing to the right argument inverts it:
`⟨permute σ W, T⟩ = ⟨W, permute σ⁻¹ T⟩`. -/
theorem tensorInnerPointwise_permuteCcTensor_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W T : SmoothCcTensor g 0 s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ W).toSection x))
        (TensorRSSpace.toModel (T.toSection x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x))
        (TensorRSSpace.toModel ((permuteCcTensor (I := I) g σ.symm T).toSection x)) := by
  conv_lhs => rw [show T = permuteCcTensor (I := I) g σ (permuteCcTensor (I := I) g σ.symm T) from
    (permuteCcTensor_symm_cancel (I := I) (M := M) g σ T).symm]
  exact tensorInnerPointwise_permuteCcTensor (I := I) (M := M) g s σ W
    (permuteCcTensor (I := I) g σ.symm T) x

set_option linter.unusedSectionVars false in
/-- **Slot-permutation invariance of the inner-product scalar of sections.**  The
`tensorInnerScalar` form of the pairing invariance. -/
theorem tensorInnerScalar_permuteCcTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W T : SmoothCcTensor g 0 s) (x : M) :
    tensorInnerScalar (I := I) (M := M) g 0 s
        (permuteCcTensor (I := I) g σ W).toSection
        (permuteCcTensor (I := I) g σ T).toSection x =
      tensorInnerScalar (I := I) (M := M) g 0 s W.toSection T.toSection x := by
  rw [tensorInnerScalar_apply, tensorInnerScalar_apply]
  exact tensorInnerPointwise_permuteCcTensor (I := I) (M := M) g s σ W T x

/-! ### Covariant-gradient commutation -/

set_option linter.unusedSectionVars false in
/-- **Directional covariant-derivative commutation with the slot reindexing (unit-model form).**
The unit-evaluated model form of the directional covariant derivative of the slot-reindexed
section is the slot reindexing of that of the original section.  This is the proven naturality
core `tensorCovDerivAt_unit_toModel_domDomCongr_of_section` instantiated at
`S' := permuteCcTensor g σ W` (whose unit-model relation is `permuteCcTensor_unitModel`),
re-typed into the explicit `toModel`/`tensorCovDerivAt` vocabulary. -/
theorem tensorCovDerivAt_permuteCcTensor_unit_toModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g σ W) x v)
          (unitTensor (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorCovDerivAt (I := I) (M := M) g 0 s W x v)
            (unitTensor (I := I) (M := M) x))) :=
  tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M) g s σ W
    (permuteCcTensor (I := I) g σ W)
    (fun y => permuteCcTensor_unitModel (I := I) g σ W y) x v

set_option linter.unusedSectionVars false in
/-- **The covariant gradient commutes with the slot reindexing.**  The covariant gradient of the
slot-reindexed `(0, s)`-tensor section is the slot-reindexed covariant gradient, the permutation
extended to `Fin (s + 1)` by fixing the new leading (gradient) slot:
```
∇(permute σ W) = permute (decomposeFin.symm (0, σ)) (∇W).
```
The constant slot reindexing is a parallel bundle automorphism, so it commutes with the
Levi-Civita covariant derivative (`tensorCovDerivAt_unit_toModel_domDomCongr_of_section`); the
leading-slot reading of `covGrad` (`covGrad_toSection_apply_eval`) fixes the gradient slot. -/
theorem covGrad_permuteCcTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g σ W) =
      permuteCcTensor (I := I) g (Equiv.Perm.decomposeFin.symm (0, σ))
        (covGrad (I := I) (M := M) g 0 s W) := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [permuteCcTensor_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  have hLread : unitModel (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g σ W)) x v =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g σ W) x (v 0))
        (unitTensor (I := I) (M := M) x)) (Matrix.vecTail v) :=
    covGrad_toSection_apply_eval (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g σ W) x
      (unitTensor (I := I) (M := M) x) v
  have hRread : unitModel (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s W) x
      (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s W x
          (v ((Equiv.Perm.decomposeFin.symm (0, σ)) (0 : Fin (s + 1)))))
        (unitTensor (I := I) (M := M) x))
      (Matrix.vecTail fun k : Fin (s + 1) => v ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) :=
    covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x
      (unitTensor (I := I) (M := M) x)
      (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ)) k))
  rw [hLread, ContinuousMultilinearMap.domDomCongr_apply, hRread]
  have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ)) (0 : Fin (s + 1))) = v 0 := by
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail :
      (Matrix.vecTail fun k : Fin (s + 1) =>
          v ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
        fun j : Fin s => Matrix.vecTail v (σ j) := by
    funext j
    change v ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = v (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [hzero, htail]
  rw [tensorCovDerivAt_permuteCcTensor_unit_toModel (I := I) (M := M) g s σ W x (v 0)]
  rw [ContinuousMultilinearMap.domDomCongr_apply]

/-! ### The slot-`k`-to-front specialisation `Ξ_k` -/

set_option linter.unusedSectionVars false in
/-- **The slot-`k`-to-front reading.**  Under the cycle `Fin.cycleRange k` (sending `k ↦ 0`,
`j ↦ j + 1` for `j < k`, fixing the slots beyond `k`) the unit-evaluated model form of the
transposed section reads the original section with the leading argument inserted at slot `k`. -/
theorem permuteCcTensor_cycleRange_unitModel_apply
    (g : SmoothRiemannianMetric I M) {s : ℕ} (k : Fin s)
    (W : SmoothCcTensor g 0 s) (x : M) (v : Fin s → E) :
    unitModel (I := I) (M := M) g s
        (permuteCcTensor (I := I) g (Fin.cycleRange k) W) x v =
      unitModel (I := I) (M := M) g s W x (fun j => v (Fin.cycleRange k j)) := by
  rw [permuteCcTensor_unitModel, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- **Covariant-gradient commutation with the slot-`k`-to-front transpose.**  The instance of
`covGrad_permuteCcTensor` at `σ = Fin.cycleRange k`, the transpose `Ξ_k` by which a tail-slot
coupling at slot `k` is transported to the leading slot beneath the covariant gradient. -/
theorem covGrad_permuteCcTensor_cycleRange
    (g : SmoothRiemannianMetric I M) (s : ℕ) (k : Fin s)
    (W : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 s (permuteCcTensor (I := I) g (Fin.cycleRange k) W) =
      permuteCcTensor (I := I) g (Equiv.Perm.decomposeFin.symm (0, Fin.cycleRange k))
        (covGrad (I := I) (M := M) g 0 s W) :=
  covGrad_permuteCcTensor (I := I) (M := M) g s (Fin.cycleRange k) W

end DeTurck
end PDE
end DifferentialGeometry

end
