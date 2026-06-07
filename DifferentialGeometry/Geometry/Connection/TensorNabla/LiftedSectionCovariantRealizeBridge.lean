import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul

/-! # The lifted-section covariant bridge and the generic covariant slot-permutation

This file supplies two reusable covariant-calculus byproducts that connect the *lifted/curried*
covariant-derivative presentation used by the metric-realization plumbing
(`covDerivRealizeEval`, the model evaluation of `tensor0SCovariantDerivative ∘ liftedTensorSection`)
to the *bundled `(0, s)`-tensor* covariant gradient `covGrad` used by the iterated-jet machinery.

## The generic covariant slot-permutation

`permuteCcTensor g σ W` slot-reindexes a smooth compactly-supported covariant `(0, s)`-tensor section
`W` by a permutation `σ : Equiv.Perm (Fin s)`, producing another `SmoothCcTensor g 0 s`.  Its
unit-evaluated model form is the `domDomCongr σ` of `W`'s (`permuteCcTensor_unitModel`); since the
slot reindexing is a parallel fibre isometry, the public slot-permutation naturality
`riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` then gives that every iterated
covariant gradient `∇^i (permuteCcTensor g σ W)` has the *same* intrinsic squared fibre norm as
`∇^i W`.  This is the byproduct by which a *symmetric* covariant combination is jet-controlled by a
*single* representative summand.

## The lifted-section covariant bridge (the formalism bridge)

`covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval` identifies the unit-evaluated model `(0, 3)`-form
of the bundled covariant gradient `covGrad g₀ 0 2 (realizeSymmCcTensor g₀ T)` with the realized
covariant-derivative evaluation `covDerivRealizeEval g₀ T`:
```
toModel((covGrad g₀ 0 2 (realizeSymmCcTensor g₀ T)).toSection x unit) ![a, b, c]
  = covDerivRealizeEval g₀ T x a b c.
```
The bridge is the composite of three coherences: the leading-slot reading of `covGrad`
(`covGrad_toSection_apply_eval`), the unit-evaluation product rule against the parallel unit `(0,0)`-
section (`tensorRSCovariantDerivative_zeroS_unit_eval`, no correction term), and the rank-`0`
identification of the unit-evaluated realized section with its metric lift
(`liftedRealizeSymm_eval` / `realizeSymmCcTensor_ccTensorBilin_apply`).  It lets the realize-jet
plumbing `exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum` (a *linear*,
no-derivative-gain bound) be reused to control the covariant jets of the connection-difference-free
Koszul combination.
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
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ### The generic covariant slot-permutation of a `(0, s)`-tensor section -/

/-- **The slot-permuted `(0, s)`-tensor field.**  The smooth covariant `(0, s)`-tensor field whose
value at `x` is the model image of the slot reindexing `domDomCongr σ` of the unit-evaluated model
form of `W`.  Smoothness is the bundle naturality of the model-fibre slot reindexing: the trivialized
basis coordinate of the reindexed field at `τ` is the coordinate of the (smooth) unit-evaluated field
`unitEvalSection g s W` at the reindexed tuple `τ ∘ σ` (the forward trivialization precomposes every
slot with the same linear map, so it commutes with `domDomCongr σ`). -/
def permTensor0SField (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s :=
  ⟨fun x => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g s W x))), by
    classical
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := Module.finBasis ℝ E
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) b _).mpr ?_
    have hcc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) b
      (fun x => unitEvalSection (I := I) (M := M) g s W x)).mp
      (contMDiff_unitEvalSection (I := I) (M := M) g s W)
    intro τ x₀
    refine (hcc (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    have hbase := (trivializationAt (Tensor0SModel s ℝ E)
      (Bundle.continuousMultilinearMap ℝ s E (TangentSpace I)) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ x₀)
    filter_upwards [hbase] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    rfl⟩

/-- The slot-permuted tensor as a smooth mixed `(0, s)`-tensor section. -/
def permMixedSection (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (permTensor0SField (I := I) g σ W)

/-- **The slot-permuted `(0, s)`-tensor as a `SmoothCcTensor g 0 s`.**  Compact support is automatic
on the compact manifold `M`.  Its unit-evaluated model form is the `domDomCongr σ` of `W`'s
(`permuteCcTensor_unitModel`). -/
def permuteCcTensor (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 s where
  toSection := permMixedSection (I := I) g σ W
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The unit-evaluated model form of the slot-permuted tensor.**  `unitModel(permuteCcTensor g σ W)
= domDomCongr σ (unitModel W)`: evaluating the slot-permuted `(0, s)`-section at the unit and reading
off its model form recovers the slot reindexing of `W`'s unit-evaluated model form. -/
theorem permuteCcTensor_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (permuteCcTensor (I := I) g σ W) x =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s W x) := by
  classical
  rw [unitModel, unitModel]
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (permTensor0SField (I := I) g σ W x)
        (unitTensor (I := I) (M := M) x)) = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply]
  have hsc : (unitTensor (I := I) (M := M) x : Tensor0SSpace 0 I x) Fin.elim0 = (1 : ℝ) := by
    rfl
  rw [hsc, one_smul]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g s W x)))) = _
  rw [Tensor0SSpace.toModel_ofModel]
  congr 1

set_option linter.unusedSectionVars false in
/-- **Slot-permutation preserves the intrinsic squared fibre norm of every iterated covariant
gradient.**  For every order `i` and base point `x`,
`rfns(∇^i (permuteCcTensor g σ W))(x) = rfns(∇^i W)(x)`.  The slot reindexing is a parallel fibre
isometry: this is the public slot-permutation naturality
`riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` applied to the unit-model relation
`permuteCcTensor_unitModel`. -/
theorem riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor
    (g : SmoothRiemannianMetric I M) {s : ℕ} (σ : Equiv.Perm (Fin s))
    (W : SmoothCcTensor g 0 s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i (permuteCcTensor (I := I) g σ W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i W).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr (I := I) (M := M) g s σ
    W (permuteCcTensor (I := I) g σ W)
    (fun y => permuteCcTensor_unitModel (I := I) g σ W y) i x

/-! ### Rank-`0` unit extensionality -/

set_option linter.unusedSectionVars false in
/-- Every `(0, 0)`-tensor `D` is `tensor0Iso x D` times the unit `(0, 0)`-tensor. -/
private lemma zeroTensor_eq_smul_unitZero (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor0Iso (I := I) M x D) • unitZeroSec (I := I) (M := M) x := by
  classical
  have hunit : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  apply (tensor0Iso (I := I) M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

set_option linter.unusedSectionVars false in
/-- **Unit-extensionality for `(0, s)`-tensors.**  Two continuous linear maps
`φ, ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x` (i.e. two `(0, s)`-tensors) that agree on the
unit `(0, 0)`-tensor are equal (since `Tensor0SSpace 0 I x ≃L[ℝ] ℝ`, a map out of it is determined by
its value at the unit). -/
theorem tensor0s_ext_unitZero {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unitZero (I := I) (M := M) x D, map_smul, map_smul, h]

/-! ### The covariant-gradient front/back commutation in `rfns` form -/

set_option linter.unusedSectionVars false in
/-- The intrinsic squared fibre norm is invariant under a `HEq` of sections at `Nat`-equal covariant
ranks (the rank equality collapses the `HEq` to an `Eq` by `subst`). -/
theorem riemannianFiberNormSq_toSection_heq (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    {S : SmoothCcTensor g 0 a} {S' : SmoothCcTensor g 0 b} (hSS' : HEq S S') (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (S.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (S'.toSection x) := by
  subst h; rw [eq_of_heq hSS']

set_option linter.unusedSectionVars false in
/-- The section-level covariant gradient is `HEq`-natural in `Nat`-equal covariant ranks. -/
private theorem covGrad_heq_congr_local (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b} (hYZ : HEq Y Z) :
    HEq (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g 0 a Y)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g 0 b Z) := by
  subst h; rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **The covariant-gradient front/back commutation (section `HEq`).**  Differentiating `covGrad g 0 s`
once more by `∇^m` (carrying the new slot at the front) is `HEq` to differentiating `∇^{m+1}`:
`∇^m (∇W) ≍ ∇^{m+1} W`.  Proved by induction on `m` using the recursive definition of `iteratedCovGrad`
and the rank-`HEq` naturality of `covGrad`. -/
theorem iteratedCovGrad_covGrad_comm_heq_local (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (X : SmoothCcTensor g 0 s) :
    HEq (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (s + 1) m
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g 0 s X))
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s + 1) (j := k)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g 0 s X)]
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_local (I := I) (M := M) g
        (by omega : (s + 1) + k = s + (k + 1)) ih

/-! ### The lifted-section covariant bridge -/

set_option linter.unusedSectionVars false in
/-- **The unit-evaluated realized section equals its metric lift.**  As functions `M → Tensor0SSpace 2`,
the unit-evaluation `y ↦ (realizeSymmCcTensor g₀ T).toSection y (unit)` coincides with the metric lift
`liftedTensorSection g₀ 0 2 (realizeSymmCcTensor g₀ T).toSection`: both have unit-evaluated model form
`ccTensorBilinSymm g₀ T` (the rank-`0` metric lowering is a pure reindexing — `liftedRealizeSymm_eval`
on the lift side, `realizeSymmCcTensor_ccTensorBilin_apply` on the unit-evaluation side). -/
theorem unitEval_realizeSymm_eq_liftedTensorSection
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        (realizeSymmCcTensor (I := I) g₀ T).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      liftedTensorSection (I := I) (M := M) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T).toSection := by
  funext y
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hlift := liftedRealizeSymm_eval (I := I) g₀ T y (v 0) (v 1)
  have hunit : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        (realizeSymmCcTensor (I := I) g₀ T).toSection y)
        (unitZeroSec (I := I) (M := M) y)) ![v 0, v 1] =
      ccTensorBilinSymm (I := I) g₀ T y (v 0) (v 1) := by
    have h := realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ T y (v 0) (v 1)
    rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply] at h
    rw [unitZeroSec_apply]; convert h using 2
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, hunit, hlift]

set_option linter.unusedSectionVars false in
/-- **The lifted-section covariant bridge (formalism bridge).**  The unit-evaluated model `(0, 3)`-form
of the bundled covariant gradient `covGrad g₀ 0 2 (realizeSymmCcTensor g₀ T)` equals the realized
covariant-derivative evaluation:
```
toModel((covGrad g₀ 0 2 (realizeSymmCcTensor g₀ T)).toSection x unit) ![a, b, c]
  = covDerivRealizeEval g₀ T x a b c.
```
The chain: `covGrad_toSection_apply_eval` reads the leading (gradient) slot `a`; `tensorCovDerivAt_def`
unfolds to the bundled `(0, 2)`-tensor covariant derivative; `tensorRSCovariantDerivative_zeroS_unit_eval`
(unit-evaluation product rule against the parallel unit `(0, 0)`-section, no correction term) descends
to the abstract `tensor0SCovariantDerivative` of the unit-evaluated section; and
`unitEval_realizeSymm_eq_liftedTensorSection` identifies that section with the metric lift used by
`covDerivRealizeEval`. -/
theorem covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((covGrad (I := I) (M := M) g₀ 0 2
            (realizeSymmCcTensor (I := I) g₀ T)).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ T x a b c := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ T) x
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) ![a, b, c]]
  rw [tensorCovDerivAt_def, covDerivRealizeEval]
  have hbridge := tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g₀ 2
    (realizeSymmCcTensor (I := I) g₀ T).toSection x a
  rw [unitEval_realizeSymm_eq_liftedTensorSection] at hbridge
  rw [show (![a, b, c] 0) = a from rfl, ← hbridge]
  rfl

end DeTurck
end PDE
end DifferentialGeometry
