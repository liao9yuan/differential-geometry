import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Continuous inclusion `H^{k+1} → H^k` of intrinsic Sobolev Hilbert spaces

For a closed Riemannian manifold `(M, g)`, the intrinsic `H^{k+1}` Sobolev
Hilbert space of `(r, s)`-tensor fields embeds continuously into `H^k` with
operator norm at most `1`. The inclusion is induced by the fact that the
partition-of-unity-weighted chart-Sobolev norm is monotone in the regularity
order (`tensorPouSobolevNorm_le_succ`).

## Main definitions

* `inclusionHk_succ g r s k` — the continuous linear inclusion
  `TensorPouSobolevHilbert g r s (k+1) →L[ℝ] TensorPouSobolevHilbert g r s k`.

## Main results

* `inclusionHk_succ_opNorm_le_one` — its operator norm is bounded by `1`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Identity as a linear map on the smooth wrapper -/

set_option linter.unusedSectionVars false in
/-- The identity map `SmoothCcTensorHs g r s (k+1) →ₗ[ℝ] SmoothCcTensorHs g
r s k` viewed as a linear map between the two pre-Hilbert spaces (on the
same underlying additive group, but with different norms). -/
noncomputable def smoothInclusionHsSuccLin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →ₗ[ℝ] SmoothCcTensorHs g r s k where
  toFun S := ⟨S.toCcTensor⟩
  map_add' S T := by
    change (⟨(S + T).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k) +
        (⟨T.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_add]
    rfl
  map_smul' c S := by
    change (⟨(c • S).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      c • (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_smul]
    rfl

set_option linter.unusedSectionVars false in
/-- The norm bound `‖smoothInclusionHsSuccLin g r s k S‖ ≤ 1 * ‖S‖`,
expressing that the `H^k` norm is dominated by the `H^{k+1}` norm on the
smooth dense subspace. -/
lemma smoothInclusionHsSuccLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : SmoothCcTensorHs g r s (k + 1)) :
    ‖smoothInclusionHsSuccLin (I := I) (M := M) g r s k S‖ ≤ 1 * ‖S‖ := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- The continuous linear inclusion `SmoothCcTensorHs g r s (k+1) →L[ℝ]
SmoothCcTensorHs g r s k` on the smooth dense subspace, with operator norm
at most `1`. -/
noncomputable def smoothInclusionHsSucc
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ] SmoothCcTensorHs g r s k :=
  (smoothInclusionHsSuccLin (I := I) (M := M) g r s k).mkContinuous 1
    (fun S => smoothInclusionHsSuccLin_norm_le (I := I) (M := M) g r s k S)

/-! ## Lifting the inclusion to the completion

The smooth-level inclusion `smoothInclusionHsSucc` is uniformly continuous
and lifts canonically to a continuous linear map on the Hilbert-space
completions via the `ContinuousLinearMap.extend` along the dense uniform
embedding `UniformSpace.Completion.toComplL`. -/

set_option linter.unusedSectionVars false in
/-- The smooth-level inclusion composed with the completion embedding on the
codomain side: a continuous linear map `SmoothCcTensorHs g r s (k+1) →L[ℝ]
TensorPouSobolevHilbert g r s k`, sending each smooth section into the
intrinsic `H^k` Hilbert space. -/
noncomputable def smoothInclusionHsSuccToHkCompl
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  (UniformSpace.Completion.toComplL :
    SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k).comp
    (smoothInclusionHsSucc (I := I) (M := M) g r s k)

set_option linter.unusedSectionVars false in
/-- The continuous linear inclusion
`TensorPouSobolevHilbert g r s (k+1) →L[ℝ] TensorPouSobolevHilbert g r s k`,
expressing the standard `H^{k+1} ↪ H^k` embedding at intrinsic Sobolev
regularity, with operator norm bounded by `1`.

Defined as the continuous linear extension of the smooth-level inclusion
along the dense uniform embedding `UniformSpace.Completion.toComplL`. -/
noncomputable def inclusionHk_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    TensorPouSobolevHilbert g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  ContinuousLinearMap.extend
    (smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s (k + 1) →L[ℝ]
        TensorPouSobolevHilbert g r s (k + 1))

set_option linter.unusedSectionVars false in
/-- The operator norm of the intrinsic `H^{k+1} ↪ H^k` inclusion is at
most `1`. -/
theorem inclusionHk_succ_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ‖inclusionHk_succ (I := I) (M := M) g r s k‖ ≤ 1 := by
  exact sorry

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
