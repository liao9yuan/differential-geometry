import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSq
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceNormBridge
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Auxiliary scalars for bounding `riemannianFiberNormSq`

For a smooth Riemannian metric `g` on a smooth manifold `M`, this file declares the
basis-and-metric-dependent scalar `pointwiseBoundScalar g b`, built from
`metricInnerOpNorm g b` (the bilinear operator norm of `g.inner b`) and the
`E`-norms-squared of the `g`-orthonormal basis vectors used inside
`riemannianFiberNormSq`. This is the pointwise ingredient that downstream uniform
bounds package via a finite chart cover.

## Main declarations

* `orthoBasisSumNormSq g b` — the sum of `‖e i‖²` for `e` the `stdOrthonormalBasis`
  of `(TangentSpace I b, g.inner b)`.
* `pointwiseBoundScalar g b` — `1 + metricInnerOpNorm g b + orthoBasisSumNormSq g b`.
* Basic non-negativity / one-bound lemmas for both.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Bundle Set IsManifold ContinuousLinearMap Function
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Auxiliary scalar quantities -/

/-- The sum of `E`-norms-squared of the `g`-orthonormal basis vectors used inside
`riemannianFiberNormSq` at the base point `b`. Concretely, it is
`∑ i, ‖e i‖²` for `e` the `stdOrthonormalBasis` of `(TangentSpace I b, g.inner b)`,
with the norm taken in the locally-installed `g`-induced norm (so each
`‖e i‖ = 1` in that local norm). The constructor for the local `InnerProductSpace`
is taken from `RiemannianMetric.toCore` and
`InnerProductSpace.ofCoreOfTopology`; we then build the sum
`∑ i, ‖e i‖²`. -/
noncomputable def orthoBasisSumNormSq
    (g : SmoothRiemannianMetric I M) (b : M) : ℝ := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  exact ∑ i : Fin n, ‖e i‖ ^ 2

lemma orthoBasisSumNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) :
    0 ≤ orthoBasisSumNormSq (I := I) (M := M) g b := by
  unfold orthoBasisSumNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The pointwise bounding scalar at `b`:
`1 + metricInnerOpNorm g b + orthoBasisSumNormSq g b`, guaranteed to be `≥ 1`. -/
noncomputable def pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) : ℝ :=
  1 + metricInnerOpNorm (I := I) (M := M) g b +
    orthoBasisSumNormSq (I := I) (M := M) g b

lemma pointwiseBoundScalar_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) :
    0 ≤ pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

lemma pointwiseBoundScalar_one_le
    (g : SmoothRiemannianMetric I M) (b : M) :
    1 ≤ pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

lemma metricInnerOpNorm_le_pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) :
    metricInnerOpNorm (I := I) (M := M) g b ≤
      pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

lemma orthoBasisSumNormSq_le_pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) :
    orthoBasisSumNormSq (I := I) (M := M) g b ≤
      pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  linarith

end Connection
end Integral
end DifferentialGeometry

/-! ## Sanity check: axioms used. -/

open DifferentialGeometry.Integral.Connection in
#print axioms pointwiseBoundScalar_one_le

end
