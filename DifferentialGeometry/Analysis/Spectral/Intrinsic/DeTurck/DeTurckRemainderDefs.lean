import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv

/-!
# The smooth Ricci–DeTurck remainder and the smooth-tensor spectral embedding (shared defs)

This file hosts the two **shared** definitions used by both the smooth-ball Lipschitz tower
(`DeTurckRemainderTameLipschitz.lean`) and the Sobolev nonlinearity existence assembly
(`SobolevNonlinearityExistence.lean`):

* `deTurckSmoothRemainder` — the genuine Ricci–DeTurck remainder of a smooth fibre-small
  perturbation, as a smooth `(0,2)`-tensor
  `deTurckRHSSection g_bg (g₀ + T) − rawTensorConnLapSmooth g₀ 0 2 T`.
* `smoothCcToTensorHs` — the canonical embedding of smooth compactly-supported tensors into
  the spectral Sobolev scale `tensorHs g₀ 0 2 σ` (the `L²`-coordinate read-off).

Both definitions use the **sorry-free intrinsic objects directly** — no chart-rough evaluation
and no finite-support / `realizableAt` gating.  They live here, upstream of the tame-Lipschitz
tower, so that the tower (which consumes them) does not import the existence assembly that
consumes the tower's ball-uniform bound.
-/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The genuine Ricci–DeTurck remainder of a SMOOTH fibre-small perturbation, as a smooth
`(0,2)`-tensor.**

For the initial metric `g₀`, DeTurck background `g_bg`, and a smooth compactly-supported
`(0,2)`-tensor `T` whose symmetrization is `g₀`-fibre small with constant `δ < 1` (so
`g₀ + T` is a genuine `SmoothRiemannianMetric` via `tensorSectionRealizeMetric`), this is
the smooth tensor

  `deTurckRHSSection g_bg (g₀ + T) − rawTensorConnLapSmooth g₀ 0 2 T`

(the intrinsic Ricci–DeTurck right-hand side of the realized metric, minus the connection
Laplacian of the perturbation — the gauge-cancelled first-order remainder).  Because the
input is smooth this uses the **sorry-free intrinsic objects directly**: no chart-rough
evaluation, no finite-support / `realizableAt` gating. -/
def deTurckSmoothRemainder (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }
  - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

/-- **The canonical embedding of smooth tensors into the spectral Sobolev scale.**

A smooth compactly-supported `(0,2)`-tensor `T` is sent to the order-`σ` spectral element
whose eigenbasis coordinates are the `L²` coordinates of `T` (`SmoothCcTensor.toL2 T`).  Its
`H^σ` membership is `smoothCcTensor_tensorL2Coeff_weighted_summable` (smooth data is in every
`H^σ`).  This is the genuine, total, non-gating inclusion `SmoothCcTensor g₀ 0 2 → H^σ`. -/
def smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    tensorHs (I := I) (M := M) g₀ 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

/-- The eigenbasis coordinate of the smooth-tensor embedding is the `L²` coordinate of `T`. -/
@[simp] theorem smoothCcToTensorHs_coeff (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
