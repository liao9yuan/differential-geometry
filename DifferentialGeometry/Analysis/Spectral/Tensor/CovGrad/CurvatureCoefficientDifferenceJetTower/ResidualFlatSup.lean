import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Pointwise fibre-norm inputs for the capped-top-layer flat integral

Two proof blocks extracted from
`boundedFactorGrid_cappedTopLayer_integral_flat` (`ResidualFlat.lean`) so that
each elaborates in its own Lean process; the extraction is a memory refactor
only, and the hog theorem's statement is unchanged.

- `rfnsIterCont`: continuity of `x ↦ rfns(∇ˡP)(x)`, the factor family of the
  grid.
- `jetSupLow`: the low-order pointwise fibre bound `rfns(∇ᵐP) ≤ Λ²` for `m ≤ 2`
  obtained from a jet ball, with the supercritical embedding constant `Cemb` and
  its fixed-window spec passed as parameters (so this file never touches the
  supercritical lemma).

Chunk map: `../CurvatureCoefficientDifferenceJetTower.md`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower

/-- Continuity of `x ↦ rfns(g₀, 0, 2 + l)(x)((∇ˡP).toSection x)`, the factor
family of the capped-top-layer grid. -/
theorem rfnsIterCont (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (l : ℕ) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 0 2 l P)
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P) x]

set_option linter.unusedVariables false in
/-- Low-order pointwise fibre bound from a jet ball: if the supercritical
fixed-window embedding `hCemb` holds and every jet of `P` up to order `a + 2` is
bounded by `R`, then `rfns(∇ᵐP)(x) ≤ Λ²` for all `m ≤ 2`, where
`Λ = Cemb * √(a + 2) * R`. -/
theorem jetSupLow (g₀ : SmoothRiemannianMetric I M) {a : ℕ} {R Cemb Lam : ℝ}
    (hR : 0 ≤ R)
    (hCemb : ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
      (∑ m ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m W).toSection x)) ≤
        Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2)
    (hLam : Lam = Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R)
    (P : SmoothCcTensor g₀ 0 2)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R)
    (m : ℕ) (hm : m ≤ 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
  have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
        ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
      _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤
      ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) := by
    have hmmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    exact Finset.single_le_sum
      (f := fun m' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x))
      (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m') x _) hmmem
  have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hchain : ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) ≤ Lam ^ 2 := by
    refine le_trans (hCemb P x) ?_
    rw [hLam2]
    calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
        ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
  exact le_trans hsingle hchain

end CurvatureCoefficientDifferenceJetTower

end Connection
end Integral
end DifferentialGeometry

end
