import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.Eigenbasis
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroup
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **`L²`-maximal regularity for the connection Laplacian, predicate-free.**
For every forcing term `f ∈ L²([0,T]; TensorL2 r s g)` on a closed time
interval `[0,T]` with `0 < T ≤ 1`, the inhomogeneous heat equation
`∂_t u = Δ_∇ u + f`, `u(0) = 0`, has a unique mild solution `u`
belonging to the strong-solution space `H¹([0,T]; TensorL2 r s g)`,
with the maximal-regularity norm bound `‖u‖_{H¹} ≤ 2 · ‖f‖_{L²}`.

The statement is packaged as the existence of a bounded linear solution
operator `u = SolOp f` with operator-norm bound `2`. The two-derivative
gain `‖u‖_{L²([0,T]; H^2)} ≤ (1 + T) · ‖f‖_{L²([0,T]; L²)}` of the De Simon
form is the spectral identification of `H^2` with the resolvent's range
(intrinsic-spectral-eigenbasis α.4 + Hebey-block identification on the
POU side), and the present headline carries the structural bound only;
the `H^2`-gain refinement attaches to this operator downstream.

Predicate-free: no `HasLocallyConstantChartAt` hypothesis. -/
theorem connection_laplacian_maxreg_predicate_free
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {T : ℝ}
    (_hT : 0 < T) (_hT1 : T ≤ 1) :
    ∃ SolOp : timeL2 (TensorL2 r s g) T →L[ℝ]
        timeH1 (TensorL2 r s g) T,
      ‖SolOp‖ ≤ 2 := by
  -- The on-disk signature `∃ SolOp, ‖SolOp‖ ≤ 2` is satisfied vacuously
  -- by the zero CLM (`‖0‖ = 0 ≤ 2`). That is exactly the
  -- vacuous-witness-typed fill the user previously rejected at commit
  -- `f20b9ae`; the substantive intent (De Simon maximal-regularity:
  -- a particular `SolOp` is the Duhamel solution operator for
  -- `∂_t u = Δ_∇ u + f`) is not enforceable from the present
  -- existential alone. Until the signature is strengthened to specify
  -- *which* operator solves the inhomogeneous heat equation, this
  -- declaration remains an honest `sorry`.
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
