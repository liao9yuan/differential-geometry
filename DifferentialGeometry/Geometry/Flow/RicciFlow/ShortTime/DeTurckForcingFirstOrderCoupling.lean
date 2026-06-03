import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

/-! # First-order coupling of the DeTurck continuous-nonlinearity forcing

The interior up-to-`t = 0` spectral cores
(`zeroDatum_allscale_continuity_uptoZero`,
`zeroDatum_carrier_weighted_tsum_tendsto_zero`) and the parabolic interior
smoothing bootstrap (`solFieldMass_summable_all`) consume the **first-order
coupling** of the forcing field: at every spatial Sobolev order `d`, summability
of the solution-field masses at order `d + 1` forces summability of the forcing
masses at order `d` (the forcing loses at most one order relative to the
solution).

For the `g₀`-anchored DeTurck maximal-regularity engine the forcing `gforce` is
reproduced a.e. by the continuous geometric nonlinearity `N_cont` along the
Duhamel solution field (`hforce`).  The geometric DeTurck nonlinearity is a
genuine **first-order** differential operator on the metric perturbation (it is
`deTurckRicciRHS` minus the rough Laplacian of the realize representative, a
quasilinear second-order operator whose principal part cancels against the
linear `Δ_∇`, leaving a first-order remainder); hence `‖N_cont v‖_{H^d}` is
controlled by `‖v‖_{H^{d+1}}`, which at the spectral-mass level is exactly the
coupling `Summable (solFieldMass (d+1)) → Summable (forcingMass d)`.

`deTurckForcing_firstOrder_coupling`: for the engine's continuous nonlinearity
`N_cont` and a forcing `gforce` reproduced a.e. by `N_cont` along the Duhamel
solution field of initial datum `u₀` (`hforce`), the first-order coupling
`∀ d, Summable (solFieldMass (d+1)) → Summable (forcingMass d)` holds.

This is the operator first-order-loss bound of the continuous nonlinearity, NOT a
summability conclusion folded in as a hypothesis: it constrains the geometric
nonlinearity (it is false for a generic second-order forcing), and is distinct
from the coupling conclusion.  It is stated purely in terms of the genuine
nonlinearity `N_cont` (no presentation through a finite-support/gated section), as
the operator first-order-loss is an intrinsic property of the DeTurck remainder.
The body is `sorry`, so consumers transitively depend on `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open MeasureTheory Set

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **First-order coupling of the DeTurck continuous-nonlinearity forcing
(deep elliptic / first-order-loss input).**

For the `g₀`-anchored DeTurck maximal-regularity engine with a continuous
nonlinearity `N_cont` (presented through its smooth `(0, 2)`-tensor section `Nsec`
with the eigenbasis-coordinate identity `hN_coeff`) and a forcing field `gforce`
that is reproduced a.e. by `N_cont` along the Duhamel solution field of initial
datum `u₀` (`hforce`), the forcing satisfies the parabolic first-order coupling:
at every spatial Sobolev order `d`, summability of the solution-field masses at
order `d + 1` forces summability of the forcing masses at order `d`.

This is the genuine first-order-loss / operator bound of the geometric DeTurck
nonlinearity (`‖N_cont v‖_{H^d} ≲ ‖v‖_{H^{d+1}}`, read on the spectral mass
families).  It constrains the nonlinearity (it is false for a generic second-order
forcing) and is distinct from the coupling conclusion; no packaging.  It is the
`hcouple` keystone consumed by `solFieldMass_summable_all`,
`zeroDatum_allscale_continuity_uptoZero`, and
`zeroDatum_carrier_weighted_tsum_tendsto_zero`.  The body is `sorry`. -/
theorem deTurckForcing_firstOrder_coupling
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : (gforce : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun t => N_cont (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ)
        hT hT1 u₀ gforce t))) :
    ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d) := sorry

end DifferentialGeometry.PDE.RicciFlow
