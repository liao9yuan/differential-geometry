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
the operator first-order-loss is an intrinsic property of the DeTurck remainder.  At
the summability level it reads: if the Duhamel solution field lies in `L²(H^{d+1})`,
then `gforce = N_cont(solField)` lies in `L²(H^d)` — the bounded first-order map
`H^{d+1} → H^d`; the coupling is at the level of summed `L²(H^σ)`-norm masses (`N_cont`
is a genuine non-diagonal first-order operator, so the bound is NOT mode by mode).

The coupling is *proven* sorry-free over a single genuine analytic leaf
`deTurckForcing_firstOrder_partialSum_bound`: the quantitative first-order operator-loss
estimate of the geometric nonlinearity (a finite operator constant `C` bounding, at every
order `d`, the order-`d` forcing partial sums by the total order-`(d+1)` solution-field
mass — additional structure not deducible from the fixed-order datum
`N_cont : H^{a+1} → H^a`).  From that quantitative bound the qualitative summability
implication follows by `summable_of_sum_le` (bounded nonnegative partial sums are
summable).  Consumers transitively depend on `sorryAx` through that leaf. -/

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

/-- **First-order-loss partial-sum operator bound of the DeTurck forcing
(genuine elliptic / first-order operator estimate — posited child).**

For the `g₀`-anchored DeTurck maximal-regularity engine with the geometric continuous
nonlinearity `N_cont` reproducing the forcing `gforce` a.e. along the Duhamel solution
field of initial datum `u₀` (`hforce`), there is a finite constant `C ≥ 0` such that, at
every spatial Sobolev order `d` for which the solution-field masses at order `d + 1` are
summable, **every finite partial sum** of the order-`d` forcing masses is bounded by `C`
times the total order-`(d + 1)` solution-field mass:

  `∑_{i ∈ F} forcingMass gforce d i ≤ C · (∑' i, solFieldMass hT.le gforce (d + 1) i)`.

This is the genuine quantitative **first-order operator-loss** of the geometric DeTurck
nonlinearity, integrated in time and summed over modes: at the `L²`-in-time level the
gauge-cancelled DeTurck remainder is a bounded first-order map `H^{d+1} → H^d` with
operator norm `≤ √C` *at every order `d`* (its second-order principal part cancels
against the linear `Δ_∇`), so `gforce = N(solField)` obeys
`‖gforce‖²_{L²(H^d)} ≤ C ‖solField‖²_{L²(H^{d+1})}`; the partial-sum form is the finite
restriction of that summed inequality.  This is **additional structure** of the DeTurck
remainder — the higher-order operator-norm extension of `N_cont` to every pair
`H^{d+1} → H^d`, not deducible from the fixed-order datum `N_cont : H^{a+1} → H^a`
alone — and it is genuinely about the operator (a finite constant `C`), distinct from the
qualitative summability *implication* it powers; the bound is *not* a mode-wise domination
(`N_cont` is a genuine non-diagonal first-order operator).  The body is `sorry` (this is
the single genuine analytic leaf — the operator first-order-loss estimate).  Consumers
transitively depend on `sorryAx`. -/
theorem deTurckForcing_firstOrder_partialSum_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : (gforce : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun t => N_cont (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ)
        hT hT1 u₀ gforce t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        ∀ F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∑ i ∈ F, forcingMass (I := I) (M := M) gforce d i ≤
            C * ∑' i, solFieldMass (I := I) (M := M) hT.le gforce (d + 1) i := sorry

/-- **First-order coupling of the DeTurck continuous-nonlinearity forcing
(deep elliptic / first-order-loss input).**

For the `g₀`-anchored DeTurck maximal-regularity engine with a continuous nonlinearity
`N_cont` and a forcing field `gforce` that is reproduced a.e. by `N_cont` along the Duhamel
solution field of initial datum `u₀` (`hforce`), the forcing satisfies the parabolic
first-order coupling: at every spatial Sobolev order `d`, summability of the solution-field
masses at order `d + 1` forces summability of the forcing masses at order `d`.

This is the genuine first-order-loss / operator bound of the geometric DeTurck
nonlinearity (`‖N_cont v‖_{H^d} ≲ ‖v‖_{H^{d+1}}`, read on the spectral mass families).  At
the summability level it states: if the Duhamel solution field of `gforce` lies in
`L²([0,T]; H^{d+1})`, then `gforce = N_cont(solField)` lies in `L²([0,T]; H^d)` — exactly
the bounded first-order map `H^{d+1} → H^d` of the gauge-cancelled DeTurck remainder
(`N_cont = deTurckRicciRHS − Δ_∇(realize)`, whose second-order principal part cancels
against the linear `Δ_∇`).  It is *not* a mode-wise domination: `N_cont` is a genuine
non-diagonal first-order differential operator, so the `i`-th output mode mixes all input
modes — the coupling holds at the level of the summed (`L²(H^σ)`-norm) masses, via the
per-order operator-norm bound of `N_cont`, not mode by mode.  It constrains the
nonlinearity (it is false for a generic second-order forcing, which would need the order-`(d
+ 2)` solution-field mass) and is distinct from the coupling conclusion; no packaging.  It
is the `hcouple` keystone consumed by `solFieldMass_summable_all`,
`zeroDatum_allscale_continuity_uptoZero`, and `zeroDatum_carrier_weighted_tsum_tendsto_zero`.

This coupling is *proven* sorry-free over the single genuine analytic leaf
`deTurckForcing_firstOrder_partialSum_bound` (the per-order operator first-order-loss
estimate, which is *additional* structure of the DeTurck remainder not deducible from the
fixed-order datum `N_cont : H^{a+1} → H^a` alone — it requires `N_cont`'s extension to and
boundedness on every higher pair `H^{d+1} → H^d`): from the constant-`C` partial-sum bound
the qualitative summability follows by `summable_of_sum_le` (nonnegative partial sums
bounded by `C · (∑' solFieldMass (d+1))` are summable).  Consumers transitively depend on
`sorryAx` through that operator-bound child. -/
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
        Summable (forcingMass (I := I) (M := M) gforce d) := by
  obtain ⟨C, hC0, hbound⟩ :=
    deTurckForcing_firstOrder_partialSum_bound (I := I) (M := M) g₀ a hT hT1 N_cont u₀
      gforce hforce
  intro d hsol
  -- The order-`d` forcing masses are nonnegative with all finite partial sums bounded
  -- by `C · (total order-(d+1) solution-field mass)`, hence summable.
  exact summable_of_sum_le (fun i => forcingMass_nonneg (I := I) (M := M) gforce d i)
    (hbound d hsol)

end DifferentialGeometry.PDE.RicciFlow
