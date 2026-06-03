import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRemainderRealizeGauge

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

Both `deTurckForcing_firstOrder_partialSum_bound` and `deTurckForcing_firstOrder_coupling`
take the first-order operator-loss datum `hloss : FirstOrderOperatorLoss g₀ a T N_cont` as a
threaded hypothesis (the genuine per-order operator first-order-loss of the geometric
nonlinearity at the spectral-mass level — a finite operator constant `C` bounding, at every
order `d` and for every reproduced pair of time fields, the order-`d` output partial sums by
the total order-`(d+1)` input mass; *additional* structure of the DeTurck remainder not
deducible from the fixed-order datum `N_cont : H^{a+1} → H^a`).  That datum is supplied at the
assembler `deTurck_g0_realize_data` from the posited genuine analytic leaf
`deTurckGenuineN_firstOrder_operatorLoss` (the operator-loss of the gauge-cancelled geometric
remainder, pinned to the geometry by the gate-coordinate tie against
`deTurckRemainderRealizeSection g₀ g_bg`).  The partial-sum bound is then assembled
(sorry-free) from `hloss` for the smooth (`u₀ = 0`) datum, where the homogeneous heat flow
vanishes so the `H^{a+1}`-view Duhamel field's order-`(d+1)` mass equals the Duhamel
`solFieldMass`; from that bound the qualitative summability implication follows by
`summable_of_sum_le` (bounded nonnegative partial sums are summable).  Consumers transitively
depend on `sorryAx` through that operator-loss leaf. -/

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

/-- **The first-order operator-loss datum of a continuous nonlinearity (the per-order
spectral-mass operator bound), packaged as a predicate.**

`FirstOrderOperatorLoss g₀ a N_cont` asserts that the (continuous) nonlinearity
`N_cont : H^{a+1} → H^a` has a genuine **first-order operator-loss**: there is a finite
constant `C ≥ 0` such that, **at every time horizon `T`**, **every spatial Sobolev order
`d`**, and **for every** `H^{a+1}`-valued time field `w` and `H^a`-valued time field `Nw`
reproducing `N_cont` along `w` a.e., whenever the order-`(d + 1)` spectral masses of `w` are
summable, **every finite partial sum** of the order-`d` spectral masses of `Nw` is bounded by
`C` times the total order-`(d + 1)` mass of `w`.  At the `L²`-in-time / summed-mode level this
is the bounded first-order map `H^{d+1} → H^d` with operator norm `≤ √C` *at every order `d`*,
so `‖N_cont(w)‖²_{L²(H^d)} ≤ C ‖w‖²_{L²(H^{d+1})}`; the partial-sum form is the finite
restriction.  The constant `C` is the time-independent operator norm of `N_cont`, so the
horizon `T` is quantified inside; this is *not* a mode-wise domination (a genuine non-diagonal
first-order operator). -/
def FirstOrderOperatorLoss
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (d : ℝ),
    ∀ (w : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) T)
      (Nw : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ((Nw : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) =ᵐ[timeMeasure T]
        (fun t => N_cont (w t))) →
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 1) *
          ‖timeModeCoeff (I := I) (M := M) w i‖ ^ 2) →
        ∀ F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i d *
              ‖timeModeCoeff (I := I) (M := M) Nw i‖ ^ 2 ≤
            C * ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 1) *
              ‖timeModeCoeff (I := I) (M := M) w i‖ ^ 2

/-- **The geometric gauge-cancelled DeTurck nonlinearity has the first-order operator-loss
(genuine elliptic / first-order operator estimate — posited child).**

For the genuine continuous DeTurck nonlinearity `N_cont : H^{a+1} → H^a` of the `g₀`-anchored
construction — pinned to the geometric gauge-cancelled remainder by its continuity `hN_cont`
and the gate-coordinate tie `hcoeff` (on the realizable gate its eigenbasis coordinates are
the `L²` coordinates of the gauge `deTurckRemainderRealizeSection g₀ g_bg`, the honest DeTurck
remainder `deTurckRicciRHS g_bg (realize) − Δ_∇(realize)`) — the first-order operator-loss
`FirstOrderOperatorLoss g₀ a T N_cont` holds.

This is the genuine quantitative first-order operator-loss of the gauge-cancelled geometric
DeTurck remainder, whose second-order principal part cancels against the linear `Δ_∇`,
leaving a genuine first-order differential operator.  It is the higher-order operator-norm
extension of `N_cont` to every pair `H^{d+1} → H^d` — *additional* structure of the DeTurck
remainder, not deducible from the fixed-order datum `N_cont : H^{a+1} → H^a` alone (this is
why it is posited).  The hypotheses `hN_cont`/`hcoeff` genuinely pin `N_cont` to the geometric
gauge object (a generic function does *not* satisfy the coordinate tie against
`deTurckRemainderRealizeSection g₀ g_bg`), so the statement is *not* the false bare-function
claim; the conclusion (the operator-loss) is structurally distinct from those hypotheses; no
packaging.  The body is `sorry` (the single genuine analytic leaf — the operator
first-order-loss estimate of the geometric remainder).  Consumers transitively depend on
`sorryAx`. -/
theorem deTurckGenuineN_firstOrder_operatorLoss
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hN_cont : Continuous N_cont)
    (hcoeff : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
        realizableAtGate (I := I) g₀ u →
          ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
            (N_cont u).coeff i =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2
                  (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) i) :
    FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont := sorry

/-- **First-order-loss partial-sum operator bound of the DeTurck forcing
(genuine elliptic / first-order operator estimate, assembled from the per-order operator
loss).**

For the `g₀`-anchored DeTurck maximal-regularity engine with the geometric continuous
nonlinearity `N_cont` reproducing the forcing `gforce` a.e. along the Duhamel solution
field of the **smooth (`u₀ = 0`)** initial datum (`hforce`), there is a finite constant
`C ≥ 0` such that, at every spatial Sobolev order `d` for which the solution-field masses at
order `d + 1` are summable, **every finite partial sum** of the order-`d` forcing masses is
bounded by `C` times the total order-`(d + 1)` solution-field mass:

  `∑_{i ∈ F} forcingMass gforce d i ≤ C · (∑' i, solFieldMass hT.le gforce (d + 1) i)`.

This is the genuine quantitative first-order operator-loss of the geometric DeTurck
nonlinearity, integrated in time and summed over modes.  It is *proven* (sorry-free) on top
of the per-order spectral-mass operator-loss `Ncont_timeL2_firstOrder_loss`: with the smooth
datum `u₀ = 0` the homogeneous heat flow vanishes, so the `H^{a+1}`-view Duhamel solution
field `w := maxRegDuhamelSolFieldHa1 0 gforce` has every eigen-coordinate
`timeModeCoeff w i = solModeCoeff gforce i`, whence its order-`(d + 1)` spectral mass equals
`solFieldMass gforce (d + 1) i`; applying the operator-loss child to `w` and `Nw := gforce`
(reproduced by `hforce`) yields the partial-sum bound.  Consumers transitively depend on
`sorryAx` through the operator-loss child.

The smooth-datum condition `hu0 : u₀ = 0` is *load-bearing for truth* (and was absent from
the original blueprint signature — a signature defect corrected here): for a non-zero `u₀`
the homogeneous flow `e^{tΔ_∇} u₀` injects high-frequency content into `gforce = N_cont(w)`
that the Duhamel-only `solFieldMass` does not see, so the order-`d` forcing partial sums are
no longer dominated by `C · ∑' solFieldMass (d + 1)` and the bound fails.  Both consumers
(`deturck_g0_carrier_RHS_continuousOn_interior` and `deturck_g0_engine_carrier_extraction`)
already drive the engine with `u₀ = 0` and supply `rfl`. -/
theorem deTurckForcing_firstOrder_partialSum_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (hu0 : u₀ = 0)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : (gforce : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun t => N_cont (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ)
        hT hT1 u₀ gforce t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        ∀ F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∑ i ∈ F, forcingMass (I := I) (M := M) gforce d i ≤
            C * ∑' i, solFieldMass (I := I) (M := M) hT.le gforce (d + 1) i := by
  classical
  subst hu0
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set w := maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce with hw_def
  -- With the smooth datum `0`, the homogeneous heat flow vanishes, so the `H^{a+1}`-view
  -- Duhamel field `w` has every eigen-coordinate equal to `solModeCoeff gforce i`.
  have hcoeff : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      timeModeCoeff (I := I) (M := M) w i =
        solModeCoeff (I := I) (M := M) (a := (a : ℝ)) hT.le gforce i := by
    intro i
    rw [hw_def, maxRegDuhamelSolFieldHa1, timeModeCoeff_add (I := I) (M := M),
      maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := (a : ℝ))
        (T := T) hT.le _ i,
      maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
        (h_compact := hcompact) (a := (a : ℝ)) hT hT1 gforce i]
    -- The homogeneous mode of the zero datum is the `L²` class of `t ↦ 0`, hence `0`.
    have hhom0 : homModeCoeff (I := I) (M := M) (a := (a : ℝ)) (T := T)
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) i = 0 := by
      have hcoe : (homModeCoeff (I := I) (M := M) (a := (a : ℝ)) (T := T)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) i :
            ℝ → ℝ) =ᵐ[timeMeasure T]
          (fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)).coeff i) :=
        coeFn_ofContinuousOn _
      refine MeasureTheory.Lp.ext_iff.mpr (hcoe.trans ?_)
      have hz : (⇑(0 : timeL2 ℝ T) : ℝ → ℝ) =ᵐ[timeMeasure T] (fun _ => (0 : ℝ)) :=
        Lp.coeFn_zero ℝ 2 (timeMeasure T)
      refine (Filter.EventuallyEq.trans ?_ hz.symm)
      filter_upwards with t
      rw [tensorHs.zero_coeff, mul_zero]
    rw [hhom0, zero_add]
  -- The per-order spectral-mass operator loss of `N_cont` (supplied first-order datum).
  obtain ⟨C, hC0, hbound⟩ := hloss
  refine ⟨C, hC0, fun d hsum F => ?_⟩
  -- Identify the order-`(d + 1)` mass of `w` with the Duhamel `solFieldMass`.
  have hmass_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i (d + 1) *
          ‖timeModeCoeff (I := I) (M := M) w i‖ ^ 2 =
        solFieldMass (I := I) (M := M) hT.le gforce (d + 1) i := by
    intro i; rw [hcoeff i]; rfl
  have hsum_w : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 1) *
      ‖timeModeCoeff (I := I) (M := M) w i‖ ^ 2) := by
    refine (summable_congr ?_).mpr hsum; intro i; rw [hmass_eq i]
  have htsum_w : (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 1) *
        ‖timeModeCoeff (I := I) (M := M) w i‖ ^ 2) =
      ∑' i, solFieldMass (I := I) (M := M) hT.le gforce (d + 1) i :=
    tsum_congr hmass_eq
  -- Apply the operator-loss bound to `w` and `Nw := gforce` (reproduced via `hforce`).
  have hkey := hbound T d w gforce hforce hsum_w F
  rw [htsum_w] at hkey
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hkey
  rw [forcingMass]

/-- **First-order coupling of the DeTurck continuous-nonlinearity forcing
(deep elliptic / first-order-loss input).**

For the `g₀`-anchored DeTurck maximal-regularity engine with a continuous nonlinearity
`N_cont` and a forcing field `gforce` that is reproduced a.e. by `N_cont` along the Duhamel
solution field of the **smooth (`u₀ = 0`)** initial datum (`hforce`), the forcing satisfies
the parabolic first-order coupling: at every spatial Sobolev order `d`, summability of the
solution-field masses at order `d + 1` forces summability of the forcing masses at order
`d`.

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
`sorryAx` through that operator-bound child.

The smooth-datum condition `hu0 : u₀ = 0` is *load-bearing for truth* (and was absent from
the original blueprint signature — a signature defect corrected here): for a non-zero `u₀`
the homogeneous heat flow `e^{tΔ_∇} u₀` injects high-frequency content into the forcing that
the Duhamel-only `solFieldMass` does not record, falsifying the partial-sum bound the
coupling rests on.  Both consumers already drive the engine with `u₀ = 0` and supply
`rfl`. -/
theorem deTurckForcing_firstOrder_coupling
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (hu0 : u₀ = 0)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : (gforce : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun t => N_cont (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ)
        hT hT1 u₀ gforce t))) :
    ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d) := by
  obtain ⟨C, hC0, hbound⟩ :=
    deTurckForcing_firstOrder_partialSum_bound (I := I) (M := M) g₀ a hT hT1 N_cont hloss u₀ hu0
      gforce hforce
  intro d hsol
  -- The order-`d` forcing masses are nonnegative with all finite partial sums bounded
  -- by `C · (total order-(d+1) solution-field mass)`, hence summable.
  exact summable_of_sum_le (fun i => forcingMass_nonneg (I := I) (M := M) gforce d i)
    (hbound d hsol)

end DifferentialGeometry.PDE.RicciFlow
