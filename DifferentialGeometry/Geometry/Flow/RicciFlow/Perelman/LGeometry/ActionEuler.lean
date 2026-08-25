import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.KineticChart

/-!
# Stationarity of the regularized L-action

This file begins the Tonelli stage with the actual first variation of the
nonlinear regularized action.  It deliberately records stationarity only for
smooth fixed-endpoint variations: passing this identity to a weak chart-H1
Euler equation needs a nonlinear Nemytskii differentiability theorem.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

/-- The nonlinear regularized Lagrangian in one fixed manifold chart.  Its
coefficient is evaluated at the continuous `timeH1` representative, so the
dependence on the curve is not frozen. -/
noncomputable def lChartLag
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : Real :=
  inner Real
    (((1 / 2 : Real) • chartGramOp (I := I) S.family p
      (T - (a + r) ^ 2, u.toFun r)) (u.deriv r))
    (u.deriv r) +
  2 * (a + r) ^ 2 * S.scalar (T - (a + r) ^ 2)
    ((extChartAt I p).symm (u.toFun r))

/-- The nonlinear local chart action on the interval from `a` to `a + L`.
For chart-valued curves, this is the fixed-chart expression underlying the
regularized L-action. -/
noncomputable def lChartAct
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) : Real :=
  ∫ r in (0 : Real)..L, lChartLag S T a p u r

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
/-- A regularized L-action is stationary along any actual smooth variation
which fixes both endpoints for every variation parameter. -/
theorem lRegAction_stat
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular)
    (hmin : IsLocalMin (fun z : Real ↦ lRegAction S T (f z) a b) 0)
    (hfixa : ∀ z : Real, f z a = f 0 a)
    (hfixb : ∀ z : Real, f z b = f 0 b) :
    ∫ s in a..b, lRegEulerPair S T (f 0) s
      (lVelocity (I := I) (fun z : Real ↦ f z s) 0) = 0 := by
  have hva : lVelocity (I := I) (fun z : Real ↦ f z a) 0 = 0 := by
    have heq : (fun z : Real ↦ f z a) = fun _ ↦ f 0 a := by
      funext z
      exact hfixa z
    rw [heq]
    simp only [lVelocity, mfderiv_const, ContinuousLinearMap.zero_apply]
  have hvb : lVelocity (I := I) (fun z : Real ↦ f z b) 0 = 0 := by
    have heq : (fun z : Real ↦ f z b) = fun _ ↦ f 0 b := by
      funext z
      exact hfixb z
    rw [heq]
    simp only [lVelocity, mfderiv_const, ContinuousLinearMap.zero_apply]
  have hact := lRegAction_first (I := I) S hS T f hf a b ht
  have hzero := hmin.deriv_eq_zero
  rw [hact.deriv] at hzero
  simp only [hva, hvb, ContinuousLinearMap.map_zero,
    ContinuousLinearMap.zero_apply, zero_sub] at hzero
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
