import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Discharging Lemma 3.11's metric-equivalence inputs from a Ricci flow (P1)

MSM135 Lemma 3.11, equation (3.3) consumes a `MetricLogDerivativeInput`. Its
`metric_deriv` field is exactly the Ricci-flow metric-variation equation
`d/dt g(t)(v,v) = -2 Ric(t)(v,v)`. This file discharges that field from the
actual flow predicate `IsSolutionOn`, turning the honest-input package into a
producer. The within-derivative on the time carrier is upgraded to a full
derivative at regular times via `RealTimeInterval.regular_mem_nhds`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- **Lemma 3.11 `metric_deriv` content.** Along a Ricci-flow solution, the time
derivative of the metric quadratic form at a regular time `t` is
`-2 Ric(t)(v,v)`. This upgrades the carrier-local within-derivative recorded by
`IsSolutionOn.equation` to a full `HasDerivAt`. -/
theorem ricciFlow_metric_hasDerivAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    {t : Real} (ht : t ∈ D.regular) (x : M) (v : TangentSpace I x) :
    HasDerivAt
      (fun s : Real => (S.family.metric s).inner x v v)
      ((-2 : Real) *
        S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v))
      t := by
  have hwithin := hS.equation ⟨t, ht⟩ x v v
  exact hwithin.hasDerivAt (D.regular_mem_nhds ht)

section FixedDomain

variable [SigmaCompactSpace M]

/-- **Lemma 3.11, eq (3.3) producer.** A sequence of Ricci-flow solutions on a
common source domain `M`, with a Ricci quadratic bound `|Ric(v,v)| ≤ A·g(v,v)`
on a regular time window and the textbook log-derivative integrability, yields a
genuine `MetricLogDerivativeInput`. The `metric_deriv` field is discharged from
the flow equation (`ricciFlow_metric_hasDerivAt`); `quad_bound` is the book's
curvature hypothesis and `log_integrable` is the regularity input. -/
theorem metricLogDerivativeInput_of_solutions
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 A : Real)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (hA : 0 <= A)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i s => (S i).family.metric s)
      (fun i t x => (S i).ricciAt t x) A where
  quad_bound := ⟨hA, fun i t ht x hx v => hquad i t ht x hx v⟩
  metric_deriv := fun i x _hx v _hv t ht =>
    ricciFlow_metric_hasDerivAt (S i) (hS i) (hwin ht) x v
  log_integrable := fun i x hx v hv t ht => hint i x hx v hv t ht

/-- **Lemma 3.11, eq (3.3) for a Ricci-flow sequence.** Whole-window metric
equivalence `g_i(t) ≃ gRef` with factor `C·exp(2A|t-t0|)`, from time-`t0`
equivalence plus the flow and the Ricci bound. -/
theorem metricUniformEquivalentOnWindow_of_solutions
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hS : forall i : Nat, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (S i))
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hwin : Set.Icc β ψ ⊆ D.regular)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hA : 0 <= A)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef ((S i).family.metric t0) C)
    (hquad :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |(S i).ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)| <=
            A * ((S i).family.metric t).inner x v v)
    (hint :
      forall i : Nat, forall x : M, x ∈ K -> forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) *
                (S i).ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v)) /
                ((S i).family.metric s).inner x v v)
            MeasureTheory.volume t0 t) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i s => (S i).family.metric s)
      (fun t : Real => metricEquivalenceFactor C A t t0) :=
  metricUniformEquivalentOnWindow_of_logDerivativeInput (I := I) K β ψ t0 C A gRef
    (fun i s => (S i).family.metric s) (fun i t x => (S i).ricciAt t x)
    ht0 hC hequiv0
    (metricLogDerivativeInput_of_solutions (I := I) S hS K β ψ t0 A hwin hA hquad hint)

end FixedDomain

end HCGCompactness
end DifferentialGeometry
