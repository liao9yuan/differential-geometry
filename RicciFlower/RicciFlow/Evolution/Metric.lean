import RicciFlower.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Flow Metric Evolution in a Fixed Frame

This file translates the first Section 6.2 metric calculation into the realized
interval API.  The core geometric input is the Ricci-flow equation
`partial_t g = -2 Ric`; the inverse-metric result is obtained by differentiating
the frame identity `g^{-1} g = I`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]

/-- Metric component in a fixed local frame. -/
def metricCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (S.family.metric t).inner x (frame i x) (frame j x)

@[simp] theorem metricCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrame (I := I) S frame t x i j =
      (S.family.metric t).inner x (frame i x) (frame j x) := by
  rfl

/-- Fixed-frame metric evolution, directly extracted from `IsSolutionOn`. -/
theorem metricCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [metricCompInFrame, ricciCompInFrame] using
    metric_derivWithin_eq_neg_two_ricci (I := I) S hS t x
      (frame i x) (frame j x)

/-- The inverse components invert the frame Gram matrix at all times. -/
def InverseMetricComponentsInFrameOn [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)

/-- Symmetry of the inverse metric components in the chosen frame.  This is a
separate v1 hypothesis because the existing frame-inverse predicate records
left/right inverse identities but not symmetry. -/
def SymmetricInverseMetricComponentsInFrameOn
    (gInv : Real -> Realized.InverseMetricComponents M Idx) : Prop :=
  forall t x i j, gInv t x i j = gInv t x j i

/-- Componentwise regularity of a supplied inverse-metric component family. -/
def InverseMetricDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (gInvDt (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Metric-side regularity in a fixed local frame.

This package is deliberately metric-side: it records smooth time dependence of
the frame Gram matrix, nondegeneracy through a chosen two-sided inverse frame
matrix, time differentiability of that inverse matrix, and uniqueness of time
derivatives on the interval.  The inverse evolution formula itself is still
proved by differentiating the inverse identity in
`inverseMetricEvolutionEquationInFrame_of_inverse_components`; it is not assumed
here. -/
structure MetricFrameTimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop where
  metricSmooth :
    forall x : M, x ∈ u -> forall i j : Idx,
      ContDiffOn Real ⊤
        (fun t : Real => metricCompInFrame (I := I) S frame t x i j)
        D.carrier
  /-- Nondegeneracy is represented by an explicit two-sided inverse of the
  frame Gram matrix. -/
  nondegenerateGram :
    InverseMetricComponentsInFrameOn (I := I) S gInv frame
  inverseSymmetric :
    SymmetricInverseMetricComponentsInFrameOn gInv
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)

/-- Spacetime metric regularity in a fixed local frame.

The extra mixed-derivative field is the fixed-base statement
`∂s d_x(g_s) = d_x(∂s g_s)` specialized to the Ricci-flow metric variation
`∂s g_s = -2 Ric_s`.  This is weaker than, and does not assert, commutation of
`∂t` with the evolving covariant derivative. -/
structure MetricFrameSpacetimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop extends
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u where
  frameMetricSpacetimeSmooth :
    forall i j : Idx,
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
        (fun p : Real × M => metricCompInFrame (I := I) S frame p.1 p.2 i j)
        (D.carrier ×ˢ u)
  frameMetricExtDerivTimeDerivative :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall d a b : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x))
          ((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x))
          D.carrier
          (t : Real)

private theorem inverseMetric_derivative_row_eq
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    (∑ a : Idx,
        (gInvDt (t : Real) x i a *
          metricCompInFrame (I := I) S frame (t : Real) x a j +
        gInv (t : Real) x i a *
          ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j))) =
      0 := by
  let lhs : Real -> Real :=
    fun s => ∑ a : Idx,
      gInv s x i a * metricCompInFrame (I := I) S frame s x a j
  have hlhs :
      HasDerivWithinAt lhs
        (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        D.carrier
        (t : Real) := by
    dsimp [lhs]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          gInv s x i a * metricCompInFrame (I := I) S frame s x a j)
        (A' := fun a =>
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha =>
          by
            exact (hdt t x i a).mul
              (metricCompInFrame_hasDerivWithinAt (I := I) S hS frame t x a j)))
  have hconst :
      HasDerivWithinAt lhs 0 D.carrier (t : Real) := by
    dsimp [lhs]
    exact
      (hasDerivWithinAt_const
        (x := (t : Real)) (s := D.carrier)
        (c := (if i = j then 1 else 0 : Real))).congr
        (fun s _hs => by
          exact (hinv s x i j).1)
        (by
          exact (hinv (t : Real) x i j).1)
  have h1 := hlhs.derivWithin (hunique t)
  have h0 := hconst.derivWithin (hunique t)
  exact h1.symm.trans h0

private theorem inverseMetric_derivative_solve
    [DecidableEq Idx]
    (metric ric gInv gInvDt : Idx -> Idx -> Real)
    (i : Idx)
    (hrow : forall j : Idx,
      (∑ a : Idx,
        (gInvDt i a * metric a j + gInv i a * ((-2 : Real) * ric a j))) = 0)
    (hright : forall a b : Idx,
      (∑ k : Idx, metric a k * gInv k b) = (if a = b then 1 else 0))
    (hsymm : forall a b : Idx, gInv a b = gInv b a)
    (j : Idx) :
    gInvDt i j =
      2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
  have hrow' : forall m : Idx,
      (∑ a : Idx, gInvDt i a * metric a m) =
        2 * (∑ a : Idx, gInv i a * ric a m) := by
    intro m
    have hm := hrow m
    rw [Finset.sum_add_distrib] at hm
    have hm' :
        (∑ a : Idx, gInvDt i a * metric a m) +
            (-2 : Real) * (∑ a : Idx, gInv i a * ric a m) = 0 := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hm
    linarith
  calc
    gInvDt i j
        = ∑ a : Idx, gInvDt i a * (if a = j then 1 else 0) := by
            simp
    _ = ∑ a : Idx, gInvDt i a *
          (∑ k : Idx, metric a k * gInv k j) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            rw [hright a j]
    _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
            calc
              (∑ a : Idx, gInvDt i a *
                  (∑ k : Idx, metric a k * gInv k j))
                  =
                ∑ a : Idx, ∑ k : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ k : Idx, ∑ a : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    rw [Finset.sum_comm]
              _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
                    refine Finset.sum_congr rfl fun k _hk => ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    ring
    _ = ∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [hrow' k]
    _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
            calc
              (∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j)
                  =
                2 * (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _hk => ?_
                  ring
              _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
                  congr 1
                  calc
                    (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j)
                        =
                      ∑ k : Idx, ∑ a : Idx,
                        (gInv i a * ric a k) * gInv k j := by
                          refine Finset.sum_congr rfl fun k _hk => ?_
                          rw [Finset.sum_mul]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        (gInv i a * ric a b) * gInv b j := by
                          rw [Finset.sum_comm]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        gInv i a * gInv j b * ric a b := by
                          refine Finset.sum_congr rfl fun a _ha => ?_
                          refine Finset.sum_congr rfl fun b _hb => ?_
                          rw [hsymm b j]
                          ring

/-- Inverse-metric evolution from the differentiated identity `g^{-1}g = I`.

The proof uses the Ricci-flow metric derivative, the product rule on the
left-inverse identity, uniqueness of the interval derivative, and the right
inverse identity to solve for the component derivative.  The symmetry hypothesis
aligns the solved component with the existing `raisedRicciCompInFrame`
convention. -/
theorem inverseMetricEvolutionEquationInFrame_of_inverse_components
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hsymm : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame := by
  intro t x i j
  have hrow : forall m : Idx,
      (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a m +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a m))) =
        0 := by
    intro m
    exact inverseMetric_derivative_row_eq
      (I := I) S hS gInv gInvDt frame hdt hinv hunique t x i m
  have hsolve :
      gInvDt (t : Real) x i j =
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j := by
    unfold inverseMetricEvolutionRHSInFrame raisedRicciCompInFrame
    exact inverseMetric_derivative_solve
      (metric := fun a b => metricCompInFrame (I := I) S frame (t : Real) x a b)
      (ric := fun a b => ricciCompInFrame (I := I) S frame (t : Real) x a b)
      (gInv := fun a b => gInv (t : Real) x a b)
      (gInvDt := fun a b => gInvDt (t : Real) x a b)
      i
      hrow
      (fun a b => (hinv (t : Real) x a b).2)
      (fun a b => hsymm (t : Real) x a b)
      j
  exact (hdt t x i j).congr_deriv hsolve

/-- Metric-frame regularity produces the inverse-metric evolution equation.

The computation is the existing inverse-identity differentiation theorem; this
wrapper keeps the future matrix-inverse smoothness work attached to the metric
regularity package rather than to the Christoffel evolution layer. -/
theorem inverseMetricEvolution_of_metricFrameTimeRegularity
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) S hS gInv gInvDt frame
    hreg.inverseMetricDerivative
    hreg.nondegenerateGram
    hreg.inverseSymmetric
    hreg.uniqueTimeDerivatives

end Components

end RicciFlow
end RicciFlower
