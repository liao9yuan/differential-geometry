import RicciFlower.RicciFlow.Evolution.Metric
import RicciFlower.Coordinates.Christoffel
import RicciFlower.Realized.CurvatureComponents

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Flow Connection Evolution in a Fixed Frame

The geometric calculation is the lowered pairing formula

`partial_t g_t(d/ds nabla^s_i e_j, e_l)
  = -nabla_i Ric_jl - nabla_j Ric_il + nabla_l Ric_ij`.

This file turns that pairing statement into raised Christoffel components by
the fixed-frame coefficient identity
`coeff_k V = sum_l g^{kl} g(e_l,V)`.
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

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- Lowered Ricci-flow Christoffel variation term:
`-nabla_i Ric_jl - nabla_j Ric_il + nabla_l Ric_ij`. -/
def christoffelVariationLoweredRHSInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j l : Idx) : Real :=
  -nablaRic t x i j l - nablaRic t x j i l + nablaRic t x l i j

/-- `g^{kl} (nabla_i Ric)_{jl}`. -/
def nablaRicLastRaisedInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x i j l

/-- `g^{kl} (nabla_l Ric)_{ij}`. -/
def nablaRicDirectionRaisedInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x l i j

/-- Raised Ricci-flow Christoffel RHS in the convention of
`Coordinates.ricciFlowChristoffelEvolutionRHSInFrame`. -/
def christoffelEvolutionRHSInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l

theorem christoffelEvolutionRHSInFrame_eq_coordinates_rhs
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) :
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
      RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        t x i j k := by
  simp [christoffelEvolutionRHSInFrame, christoffelVariationLoweredRHSInFrame,
    RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame,
    nablaRicLastRaisedInFrame, nablaRicDirectionRaisedInFrame,
    Finset.mul_sum]
  ring

/-- The lowered pairing variation formula for the connection along Ricci flow.

The metric is frozen at the differentiating time `t`; only the connection
family varies in the scalar function. -/
def ConnectionVariationPairingEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
      D.carrier
      (t : Real)

/-- Interval Christoffel component evolution in a local frame. -/
def ChristoffelEvolutionEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
          (t : Real) x i j k)
        D.carrier
        (t : Real)

theorem frameCoeff_eq_sum_inv_metricPairing
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          Realized.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

/-- Raise the connection-variation pairing formula to Christoffel components. -/
theorem christoffelEvolutionEquationInFrameOn_of_pairing
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair : ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx,
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))
  · symm
    exact frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))

end Components

end RicciFlow
end RicciFlower
