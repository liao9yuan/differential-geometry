import DifferentialGeometry.Synthetic.Realization.Coordinates.Basic
import DifferentialGeometry.Synthetic.Analysis.TimeOnTensors

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Christoffel Symbols in a Local Frame

Mathlib's bundled covariant derivative has argument order
`cov sigma x v = (nabla_v sigma)(x)`. Given a local frame `frame i`, the
Christoffel coefficient is the `k`-th frame coefficient of
`nabla_{frame i} frame j`:

`Gamma^k_{ij}(x) = coeff_k ((cov (frame j) x) (frame i x))`.

The definitions below are frame-based. Coordinate charts can supply their
coordinate frame later, while arbitrary local frames already support the
normal-coordinate and connection-variation APIs needed for local calculations.

For a fixed frame, the Christoffel symbol as a scalar function is simply
`fun x => christoffelSymbolInFrame cov frame hframe x i j k`; this file avoids
separate currying wrappers.
-/

noncomputable section

open Bundle Module
open scoped BigOperators Manifold ContDiff

section FrameChristoffel

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {ι : Type*}
  {u : Set M}

/-- Christoffel coefficients in a local frame:
`Gamma^k_{ij}(x) = coeff_k(nabla_{frame_i} frame_j)`. -/
noncomputable def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) : Real :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))

theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

/-- Expansion of `nabla_{frame i} frame j` in the local frame. -/
theorem covariantDerivative_eq_sum_christoffel
    [Fintype ι]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : ι) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx

/-- A local frame has vanishing Christoffel symbols at a point. This is the
normal-coordinate condition on the connection part of the frame. -/
def ChristoffelSymbolsVanishAtFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : ι, christoffelSymbolInFrame cov frame hframe x i j k = 0

section Difference

variable [FiniteDimensional Real E]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

/-- Components of the tensorial connection difference `cov - cov'` in a local frame.

This is deliberately not defined as the pointwise subtraction of Christoffel
symbols. `CovariantDerivative.difference cov cov'` is tensorial in the section
slot and can be evaluated pointwise. The theorem
`christoffelSymbolDifferenceInFrame_eq_sub` identifies it with
`Gamma(cov) - Gamma(cov')` when the acted-on frame section is differentiable at
the point. -/
noncomputable def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : ι) : Real :=
  hframe.coeff k x (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))

/-- Expansion of the connection-difference tensor in the local frame. -/
theorem christoffelSymbolDifference_expansion
    [Fintype ι]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : ι) :
    ((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x) =
      ∑ k, christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq
    (fun y => ((CovariantDerivative.difference cov cov' y) (frame j y)) (frame i y)) hx

/-- If the frame vector `frame j` is differentiable at `x`, the tensorial
connection-difference coefficient agrees with the pointwise subtraction
`Gamma(cov) - Gamma(cov')`. -/
theorem christoffelSymbolDifferenceInFrame_eq_sub
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : ι)
    (hframe_j : MDiffAt (T% (frame j)) x) :
    christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov' frame hframe x i j k := by
  unfold christoffelSymbolDifferenceInFrame christoffelSymbolInFrame
  change hframe.coeff k x
      (((cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv x)
        (frame j x)) (frame i x)) =
    hframe.coeff k x ((cov (frame j) x) (frame i x)) -
      hframe.coeff k x ((cov' (frame j) x) (frame i x))
  rw [IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := frame j) (x := x) (hx := by trivial) hframe_j]
  simp

end Difference

section TimeDerivative

variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- The coordinate-facing time derivative `partial_t Gamma^k_ij` in a fixed local frame. -/
noncomputable def christoffelSymbolTimeDerivativeInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : ι) : Real :=
  td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t

theorem christoffelSymbolTimeDerivativeInFrame_eval
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : ι) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t := by
  rfl

/-- A named coordinate evolution equation for Christoffel coefficients. The intended Ricci-flow
right hand side is supplied by `ricciFlowChristoffelEvolutionRHSInFrame` below. -/
def ChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> ι -> ι -> ι -> Real) : Prop :=
  forall t x i j k,
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k

theorem christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> ι -> ι -> ι -> Real)
    (h_evol : ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe rhs)
    (t : Time) (x : M) (i j k : ι) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k :=
  h_evol t x i j k

/-- Ricci-flow right hand side for Lemma 14.23 in a local frame.

`nablaRicLastRaised t x i j k` represents `g^{kl} (nabla_i Ric)_{jl}`.
`nablaRicDirectionRaised t x i j k` represents `g^{kl} (nabla_l Ric)_{ij}`.
Supplying these already-raised contractions keeps this file independent of the
future coordinate metric/Ricci component API. -/
def ricciFlowChristoffelEvolutionRHSInFrame
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> ι -> ι -> ι -> Real)
    (t : Time) (x : M) (i j k : ι) : Real :=
  - nablaRicLastRaised t x i j k -
    nablaRicLastRaised t x j i k +
    nablaRicDirectionRaised t x i j k

/-- Coordinate statement of Lemma 14.23, parameterized by the raised Ricci-derivative
components that will be supplied by the later metric/Ricci coordinate realization. -/
def RicciFlowChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> ι -> ι -> ι -> Real) : Prop :=
  ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe
    (ricciFlowChristoffelEvolutionRHSInFrame nablaRicLastRaised nablaRicDirectionRaised)

theorem ricciFlow_christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> ι -> ι -> ι -> Real)
    (h_evol : RicciFlowChristoffelSymbolEvolutionEquationInFrame
      td covFam frame hframe nablaRicLastRaised nablaRicDirectionRaised)
    (t : Time) (x : M) (i j k : ι) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      - nablaRicLastRaised t x i j k -
        nablaRicLastRaised t x j i k +
        nablaRicDirectionRaised t x i j k := by
  simpa [RicciFlowChristoffelSymbolEvolutionEquationInFrame,
    ChristoffelSymbolEvolutionEquationInFrame, ricciFlowChristoffelEvolutionRHSInFrame]
    using h_evol t x i j k

end TimeDerivative

end FrameChristoffel

end
