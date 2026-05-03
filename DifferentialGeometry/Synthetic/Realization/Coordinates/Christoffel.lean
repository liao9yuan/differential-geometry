import DifferentialGeometry.Synthetic.Realization.Coordinates.Basic
import DifferentialGeometry.Synthetic.Algebra.Metric
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

/-- Lower-index Christoffel coefficient:
`Gamma_{ij l}(x) = g_x(nabla_{frame_i} frame_j, frame_l)`.

Unlike `christoffelSymbolInFrame`, this metric-paired version does not need
frame coefficient extraction. It is the coordinate-facing form of the invariant
connection evolution theorem before raising the final index. -/
noncomputable def christoffelSymbolLowerInFrame
    (fiberMetric : (x : M) -> MetricDuality Real (TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (x : M) (i j l : ι) : Real :=
  (fiberMetric x).g ((cov (frame j) x) (frame i x)) (frame l x)

theorem christoffelSymbolLowerInFrame_eval
    (fiberMetric : (x : M) -> MetricDuality Real (TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (x : M) (i j l : ι) :
    christoffelSymbolLowerInFrame fiberMetric cov frame x i j l =
      (fiberMetric x).g ((cov (frame j) x) (frame i x)) (frame l x) := by
  rfl

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

/-- Time derivative of the metric-paired Christoffel coefficient with the metric frozen at `t`. -/
noncomputable def christoffelSymbolLowerTimeDerivativeInFrame
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j l : ι) : Real :=
  td.dt_apply
    (fun s => christoffelSymbolLowerInFrame (fiberMetricFam t) (covFam s) frame x i j l) t

theorem christoffelSymbolLowerTimeDerivativeInFrame_eval
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j l : ι) :
    christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam frame t x i j l =
      td.dt_apply
        (fun s => christoffelSymbolLowerInFrame (fiberMetricFam t) (covFam s) frame x i j l) t := by
  rfl

/-- Ricci-flow RHS for the lower-index Christoffel evolution:
`-nabla_i Ric_{jl} - nabla_j Ric_{il} + nabla_l Ric_{ij}`. -/
def ricciFlowChristoffelLowerEvolutionRHSInFrame
    (nablaRic : Time -> M -> ι -> ι -> ι -> Real)
    (t : Time) (x : M) (i j l : ι) : Real :=
  - nablaRic t x i j l - nablaRic t x j i l + nablaRic t x l i j

/-- Coordinate-facing lower-index form of Lemma 14.23. -/
def RicciFlowChristoffelLowerEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> ι -> ι -> ι -> Real) : Prop :=
  forall t x i j l,
    christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam frame t x i j l =
      ricciFlowChristoffelLowerEvolutionRHSInFrame nablaRic t x i j l

theorem ricciFlow_christoffelLowerEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> ι -> ι -> ι -> Real)
    (h_evol : RicciFlowChristoffelLowerEvolutionEquationInFrame
      td fiberMetricFam covFam frame nablaRic)
    (t : Time) (x : M) (i j l : ι) :
    christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam frame t x i j l =
      - nablaRic t x i j l - nablaRic t x j i l + nablaRic t x l i j := by
  simpa [RicciFlowChristoffelLowerEvolutionEquationInFrame,
    ricciFlowChristoffelLowerEvolutionRHSInFrame] using h_evol t x i j l

/-- Component bridge for the covariant derivative of Ricci in a frame.

This is the precise coordinate-realization obligation: the scalar component
`nablaRic t x a b c` must be the invariant covariant Ricci derivative evaluated
on the three frame vectors at `x`. -/
def RicciCovDerivComponentsInFrame
    (fiberRicciCovDeriv :
      (t : Time) -> (x : M) ->
        TangentSpace I x -> TangentSpace I x -> TangentSpace I x -> Real)
    (frame : ι -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> ι -> ι -> ι -> Real) : Prop :=
  forall t x a b c,
    nablaRic t x a b c =
      fiberRicciCovDeriv t x (frame a x) (frame b x) (frame c x)

/-- Bridge from an invariant metric-paired connection evolution statement to
the lower-index coordinate Christoffel evolution equation.

The hypotheses isolate the two realization facts still owed:
1. the time derivative of the lower Christoffel coefficient is the metric-paired
   connection variation component;
2. the invariant connection evolution is the Ricci-derivative combination, and
   `RicciCovDerivComponentsInFrame` identifies those invariant derivatives with
   the named coordinate components. -/
theorem ricciFlowChristoffelLowerEvolution_from_invariant_components
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : ι -> (x : M) -> TangentSpace I x)
    (connectionVariationLower : Time -> M -> ι -> ι -> ι -> Real)
    (fiberRicciCovDeriv :
      (t : Time) -> (x : M) ->
        TangentSpace I x -> TangentSpace I x -> TangentSpace I x -> Real)
    (nablaRic : Time -> M -> ι -> ι -> ι -> Real)
    (h_dt : forall t x i j l,
      christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam frame t x i j l =
        connectionVariationLower t x i j l)
    (h_components : RicciCovDerivComponentsInFrame fiberRicciCovDeriv frame nablaRic)
    (h_invariant : forall t x i j l,
      connectionVariationLower t x i j l =
        - fiberRicciCovDeriv t x (frame i x) (frame j x) (frame l x) -
          fiberRicciCovDeriv t x (frame j x) (frame i x) (frame l x) +
          fiberRicciCovDeriv t x (frame l x) (frame i x) (frame j x)) :
    RicciFlowChristoffelLowerEvolutionEquationInFrame
      td fiberMetricFam covFam frame nablaRic := by
  intro t x i j l
  calc
    christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam frame t x i j l
        = connectionVariationLower t x i j l := h_dt t x i j l
    _ = - fiberRicciCovDeriv t x (frame i x) (frame j x) (frame l x) -
          fiberRicciCovDeriv t x (frame j x) (frame i x) (frame l x) +
          fiberRicciCovDeriv t x (frame l x) (frame i x) (frame j x) := h_invariant t x i j l
    _ = ricciFlowChristoffelLowerEvolutionRHSInFrame nablaRic t x i j l := by
      unfold ricciFlowChristoffelLowerEvolutionRHSInFrame
      rw [← h_components t x i j l, ← h_components t x j i l,
        ← h_components t x l i j]

section RawCoordinates

variable [FiniteDimensional Real E]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

/-- The raw coordinate domain around `x₀`, taken from Mathlib's tangent-bundle
trivialization. -/
def rawCoordinateDomain (x₀ : M) : Set M :=
  (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet

/-- The raw coordinate frame around `x₀`: the standard model-space basis
transported by Mathlib's tangent-bundle trivialization at `x₀`. This is the
coordinate frame used for chart-level Christoffel calculations. -/
noncomputable def rawCoordinateFrame (x₀ : M) :
    Fin (Module.finrank Real E) -> (x : M) -> TangentSpace I x :=
  (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame
    (Module.finBasis Real E)

theorem rawCoordinateFrame_isLocalFrameOn (x₀ : M) :
    IsLocalFrameOn I E 1 (rawCoordinateFrame (I := I) (M := M) x₀)
      (rawCoordinateDomain (I := I) (M := M) x₀) := by
  unfold rawCoordinateFrame rawCoordinateDomain
  exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).isLocalFrameOn_localFrame_baseSet
    I 1 (Module.finBasis Real E)

/-- Raw-coordinate Christoffel coefficients `Γ^k_ij` in the coordinate frame
coming from `trivializationAt ... x₀`. -/
noncomputable def christoffelSymbolInRawCoordinates
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ x : M)
    (i j k : Fin (Module.finrank Real E)) : Real :=
  christoffelSymbolInFrame cov (rawCoordinateFrame (I := I) (M := M) x₀)
    (rawCoordinateFrame_isLocalFrameOn (I := I) (M := M) x₀) x i j k

theorem christoffelSymbolInRawCoordinates_eq_frame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ x : M) (i j k : Fin (Module.finrank Real E)) :
    christoffelSymbolInRawCoordinates (I := I) (M := M) cov x₀ x i j k =
      christoffelSymbolInFrame cov (rawCoordinateFrame (I := I) (M := M) x₀)
        (rawCoordinateFrame_isLocalFrameOn (I := I) (M := M) x₀) x i j k := by
  rfl

/-- Lower-index raw-coordinate Christoffel coefficients `Γ_ijℓ`. -/
noncomputable def christoffelSymbolLowerInRawCoordinates
    (fiberMetric : (x : M) -> MetricDuality Real (TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ x : M)
    (i j l : Fin (Module.finrank Real E)) : Real :=
  christoffelSymbolLowerInFrame fiberMetric cov (rawCoordinateFrame (I := I) (M := M) x₀)
    x i j l

theorem christoffelSymbolLowerInRawCoordinates_eq_frame
    (fiberMetric : (x : M) -> MetricDuality Real (TangentSpace I x))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ x : M) (i j l : Fin (Module.finrank Real E)) :
    christoffelSymbolLowerInRawCoordinates (I := I) (M := M) fiberMetric cov x₀ x i j l =
      christoffelSymbolLowerInFrame fiberMetric cov
        (rawCoordinateFrame (I := I) (M := M) x₀) x i j l := by
  rfl

/-- Lower-index raw-coordinate time derivative `∂ₜ Γ_ijℓ`, with the metric
frozen at the differentiated time as in the lower-index frame API. -/
noncomputable def christoffelSymbolLowerTimeDerivativeInRawCoordinates
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Time) (x₀ x : M)
    (i j l : Fin (Module.finrank Real E)) : Real :=
  christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam
    (rawCoordinateFrame (I := I) (M := M) x₀) t x i j l

theorem christoffelSymbolLowerTimeDerivativeInRawCoordinates_eq_frame
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Time) (x₀ x : M) (i j l : Fin (Module.finrank Real E)) :
    christoffelSymbolLowerTimeDerivativeInRawCoordinates (I := I) (M := M)
      td fiberMetricFam covFam t x₀ x i j l =
      christoffelSymbolLowerTimeDerivativeInFrame td fiberMetricFam covFam
        (rawCoordinateFrame (I := I) (M := M) x₀) t x i j l := by
  rfl

/-- Raw coordinate components of the invariant covariant derivative of Ricci:
`(∇_a Ric)_{bc}` in the coordinate frame around `x₀`. -/
def ricciCovDerivComponentsInRawCoordinates
    (fiberRicciCovDeriv :
      (t : Time) -> (x : M) ->
        TangentSpace I x -> TangentSpace I x -> TangentSpace I x -> Real)
    (x₀ : M) :
    Time -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Real :=
  fun t x a b c =>
    fiberRicciCovDeriv t x
      (rawCoordinateFrame (I := I) (M := M) x₀ a x)
      (rawCoordinateFrame (I := I) (M := M) x₀ b x)
      (rawCoordinateFrame (I := I) (M := M) x₀ c x)

theorem ricciCovDerivComponentsInRawCoordinates_components
    (fiberRicciCovDeriv :
      (t : Time) -> (x : M) ->
        TangentSpace I x -> TangentSpace I x -> TangentSpace I x -> Real)
    (x₀ : M) :
    RicciCovDerivComponentsInFrame fiberRicciCovDeriv
      (rawCoordinateFrame (I := I) (M := M) x₀)
      (ricciCovDerivComponentsInRawCoordinates (I := I) (M := M)
        fiberRicciCovDeriv x₀) := by
  intro t x a b c
  rfl

/-- Raw-coordinate lower-index Christoffel evolution. This removes the former
`nablaRic` component placeholder by choosing the actual coordinate components
of the invariant Ricci covariant derivative in the tangent-trivialization
coordinate frame around `x₀`.

The remaining hypotheses are the invariant connection-variation/time-derivative
bridge and the invariant Ricci-flow connection evolution, normally supplied by
`christoffel_evolution_metric_paired` after realization. -/
theorem ricciFlowChristoffelLowerEvolution_in_raw_coordinates
    (td : TimeDerivativeData Real A Time)
    (fiberMetricFam : Time -> (x : M) -> MetricDuality Real (TangentSpace I x))
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M)
    (connectionVariationLower :
      Time -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
        Fin (Module.finrank Real E) -> Real)
    (fiberRicciCovDeriv :
      (t : Time) -> (x : M) ->
        TangentSpace I x -> TangentSpace I x -> TangentSpace I x -> Real)
    (h_dt : forall t x i j l,
      christoffelSymbolLowerTimeDerivativeInRawCoordinates (I := I) (M := M)
        td fiberMetricFam covFam t x₀ x i j l =
        connectionVariationLower t x i j l)
    (h_invariant : forall t x i j l,
      connectionVariationLower t x i j l =
        - fiberRicciCovDeriv t x
            (rawCoordinateFrame (I := I) (M := M) x₀ i x)
            (rawCoordinateFrame (I := I) (M := M) x₀ j x)
            (rawCoordinateFrame (I := I) (M := M) x₀ l x) -
          fiberRicciCovDeriv t x
            (rawCoordinateFrame (I := I) (M := M) x₀ j x)
            (rawCoordinateFrame (I := I) (M := M) x₀ i x)
            (rawCoordinateFrame (I := I) (M := M) x₀ l x) +
          fiberRicciCovDeriv t x
            (rawCoordinateFrame (I := I) (M := M) x₀ l x)
            (rawCoordinateFrame (I := I) (M := M) x₀ i x)
            (rawCoordinateFrame (I := I) (M := M) x₀ j x)) :
    RicciFlowChristoffelLowerEvolutionEquationInFrame td fiberMetricFam covFam
      (rawCoordinateFrame (I := I) (M := M) x₀)
      (ricciCovDerivComponentsInRawCoordinates (I := I) (M := M)
        fiberRicciCovDeriv x₀) := by
  refine ricciFlowChristoffelLowerEvolution_from_invariant_components
    td fiberMetricFam covFam (rawCoordinateFrame (I := I) (M := M) x₀)
    connectionVariationLower fiberRicciCovDeriv
    (ricciCovDerivComponentsInRawCoordinates (I := I) (M := M)
      fiberRicciCovDeriv x₀) ?_ ?_ h_invariant
  · intro t x i j l
    exact h_dt t x i j l
  · exact ricciCovDerivComponentsInRawCoordinates_components
      (I := I) (M := M) fiberRicciCovDeriv x₀

end RawCoordinates

end TimeDerivative

end FrameChristoffel

end
