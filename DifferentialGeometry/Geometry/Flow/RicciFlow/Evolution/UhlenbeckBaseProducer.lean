import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Rm13DerivProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Uhlenbeck base `∂ₜRm04` discharge — Lemma 6.1 (in progress)

Discharge of `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (Hamilton's curvature
evolution `∂ₜRm = ΔRm + Rm∗Rm`), the gating geometric input of the BBS pillar.  See
`UhlenbeckBaseProducer.md` for the full route.  Built so far:

* `metricCompInFrame_timeDeriv` — the component metric evolution `∂ₜg_{ij} = −2 Ric_{ij}`
  in a local frame, directly from the Ricci-flow PDE.  Input #1 to the A2 lowering
  product rule `∂ₜRm04 = (∂ₜg)·Rm13 + g·(∂ₜRm13)`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*}

/-- **Component metric evolution `∂ₜg_{ij} = −2 Ric_{ij}`.**  The time derivative of the
local-frame metric components of a Ricci-flow solution, extracted from the PDE
`MetricVariationEquationOn`.  Frame vectors are held fixed; the derivative is taken
within `D.carrier` at a regular time. -/
theorem metricCompInFrame_timeDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have h := hS.equation t x (frame i x) (frame j x)
  simpa [metricCompInFrame, ricciCompInFrame, RicciAtFamily.toTensorField_apply] using h

/-- **Component lowering realization (A2 gateway).**  At the centre `x₀` of the
coordinate frame, the lowered Riemann base component array is the metric-lowering of the
`(1,3)` Christoffel curvature coefficient:
`Rm04_{m₀m₁m₂m₃} = Σ_p curvCoeff^p_{m₀m₁m₂} · g_{m₃ p}`.
Derived by chaining the tensor-level lowering `solution_rm04LowersRm13At` with the
component realization `rm13_eval_eq_christoffelCurvCoord` and evaluating the metric flat. -/
theorem realizedRmBase_eq_curvCoeff_lower
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (1 : WithTop ℕ∞))
    (hRm : DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
      (S.family.connection t) (S.base.rm13 t))
    (hcurv : DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I)
      (S.family.connection t) x₀)
    (m : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
    realizedRmBase (I := I) S x₀ t x₀ m
      = ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection t) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ (m 3) p := by
  classical
  have hvec : (fun q : Fin 4 => coordinateFrameAt (I := I) x₀ (m q) x₀)
      = DifferentialGeometry.Integral.Connection.vec4
          (coordinateFrameAt (I := I) x₀ (m 0) x₀)
          (coordinateFrameAt (I := I) x₀ (m 1) x₀)
          (coordinateFrameAt (I := I) x₀ (m 2) x₀)
          (coordinateFrameAt (I := I) x₀ (m 3) x₀) := by
    funext q; fin_cases q <;> rfl
  rw [realizedRmBase_apply, hvec,
    solution_rm04LowersRm13At S t x₀
      (coordinateFrameAt (I := I) x₀ (m 0) x₀)
      (coordinateFrameAt (I := I) x₀ (m 1) x₀)
      (coordinateFrameAt (I := I) x₀ (m 2) x₀)
      (coordinateFrameAt (I := I) x₀ (m 3) x₀),
    DifferentialGeometry.Integral.Connection.rm13_eval_eq_christoffelCurvCoord
      (I := I) (S.family.connection t) hcov (S.base.rm13 t) x₀
      (dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) (S.base.metric t) x₀)
          (coordinateFrameAt (I := I) x₀ (m 3) x₀)))
      hRm hcurv (m 0) (m 1) (m 2)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1

/-- **A2 — the lowered Riemann time derivative `∂ₜRm04` in `∇²Ric`-expanded form.**
Differentiating the component lowering realization `realizedRmBase_eq_curvCoeff_lower`
through the product rule: `∂ₜ(curvCoeff·g) = (∂ₜcurvCoeff)·g + curvCoeff·(∂ₜg)`, with
`∂ₜcurvCoeff = rm13Deriv_of_solution` and `∂ₜg = metricCompInFrame_timeDeriv = −2Ric`.
The output is the expanded `∇²Ric` form; step B converts it to `ΔRm04 + 2B − drift`. -/
theorem realizedRmBase_timeDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt : Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal (I := I) S
      (coordInv (I := I) S x₀) gInvDt (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀))
    (hSmooth : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M => (S.family.metric q.1).inner q.2
          (coordinateFrameAt (I := I) x₀ a q.2) (coordinateFrameAt (I := I) x₀ b q.2)) (s, x))
    (hFdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.carrier ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y
          (coordinateFrameAt (I := I) x₀ a y) (coordinateFrameAt (I := I) x₀ b y)) x)
    (hFtdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s y a b) x)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
        (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)))
    (hcov : ∀ s, s ∈ D.carrier ->
      CovariantDerivative.ContMDiffCovariantDerivativeLocally (S.family.connection s) (1 : WithTop ℕ∞))
    (hRm : ∀ s, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection s) (S.base.rm13 s))
    (hcurv : ∀ s, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I)
        (S.family.connection s) x₀)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (m : Fin 4 -> CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ((christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 0) p (m 1) (m 2)
            - christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 1) p (m 0) (m 2))
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p
          + DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (S.family.connection (t : Real)) x₀ (m 0) (m 1) (m 2) p
            * ((-2 : Real) * ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p)))
      D.carrier
      (t : Real) := by
  have hbase : ∀ s, s ∈ D.carrier ->
      realizedRmBase (I := I) S x₀ s x₀ m =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection s) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ (m 3) p :=
    fun s hs => realizedRmBase_eq_curvCoeff_lower S x₀ s (hcov s hs) (hRm s hs) (hcurv s hs) m
  have hterm : ∀ p ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
            (S.family.connection s) x₀ (m 0) (m 1) (m 2) p
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ (m 3) p)
        ((christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 0) p (m 1) (m 2)
            - christoffelVariationCovDerivCoordAt (I := I) (S.family.connection (t : Real))
              (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
                (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
              (t : Real) x₀ (m 1) p (m 0) (m 2))
            * metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p
          + DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (S.family.connection (t : Real)) x₀ (m 0) (m 1) (m 2) p
            * ((-2 : Real) * ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ (m 3) p))
        D.carrier (t : Real) := by
    intro p _
    have h1 := rm13Deriv_of_solution (I := I) S hS x₀ gInvDt hmetricFrame hSmooth hFdiff hFtdiff hmix
      t (m 0) (m 1) (m 2) p
    have h2 := metricCompInFrame_timeDeriv (I := I) S hS (coordinateFrameAt (I := I) x₀) t x₀ (m 3) p
    exact h1.mul h2
  exact (HasDerivWithinAt.sum hterm).congr
    (fun y hy => by rw [Finset.sum_apply]; exact hbase y hy)
    (by rw [Finset.sum_apply]; exact hbase (t : Real) (D.regular_subset t.2))

end DifferentialGeometry.PDE.RicciFlow
