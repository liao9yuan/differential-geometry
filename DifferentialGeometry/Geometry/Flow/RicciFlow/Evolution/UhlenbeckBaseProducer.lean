import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Rm13DerivProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.BookData
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RiemannFromRicci
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm

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

/-- **B3a′+B3b-input: the sign-correct 3D Kulkarni–Nomizu identity for the solution.**
For a Ricci-flow solution in dim 3, the lowered Riemann tensor is the metric KN combination
of the *geometric* Ricci/scalar fields (the convention used by the proved `∂ₜRic`/`∂ₜS`).
The displayed-vs-geometric sign bridge is isolated here (via the banked `traceData_can`, which
produces the trace data with `−Ric`/`−scalar`), so downstream differentiation works purely in
the geometric convention.  The orthonormal basis is only a proof device — the conclusion is
basis-free. -/
theorem solution_rm04_kn_firstTrace_gform_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis)
    (X Y Z W : TangentSpace I x) :
    S.base.rm04 t x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      -(S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
          * (S.base.metric t).inner x Y W
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
          * (S.base.metric t).inner x X W
        + S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
          * (S.base.metric t).inner x Y Z
        - S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
          * (S.base.metric t).inner x X Z
        + (S.scalar t x / 2)
          * ((S.base.metric t).inner x X Z * (S.base.metric t).inner x Y W
              - (S.base.metric t).inner x Y Z * (S.base.metric t).inner x X W) := by
  have h :=
    DifferentialGeometry.Integral.Connection.rm04_kn_gform (I := I)
      (traceData_can (I := I) S horth) X Y Z W
  simp only [ContinuousMultilinearMap.neg_apply] at h
  rw [h]; ring

/-- **Step 2 — the KN identity as a pointwise field (basis hidden).**  At any time `s`
and point `x` of a dim-3 solution, the lowered Riemann tensor is the geometric KN
combination of `Ric`/`scalar`/`g`.  The orthonormal basis is produced internally by
`exists_orthonormalBasisAt`, so this is differentiable in `s` (for B3b) and in `x`. -/
theorem solution_rm04_kn_field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (X Y Z W : TangentSpace I x) :
    S.base.rm04 s x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      -(S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
          * (S.base.metric s).inner x Y W
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
          * (S.base.metric s).inner x X W
        + S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
          * (S.base.metric s).inner x Y Z
        - S.ricciAt s x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
          * (S.base.metric s).inner x X Z
        + (S.scalar s x / 2)
          * ((S.base.metric s).inner x X Z * (S.base.metric s).inner x Y W
              - (S.base.metric s).inner x Y Z * (S.base.metric s).inner x X W) := by
  obtain ⟨basis, horth⟩ :=
    DifferentialGeometry.Integral.Connection.exists_orthonormalBasisAt (I := I)
      (S.base.metric s) x hdim
  exact solution_rm04_kn_firstTrace_gform_at (I := I) S s x horth X Y Z W

/-- **Step 4 (B3b) — time derivative of `Rm04` via the KN identity.**  Differentiate the
pointwise KN field `solution_rm04_kn_field` in `t`: the product rule on the `Ric`/`scalar`/`g`
scalar factors, with `∂ₜg = −2Ric` supplied internally by the PDE (`hS.equation`) and the
`Ric`/`scalar` time-derivatives taken as hypotheses (to be discharged from the proved
Ricci/scalar evolutions in the final assembly).  The derivative is the full 3D reaction–diffusion
right-hand side prior to the diffusion-split and reaction normalization. -/
theorem solution_rm04_timeDeriv_kn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (X Y Z W : TangentSpace I x)
    {ricXZ' ricYZ' ricXW' ricYW' sc' : Real}
    (hXZ : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
      ricXZ' D.carrier (t : Real))
    (hYZ : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z))
      ricYZ' D.carrier (t : Real))
    (hXW : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W))
      ricXW' D.carrier (t : Real))
    (hYW : HasDerivWithinAt
      (fun σ : Real => S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W))
      ricYW' D.carrier (t : Real))
    (hSc : HasDerivWithinAt (fun σ : Real => S.scalar σ x) sc' D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun σ : Real => S.base.rm04 σ x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W))
      (-(ricXZ' * (S.base.metric (t : Real)).inner x Y W
          + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z)
            * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)))
        + (ricYZ' * (S.base.metric (t : Real)).inner x X W
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)))
        + (ricXW' * (S.base.metric (t : Real)).inner x Y Z
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)))
        - (ricYW' * (S.base.metric (t : Real)).inner x X Z
            + S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
              * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z)))
        + (sc' / 2
            * ((S.base.metric (t : Real)).inner x X Z * (S.base.metric (t : Real)).inner x Y W
                - (S.base.metric (t : Real)).inner x Y Z * (S.base.metric (t : Real)).inner x X W)
          + S.scalar (t : Real) x / 2
            * ((-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
                  * (S.base.metric (t : Real)).inner x Y W
                + (S.base.metric (t : Real)).inner x X Z
                  * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W))
                - ((-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z))
                      * (S.base.metric (t : Real)).inner x X W
                    + (S.base.metric (t : Real)).inner x Y Z
                      * (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W))))))
      D.carrier (t : Real) := by
  have hfield :
      (fun σ : Real => S.base.rm04 σ x (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W))
        = fun σ : Real =>
          -(S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Z))
              * (S.base.metric σ).inner x Y W
            + S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y Z)
              * (S.base.metric σ).inner x X W
            + S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) X W)
              * (S.base.metric σ).inner x Y Z
            - S.ricciAt σ x (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y W)
              * (S.base.metric σ).inner x X Z
            + (S.scalar σ x / 2)
              * ((S.base.metric σ).inner x X Z * (S.base.metric σ).inner x Y W
                  - (S.base.metric σ).inner x Y Z * (S.base.metric σ).inner x X W) :=
    funext fun σ => solution_rm04_kn_field (I := I) S σ x hdim X Y Z W
  rw [hfield]
  have hg : ∀ P Q : TangentSpace I x,
      HasDerivWithinAt (fun σ : Real => (S.base.metric σ).inner x P Q)
        (-2 * S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (I := I) P Q))
        D.carrier (t : Real) := by
    intro P Q
    have h := hS.equation t x P Q
    simpa [RicciAtFamily.toTensorField_apply] using h
  have hd :=
    ((((((hXZ.neg.mul (hg Y W)).add ((hYZ.mul (hg X W)))).add (hXW.mul (hg Y Z))).sub
      (hYW.mul (hg X Z))).add
      (((hSc.div_const 2).mul (((hg X Z).mul (hg Y W)).sub ((hg Y Z).mul (hg X W)))))))
  convert hd using 1
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.sub_apply]
  ring

end DifferentialGeometry.PDE.RicciFlow
