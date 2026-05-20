import RicciFlower.RicciFlow.Evolution.Ricci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Norm Evolution Producers

This file is the Ricci-flow evolution layer for intrinsic Ricci-norm data.
`RicciFlow.Basic` owns the definitions and algebraic component assembly; this
file owns the smooth-solution producers that need Section 6 evolution inputs.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Regularity package needed to use scalar-Laplacian linearity on the
intrinsic trace-free Ricci norm expression.  This is kept below Section 10 so
the book-facing theorem does not acquire regularity assumptions. -/
structure TFLapReg
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  ricci_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) y
  ricci_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x
  scalar_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) y
  scalar_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t) (S.scalar t) y) x
  scalar_sq_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => S.scalar t z ^ 2) y
  scalar_sq_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2) y) x
  scalar_sq_div_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => S.scalar t z ^ 2 / 3) y
  scalar_sq_div_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2 / 3) y) x

/-- Smooth solutions provide the spatial regularity needed by the intrinsic
trace-free Ricci-norm Laplacian identity.

This is a lower regularity producer: it should eventually be proved from
spatial smoothness of metric-derived scalar and Ricci tensors, plus smoothness
of tensor norms. -/
theorem tfLapReg
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    TFLapReg (I := I) S := by
  exact
    { ricci_space := hS.ricciRegular.ricci_norm_space
      ricci_grad := hS.ricciRegular.ricci_norm_grad
      scalar_space := hS.scalarRegular.scalar_space
      scalar_grad := hS.scalarRegular.scalar_grad
      scalar_sq_space := hS.scalarRegular.scalar_sq_space
      scalar_sq_grad := hS.scalarRegular.scalar_sq_grad
      scalar_sq_div_space := hS.scalarRegular.scalar_sq_div_space
      scalar_sq_div_grad := hS.scalarRegular.scalar_sq_div_grad }

/-- Intrinsic scalar-Laplacian identity for
`|Ric|² - R² / 3`, written without Section 10 names. -/
theorem tfLapCore
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    ∀ t, t ∈ D.carrier -> ∀ x,
      Realized.laplacianAt (I := I) (flowG (I := I) S) t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
        ricciNormLap (I := I) S t x -
          (2 * S.scalar t x *
              Realized.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x +
            2 * (S.family.metric t).inner x
              (Realized.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
              (Realized.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)) / 3 := by
  intro t ht x
  let G : Realized.RealizedMetricFamily (I := I) (M := M) Real :=
    flowG (I := I) S
  have hreg := tfLapReg (I := I) S hS
  have hsq :
      Realized.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2) x =
        2 * S.scalar t x * Realized.laplacianAt (I := I) G t
            (S.scalar t) x +
          2 * (G.metric t).inner x
            (Realized.gradientAt (I := I) G t (S.scalar t) x)
            (Realized.gradientAt (I := I) G t (S.scalar t) x) :=
    Realized.laplacianAt_sq_of_scalarRegular (I := I) G t
      (hreg.scalar_space t ht) (hreg.scalar_grad t ht)
  have hdivFun :
      (fun y : M => S.scalar t y ^ 2 / 3) =
        ((1 / 3 : Real) • fun y : M => S.scalar t y ^ 2) := by
    funext y
    simp [Pi.smul_apply]
    ring
  have hdiv :
      Realized.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2 / 3) x =
        Realized.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2) x / 3 := by
    rw [hdivFun]
    rw [Realized.laplacianAt_smul (I := I) G t (1 / 3 : Real)
      (hreg.scalar_sq_space t ht) (hreg.scalar_sq_grad t ht x)]
    ring
  have hsub :
      Realized.laplacianAt (I := I) G t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
          Realized.laplacianAt (I := I) G t (ricciNorm (I := I) S t) x -
          Realized.laplacianAt (I := I) G t
            (fun y : M => S.scalar t y ^ 2 / 3) x :=
    Realized.laplacianAt_sub (I := I) G t
      (hreg.ricci_space t ht) (hreg.scalar_sq_div_space t ht)
      (hreg.ricci_grad t ht x) (hreg.scalar_sq_div_grad t ht x)
  calc
    Realized.laplacianAt (I := I) (flowG (I := I) S) t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
        Realized.laplacianAt (I := I) G t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x := rfl
    _ = Realized.laplacianAt (I := I) G t (ricciNorm (I := I) S t) x -
          Realized.laplacianAt (I := I) G t
            (fun y : M => S.scalar t y ^ 2 / 3) x := hsub
    _ = ricciNormLap (I := I) S t x -
          (2 * S.scalar t x *
              Realized.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x +
            2 * (S.family.metric t).inner x
              (Realized.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
              (Realized.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)) / 3 := by
          rw [hdiv, hsq]
          simp [G, ricciNormLap, flowG]

/-- Canonical component data needed to assemble the intrinsic Ricci-norm heat
equation.

The shared `roughLapInner` field is the contraction `<Delta Ric, Ric>`.
Producing this package from a smooth Ricci flow is the genuine Ricci tensor
evolution/Bochner frontier; consuming it is just algebra. -/
structure RicciHeatData
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) where
  roughLapInner : Real -> M -> Real
  timeDeriv :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNorm (I := I) S) roughLapInner (ricciReact (I := I) S)
  laplacian :
    RicciNormLaplacianComponentsOn
      (ricciNormLap (I := I) S) roughLapInner (ricciGradSq (I := I) S)

/-- Algebraic assembly of the intrinsic Ricci-norm heat equation from the
canonical component data. -/
theorem ricciHeat_of_data
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (h : RicciHeatData (I := I) S) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNorm (I := I) S)
      (ricciNormLap (I := I) S)
      h.roughLapInner
      (ricciGradSq (I := I) S)
      (ricciReact (I := I) S)
      h.timeDeriv
      h.laplacian

/-- Canonical inverse-metric coefficients in the coordinate frame centered at
`x0`, for the metric at time `t`. -/
noncomputable def coordInv
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    Real -> Realized.InverseMetricComponents M
      (Coordinates.CoordinateIdx (𝕜 := Real) E) :=
  fun t x i j =>
    Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.family.metric t) x0 i j (extChartAt I x0 x)

/-- The canonical coordinate inverse really is the inverse metric in the
centered coordinate basis at the center point. -/
theorem coordInvReal
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) (t : Real) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x0
      (Coordinates.coordinateFrameAt_toBasis (I := I) x0)
      (fun i j => coordInv (I := I) S x0 t x0 i j) := by
  simpa [coordInv] using
    Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) (S.family.metric t) x0

/-- Canonical coordinate rough Laplacian components
`g^{ab} (nabla_a nabla_b Ric)_ij` in the coordinate frame centered at `x0`,
once the coordinate components of `nabla^2 Ric` have been produced. -/
noncomputable def coordRoughRic
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M)
    (nabla2Ric : Real -> M ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) :
    Real -> M ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
  roughLapRicInFrame
    (M := M) (coordInv (I := I) S x0) nabla2Ric

/-- Produce intrinsic Ricci-norm heat data from an existing frame-level Ricci
evolution and Bochner route, plus the frame-to-intrinsic identifications. -/
private def ricciDataOfFrame
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) (ricciNormLap (I := I) S)
      roughLapRic (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hnorm : forall t x,
      ricciNormSqInFrame (I := I) S gInv frame t x =
        ricciNorm (I := I) S t x)
    (hnabla : forall t x,
      nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
        ricciGradSq (I := I) S t x)
    (hreact : forall t x,
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
        ricciReact (I := I) S t x) :
    RicciHeatData (I := I) S := by
  refine
    { roughLapInner :=
        roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
      timeDeriv := ?_
      laplacian := ?_ }
  · have hdt :=
      ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S Rm04 gInv frame roughLapRic
        h_inv h_ricci hInvSym hRicSym
    intro t x
    change
      HasDerivWithinAt
        (fun s : Real => ricciNorm (I := I) S s x)
        (2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
            (t : Real) x +
          4 * ricciReact (I := I) S (t : Real) x)
        D.carrier
        (t : Real)
    have hframeDeriv :=
      (hdt t x).congr_deriv (by
        rw [hreact (t : Real) x])
    refine hframeDeriv.congr_of_eventuallyEq ?_ ?_
    filter_upwards with s
    exact (hnorm s x).symm
    exact (hnorm (t : Real) x).symm
  · have hlap :=
      ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S gInv frame roughLapRic (ricciNormLap (I := I) S)
        nablaRic h_lap
    intro t x
    change
      ricciNormLap (I := I) S t x =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x +
          2 * ricciGradSq (I := I) S t x
    exact (hlap t x).trans (by
      rw [hnabla t x])

/-- Canonical coordinate-frame data still missing from the smooth-solution
producer.

The component functions are fixed by `SolutionOn`: inverse-metric coefficients
are `coordInv`, the frame is `coordinateFrameAt`, `nablaRic` is the canonical
`nablaRicComp`, and the rough Laplacian is the metric trace `coordRoughRic` of
the produced `nabla2Ric` components.  The remaining fields are the genuine
lower producers: inverse-metric evolution, Ricci evolution,
Bochner/Laplacian realization, and symmetry bookkeeping. -/
structure RicciCoordData
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) where
  nabla2Ric : forall _x0, Real -> M ->
    Coordinates.CoordinateIdx (𝕜 := Real) E ->
    Coordinates.CoordinateIdx (𝕜 := Real) E ->
    Coordinates.CoordinateIdx (𝕜 := Real) E ->
    Coordinates.CoordinateIdx (𝕜 := Real) E -> Real
  invEvol : forall x0,
    InverseMetricEvolutionEquationInFrame
      (I := I) S (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0)
  ricciEvol : forall x0,
    RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0)
      (coordRoughRic (I := I) S x0 (nabla2Ric x0))
  invSymm : forall x0 t x i j,
    coordInv (I := I) S x0 t x i j =
      coordInv (I := I) S x0 t x j i
  ricciSymm : forall x0 t x i j,
    ricciCompInFrame (I := I) S
        (Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      ricciCompInFrame (I := I) S
        (Coordinates.coordinateFrameAt (I := I) x0) t x j i
  lap : forall x0,
    Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) (ricciNormLap (I := I) S)
      (coordRoughRic (I := I) S x0 (nabla2Ric x0))
      (ricciTwoTensorField (I := I) S)
      (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0)
      (nablaRicComp (I := I) S (Coordinates.coordinateFrameAt (I := I) x0))

/-- The coordinate-frame zero-order reaction at the center is the intrinsic
reaction scalar.  This is not independent data: it is the coordinate expression
of the intrinsic contraction defining `ricciReact`. -/
theorem coordReact
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) (t : Real) :
    ricciNormCurvatureReactionInFrame
      (I := I) S S.base.rm04 (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0) t x0 =
      ricciReact (I := I) S t x0 := by
  -- Routine finite-sum bridge from the `inner0S_eq_coord` expansion of
  -- `ricciPair04` to `curvRicciRicciInFrame`.
  sorry

/-- Produce intrinsic Ricci-norm heat data from pointwise coordinate-frame
data.

At each spatial point `x`, this uses the coordinate frame centered at `x`
only to prove the two identities at that same point.  This avoids assuming any
global frame on `M`. -/
def ricciDataAtCoord
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hcoord : RicciCoordData (I := I) S) :
    RicciHeatData (I := I) S := by
  refine
    { roughLapInner := fun t x =>
        roughLapRicciInnerInFrame
          (I := I) S (coordRoughRic (I := I) S x (hcoord.nabla2Ric x))
          (coordInv (I := I) S x)
          (Coordinates.coordinateFrameAt (I := I) x) t x
      timeDeriv := ?_
      laplacian := ?_ }
  · intro t x
    let frame := Coordinates.coordinateFrameAt (I := I) x
    have hdt :=
      ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S S.base.rm04 (coordInv (I := I) S x) frame
        (coordRoughRic (I := I) S x (hcoord.nabla2Ric x))
        (hcoord.invEvol x) (hcoord.ricciEvol x)
        (hcoord.invSymm x) (hcoord.ricciSymm x)
    have hnorm : forall s : Real,
        ricciNormSqInFrame (I := I) S (coordInv (I := I) S x) frame s x =
          ricciNorm (I := I) S s x := by
      intro s
      have hbasis :
          forall i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            Coordinates.coordinateFrameAt_toBasis (I := I) x i = frame i x := by
        intro i
        simp [frame, Coordinates.coordinateFrameAt_toBasis_apply]
      simpa [ricciNorm] using
        ricciNormSq_basis (I := I) S (coordInv (I := I) S x) frame
          (Coordinates.coordinateFrameAt_toBasis (I := I) x)
          (coordInvReal (I := I) S x s) hbasis
    change
      HasDerivWithinAt
        (fun s : Real => ricciNorm (I := I) S s x)
        (2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (hcoord.nabla2Ric x))
              (coordInv (I := I) S x)
              frame (t : Real) x +
          4 * ricciReact (I := I) S (t : Real) x)
        D.carrier (t : Real)
    have hframeDeriv :=
      (hdt t x).congr_deriv (by
        rw [coordReact (I := I) S x (t : Real)])
    refine hframeDeriv.congr_of_eventuallyEq ?_ ?_
    filter_upwards with s
    exact (hnorm s).symm
    exact (hnorm (t : Real)).symm
  · intro t x
    let frame := Coordinates.coordinateFrameAt (I := I) x
    have hlap :=
      ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S (coordInv (I := I) S x) frame
        (coordRoughRic (I := I) S x (hcoord.nabla2Ric x))
        (ricciNormLap (I := I) S)
        (nablaRicComp (I := I) S frame) (hcoord.lap x)
    have hbasis :
        forall i : Coordinates.CoordinateIdx (𝕜 := Real) E,
          Coordinates.coordinateFrameAt_toBasis (I := I) x i = frame i x := by
      intro i
      simp [frame, Coordinates.coordinateFrameAt_toBasis_apply]
    have hnabla :
        nablaRicciNormSqInFrame (M := M) (nablaRicComp (I := I) S frame)
            (coordInv (I := I) S x) t x =
          ricciGradSq (I := I) S t x := by
      exact
        nablaRicciNorm_can (I := I) S (coordInv (I := I) S x) frame
          (Coordinates.coordinateFrameAt_toBasis (I := I) x)
          (coordInvReal (I := I) S x t)
          hbasis
    change
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (hcoord.nabla2Ric x))
              (coordInv (I := I) S x)
              frame t x +
          2 * ricciGradSq (I := I) S t x
    exact (hlap t x).trans (by
      rw [hnabla])

/-- Smooth-solution producer for canonical Ricci-norm component data.

This is the remaining lower-layer frontier.  It should be produced from the
canonical Ricci evolution equation, inverse-metric variation, canonical
`nabla Ric`, and the tensor norm-square Bochner/Laplacian realization. -/
def ricciHeatDataSmooth
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    RicciHeatData (I := I) S := by
  have hcoord : RicciCoordData (I := I) S := by
    sorry
  exact ricciDataAtCoord (I := I) S hcoord

/-- Canonical Ricci-norm heat producer from a smooth Ricci-flow solution.

This theorem is now a thin consumer of `ricciHeatDataSmooth`; the remaining
frontier is the component-data producer, not this algebraic heat assembly. -/
theorem ricciHeatSmooth
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) := by
  exact ricciHeat_of_data (I := I) S (ricciHeatDataSmooth (I := I) S _hS)

end RicciFlow
end RicciFlower
