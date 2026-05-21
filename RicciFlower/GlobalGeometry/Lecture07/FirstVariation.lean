import RicciFlower.GlobalGeometry.Jacobi
import RicciFlower.GlobalGeometry.Lecture07.CoordinateEquation
import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.LeviCivita.Torsion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.4: first variation of arc length

This file adds the book-facing arc-length and energy interfaces for Lecture 7.4.
The actual first-variation formula is represented by predicates whose right
hand sides use the pullback covariant-derivative API from Lecture 7.3.  Formal
fixed-endpoint and geodesic corollaries are proved here; the remaining analytic
producer is the metric-compatible product rule along a smooth variation plus
differentiation under the interval integral.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter intervalIntegral
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Metric product-rule producer -/

/-- Expand a tangent-space inner product in any local frame. -/
private theorem inner_eq_sum_frame
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    (u v : TangentSpace I x) :
    g.inner x u v =
      ∑ i : ι, ∑ j : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
  classical
  have hu :
      u = ∑ i : ι,
        frameVec (I := I) e b u i • e.localFrame b i x := by
    calc
      u = ∑ i : ι, (e.basisAt b hx).repr u i • e.localFrame b i x := by
        simpa [e.localFrame_apply_of_mem_baseSet b hx] using
          ((e.basisAt b hx).sum_repr u).symm
      _ = ∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [frameVec, localFrame_coeff_eq_basis_repr (I := I) e b hx i u]
  have hv :
      v = ∑ j : ι,
        frameVec (I := I) e b v j • e.localFrame b j x := by
    calc
      v = ∑ j : ι, (e.basisAt b hx).repr v j • e.localFrame b j x := by
        simpa [e.localFrame_apply_of_mem_baseSet b hx] using
          ((e.basisAt b hx).sum_repr v).symm
      _ = ∑ j : ι, frameVec (I := I) e b v j • e.localFrame b j x := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [frameVec, localFrame_coeff_eq_basis_repr (I := I) e b hx j v]
  calc
    g.inner x u v =
        g.inner x
          (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x) v := by
            exact congrArg (fun z => g.inner x z v) hu
    _ =
        g.inner x
          (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x)
          (∑ j : ι, frameVec (I := I) e b v j • e.localFrame b j x) := by
            exact congrArg (fun z =>
              g.inner x
                (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x) z) hv
    _ = ∑ j : ι, ∑ i : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
            simp [Coordinates.metricCompForMetricInFrame, map_sum, Finset.mul_sum,
              mul_assoc, mul_left_comm]
    _ = ∑ i : ι, ∑ j : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
            rw [Finset.sum_comm]

/-- A fixed-frame along-curve covariant-derivative witness contains the
ordinary derivative of the frame-coordinate vector. -/
private theorem HasFrameAlongAt.hasDerivAt_frameVec
    {ι : Type*} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {gamma : Curve M}
    {S : VectorFieldAlong I gamma} {t : Real}
    {A : TangentSpace I (gamma t)}
    (hA : HasFrameAlongAt (I := I) cov e b gamma S t A) :
    HasDerivAt (fun r : Real => frameVec (I := I) e b (S r))
      (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
        e b gamma S t (1 : TangentSpace 𝓘(Real, Real) t)) t := by
  rw [hasDerivAt_pi]
  intro k
  have hkmd :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t :=
    (hA.2.2 k).1
  have hkmf :
      HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t) :=
    hkmd.hasMFDerivAt
  have hkf :
      HasFDerivAt
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r))
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t) t :=
    HasMFDerivAt.hasFDerivAt hkmf
  have hk :
      HasDerivAt
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r))
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t)
            (1 : TangentSpace 𝓘(Real, Real) t)) t :=
    HasFDerivAt.hasDerivAt hkf
  simpa [frameVec, frameDerivVec, frameCoeffDeriv,
    RicciFlower.extDerivFun_real_eq_mfderiv] using hk

/-- Metric compatibility gives the derivative of local-frame metric
components along a differentiable real curve. -/
private theorem metricComp_hasDerivAt_along
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {gamma : Curve M} {t : Real}
    (hx : gamma t ∈ e.baseSet)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (a c : ι) :
    HasDerivAt
      (fun r : Real =>
        Coordinates.metricCompForMetricInFrame (I := I) g
          (e.localFrame b) (gamma r) a c)
      ((∑ p : ι,
          frameGamma (I := I) (M := M) cov e b (gamma t)
            (curveVelocity I gamma t) a p *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (e.localFrame b) (gamma t) p c) +
        (∑ p : ι,
          frameGamma (I := I) (M := M) cov e b (gamma t)
            (curveVelocity I gamma t) c p *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (e.localFrame b) (gamma t) a p)) t := by
  classical
  let frame := e.localFrame b
  let hframe := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hf : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => Coordinates.metricCompForMetricInFrame (I := I) g frame y a c)
      (gamma t) :=
    Coordinates.metricComp_mdiffAt (I := I) g frame hframe e.open_baseSet hx a c
  have hderiv :
      HasDerivAt
        (fun r : Real =>
          Coordinates.metricCompForMetricInFrame (I := I) g frame (gamma r) a c)
        (extDerivFun (I := I)
          (fun y : M => Coordinates.metricCompForMetricInFrame (I := I) g frame y a c)
          (gamma t) (curveVelocity I gamma t)) t :=
    extDerivFun_along_curve_eq_deriv (I := I) hf hgamma
  have hformula :=
    Coordinates.metricComp_extDeriv_tangent
      (I := I) g cov hmc frame hframe e.open_baseSet hx
      (curveVelocity I gamma t) a c
  rw [hformula] at hderiv
  simpa [frame, hframe, frameGamma, Coordinates.christoffelAlongInFrame]
    using hderiv

/-- Pure coefficient algebra behind metric compatibility:
differentiate `Sᵢ Tⱼ Gᵢⱼ`, substitute
`G'ᵢⱼ = Γᵖᵢ Gₚⱼ + Γᵖⱼ Gᵢₚ`, and reindex the Christoffel terms into
`⟨∇S,T⟩ + ⟨S,∇T⟩`. -/
private theorem frame_inner_product_rule_algebra
    {ι : Type*} [Fintype ι]
    (S T dS dT : ι -> Real) (Γ : Matrix ι ι Real)
    (G : ι -> ι -> Real) :
    (∑ i : ι, ∑ j : ι,
        ((dS i * T j + S i * dT j) * G i j +
          (S i * T j) *
            ((∑ p : ι, Γ p i * G p j) +
              (∑ p : ι, Γ p j * G i p)))) =
      (∑ i : ι, ∑ j : ι,
        coeffCov Γ dS S i * T j * G i j) +
      (∑ i : ι, ∑ j : ι,
        S i * coeffCov Γ dT T j * G i j) := by
  classical
  have hΓS :
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p i * G p j)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, Γ i p * S p) * T j * G i j) := by
    calc
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p i * G p j))
          = ∑ i : ι, ∑ j : ι, ∑ p : ι,
              S i * T j * (Γ p i * G p j) := by
              simp [Finset.mul_sum]
      _ = ∑ i : ι, ∑ p : ι, ∑ j : ι,
              S i * T j * (Γ p i * G p j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ i : ι, ∑ j : ι,
              S i * T j * (Γ p i * G p j) := by
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ j : ι, ∑ i : ι,
              S i * T j * (Γ p i * G p j) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ j : ι,
              (∑ i : ι, Γ p i * S i) * T j * G p j := by
              refine Finset.sum_congr rfl fun p _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      _ = ∑ i : ι, ∑ j : ι,
              (∑ p : ι, Γ i p * S p) * T j * G i j := rfl
  have hΓT :
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p j * G i p)) =
        (∑ i : ι, ∑ j : ι,
          S i * (∑ p : ι, Γ j p * T p) * G i j) := by
    calc
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p j * G i p))
          = ∑ i : ι, ∑ j : ι, ∑ p : ι,
              S i * T j * (Γ p j * G i p) := by
              simp [Finset.mul_sum]
      _ = ∑ i : ι, ∑ p : ι, ∑ j : ι,
              S i * T j * (Γ p j * G i p) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ p : ι,
              S i * (∑ j : ι, Γ p j * T j) * G i p := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.mul_sum]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
      _ = ∑ i : ι, ∑ j : ι,
              S i * (∑ p : ι, Γ j p * T p) * G i j := rfl
  have hΓS' :
      (∑ i : ι, ∑ j : ι, ∑ p : ι,
          S i * T j * (Γ p i * G p j)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, Γ i p * S p) * T j * G i j) := by
    simpa [Finset.mul_sum] using hΓS
  have hΓT' :
      (∑ i : ι, ∑ j : ι, ∑ p : ι,
          S i * T j * (Γ p j * G i p)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, S i * (Γ j p * T p)) * G i j) := by
    simpa [Finset.mul_sum] using hΓT
  simp [coeffCov, Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, add_mul]
  rw [hΓS', hΓT']
  ring

/-- Metric-compatible product rule for the inner product of two pullback
fields along a real curve. -/
theorem inner_hasDerivAt_of_pbCov
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {gamma : Curve M} {S T : VectorFieldAlong I gamma} {t : Real}
    {A B : TangentSpace I (gamma t)}
    (hS : HasPBCovAlongAt (I := I) cov gamma S t A)
    (hT : HasPBCovAlongAt (I := I) cov gamma T t B) :
    HasDerivAt
      (fun r : Real => g.inner (gamma r) (S r) (T r))
      (g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B) t := by
  classical
  let e := Coordinates.coordinateTrivializationAt (I := I) (gamma t)
  let b : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real E :=
    Module.finBasis Real E
  have hx : gamma t ∈ e.baseSet := by
    change (chartAt H (gamma t)).source (gamma t)
    exact mem_chart_source H (gamma t)
  have hSf : HasFrameAlongAt (I := I) cov e b gamma S t A := by
    simpa [HasPBCovAlongAt, HasFrameAlongAt] using
      (HasPBCovDerivAt.toFrame (I := I) (I' := 𝓘(Real, Real))
        (cov := cov) (f := gamma) (S := S) (y := t)
        (u := (1 : TangentSpace 𝓘(Real, Real) t)) (A := A)
        hS e b hx)
  have hTf : HasFrameAlongAt (I := I) cov e b gamma T t B := by
    simpa [HasPBCovAlongAt, HasFrameAlongAt] using
      (HasPBCovDerivAt.toFrame (I := I) (I' := 𝓘(Real, Real))
        (cov := cov) (f := gamma) (S := T) (y := t)
        (u := (1 : TangentSpace 𝓘(Real, Real) t)) (A := B)
        hT e b hx)
  let Γ : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b gamma t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let dS : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma S t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let dT : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma T t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let G : Real ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun r i j =>
      Coordinates.metricCompForMetricInFrame (I := I) g
        (e.localFrame b) (gamma r) i j
  let dG : Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γ p i * G t p j) +
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γ p j * G t i p)
  let Q : Real -> Real :=
    fun r =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
          frameVec (I := I) e b (S r) i *
            frameVec (I := I) e b (T r) j * G r i j
  let dQ : Real :=
    ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ((dS i * frameVec (I := I) e b (T t) j +
            frameVec (I := I) e b (S t) i * dT j) * G t i j +
          (frameVec (I := I) e b (S t) i *
              frameVec (I := I) e b (T t) j) * dG i j)
  have hSder :
      HasDerivAt (fun r : Real => frameVec (I := I) e b (S r)) dS t := by
    simpa [dS] using hSf.hasDerivAt_frameVec (I := I)
  have hTder :
      HasDerivAt (fun r : Real => frameVec (I := I) e b (T r)) dT t := by
    simpa [dT] using hTf.hasDerivAt_frameVec (I := I)
  have hGder (i j : Coordinates.CoordinateIdx (𝕜 := Real) E) :
      HasDerivAt (fun r : Real => G r i j) (dG i j) t := by
    have hγ : MDifferentiableAt 𝓘(Real, Real) I gamma t := hSf.2.1
    have hmetric :=
      metricComp_hasDerivAt_along (I := I) g cov hmc e b hx hγ i j
    simpa [G, dG, Γ, frameGammaMat] using hmetric
  have hQ : HasDerivAt Q dQ t := by
    dsimp [Q, dQ]
    refine HasDerivAt.fun_sum ?_
    intro i _hi
    refine HasDerivAt.fun_sum ?_
    intro j _hj
    have hSij := hasDerivAt_pi.mp hSder i
    have hTij := hasDerivAt_pi.mp hTder j
    exact ((hSij.mul hTij).mul (hGder i j))
  have hmem : ∀ᶠ r : Real in 𝓝 t, gamma r ∈ e.baseSet :=
    hSf.2.1.continuousAt.tendsto.eventually (e.open_baseSet.mem_nhds hx)
  have heq :
      (fun r : Real => g.inner (gamma r) (S r) (T r)) =ᶠ[𝓝 t] Q := by
    filter_upwards [hmem] with r hr
    exact inner_eq_sum_frame (I := I) g e b hr (S r) (T r)
  have hderiv : HasDerivAt
      (fun r : Real => g.inner (gamma r) (S r) (T r)) dQ t :=
    hQ.congr_of_eventuallyEq heq
  have hdQ :
      dQ = g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B := by
    have hAvec := HasFrameDerivAt.frame_vec_eq (I := I) hSf
    have hBvec := HasFrameDerivAt.frame_vec_eq (I := I) hTf
    have hAlg :=
      frame_inner_product_rule_algebra
        (S := frameVec (I := I) e b (S t))
        (T := frameVec (I := I) e b (T t))
        (dS := dS) (dT := dT) (Γ := Γ) (G := G t)
    calc
      dQ =
          (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              coeffCov Γ dS (frameVec (I := I) e b (S t)) i *
                frameVec (I := I) e b (T t) j * G t i j) +
          (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              frameVec (I := I) e b (S t) i *
                coeffCov Γ dT (frameVec (I := I) e b (T t)) j * G t i j) := by
            simpa [dQ, dG, G] using hAlg
      _ = g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B := by
            rw [inner_eq_sum_frame (I := I) g e b hx A (T t)]
            rw [inner_eq_sum_frame (I := I) g e b hx (S t) B]
            rw [hAvec, hBvec]
  simpa [hdQ] using hderiv

/-! ## Arc-length and energy functionals -/

/-- Pointwise speed of a curve with respect to `g`. -/
def pathSpeed (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t : Real) :
    Real :=
  Real.sqrt (speedSq (I := I) g gamma t)

/-- Arc length of a curve on the oriented interval `a..b`. -/
def pathLength (g : SmoothRiemannianMetric I M) (gamma : Curve M)
    (a b : Real) : Real :=
  ∫ t in a..b, pathSpeed (I := I) g gamma t

/-- Energy of a curve on the oriented interval `a..b`, using squared speed. -/
def pathEnergy (g : SmoothRiemannianMetric I M) (gamma : Curve M)
    (a b : Real) : Real :=
  ∫ t in a..b, speedSq (I := I) g gamma t

/-- Length of the time curves in a two-parameter variation. -/
def variationLength (g : SmoothRiemannianMetric I M) (F : Surface M)
    (a b s : Real) : Real :=
  pathLength (I := I) g (timeCurve F s) a b

/-- Energy of the time curves in a two-parameter variation. -/
def variationEnergy (g : SmoothRiemannianMetric I M) (F : Surface M)
    (a b s : Real) : Real :=
  pathEnergy (I := I) g (timeCurve F s) a b

/-- The unit tangent field `T / |T|` along a curve.  This is only intended for
use under the usual nonzero-speed hypotheses; no such hypothesis is needed to
state the expression. -/
def unitTangentAlong (g : SmoothRiemannianMetric I M) (gamma : Curve M) :
    VectorFieldAlong I gamma :=
  fun t => (pathSpeed (I := I) g gamma t)⁻¹ • curveVelocity I gamma t

theorem pathSpeed_eq_one_of_unitSpeed
    {g : SmoothRiemannianMetric I M} {gamma : Curve M}
    (h : IsUnitSpeed (I := I) g gamma) (t : Real) :
    pathSpeed (I := I) g gamma t = 1 := by
  simp [pathSpeed, h t]

theorem unitTangentAlong_eq_velocityAlong_of_unitSpeed
    {g : SmoothRiemannianMetric I M} {gamma : Curve M}
    (h : IsUnitSpeed (I := I) g gamma) :
    unitTangentAlong (I := I) g gamma = velocityAlong I gamma := by
  funext t
  simp [unitTangentAlong, velocityAlong, pathSpeed_eq_one_of_unitSpeed (I := I) h t]

/-! ## Boundary and first-variation right hand sides -/

/-- Boundary term `⟨V,U⟩|_a^b` for a variation field `V` and a chosen field `U`
along the base time curve. -/
def lengthBoundaryTerm (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (U : VectorFieldAlong I (timeCurve F s0)) : Real :=
  g.inner (F (s0, b)) (variationField I F s0 b) (U b) -
    g.inner (F (s0, a)) (variationField I F s0 a) (U a)

/-- Interior term `∫ ⟨V,A⟩` for the first variation formula. -/
def lengthInteriorTerm (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  ∫ t in a..b, g.inner (F (s0, t)) (variationField I F s0 t) (A t)

/-- RHS of the full length first-variation formula using `U = T / |T|` and
`A = ∇_T U`. -/
def lengthFirstVariationRHS (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  -lengthInteriorTerm (I := I) g F s0 a b A +
    lengthBoundaryTerm (I := I) g F s0 a b
      (unitTangentAlong (I := I) g (timeCurve F s0))

/-- RHS of the unit-speed length first-variation formula using
`A = ∇_T T`. -/
def unitSpeedLengthFirstVariationRHS
    (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  -lengthInteriorTerm (I := I) g F s0 a b A +
    lengthBoundaryTerm (I := I) g F s0 a b (velocityAlong I (timeCurve F s0))

/-- Full first variation formula, with an explicit field `A = ∇_T(T/|T|)`.
The proof producer is intentionally separate from the formula interface. -/
def HasLengthFirstVariationAtWith
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real)
    (A : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  (∀ t ∈ Set.uIcc a b,
    HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (unitTangentAlong (I := I) g (timeCurve F s0)) t (A t)) ∧
  HasDerivAt (fun s => variationLength (I := I) g F a b s)
    (lengthFirstVariationRHS (I := I) g F s0 a b A) s0

/-- Existential form of the full first variation formula. -/
def HasLengthFirstVariationAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real) : Prop :=
  ∃ A : VectorFieldAlong I (timeCurve F s0),
    HasLengthFirstVariationAtWith (I := I) g cov F s0 a b A

/-- Unit-speed first variation formula, with an explicit acceleration field
`A = ∇_T T`. -/
def HasUnitSpeedLengthFirstVariationAtWith
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real)
    (A : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  IsUnitSpeed (I := I) g (timeCurve F s0) ∧
  (∀ t ∈ Set.uIcc a b,
    HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) ∧
  HasDerivAt (fun s => variationLength (I := I) g F a b s)
    (unitSpeedLengthFirstVariationRHS (I := I) g F s0 a b A) s0

/-- Existential form of the unit-speed first variation formula. -/
def HasUnitSpeedLengthFirstVariationAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real) : Prop :=
  ∃ A : VectorFieldAlong I (timeCurve F s0),
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A

/-- Unit-speed first variation of arc length.

The checked geometric input now includes the pullback metric-compatible product
rule `inner_hasDerivAt_of_pbCov`.  The remaining proof content is the analytic
step differentiating the interval integral of the speed in the variation
parameter. -/
theorem firstVariation_unitSpeed
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htf : RicciFlower.LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (hF : SmoothSurface (I := I) F)
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0))
    (hA : ∀ t ∈ Set.uIcc a b,
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) :
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A := by
  refine ⟨hunit, hA, ?_⟩
  /-
  Remaining analytic bridge:
  for the smooth two-parameter speed integrand, differentiate
  `s ↦ ∫ t in a..b, sqrt (speedSq g (timeCurve F s) t)` at `s0`;
  use `inner_hasDerivAt_of_pbCov`, `hF.hasTime_param_eq_dsTime htf`,
  unit speed, and integration by parts in `t`.
  -/
  sorry

theorem HasLengthFirstVariationAtWith.unitSpeed
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0)) :
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A := by
  rcases h with ⟨hA, hderiv⟩
  refine ⟨hunit, ?_, ?_⟩
  · intro t ht
    simpa [HasPBCovAccelAt, unitTangentAlong_eq_velocityAlong_of_unitSpeed
      (I := I) hunit] using hA t ht
  · simpa [lengthFirstVariationRHS, unitSpeedLengthFirstVariationRHS,
      lengthBoundaryTerm, unitTangentAlong_eq_velocityAlong_of_unitSpeed
      (I := I) hunit] using hderiv

/-! ## Fixed-endpoint formal consequences -/

/-- The endpoint `t` is fixed to first order in the variation parameter near
`s0`. -/
def HasFixedEndpointAt (F : Surface M) (s0 t : Real) : Prop :=
  Filter.EventuallyEq (𝓝 s0) (fun s : Real => F (s, t))
    (fun _s : Real => F (s0, t))

theorem variationField_eq_zero_of_fixedEndpoint
    {F : Surface M} {s0 t : Real}
    (h : HasFixedEndpointAt F s0 t) :
    variationField I F s0 t = 0 := by
  unfold variationField paramCurve HasFixedEndpointAt at *
  have hvel :
      curveVelocity I (fun s : Real => F (s, t)) s0 =
        curveVelocity I (fun _s : Real => F (s0, t)) s0 := by
    unfold curveVelocity
    rw [Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) h]
  rw [hvel]
  exact curveVelocity_const (I := I) (x := F (s0, t)) s0

theorem lengthBoundaryTerm_eq_zero_of_fixedEndpoints
    {g : SmoothRiemannianMetric I M} {F : Surface M}
    {s0 a b : Real} {U : VectorFieldAlong I (timeCurve F s0)}
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b) :
    lengthBoundaryTerm (I := I) g F s0 a b U = 0 := by
  have hVa : variationField I F s0 a = 0 :=
    variationField_eq_zero_of_fixedEndpoint (I := I) ha
  have hVb : variationField I F s0 b = 0 :=
    variationField_eq_zero_of_fixedEndpoint (I := I) hb
  rw [lengthBoundaryTerm, hVa, hVb]
  have hb0 :
      g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) (U b) = 0 := by
    rw [show g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) =
      (0 : TangentSpace I (F (s0, b)) →L[Real] Real) by simp]
    rfl
  have ha0 :
      g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) (U a) = 0 := by
    rw [show g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) =
      (0 : TangentSpace I (F (s0, a)) →L[Real] Real) by simp]
    rfl
  change
    g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) (U b) -
      g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) (U a) = 0
  rw [hb0, ha0]
  ring

theorem HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s)
      (-lengthInteriorTerm (I := I) g F s0 a b A) s0 := by
  rcases h with ⟨_hunit, _hA, hderiv⟩
  simpa [unitSpeedLengthFirstVariationRHS,
    lengthBoundaryTerm_eq_zero_of_fixedEndpoints (I := I) (g := g)
      (F := F) (U := velocityAlong I (timeCurve F s0)) ha hb] using hderiv

theorem HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints_geodesic
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b)
    (hA0 : ∀ t : Real, A t = 0) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s) 0 s0 := by
  have hfixed :=
    HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints (I := I)
      (g := g) (cov := cov) (F := F) (s0 := s0) (a := a) (b := b)
      (A := A) h ha hb
  have hint :
      lengthInteriorTerm (I := I) g F s0 a b A = 0 := by
    unfold lengthInteriorTerm
    rw [show (∫ t in a..b,
        g.inner (F (s0, t)) (variationField I F s0 t) (A t)) =
          ∫ _t in a..b, (0 : Real) from ?_]
    · simp
    · apply intervalIntegral.integral_congr
      intro t _ht
      change g.inner (F (s0, t)) (variationField I F s0 t) (A t) = 0
      rw [hA0 t]
      exact map_zero (g.inner (F (s0, t)) (variationField I F s0 t))
  simpa [hint] using hfixed

end Lecture07
end GlobalGeometry
end RicciFlower
