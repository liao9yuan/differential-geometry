import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSdec
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueDensReg
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueConnBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSpeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04ProducerTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TimeRecursion
import DifferentialGeometry.Tensor.Auxiliary.SlotAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Wiring black box (B) into the endgame assembly (Route-K brick K7)

`Evolution/ForwardUniqueAssembly.lean` proves `forward_unique_of_inputs`: black box (B)'s exact
statement, with five data carriers and one residual `Prop` bundle `ForwardUniqueInputs` added.
This file **constructs the five carriers from (B)'s own fields** and discharges the bundle
members that today's producers can supply, so that instantiating the assembly at the endpoint
is a matter of supplying the remaining, precisely-named, quantitative inputs.

## The carriers

All five are built from the two metric families alone:

* `fuAvec` — `christoffelDiffSpeed` at the canonical chart-frame inverse/`∇Ric` families
  (`ForwardUniqueLifts.lean`);
* `fuSvec` — `uhlRmDiffSpeed` at the per-point-centred coordinate component families
  (`Rm04Producer.lean`) of the two flows;
* `fuSfield` — the genuine smooth `(0,4)` field `Rm⁰⁴(g₁) − g₁♭Rm¹³(g₂)`, whose pointwise value
  is `rmDiffLowAt`;
* `fuUflux`, `fuRem` — `sdecUflux` / `sdecRemFam` at those data.

The component families are indexed by a *reference* time interval `refD`; every `RealTimeInterval`
argument of `rm04Fam`/`rm04LapFam`/`rm04BFam`/`ricUpFam` and of `solOfMetric` is a phantom index
— the value depends on the solution only through its metric family — so `fam_refD` transports a
tail-interval statement to the reference one by `rfl`.

## The discharge lemmas

* `fuGamma` — the bundle's `gamma`, from `gamma_of_gram`;
* `fuRmContAt` — the time-continuity auxiliary of the Uhlenbeck conversion, *unconditional*
  on a positive-time tail: raising undoes lowering (`raiseAt_lower`), the lowered components
  are differentiable by the tail evolution, the Gram matrix is differentiable by the
  Ricci-flow equation, and the inverse of a continuous invertible matrix family is continuous;
* `fuRm` — the bundle's `rm`, from `rm_of_uhlenbeck` fed by the unconditional tail producer
  `rm04EvolFamTail` at the midpoint tail `t₀ = (a+t)/2`;
* `fuSdec` — the bundle's `sdec`, from `sdec_of_uhlenbeck` at the same tail;
* `fuSfield_apply` — the bundle's `car`, by construction of `fuSfield`;
* the density-regularity members `dens`, `densCont`, `densInt`, `lapInt`, `divInt`, `nabInt`,
  `disInt`, inside `fuInputs_of_gram`, from `ForwardUniqueDensReg.lean`;
* `pairInt`, `restInt`, `remInt` — the three slots pairing a *bare pointwise* speed family —
  from `fuPairInt`, `fuRestInt`, `fuRemInt`;
* `energyCont` at every interior time, from `fuEnergyDeriv`.

## What is NOT discharged here

`bounds` (the six slab-uniform pointwise estimates), and `energyCont` at the **single** closed
initial time `a`.  They are named, with their frontier, in `fuInputs_of_gram`'s hypothesis list
and in `ForwardUniqueWiring.md`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ## The reference time interval

Every component family below reads its solution argument only through the underlying metric
family, so the interval index is a phantom.  Fixing one reference interval keeps the carriers
independent of the tail parameter chosen inside the proofs. -/

/-- Reference interval used only to *name* the component families: all of them depend on the
solution package solely through its metric family.  Private: the transport lemmas
`fuRm04_eq` … `fuRicUp_eq` are the public interface to this choice. -/
private def refD : RealTimeInterval := RealTimeInterval.univ 0

/-! ## The data carriers of `ForwardUniqueInputs` -/

/-- The flow's own smooth `(0,4)` curvature field, as a time-indexed family. -/
def fuTf (g : Real → SmoothRiemannianMetric I M) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 :=
  metricRm04 (I := I) (g t)

/-- **The `Sfield` carrier**: the curvature-difference `(0,4)` field `S₀₄`, both terms lowered
with `g₁`.  Its pointwise value is `rmDiffLowAt (g₁ t) (g₂ t)` (`fuSfield_apply`). -/
def fuSfield (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 :=
  CovariantDerivative.rm04Section (I := I) (g₁ t) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t)) -
    CovariantDerivative.rm04Section (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t))

/-- The per-point-centred lowered-curvature component family of a metric family. -/
def fuRm04 (g : Real → SmoothRiemannianMetric I M) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  rm04Fam (I := I) (D := refD) (solOfMetric (I := I) g)

/-- The per-point-centred rough-Laplacian component family of a metric family. -/
def fuLapRm (g : Real → SmoothRiemannianMetric I M) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  rm04LapFam (I := I) (D := refD) (solOfMetric (I := I) g)

/-- The per-point-centred Uhlenbeck `B` component family of a metric family. -/
def fuBRm (g : Real → SmoothRiemannianMetric I M) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  rm04BFam (I := I) (D := refD) (solOfMetric (I := I) g)

/-- The per-point-centred once-raised Ricci component family of a metric family. -/
def fuRicUp (g : Real → SmoothRiemannianMetric I M) :
    MatrixComp M (CoordinateIdx (𝕜 := Real) E) :=
  ricUpFam (I := I) (D := refD) (solOfMetric (I := I) g)

/-- **The `Avec` carrier**: the bundled bilinear speed of the connection difference, at the
canonical chart-frame inverse and `∇Ric` families of the two flows. -/
def fuAvec (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  christoffelDiffSpeed (I := I) (chartFrameInv (I := I) g₁) (chartFrameInv (I := I) g₂)
    (chartNablaRic (I := I) g₁) (chartNablaRic (I := I) g₂) t x

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The `Svec` carrier**: the bundled trilinear speed of the raised curvature difference. -/
def fuSvec (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (y : M) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
      TangentSpace I y :=
  uhlRmDiffSpeed (I := I) g₁ g₂ (coordBasisAt (I := I))
    (fuRm04 (I := I) g₁) (fuLapRm (I := I) g₁) (fuBRm (I := I) g₁) (fuRicUp (I := I) g₁)
    (fuRm04 (I := I) g₂) (fuLapRm (I := I) g₂) (fuBRm (I := I) g₂) (fuRicUp (I := I) g₂) t y

/-- **The `Uflux` carrier**: the K2 divergence flux of the `S`-equation. -/
def fuUflux (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5 :=
  sdecUflux (I := I) g₁ g₂ (fuTf (I := I) g₁) (fuTf (I := I) g₂) (fuSfield (I := I) g₁ g₂) t

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The `rem` carrier**: the K2 remainder of the `S`-equation. -/
def fuRem (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  sdecRemFam (I := I) g₁ g₂ (coordBasisAt (I := I))
    (fuRm04 (I := I) g₁) (fuBRm (I := I) g₁) (fuRicUp (I := I) g₁)
    (fuRm04 (I := I) g₂) (fuLapRm (I := I) g₂) (fuBRm (I := I) g₂) (fuRicUp (I := I) g₂)
    (fuTf (I := I) g₁) (fuTf (I := I) g₂) (fuSfield (I := I) g₁ g₂) t x

/-! ## Realization of the carriers -/

/-- **The bundle's `car` member, by construction.**  The supplied smooth `(0,4)` field is the
curvature-difference carrier `S₀₄`. -/
theorem fuSfield_apply (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    fuSfield (I := I) g₁ g₂ t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x := rfl

/-- The `(0,4)` field carrier of one flow is that flow's own lowered curvature. -/
theorem fuTf_apply (g : Real → SmoothRiemannianMetric I M) (t : Real) (y : M) :
    fuTf (I := I) g t y = metricRm04At (I := I) (g t) y := rfl

/-! ## Transport of the component families across the interval index -/

/-- The lowered-curvature component family does not see the interval index. -/
theorem fuRm04_eq {D : RealTimeInterval} (g : Real → SmoothRiemannianMetric I M) :
    rm04Fam (I := I) (D := D) (solOfMetric (I := I) g) = fuRm04 (I := I) g := rfl

/-- The rough-Laplacian component family does not see the interval index. -/
theorem fuLapRm_eq {D : RealTimeInterval} (g : Real → SmoothRiemannianMetric I M) :
    rm04LapFam (I := I) (D := D) (solOfMetric (I := I) g) = fuLapRm (I := I) g := rfl

/-- The Uhlenbeck `B` component family does not see the interval index. -/
theorem fuBRm_eq {D : RealTimeInterval} (g : Real → SmoothRiemannianMetric I M) :
    rm04BFam (I := I) (D := D) (solOfMetric (I := I) g) = fuBRm (I := I) g := rfl

/-- The raised-Ricci component family does not see the interval index. -/
theorem fuRicUp_eq {D : RealTimeInterval} (g : Real → SmoothRiemannianMetric I M) :
    ricUpFam (I := I) (D := D) (solOfMetric (I := I) g) = fuRicUp (I := I) g := rfl

/-- **`hreal`**: the lowered-curvature component family is the metric's own lowered curvature
read on the per-point coordinate basis. -/
theorem fuRm04_real (g : Real → SmoothRiemannianMetric I M)
    (r : Real) (y : M) (i j k l : CoordinateIdx (𝕜 := Real) E) :
    fuRm04 (I := I) g r y i j k l =
      metricRm04At (I := I) (g r) y
        (vec4 (I := I) (coordBasisAt (I := I) y i) (coordBasisAt (I := I) y j)
          (coordBasisAt (I := I) y k) (coordBasisAt (I := I) y l)) :=
  rm04Fam_real (I := I) (D := refD) (solOfMetric (I := I) g) r y i j k l

/-- **`hL`**: the rough-Laplacian component family realizes the intrinsic rough Laplacian of
the flow's own `(0,4)` curvature field. -/
theorem fuLapRm_real (g : Real → SmoothRiemannianMetric I M)
    (r : Real) (y : M) (i j k l : CoordinateIdx (𝕜 := Real) E) :
    fuLapRm (I := I) g r y i j k l =
      roughLap0SField (I := I) (g r) (fuTf (I := I) g r) y
        (frameVec4 (I := I) (fun m z => coordBasisAt (I := I) z m) y i j k l) :=
  rm04LapFam_real (I := I) (D := refD) (solOfMetric (I := I) g) r y i j k l

private theorem fuInv_real (g : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    MetricInverseInBasis_gen (I := I) (g t) x (coordBasisAt (I := I) x)
      (fun i j => coordInv (I := I) (solOfMetric (I := I) (D := refD) g) x t x i j) := by
  have hbasis :
      coordBasisAt (I := I) x =
        coordinateFrameAt_toBasis (I := I) x := by
    ext i
    simp
  simpa only [solOfMetric_metric, hbasis] using
    coordInvReal (I := I) (solOfMetric (I := I) (D := refD) g) x t

set_option maxHeartbeats 1000000 in
/-- The canonical Uhlenbeck `B` components reconstruct the invariant
quadratic curvature combination, independently of the metric used to lower
the supplied component array. -/
theorem fuB_low (gN g : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (gN t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          fuBRm (I := I) g t x i j k l - fuBRm (I := I) g t x i j l k +
            fuBRm (I := I) g t x i k j l - fuBRm (I := I) g t x i l j k) =
      bComb (I := I) (g t) (fuTf (I := I) g t) x := by
  let basis := coordBasisAt (I := I) x
  let gInv := fun i j =>
    coordInv (I := I) (solOfMetric (I := I) (D := refD) g) x t x i j
  have hinv : MetricInverseInBasis_gen (I := I) (g t) x basis gInv := by
    simpa only [basis, gInv] using fuInv_real (I := I) g t x
  have hRm : ∀ i j k l,
      component0S (I := I) basis (fuTf (I := I) g t x) ![i, j, k, l] =
        fuRm04 (I := I) g t x i j k l := by
    intro i j k l
    simpa only [basis, component0S_apply, fuTf_apply] using
      (fuRm04_real (I := I) g t x i j k l).symm
  have hB (a b c d : CoordinateIdx (𝕜 := Real) E) :
      fuBRm (I := I) g t x a b c d =
        ∑ f, ∑ r, ∑ e, ∑ q,
          gInv f r * gInv e q *
            fuRm04 (I := I) g t x a e b f *
              fuRm04 (I := I) g t x c q d r := by
    change
      (∑ e, ∑ q, ∑ f, ∑ r,
        gInv e q * gInv f r *
          fuRm04 (I := I) g t x a e b f *
            fuRm04 (I := I) g t x c q d r) = _
    rw [DifferentialGeometry.Tensor.SlotAlgebra.sum_rotate4_two]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  apply lowOfComp_ext (I := I)
  intro i j k l
  have hcomp := bComb_comp (I := I) (g t) basis gInv hinv
    (fuTf (I := I) g t) ![i, j, k, l]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, hRm] at hcomp
  simp only [component0S_apply, basis] at hcomp
  simp only [Matrix.head_cons, Matrix.tail_cons] at hcomp
  have hslots :
      (fun a : Fin 4 => coordBasisAt (I := I) x (![i, j, k, l] a)) =
        vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l) := by
    funext p
    fin_cases p <;> simp [vec4]
  rw [hslots] at hcomp
  rw [hcomp, hB i j k l, hB i j l k, hB i k j l, hB i l j k]

set_option maxHeartbeats 1000000 in
/-- The canonical raised-Ricci and curvature components reconstruct the
invariant Ricci drift, independently of the reconstruction metric. -/
theorem fuDrift_low (gN g : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (gN t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          riemann04RicciDriftInFrame (fuRicUp (I := I) g) (fuRm04 (I := I) g)
            t x i j k l) =
      ricciDrift04 (I := I) (g t) x := by
  let basis := coordBasisAt (I := I) x
  let gInv := fun i j =>
    coordInv (I := I) (solOfMetric (I := I) (D := refD) g) x t x i j
  have hinv : MetricInverseInBasis_gen (I := I) (g t) x basis gInv := by
    simpa only [basis, gInv] using fuInv_real (I := I) g t x
  have hUp (i p : CoordinateIdx (𝕜 := Real) E) :
      fuRicUp (I := I) g t x i p =
        ∑ a, gInv p a *
          metricRicciAt (I := I) (g t) x
            (vec2 (I := I) (basis i) (basis a)) := by
    simp only [fuRicUp, ricUpFam, ricciOneUpCompInFrame,
      ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt,
      solOfMetric_metric, coordBasisAt_coe, basis, gInv]
  apply lowOfComp_ext (I := I)
  intro i j k l
  change
    ricciDrift04 (I := I) (g t) x
        (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
      riemann04RicciDriftInFrame (fuRicUp (I := I) g) (fuRm04 (I := I) g)
        t x i j k l
  rw [ricciDrift_comp (I := I) (g t) basis gInv hinv]
  simp only [riemann04RicciDriftInFrame, hUp, fuRm04_real, basis]

set_option maxHeartbeats 1000000 in
/-- Lowering the canonical raised Uhlenbeck speed by its own metric gives the
coordinate-free curvature speed tensor. -/
theorem fuSpeed_low (g : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowerTri (I := I) (metricTensorField (I := I) (g t) x)
        (uhlRm2Vec (I := I) g (coordBasisAt (I := I))
          (fuRm04 (I := I) g) (fuLapRm (I := I) g) (fuBRm (I := I) g)
          (fuRicUp (I := I) g) t x) =
      uhlSpeed04 (I := I) (g t) (fuTf (I := I) g t) x := by
  rw [← uhlSpeed_low (I := I) g (coordBasisAt (I := I))
    (fuRm04 (I := I) g) (fuLapRm (I := I) g) (fuBRm (I := I) g)
    (fuRicUp (I := I) g) t x]
  rw [← uhlSpeed04_low (I := I) (g t) (fuTf (I := I) g t) x
    (coordBasisAt (I := I) x)]
  apply lowOfComp_ext (I := I)
  intro i j k l
  rw [fuLapRm_real (I := I) g t x i j k l]
  have hB := congrArg
    (fun T => T (vec4 (I := I) (coordBasisAt (I := I) x i)
      (coordBasisAt (I := I) x j) (coordBasisAt (I := I) x k)
      (coordBasisAt (I := I) x l)))
    (fuB_low (I := I) g g t x)
  have hD := congrArg
    (fun T => T (vec4 (I := I) (coordBasisAt (I := I) x i)
      (coordBasisAt (I := I) x j) (coordBasisAt (I := I) x k)
      (coordBasisAt (I := I) x l)))
    (fuDrift_low (I := I) g g t x)
  simp only [lowOfComp_eval] at hB hD
  rw [hB, hD]
  rw [lowOfComp_eval]
  simp only [frameVec4]

set_option maxHeartbeats 1000000 in
private theorem fuB_diff_low (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          (fuBRm (I := I) g₁ t x i j k l - fuBRm (I := I) g₂ t x i j k l) -
              (fuBRm (I := I) g₁ t x i j l k - fuBRm (I := I) g₂ t x i j l k) +
            (fuBRm (I := I) g₁ t x i k j l - fuBRm (I := I) g₂ t x i k j l) -
              (fuBRm (I := I) g₁ t x i l j k - fuBRm (I := I) g₂ t x i l j k)) =
      bComb (I := I) (g₁ t) (fuTf (I := I) g₁ t) x -
        bComb (I := I) (g₂ t) (fuTf (I := I) g₂ t) x := by
  rw [← fuB_low (I := I) g₁ g₁ t x, ← fuB_low (I := I) g₁ g₂ t x]
  apply lowOfComp_ext (I := I)
  intro i j k l
  change
    (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) -
      (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) = _
  rw [lowOfComp_eval, lowOfComp_eval]
  ring

set_option maxHeartbeats 1000000 in
private theorem fuDrift_diff_low (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          riemann04RicciDriftInFrame (fuRicUp (I := I) g₁) (fuRm04 (I := I) g₁)
              t x i j k l -
            riemann04RicciDriftInFrame (fuRicUp (I := I) g₂) (fuRm04 (I := I) g₂)
              t x i j k l) =
      ricciDrift04 (I := I) (g₁ t) x - ricciDrift04 (I := I) (g₂ t) x := by
  rw [← fuDrift_low (I := I) g₁ g₁ t x, ← fuDrift_low (I := I) g₁ g₂ t x]
  apply lowOfComp_ext (I := I)
  intro i j k l
  change
    (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) -
      (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) = _
  rw [lowOfComp_eval, lowOfComp_eval]

private theorem lowerRm_cross
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    lowerTri (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x) =
      CovariantDerivative.riemannCurvature04At (I := I) g₁
        (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  calc
    lowerTri (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) =
      metricTensorField (I := I) g₁ x
        (fun a : Fin 2 =>
          if a = 0 then
            riemannOp (metricCov (I := I) g₂) x (v 0) (v 1) (v 2)
          else v 3) :=
      lowerTri_apply (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3))
    _ = g₁.inner x (riemannOp (metricCov (I := I) g₂) x (v 0) (v 1) (v 2))
        (v 3) := by
      rw [metricTensorField_apply]
      simp
    _ = CovariantDerivative.riemannCurvature04At (I := I) g₁
        (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
          (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) :=
      (rm04mix_inner (I := I) g₁ g₂ x (v 0) (v 1) (v 2) (v 3)).symm

/-! ## The `SolutionOn` package of a flow, and the tail Uhlenbeck interface -/

/-- **(B)'s fields give a Ricci-flow solution package.**  Joint chart-Gram `C∞` on the
`Ico`-slab plus the one-sided Ricci-flow equation is exactly `solutionOn_of_joint`'s input. -/
theorem fuIsSol (g : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v w) (Ici a) t) :
    IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g) :=
  solutionOn_of_joint (I := I) hab g hjoint hpde

/-- **`hev` on a positive-time tail, in the wiring carriers.**  `rm04EvolFamTail` transported
across the phantom interval index. -/
theorem fuEvolTail (g : Real → SmoothRiemannianMetric I M) {a b t₀ : Real} {hab : a < b}
    {hb : t₀ < b} (hS : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g))
    (ha : a < t₀) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := RealTimeInterval.closedOpen t₀ b hb)
      (fuRm04 (I := I) g) (fuLapRm (I := I) g) (fuBRm (I := I) g) (fuRicUp (I := I) g) := by
  rw [← fuRm04_eq (I := I) (D := RealTimeInterval.closedOpen t₀ b hb) g,
    ← fuLapRm_eq (I := I) (D := RealTimeInterval.closedOpen t₀ b hb) g,
    ← fuBRm_eq (I := I) (D := RealTimeInterval.closedOpen t₀ b hb) g,
    ← fuRicUp_eq (I := I) (D := RealTimeInterval.closedOpen t₀ b hb) g]
  exact rm04EvolFamTail (I := I) hS ha rfl

/-! ## The bundle members `gamma`, `rm`, `sdec`

The three evolution members are produced at the *midpoint tail* `t₀ = (a+t)/2` of each interior
time `t`: the tail producers are stated on `Ico t₀ b` with `a < t₀`, and `t` is interior to that
tail, so the restriction costs nothing.  The carriers are the fixed reference-interval ones, so
the same `Avec`/`Svec` serves every `t`. -/

/-- Within-at continuity of a finite sum, the `ContinuousWithinAt` analogue of
`continuous_finset_sum` (absent from Mathlib). -/
private theorem cwaSum {ι : Type*} {N : Type*} [AddCommMonoid N] [TopologicalSpace N]
    [ContinuousAdd N] {f : ι → Real → N} (s : Finset ι) {u : Set Real} {t : Real}
    (h : ∀ i ∈ s, ContinuousWithinAt (f i) u t) :
    ContinuousWithinAt (fun r : Real => ∑ i ∈ s, f i r) u t := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousWithinAt_const
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

set_option maxHeartbeats 1000000 in
/-- **Time-continuity of the raised curvature on a positive-time tail — unconditional.**

The one auxiliary of the Uhlenbeck conversion beyond the evolution itself.  It is *not* an
input: at a fixed point the raised curvature is the inverse Gram matrix applied to the lowered
components (`raiseAt_lower`), the lowered components are differentiable in time by the tail
evolution, and the Gram matrix is differentiable in time by the Ricci-flow equation — so
Cramer's rule for the inverse of a continuous invertible matrix family closes it. -/
theorem fuRmContAt (g : Real → SmoothRiemannianMetric I M) {a b t₀ : Real} {hab : a < b}
    {hb : t₀ < b}
    (hS : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g))
    (ha : a < t₀)
    (hpde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo t₀ b) (y : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContinuousWithinAt
      (fun r : Real => riemannOp (metricCov (I := I) (g r)) y
        (coordBasisAt (I := I) y i) (coordBasisAt (I := I) y j) (coordBasisAt (I := I) y k))
      (Ico t₀ b) t := by
  classical
  have htab : t ∈ Ico a b := ⟨(lt_trans ha ht.1).le, ht.2⟩
  have hsubIci : Ico t₀ b ⊆ Ici a := fun s hs => le_trans ha.le hs.1
  -- the Gram matrix family of the coordinate basis, and its inverse
  have hmul : ∀ r : Real,
      (Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
          (g r).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m)) *
        (Matrix.of fun p l : CoordinateIdx (𝕜 := Real) E =>
          basisInvMetric (I := I) (g r) y (coordBasisAt (I := I) y) p l) = 1 := by
    intro r
    ext p q
    have h := (basisInvMetric_real (I := I) (g r) y (coordBasisAt (I := I) y) p q).2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hinvEq : ∀ r : Real,
      (Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
          (g r).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m))⁻¹ =
        Matrix.of fun p l : CoordinateIdx (𝕜 := Real) E =>
          basisInvMetric (I := I) (g r) y (coordBasisAt (I := I) y) p l :=
    fun r => Matrix.inv_eq_right_inv (hmul r)
  have hGcont : ContinuousWithinAt
      (fun r : Real => (Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
        (g r).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m)))
      (Ico t₀ b) t := by
    refine continuousWithinAt_pi.2 fun l => continuousWithinAt_pi.2 fun m => ?_
    exact ((hpde t htab y (coordBasisAt (I := I) y l)
      (coordBasisAt (I := I) y m)).continuousWithinAt).mono hsubIci
  have hdet0 : (Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
      (g t).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m)).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (hmul t)).ne_zero
  have hRinv : ContinuousAt (Ring.inverse : Real → Real)
      ((Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
        (g t).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m)).det) := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet0
  have hInvCont : ContinuousWithinAt
      (fun r : Real => (Matrix.of fun l m : CoordinateIdx (𝕜 := Real) E =>
        (g r).inner y (coordBasisAt (I := I) y l) (coordBasisAt (I := I) y m))⁻¹)
      (Ico t₀ b) t :=
    Filter.Tendsto.comp (continuousAt_matrix_inv _ hRinv) hGcont
  have hBcont : ∀ p l : CoordinateIdx (𝕜 := Real) E,
      ContinuousWithinAt
        (fun r : Real => basisInvMetric (I := I) (g r) y (coordBasisAt (I := I) y) p l)
        (Ico t₀ b) t := by
    intro p l
    have hfun : (fun r : Real =>
          basisInvMetric (I := I) (g r) y (coordBasisAt (I := I) y) p l) =
        fun r : Real => (Matrix.of fun c m : CoordinateIdx (𝕜 := Real) E =>
          (g r).inner y (coordBasisAt (I := I) y c) (coordBasisAt (I := I) y m))⁻¹ p l := by
      funext r; rw [hinvEq r]; rfl
    rw [hfun]
    exact continuousWithinAt_pi.1 (continuousWithinAt_pi.1 hInvCont p) l
  -- the lowered components are differentiable in time by the tail evolution
  have hc : ∀ l : CoordinateIdx (𝕜 := Real) E,
      ContinuousWithinAt (fun r : Real => fuRm04 (I := I) g r y i j k l) (Ico t₀ b) t :=
    fun l => (fuEvolTail (I := I) (hb := hb) g hS ha ⟨t, ht⟩ y i j k l).continuousWithinAt
  -- raising undoes lowering
  have hV : ∀ r : Real,
      riemannOp (metricCov (I := I) (g r)) y (coordBasisAt (I := I) y i)
          (coordBasisAt (I := I) y j) (coordBasisAt (I := I) y k) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          (∑ l : CoordinateIdx (𝕜 := Real) E,
            basisInvMetric (I := I) (g r) y (coordBasisAt (I := I) y) p l *
              fuRm04 (I := I) g r y i j k l) • coordBasisAt (I := I) y p := by
    intro r
    have hlow : (fun l : CoordinateIdx (𝕜 := Real) E => (g r).inner y
          (riemannOp (metricCov (I := I) (g r)) y (coordBasisAt (I := I) y i)
            (coordBasisAt (I := I) y j) (coordBasisAt (I := I) y k))
          (coordBasisAt (I := I) y l)) =
        fun l : CoordinateIdx (𝕜 := Real) E => fuRm04 (I := I) g r y i j k l := by
      funext l
      rw [fuRm04_real (I := I) g r y i j k l, metricRm04At_inner]
    have hraise := raiseAt_lower (I := I) (g r) y (coordBasisAt (I := I) y)
      (riemannOp (metricCov (I := I) (g r)) y (coordBasisAt (I := I) y i)
        (coordBasisAt (I := I) y j) (coordBasisAt (I := I) y k))
    rw [hlow] at hraise
    rw [← hraise, raiseAt_eq]
  rw [funext hV]
  exact cwaSum _ fun p _ =>
    (cwaSum _ fun l _ => (hBcont p l).mul (hc l)).smul continuousWithinAt_const

/-- **The bundle's `gamma` member, from (B)'s own fields.**  This is `gamma_of_gram` with the
`Avec` carrier named. -/
theorem fuGamma (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((fuAvec (I := I) g₁ g₂ t x (chartFrame I x j x)) (chartFrame I x i x))) t :=
  gamma_of_gram (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `rm` member, from (B)'s own fields plus the two time-continuity inputs.**
The Uhlenbeck evolution of each flow is supplied unconditionally by `fuEvolTail` on the
midpoint tail. -/
theorem fuRm (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} {hab : a < b}
    (hS₁ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₁))
    (hS₂ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₂))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, ∀ (x : M) (X Y Z : TangentSpace I x),
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
        (((fuSvec (I := I) g₁ g₂ t x X) Y) Z) t := by
  intro t ht x X Y Z
  have ha0 : a < (a + t) / 2 := by have := ht.1; linarith
  have ht0 : (a + t) / 2 < t := by have := ht.1; linarith
  have hb0 : (a + t) / 2 < b := lt_trans ht0 ht.2
  have hsub : Ico ((a + t) / 2) b ⊆ Ico a b := fun s hs => ⟨le_trans ha0.le hs.1, hs.2⟩
  have hsub' : Ioo ((a + t) / 2) b ⊆ Ioo a b := fun s hs => ⟨lt_trans ha0 hs.1, hs.2⟩
  refine rm_of_uhlenbeck (I := I)
    (D := RealTimeInterval.closedOpen ((a + t) / 2) b hb0) g₁ g₂ (coordBasisAt (I := I))
    (fuRm04 (I := I) g₁) (fuLapRm (I := I) g₁) (fuBRm (I := I) g₁) (fuRicUp (I := I) g₁)
    (fuRm04 (I := I) g₂) (fuLapRm (I := I) g₂) (fuBRm (I := I) g₂) (fuRicUp (I := I) g₂)
    (a := (a + t) / 2) (b := b) (fun s hs => hs)
    (fuEvolTail (I := I) g₁ hS₁ ha0) (fuEvolTail (I := I) g₂ hS₂ ha0)
    (fun r y i j k l => fuRm04_real (I := I) g₁ r y i j k l)
    (fun r y i j k l => fuRm04_real (I := I) g₂ r y i j k l)
    (fun s hs y i j k => fuRmContAt (I := I) (hb := hb0) g₁ hS₁ ha0 hpde₁ hs y i j k)
    (fun s hs y i j k => fuRmContAt (I := I) (hb := hb0) g₂ hS₂ ha0 hpde₂ hs y i j k)
    (fun s hs y U W => (pde_hasDerivAt (I := I) g₁ hpde₁ (hsub' hs) y U W).hasDerivWithinAt)
    (fun s hs y U W => (pde_hasDerivAt (I := I) g₂ hpde₂ (hsub' hs) y U W).hasDerivWithinAt)
    t ⟨ht0, ht.2⟩ x X Y Z

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `sdec` member, from (B)'s own fields plus the two time-continuity inputs.**
The flux and remainder carriers are the constructed `fuUflux`/`fuRem`. -/
theorem fuSdec (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} {hab : a < b}
    (hS₁ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₁))
    (hS₂ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₂))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, ∀ x : M,
      rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x =
        roughLap0SField (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x +
          covDiv0SField (I := I) (g₁ t) (fuUflux (I := I) g₁ g₂ t) x +
          fuRem (I := I) g₁ g₂ t x := by
  intro t ht x
  have ha0 : a < (a + t) / 2 := by have := ht.1; linarith
  have ht0 : (a + t) / 2 < t := by have := ht.1; linarith
  have hb0 : (a + t) / 2 < b := lt_trans ht0 ht.2
  have hsub : Ico ((a + t) / 2) b ⊆ Ico a b := fun s hs => ⟨le_trans ha0.le hs.1, hs.2⟩
  have hsub' : Ioo ((a + t) / 2) b ⊆ Ioo a b := fun s hs => ⟨lt_trans ha0 hs.1, hs.2⟩
  refine sdec_of_uhlenbeck (I := I)
    (D := RealTimeInterval.closedOpen ((a + t) / 2) b hb0) g₁ g₂ (coordBasisAt (I := I))
    (fuRm04 (I := I) g₁) (fuLapRm (I := I) g₁) (fuBRm (I := I) g₁) (fuRicUp (I := I) g₁)
    (fuRm04 (I := I) g₂) (fuLapRm (I := I) g₂) (fuBRm (I := I) g₂) (fuRicUp (I := I) g₂)
    (fuTf (I := I) g₁) (fuTf (I := I) g₂) (fuSfield (I := I) g₁ g₂)
    (a := (a + t) / 2) (b := b) (fun s hs => hs)
    (fuEvolTail (I := I) g₁ hS₁ ha0) (fuEvolTail (I := I) g₂ hS₂ ha0)
    (fun r y i j k l => fuRm04_real (I := I) g₁ r y i j k l)
    (fun r y i j k l => fuRm04_real (I := I) g₂ r y i j k l)
    (fun s hs y i j k => fuRmContAt (I := I) (hb := hb0) g₁ hS₁ ha0 hpde₁ hs y i j k)
    (fun s hs y i j k => fuRmContAt (I := I) (hb := hb0) g₂ hS₂ ha0 hpde₂ hs y i j k)
    (fun s hs y U W => (pde_hasDerivAt (I := I) g₁ hpde₁ (hsub' hs) y U W).hasDerivWithinAt)
    (fun s hs y U W => (pde_hasDerivAt (I := I) g₂ hpde₂ (hsub' hs) y U W).hasDerivWithinAt)
    (fun _ _ y => fuTf_apply (I := I) g₁ _ y) (fun _ _ y => fuTf_apply (I := I) g₂ _ y)
    (fun _ _ y => fuSfield_apply (I := I) g₁ g₂ _ y)
    (fun _ _ y i j k l => fuLapRm_real (I := I) g₁ _ y i j k l)
    (fun _ _ y i j k l => fuLapRm_real (I := I) g₂ _ y i j k l)
    t ⟨ht0, ht.2⟩ x

/-! ## The three bare-pointwise integrability slots

`pairInt`, `restInt` and `remInt` pair a **bare pointwise** family (`rmSpeed … fuSvec`,
`connSpeed … fuAvec`, `fuRem`), so `ForwardUniqueDensReg.lean`'s smooth-by-type argument does not
reach them.  They are nevertheless continuous in `x`, and the route never touches the
per-point-centred frame construction inside the carriers:

* an invariant speed enters a rate integrand only through the combination
  `movingReact0S + 2⟨Ṫ, T⟩`, which `normSq0S_moving_deriv` identifies as the time derivative of
  one of the three energy thirds — a **scalar** already known to be jointly `C∞`
  (`metricDiffSq_jointContMDiffOn`, `connDiffSq_jointContMDiffOn`, `rmDiffSq_jointContMDiffOn`);
* the one leftover reaction `movingReact0S (g₁ t) x 4 Ric₁ S₀₄` is the same derivative with the
  carrier **frozen** at time `t`, hence again the time partial of a jointly `C∞` scalar
  (`fuFrozenJoint`);
* `tderivCont` turns "jointly `C∞` on `J ×ˢ univ`" into "the time partial is continuous in `x`".

Compactness of `M` then closes each slot through `integrable_of_continuous`. -/

section SpeedContinuity

/-- The chart-Gram package of black box (B), restricted to the open window. -/
private theorem fuGramIoo (g : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
  (hjoint x₀ i j).mono (Set.prod_mono_left Ioo_subset_Ico_self)

/-- **The time partial of a jointly `C∞` scalar is continuous in space.**

For `J ⊆ ℝ` open, `t ∈ J` and `F` jointly `C∞` on `J ×ˢ univ`, the map
`x ↦ ∂ᵣF(r, x)|_{r=t}` is continuous.  Read through the chart at `x₀`, `F` becomes a `C∞`
function on an open subset of `ℝ × E` whose `fderiv` is continuous
(`ContDiffOn.continuousOn_fderiv_of_isOpen`); the time partial is that differential applied to
`(1, 0)`. -/
private theorem tderivCont {J : Set Real} (hJ : IsOpen J) {t : Real} (ht : t ∈ J)
    (F : Real → M → Real)
    (hF : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => F p.1 p.2) (J ×ˢ (univ : Set M))) :
    Continuous (fun x : M => deriv (fun r : Real => F r x) t) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  set U : Set E := interior (extChartAt I x₀).target with hUdef
  have hUopen : IsOpen U := isOpen_interior
  have hy₀ : (extChartAt I x₀) x₀ ∈ U :=
    mem_interior_iff_mem_nhds.2 (extChartAt_target_mem_nhds (I := I) x₀)
  have hprod : IsOpen (J ×ˢ U) := hJ.prod hUopen
  -- transport the joint smoothness to the model space
  have hsymm : ContMDiffOn 𝓘(Real, E) I ∞ (extChartAt I x₀).symm (extChartAt I x₀).target :=
    contMDiffOn_extChartAt_symm (I := I) x₀
  have hfst : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real) ∞
      (fun p : Real × E => p.1) (J ×ˢ U) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, E) ∞
      (fun p : Real × E => p.2) (J ×ˢ U) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  have hmaps : Set.MapsTo (fun p : Real × E => p.2) (J ×ˢ U) (extChartAt I x₀).target :=
    fun p hp => interior_subset hp.2
  have hσ : ContMDiffOn 𝓘(Real, Real × E) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × E => (p.1, (extChartAt I x₀).symm p.2)) (J ×ˢ U) :=
    hfst.prodMk (hsymm.comp hsnd hmaps)
  have hGm : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real) ∞
      (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2)) (J ×ˢ U) := by
    refine (hF.comp hσ fun p hp => ⟨hp.1, mem_univ _⟩).congr ?_
    intro p _
    rfl
  have hGd : ContDiffOn Real ∞ (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2))
      (J ×ˢ U) := hGm.contDiffOn
  have hone : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by simp
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hfdCont : ContinuousOn
      (fderiv Real fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2)) (J ×ˢ U) :=
    hGd.continuousOn_fderiv_of_isOpen hprod hone
  -- the time partial of the transported function is that differential at `(1, 0)`
  have hslice : ∀ y ∈ U, HasDerivAt
      (fun r : Real => F r ((extChartAt I x₀).symm y))
      ((fderiv Real (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2)) (t, y))
        ((1 : Real), (0 : E))) t := by
    intro y hy
    have hdiff : HasFDerivAt (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2))
        (fderiv Real (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2)) (t, y)) (t, y) :=
      ((hGd.differentiableOn hne).differentiableAt
        (hprod.mem_nhds ⟨ht, hy⟩)).hasFDerivAt
    have hline : HasDerivAt (fun r : Real => ((r, y) : Real × E)) ((1 : Real), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    simpa [Function.comp_def] using hdiff.comp_hasDerivAt t hline
  -- near `x₀` the two readings agree
  have heq : (fun x : M => deriv (fun r : Real => F r x) t) =ᶠ[nhds x₀]
      fun x : M =>
        (fderiv Real (fun p : Real × E => F p.1 ((extChartAt I x₀).symm p.2))
          (t, (extChartAt I x₀) x)) ((1 : Real), (0 : E)) := by
    have hcontφ : ContinuousAt (extChartAt I x₀) x₀ := continuousAt_extChartAt (I := I) x₀
    filter_upwards [extChartAt_source_mem_nhds (I := I) x₀,
      hcontφ.preimage_mem_nhds (hUopen.mem_nhds hy₀)] with x hx1 hx2
    have hinv : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x := (extChartAt I x₀).left_inv hx1
    have hrw : (fun r : Real => F r x) =
        fun r : Real => F r ((extChartAt I x₀).symm ((extChartAt I x₀) x)) := by
      rw [hinv]
    rw [hrw]
    exact (hslice _ hx2).deriv
  refine ContinuousAt.congr ?_ heq.symm
  have hmap : ContinuousAt (fun x : M => ((t, (extChartAt I x₀) x) : Real × E)) x₀ :=
    continuousAt_const.prodMk (continuousAt_extChartAt (I := I) x₀)
  exact ((hfdCont.continuousAt (hprod.mem_nhds ⟨ht, hy₀⟩)).comp hmap).clm_apply continuousAt_const

/-- **`movingReact0S` is a genuine time derivative: the moving fibre norm of a frozen carrier.**
Taking the tensor family constant in `normSq0S_moving_deriv` kills the pairing term, so the
reaction is the derivative of `r ↦ |W|²_{g r}` — a basis-free characterisation that makes its
spatial continuity a corollary of joint smoothness. -/
private theorem fuReactDeriv {s : ℕ} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    HasDerivAt (fun r : Real => normSq0S (I := I) (g r) x s W)
      (movingReact0S (I := I) (g t) x s Q W) t := by
  have hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun _ : Real => W v)
        ((0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) v) t := by
    intro v
    rw [Tensor0SSpace.zero_apply (I := I) s x v]
    exact hasDerivAt_const t (W v)
  have h := normSq0S_moving_deriv (I := I) g Q (fun _ => W) 0 hg hT
  have hz : inner0S (I := I) (g t) x s 0 W = 0 := by
    simpa using inner0S_smul_left (I := I) (g t) x s (0 : Real) W W
  rw [hz, mul_zero, add_zero] at h
  exact h

/-- **The frozen-carrier moving norm is jointly `C∞`.**  The brick `normSq0S_jointContMDiffOn`
with the tensor family constant in time: its chart-component input is `rmChartJoint` at the two
*constant* metric families, exactly the trick that makes `dens_continuous` unconditional. -/
private theorem fuFrozenJoint (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (t₀ : Real)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => normSq0S (I := I) (g₁ p.1) p.2 4
        (rmDiffLowAt (I := I) (g₁ t₀) (g₂ t₀) p.2))
      (Ioo a b ×ˢ (univ : Set M)) := by
  refine normSq0S_jointContMDiffOn (I := I) g₁
    (fun _ x => rmDiffLowAt (I := I) (g₁ t₀) (g₂ t₀) x) hgram₁ ?_
  intro x₀ K t ht
  have hconst : ∀ (g : SmoothRiemannianMetric I M) (y₀ : M)
      (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) g y₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) y₀).baseSet) := by
    intro g y₀ i j
    have hsnd : ContMDiffOn (𝓘(Real, Real).prod I) I ∞ (fun p : Real × M => p.2)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) y₀).baseSet) :=
      contMDiffOn_snd
    exact (chartGramMatrix_entry_contMDiffOn (I := I) g y₀ i j).comp hsnd fun p hp => hp.2
  exact rmChartJoint (I := I) (fun _ => g₁ t₀) (fun _ => g₂ t₀) x₀
    (fun i j => hconst (g₁ t₀) x₀ i j) (fun i j => hconst (g₂ t₀) x₀ i j) K ht

/-- **The leftover reaction of the curvature third is continuous in space.** -/
private theorem fuReactCont (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) :
    Continuous (fun x : M => movingReact0S (I := I) (g₁ t) x 4
      (metricRicciAt (I := I) (g₁ t) x) (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) := by
  have hcont := tderivCont (I := I) (J := Ioo a b) isOpen_Ioo ht
    (fun r x => normSq0S (I := I) (g₁ r) x 4 (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
    (fuFrozenJoint (I := I) g₁ g₂ t hgram₁)
  refine hcont.congr fun x => ?_
  exact (fuReactDeriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
    (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)).deriv

/-- The metric third's time derivative, in the moving-norm form. -/
private theorem fuMetricSqD (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) (x : M) :
    deriv (fun r : Real => metricDiffSq (I := I) (g₁ r) (g₂ r) x) t =
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) := by
  have hbase := normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
    (fun r => metricDiffAt (I := I) (g₁ r) (g₂ r) x) (metricDiffDot (I := I) g₁ g₂ t x)
    (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
    (metricDiff_hasDerivAt (I := I) g₁ g₂ (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (pde_hasDerivAt (I := I) g₂ hpde₂ ht x))
  simpa only [metricDiffSq_def] using hbase.deriv

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- The connection third's time derivative, in the moving-norm form, at the `Avec` carrier. -/
private theorem fuConnSqD (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) (x : M) :
    deriv (fun r : Real => connDiffSq (I := I) (g₁ r) (g₂ r) x) t =
      movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        2 * inner0S (I := I) (g₁ t) x 3
          (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) t x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) := by
  have hbase := normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
    (fun r => connDiffLowAt (I := I) (g₁ r) (g₂ r) x)
    (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) t x)
    (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
    (connSpeed_hasDerivAt (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (fuGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ t ht x))
  simpa only [connDiffSq_def] using hbase.deriv

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- The curvature third's time derivative, in the moving-norm form, at the `Svec` carrier.
The pairing term is exactly the bundle's `pairInt` integrand. -/
private theorem fuRmSqD (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} {hab : a < b}
    (hS₁ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₁))
    (hS₂ : IsSolutionOn (I := I)
      (solOfMetric (I := I) (D := RealTimeInterval.closedOpen a b hab) g₂))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) (x : M) :
    deriv (fun r : Real => rmDiffSq (I := I) (g₁ r) (g₂ r) x) t =
      movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        2 * inner0S (I := I) (g₁ t) x 4
          (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) := by
  have hbase := normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
    (fun r => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x)
    (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
    (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
    (rmSpeed_hasDerivAt (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (fuRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht x))
  simpa only [rmDiffSq_def] using hbase.deriv

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `pairInt` member, from (B)'s own fields.**

`2⟨Ṡ, S₀₄⟩ = ∂ₜ|S₀₄|² − movingReact0S`, and both terms on the right are time partials of jointly
`C∞` scalars, hence continuous in `x`; on a compact manifold a continuous scalar is integrable
against the moving Riemannian volume. -/
theorem fuPairInt (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4
        (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
  intro t ht
  have hgram₁ := fuGramIoo (I := I) g₁ hjoint₁
  have hS₁ := fuIsSol (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := fuIsSol (I := I) g₂ hab hjoint₂ hpde₂
  refine integrable_of_continuous (I := I) g₁ t ?_
  have hfun : (fun x : M => 2 * inner0S (I := I) (g₁ t) x 4
        (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) =
      fun x : M => deriv (fun r : Real => rmDiffSq (I := I) (g₁ r) (g₂ r) x) t -
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) := by
    funext x
    rw [fuRmSqD (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ ht x]
    ring
  rw [hfun]
  exact (tderivCont (I := I) (J := Ioo a b) isOpen_Ioo ht
      (fun r x => rmDiffSq (I := I) (g₁ r) (g₂ r) x)
      (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ (fuGramIoo (I := I) g₂ hjoint₂))).sub
    (fuReactCont (I := I) g₁ g₂ hgram₁ hpde₁ ht)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `remInt` member, from (B)'s own fields.**

The `S`-equation `fuSdec` turns the remainder pairing into the `pairInt` integrand minus the two
smooth-by-type pairings, so it inherits their continuity. -/
theorem fuRemInt (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x)
        (fuSfield (I := I) g₁ g₂ t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
  intro t ht
  have hgram₁ := fuGramIoo (I := I) g₁ hjoint₁
  have hS₁ := fuIsSol (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := fuIsSol (I := I) g₂ hab hjoint₂ hpde₂
  refine integrable_of_continuous (I := I) g₁ t ?_
  have hfun : (fun x : M => inner0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x)
        (fuSfield (I := I) g₁ g₂ t x)) =
      fun x : M =>
        (1 / 2 : Real) * (deriv (fun r : Real => rmDiffSq (I := I) (g₁ r) (g₂ r) x) t -
            movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
              (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) -
          inner0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x)
            (fuSfield (I := I) g₁ g₂ t x) -
          inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) (fuUflux (I := I) g₁ g₂ t) x)
            (fuSfield (I := I) g₁ g₂ t x) := by
    funext x
    have hcar : fuSfield (I := I) g₁ g₂ t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x :=
      fuSfield_apply (I := I) g₁ g₂ t x
    have hsplit : inner0S (I := I) (g₁ t) x 4
          (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
          (fuSfield (I := I) g₁ g₂ t x) =
        inner0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x)
            (fuSfield (I := I) g₁ g₂ t x) +
          inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) (fuUflux (I := I) g₁ g₂ t) x)
            (fuSfield (I := I) g₁ g₂ t x) +
          inner0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x)
            (fuSfield (I := I) g₁ g₂ t x) := by
      rw [fuSdec (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht x, inner0S_add_left, inner0S_add_left]
    have hpair := fuRmSqD (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ ht x
    rw [hcar] at hsplit
    rw [hcar]
    rw [hpair]
    linarith [hsplit]
  rw [hfun]
  refine (((tderivCont (I := I) (J := Ioo a b) isOpen_Ioo ht
      (fun r x => rmDiffSq (I := I) (g₁ r) (g₂ r) x)
      (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ (fuGramIoo (I := I) g₂ hjoint₂))).sub
        (fuReactCont (I := I) g₁ g₂ hgram₁ hpde₁ ht)).const_mul _ |>.sub ?_).sub ?_
  · exact inner0S_continuous (I := I) (g₁ t)
      (roughLap0SField (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t))
      (fuSfield (I := I) g₁ g₂ t)
  · exact inner0S_continuous (I := I) (g₁ t)
      (covDiv0SField (I := I) (g₁ t) (fuUflux (I := I) g₁ g₂ t))
      (fuSfield (I := I) g₁ g₂ t)

/-- **The moving-volume trace is the intrinsic metric trace of the flow speed.**  Under
`∂ₜg = −2Q` the chart-defined `traceTimeDerivMetric` equals `−2 tr_{g t} Q`, a basis-free
quantity.

This duplicates `IntrinsicSpectral.traceTime_rd`
(`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean`), which sits in a *higher* layer than
`Evolution/`, so importing it here would invert the layering.  **Relocation TODO**: both copies
belong next to `traceTimeDerivMetric` in `Analysis/Integration/Measure/Family.lean`. -/
private theorem fuTraceRd {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    traceTimeDerivMetric (I := I) g t x =
      (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by
  classical
  have htrace : traceTimeDerivMetric (I := I) g t x =
      Matrix.trace ((chartGramMatrix (I := I) (g t) x x)⁻¹ *
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          deriv (fun r : Real => chartGramMatrix (I := I) (g r) x x i j) t)) :=
    traceTimeDerivMetric_eq (I := I) g t x
  have hdG : (Matrix.of fun i j : Fin (Module.finrank Real E) =>
        deriv (fun r : Real => chartGramMatrix (I := I) (g r) x x i j) t) =
      Matrix.of fun i j : Fin (Module.finrank Real E) =>
        (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
          else chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa only [Matrix.of_apply, chartGramMatrix_apply] using
      (hg (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)).deriv
  have hInvSymm : ∀ i j : Fin (Module.finrank Real E),
      ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i =
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j := by
    intro i j
    have hHerm := (chartGramMatrix_isHermitian (I := I) (g t) x x).inv
    simpa only [star_trivial] using hHerm.apply i j
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hscalar : metricTracePair0SAt (I := I) (g t) Q =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j *
          Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) (g t) (chartBasisFamily (I := I) x hx) _
      (chartInvGram_inverse (I := I) (g t) x hx) Q]
    simp only [chartBasisFamily_apply,
      DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix]
    rfl
  rw [htrace, hdG]
  calc
    Matrix.trace ((chartGramMatrix (I := I) (g t) x x)⁻¹ *
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x))) =
        Matrix.trace ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
              else chartBasisVecFiber (I := I) x j x)) *
          (chartGramMatrix (I := I) (g t) x x)⁻¹) := by
      rw [Matrix.trace_mul_comm]
    _ = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
            else chartBasisVecFiber (I := I) x j x)) *
            ((chartGramMatrix (I := I) (g t) x x)⁻¹) j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    _ = (-2 : Real) * (∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((chartGramMatrix (I := I) (g t) x x)⁻¹) i j *
              Q (fun a : Fin 2 => if a = 0 then chartBasisVecFiber (I := I) x i x
                else chartBasisVecFiber (I := I) x j x)) := by
      simp_rw [hInvSymm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = (-2 : Real) * metricTracePair0SAt (I := I) (g t) Q := by rw [hscalar]

/-- **The moving-volume trace is continuous in space.**  Along the flow it is `−2` times the
fibre pairing of two smooth `(0,2)` fields (the metric and the Ricci section), so
`inner0S_continuous` applies. -/
private theorem fuTraceCont (g₁ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I) g₁ t x) := by
  have hgt : ∀ y : M,
      metricTensor0S (I := I) (g₁ t) y = metricTensorField (I := I) (g₁ t) y := fun y =>
    ContinuousMultilinearMap.ext fun v =>
      (metricTensor0S_apply (I := I) (g₁ t) y v).trans
        (metricTensorField_apply (I := I) (g₁ t) y v).symm
  have hric : ∀ y : M, metricRicciAt (I := I) (g₁ t) y =
      CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
        (metricCov_smooth (I := I) (g₁ t)) y := fun y =>
    (CovariantDerivative.ricciSection_apply (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t)) y).symm
  have hfun : (fun x : M => traceTimeDerivMetric (I := I) g₁ t x) =
      fun x : M => (-2 : Real) * inner0S (I := I) (g₁ t) x 2
        (metricTensorField (I := I) (g₁ t) x)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
          (metricCov_smooth (I := I) (g₁ t)) x) := by
    funext x
    rw [fuTraceRd (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)]
    have hval : metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x) =
        inner0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₁ t) x)
          (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
            (metricCov_smooth (I := I) (g₁ t)) x) := by
      rw [← hgt x, ← hric x]
      rfl
    rw [hval]
  rw [hfun]
  exact continuous_const.mul (inner0S_continuous (I := I) (g₁ t)
    (metricTensorField (I := I) (g₁ t))
    (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t))))

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `restInt` member, from (B)'s own fields.**

`rateRest` groups the metric and connection thirds as `movingReact0S + 2⟨Ṫ, T⟩`, i.e. as the time
derivatives of `|h₀₂|²` and `|A₀₃|²`; what is left is the frozen-carrier reaction of the curvature
third and the moving-volume term.  All four summands are continuous in `x`. -/
theorem fuRestInt (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ t ∈ Ioo a b, Integrable
      (fun x => rateRest (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)) t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
  intro t ht
  have hgram₁ := fuGramIoo (I := I) g₁ hjoint₁
  have hgram₂ := fuGramIoo (I := I) g₂ hjoint₂
  refine integrable_of_continuous (I := I) g₁ t ?_
  have hfun : (fun x : M => rateRest (I := I) g₁ g₂
        (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)) t x) =
      fun x : M => deriv (fun r : Real => metricDiffSq (I := I) (g₁ r) (g₂ r) x) t +
          deriv (fun r : Real => connDiffSq (I := I) (g₁ r) (g₂ r) x) t +
          movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
          forwardUniqueDensity (I := I) g₁ g₂ t x := by
    funext x
    rw [fuMetricSqD (I := I) g₁ g₂ hpde₁ hpde₂ ht x,
      fuConnSqD (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ ht x]
    simp only [rateRest]
  rw [hfun]
  refine (((tderivCont (I := I) (J := Ioo a b) isOpen_Ioo ht
      (fun r x => metricDiffSq (I := I) (g₁ r) (g₂ r) x)
      (metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂)).add
    (tderivCont (I := I) (J := Ioo a b) isOpen_Ioo ht
      (fun r x => connDiffSq (I := I) (g₁ r) (g₂ r) x)
      (connDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂))).add
    (fuReactCont (I := I) g₁ g₂ hgram₁ hpde₁ ht)).add ?_
  exact (continuous_const.mul (fuTraceCont (I := I) g₁ hpde₁ ht)).mul
    (dens_continuous (I := I) g₁ g₂ t)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The Kotschwar energy is differentiable at every interior time, from (B)'s own fields.**

`forwardUniqueEnergy_hasDerivAt` (K3) is stated with purely window-local hypotheses — an open
`U`, the chart-Gram package and the joint density smoothness on `U`, and the two flow equations
and two carrier speeds at the single time `t` — every one of which the wiring already supplies at
the constructed carriers. -/
theorem fuEnergyDeriv (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) :
    HasDerivAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
      (forwardUniqueRate (I := I) (M := M) g₁ g₂
        (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂))
        (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂)) t) t := by
  have hS₁ := fuIsSol (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := fuIsSol (I := I) g₂ hab hjoint₂ hpde₂
  exact forwardUniqueEnergy_hasDerivAt (I := I) g₁ g₂
    (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂))
    (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂)) isOpen_Ioo ht
    (fuGramIoo (I := I) g₁ hjoint₁)
    (dens_jointContMDiffOn (I := I) g₁ g₂ (fuGramIoo (I := I) g₁ hjoint₁)
      (fuGramIoo (I := I) g₂ hjoint₂))
    (fun x => pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
    (fun x => pde_hasDerivAt (I := I) g₂ hpde₂ ht x)
    (fun x => connSpeed_hasDerivAt (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (fuGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ t ht x))
    (fun x => rmSpeed_hasDerivAt (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (fuRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht x))

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The bundle's `energyCont` member, reduced to the single closed initial edge.**

The energy is differentiable — hence continuous — at every *interior* time (`fuEnergyDeriv`), so
the only content left in `energyCont` is the one-point statement at `t = a`.  That edge is a
genuine analytic gap: `dens_jointContMDiffOn` lives on the open window because the joint
Christoffel/Riemann tower (`gen_joint_christoffel`, `gen_joint_riemann`) is stated with
`ContDiffAt`, so nothing controls the density at `t = a`. -/
theorem fuEnergyCont (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    (hedge : ContinuousWithinAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) a) :
    ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hEq | hlt
  · rw [← hEq]
    exact hedge
  · exact (fuEnergyDeriv (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      (⟨hlt, ht.2⟩ : t ∈ Ioo a b)).continuousAt.continuousWithinAt

end SpeedContinuity

section SlabFields

/-! ## Slab-uniform fields at the constructed carriers

`Evolution/ForwardUniqueSup.lean` proves the six `ForwardUniqueSlab` estimates in *carrier*
form; the two that are unconditional there — `ricciLe` and, once its three background sups are
supplied, `fluxLe` — are instantiated here at the carriers this file builds.  The background
sups themselves come from the closed-edge compactness layer (`rm04SlabSup`, `metricSlabSup`),
which black box (B)'s own half-open chart-Gram fields feed after restriction to `Icc a c`. -/

/-- The `P` slot of the constructed flux is the **cross-lowered** background curvature.

`fuTf g₁ t − fuSfield g₁ g₂ t = Rm(∇²) lowered by g₁`: the flow-1 curvature minus the
curvature difference is, term by term, the `g₁`-lowering of the *second* connection's Riemann
tensor.  This is what turns `sdecFluxSq_le`'s abstract `B_P` into a curvature sup. -/
theorem fuP_eq (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    (fuTf (I := I) g₁ t - fuSfield (I := I) g₁ g₂ t) x =
      CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x := by
  have hpt : (fuTf (I := I) g₁ t - fuSfield (I := I) g₁ g₂ t) x =
      fuTf (I := I) g₁ t x - fuSfield (I := I) g₁ g₂ t x := rfl
  rw [hpt, fuTf_apply, fuSfield_apply]
  exact sub_sub_cancel _ _

/-- **The `fluxLe` field of `ForwardUniqueSlab` at the constructed carrier, unconditional.**

From black box (B)'s two chart-Gram fields alone: on every closed subslab the three background
norms of `sdecFluxSq_le` — `|Rm₂|²_{g₁}`, `|P|²_{g₁}` and `|g₂|²_{g₁}` — are bounded by the
extreme value theorem, and `fluxSlabLe` absorbs them into the energy density.  No estimate
hypothesis and no PDE enter. -/
theorem fuFluxSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {c : Real} (hc : c ∈ Ioo a b) :
    ∃ C_U : Real, ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 5 (fuUflux (I := I) g₁ g₂ t x) ≤
        C_U * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hsub : Icc a c ⊆ Ico a b := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h1smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hres₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h2smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  obtain ⟨B₂, hB₂0, hB₂⟩ := rm04SlabSup (I := I) g₁ g₂ g₂ hres₁ hres₂ hres₂
  obtain ⟨BP, hBP0, hBP⟩ := rm04SlabSup (I := I) g₁ g₁ g₂ hres₁ hres₁ hres₂
  obtain ⟨Bg, hBg0, hBg⟩ := metricSlabSup (I := I) g₁ g₂ hres₁ hres₂
  refine ⟨32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
    8 * (Module.finrank Real E : Real) ^ 10 * (BP * Bg), fun t ht x => ?_⟩
  have hIcc : t ∈ Icc a c := Ioo_subset_Icc_self ht
  have hBPx : normSq0S (I := I) (g₁ t) x 4
      ((fuTf (I := I) g₁ t - fuSfield (I := I) g₁ g₂ t) x) ≤ BP := by
    rw [fuP_eq (I := I) g₁ g₂ t x]
    exact hBP t hIcc x
  exact fluxSlabLe (I := I) g₁ g₂ (fuTf (I := I) g₂)
    (fun r => fuTf (I := I) g₁ r - fuSfield (I := I) g₁ g₂ r) t x hB₂0 hBP0 hBg0
    (hB₂ t hIcc x) hBPx (hBg t hIcc x)

/-- **The `volLe` field of `ForwardUniqueSlab`, unconditional.**

The volume drift is a background quantity of the *first* flow alone.  `fuTraceRd` reads the
chart-defined `traceTimeDerivMetric` as `−2·tr_{g₁}Ric₁` under (B)'s own Ricci-flow field, and
`volSlabSup` converts the closed-subslab Ricci sup into the constant `C_V = √(n·B)`.  No
joint continuity of the drift itself is needed — the identity replaces it. -/
theorem fuVolSlab (g₁ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    {c : Real} (hc : c ∈ Ioo a b) :
    ∃ C_V : Real, 0 ≤ C_V ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V := by
  have hsub : Icc a c ⊆ Ico a b := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h1smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  obtain ⟨B, _, hB⟩ := ricciSlabSup (I := I) g₁ g₁ hres₁ hres₁
  refine volSlabSup (I := I) g₁ (fun t ht x => ?_) (fun t ht x => hB t (Ioo_subset_Icc_self ht) x)
  exact fuTraceRd (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
    (pde_hasDerivAt (I := I) g₁ h1pde ⟨ht.1, lt_trans ht.2 hc.2⟩ x)

/-- **The `reactLe` field of `ForwardUniqueSlab`, unconditional.**

The three moving-metric reactions of the energy carriers need one background norm only,
`sup |Ric₁|²_{g₁}`, which `ricciSlabSup` produces at `(g₁, g₁)` from (B)'s first chart-Gram
field; `reactSlabLe` then pays the rank-uniform reaction bound `movingReactAbs_le`.  The
metric-variation input of that bound is (B)'s own PDE field at interior times. -/
theorem fuReactSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    {c : Real} (hc : c ∈ Ioo a b) :
    ∃ C_R : Real, 0 ≤ C_R ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hsub : Icc a c ⊆ Ico a b := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h1smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  obtain ⟨Λric, _, hΛ⟩ := ricciSlabSup (I := I) g₁ g₁ hres₁ hres₁
  exact reactSlabLe (I := I) g₁ g₂
    (fun t ht x X Y => pde_hasDerivAt (I := I) g₁ h1pde ⟨ht.1, lt_trans ht.2 hc.2⟩ x X Y)
    (fun t ht x => hΛ t (Ioo_subset_Icc_self ht) x)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The `remLe` field of `ForwardUniqueSlab` at the constructed carrier.**

Every background curvature, derivative, and metric-comparison factor in `sdecRem`
has a closed-subslab supremum supplied by the chart-Gram regularity layer.  The
four remainder summands are then controlled respectively by `rmDotRemSq_le`, the
invariant `gapDot` split, `reLowerDefSq_le`, and the traced `reLowerPair` bound. -/
theorem fuRemSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {c : Real} (hc : c ∈ Ioo a b) :
    ∃ C_rem : Real, ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x) ≤
        C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hsub : Icc a c ⊆ Ico a b := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h1smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hres₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h2smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  obtain ⟨Λ, hΛ0, hΛ⟩ := metricCompSlab (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨Ce, hCe, hEquiv⟩ := metricEquivSlab (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨BH, hBH0, hBH⟩ := metricDiffSlabSup (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨BR1, hBR10, hBR1⟩ := rm04SlabSup (I := I) g₁ g₁ g₁ hres₁ hres₁ hres₁
  obtain ⟨BR2, hBR20, hBR2⟩ := rm04SlabSup (I := I) g₁ g₂ g₂ hres₁ hres₂ hres₂
  obtain ⟨BP, hBP0, hBP⟩ := rm04SlabSup (I := I) g₁ g₁ g₂ hres₁ hres₁ hres₂
  obtain ⟨BRic21, hBRic210, hBRic21⟩ :=
    ricciSlabSup (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨B5, hB50, hB5⟩ :=
    crossRm1SlabSup (I := I) g₁ g₂ g₂ g₂ hres₁ hres₂ hres₂ hres₂
  obtain ⟨B6, hB60, hB6⟩ :=
    crossRm2SlabSup (I := I) g₁ g₂ g₂ g₂ hres₁ hres₂ hres₂ hres₂
  obtain ⟨BP1, hBP10, hBP1⟩ :=
    crossRm1SlabSup (I := I) g₁ g₁ g₂ g₁ hres₁ hres₁ hres₂ hres₁
  obtain ⟨BP2, hBP20, hBP2⟩ :=
    crossRm2SlabSup (I := I) g₁ g₁ g₂ g₁ hres₁ hres₁ hres₂ hres₁
  obtain ⟨BR2g2, hBR2g20, hBR2g2⟩ :=
    rm04SlabSup (I := I) g₂ g₂ g₂ hres₂ hres₂ hres₂
  obtain ⟨BRic2g2, hBRic2g20, hBRic2g2⟩ :=
    ricciSlabSup (I := I) g₂ g₂ hres₂ hres₂
  obtain ⟨B6g2, hB6g20, hB6g2⟩ :=
    crossRm2SlabSup (I := I) g₂ g₂ g₂ g₂ hres₂ hres₂ hres₂ hres₂
  obtain ⟨Bg, _, hBg⟩ := metricSlabSup (I := I) g₁ g₂ hres₁ hres₂
  let n : Real := Module.finrank Real E
  let KQ : Real :=
    16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
      2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * BR2 ^ 2)
  let KD : Real := 32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)
  let KR0 : Real :=
    200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 + 16 * KQ + 2 * KD
  let BSpeed : Real :=
    8 * n ^ 6 * B6g2 + 512 * n ^ 14 * BR2g2 ^ 2 +
      72 * n ^ 6 * (BRic2g2 * BR2g2)
  let KG : Real := 8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed
  let KL : Real := n ^ 12 * BP2
  let KT : Real := 4 * n ^ 17 * BP1 * Bg
  let C_rem : Real := 8 * KR0 + 8 * KG + 4 * KL + 2 * KT
  refine ⟨C_rem, fun t ht x => ?_⟩
  have hIcc : t ∈ Icc a c := Ioo_subset_Icc_self ht
  let d : Real := forwardUniqueDensity (I := I) g₁ g₂ t x
  let P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    fuTf (I := I) g₁ t - fuSfield (I := I) g₁ g₂ t
  let R0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
      (rmDotRem (I := I) (g₁ t) (g₂ t) (fuTf (I := I) g₂ t)
        (fuRm04 (I := I) g₁) (fuRm04 (I := I) g₂)
        (fuBRm (I := I) g₁) (fuBRm (I := I) g₂)
        (fuRicUp (I := I) g₁) (fuRicUp (I := I) g₂)
        (fun m z => coordBasisAt (I := I) z m) t x)
  let V₂ :
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x :=
    uhlRm2Vec (I := I) g₂ (coordBasisAt (I := I))
      (fuRm04 (I := I) g₂) (fuLapRm (I := I) g₂) (fuBRm (I := I) g₂)
      (fuRicUp (I := I) g₂) t x
  let G : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    gapDot (I := I) (g₁ t) (g₂ t) V₂
  let L : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    (reLower (I := I) (g₂ t) (g₁ t) (roughLap0SField (I := I) (g₁ t) P) -
      roughLap0SField (I := I) (g₁ t) P) x
  let K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
    lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t))
  let T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 4) (g₁ t)
      (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P) K) x
  have hR0 : normSq0S (I := I) (g₁ t) x 4 R0 ≤ KR0 * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hconn :
        connDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using connDiffSq_le_dens (I := I) g₁ g₂ t x
    have hrm :
        rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using rmDiffSq_le_dens (I := I) g₁ g₂ t x
    have hTf1 :
        normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₁ t x) ≤ BR1 := by
      simpa only [fuTf_apply, metricRm04At] using hBR1 t hIcc x
    have hTf2 :
        normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₂ t x) ≤ BR2 := by
      simpa only [fuTf_apply, metricRm04At] using hBR2 t hIcc x
    have hown0 := ownRmDiffSq_le (I := I) (g₁ t) (g₂ t) x (hBP t hIcc x)
    have hown :
        normSq0S (I := I) (g₁ t) x 4
            (fuTf (I := I) g₁ t x - fuTf (I := I) g₂ t x) ≤
          (2 + 2 * n ^ 6 * BP) * d := by
      calc
        normSq0S (I := I) (g₁ t) x 4
            (fuTf (I := I) g₁ t x - fuTf (I := I) g₂ t x) ≤
            2 * rmDiffSq (I := I) (g₁ t) (g₂ t) x +
              2 * n ^ 6 * BP * metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
          simpa only [fuTf_apply, metricRm04At, n] using hown0
        _ ≤ 2 * d + 2 * n ^ 6 * BP * d := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrm (by norm_num))
            (mul_le_mul_of_nonneg_left hmetric
              (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn 6)) hBP0))
        _ = (2 + 2 * n ^ 6 * BP) * d := by ring
    have hsum :
        normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₁ t x) +
            normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₂ t x) ≤
          BR1 + BR2 :=
      add_le_add hTf1 hTf2
    have hTf20 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₂ t x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hTf10 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₁ t x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hTf2sq :
        normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₂ t x) ^ 2 ≤ BR2 ^ 2 := by
      nlinarith
    have hQ0 := bCombDiffSq_le (I := I) (g₁ t) (g₂ t)
      (fuTf (I := I) g₁ t) (fuTf (I := I) g₂ t) x hΛ0
      (hΛ t hIcc x) (hBH t hIcc x)
    have hQ :
        normSq0S (I := I) (g₁ t) x 4
            (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
              (fun i j k l =>
                (fuBRm (I := I) g₁ t x i j k l - fuBRm (I := I) g₂ t x i j k l) -
                    (fuBRm (I := I) g₁ t x i j l k -
                      fuBRm (I := I) g₂ t x i j l k) +
                  (fuBRm (I := I) g₁ t x i k j l -
                    fuBRm (I := I) g₂ t x i k j l) -
                    (fuBRm (I := I) g₁ t x i l j k -
                      fuBRm (I := I) g₂ t x i l j k))) ≤
          KQ * d := by
      rw [fuB_diff_low (I := I) g₁ g₂ t x]
      let ND := normSq0S (I := I) (g₁ t) x 4
        (fuTf (I := I) g₁ t x - fuTf (I := I) g₂ t x)
      let N1 := normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₁ t x)
      let N2 := normSq0S (I := I) (g₁ t) x 4 (fuTf (I := I) g₂ t x)
      let HM := metricDiffSq (I := I) (g₁ t) (g₂ t) x
      have hQ0' :
          normSq0S (I := I) (g₁ t) x 4
              (bComb (I := I) (g₁ t) (fuTf (I := I) g₁ t) x -
                bComb (I := I) (g₂ t) (fuTf (I := I) g₂ t) x) ≤
            16 * (4 * n ^ 14 * ND * (N1 + N2) +
              2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
                HM * N2 ^ 2) := by
        simpa only [ND, N1, N2, HM, n] using hQ0
      have hND : ND ≤ (2 + 2 * n ^ 6 * BP) * d := by
        simpa only [ND] using hown
      have hNsum : N1 + N2 ≤ BR1 + BR2 := by
        simpa only [N1, N2] using hsum
      have hNsum0 : 0 ≤ N1 + N2 := by
        simpa only [N1, N2] using add_nonneg hTf10 hTf20
      have hCD0 : 0 ≤ (2 + 2 * n ^ 6 * BP) * d := by
        exact mul_nonneg (by positivity) hd
      have hprod1 :
          ND * (N1 + N2) ≤ ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) :=
        mul_le_mul hND hNsum hNsum0 hCD0
      have hterm1 :
          4 * n ^ 14 * ND * (N1 + N2) ≤
            4 * n ^ 14 * ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hprod1 (mul_nonneg (by norm_num) (pow_nonneg hn 14))
      have hN2sq : N2 ^ 2 ≤ BR2 ^ 2 := by
        simpa only [N2] using hTf2sq
      have hHM : HM ≤ d := by
        simpa only [HM] using hmetric
      have hprod2 : HM * N2 ^ 2 ≤ d * BR2 ^ 2 :=
        mul_le_mul hHM hN2sq (sq_nonneg _) hd
      have hcoef2 :
          0 ≤ 2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) := by
        positivity
      have hterm2 :
          2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * HM * N2 ^ 2 ≤
            2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * d *
              BR2 ^ 2 := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod2 hcoef2
      refine hQ0'.trans ?_
      dsimp only [KQ]
      calc
        _ ≤ 16 * (4 * n ^ 14 * ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) +
            2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
              d * BR2 ^ 2) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
        _ = (16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
              2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
                BR2 ^ 2)) * d := by ring
    have hD0 := ricciDriftSq_le (I := I) (g₁ t) (g₂ t) x
    have hRicDiff := ricciSlabLe (I := I) g₁ g₂ t x
    have hRicDiffUpper0 : 0 ≤ n ^ 4 * d :=
      mul_nonneg (pow_nonneg hn 4) hd
    have hRic2zero :
        0 ≤ normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hrm0 : 0 ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [rmDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hDprod1 :
        normSq0S (I := I) (g₁ t) x 2
              (metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤
          (n ^ 4 * d) * BR1 := by
      have hRm1 :
          normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤
            BR1 := by
        simpa only [fuTf_apply] using hTf1
      exact mul_le_mul hRicDiff hRm1
        (normSq0S_nonneg (I := I) (g₁ t) x 4 _) hRicDiffUpper0
    have hDprod2 :
        normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
            rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          BRic21 * d :=
      mul_le_mul (hBRic21 t hIcc x) hrm hrm0 hBRic210
    have hD :
        normSq0S (I := I) (g₁ t) x 4
            (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
              (fun i j k l =>
                riemann04RicciDriftInFrame (fuRicUp (I := I) g₁)
                    (fuRm04 (I := I) g₁) t x i j k l -
                  riemann04RicciDriftInFrame (fuRicUp (I := I) g₂)
                    (fuRm04 (I := I) g₂) t x i j k l)) ≤
          KD * d := by
      rw [fuDrift_diff_low (I := I) g₁ g₂ t x]
      refine hD0.trans ?_
      dsimp only [KD]
      calc
        _ ≤ 32 * n ^ 6 *
            ((n ^ 4 * d) * BR1 + BRic21 * d) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hDprod1 hDprod2)
            (mul_nonneg (by norm_num) (pow_nonneg hn 6))
        _ = (32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)) * d := by ring
    have hR0raw := rmDotRemSq_le (I := I) (g₁ t) (g₂ t)
      (fuTf (I := I) g₂ t) (coordBasisAt (I := I))
      (fuRm04 (I := I) g₁) (fuRm04 (I := I) g₂)
      (fuBRm (I := I) g₁) (fuBRm (I := I) g₂)
      (fuRicUp (I := I) g₁) (fuRicUp (I := I) g₂) t x
      hΛ0 (hΛ t hIcc x) (hB5 t hIcc x) (hB6 t hIcc x) hQ hD
    dsimp only [R0]
    refine hR0raw.trans ?_
    have hspace1 :
        50 * n ^ 12 * connDiffSq (I := I) (g₁ t) (g₂ t) x * B5 ≤
          50 * n ^ 12 * d * B5 := by
      have h := mul_le_mul_of_nonneg_right hconn hB50
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (pow_nonneg hn 12))
    have hspace2 :
        2 * n ^ 10 * Λ ^ 2 * metricDiffSq (I := I) (g₁ t) (g₂ t) x * B6 ≤
          2 * n ^ 10 * Λ ^ 2 * d * B6 := by
      have h := mul_le_mul_of_nonneg_right hmetric hB60
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left h
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn 10)) (sq_nonneg Λ))
    have hspace :
        4 * (50 * n ^ 12 * connDiffSq (I := I) (g₁ t) (g₂ t) x * B5 +
            2 * n ^ 10 * Λ ^ 2 * metricDiffSq (I := I) (g₁ t) (g₂ t) x * B6) ≤
          4 * (50 * n ^ 12 * d * B5 + 2 * n ^ 10 * Λ ^ 2 * d * B6) :=
      mul_le_mul_of_nonneg_left (add_le_add hspace1 hspace2) (by norm_num)
    dsimp only [KR0]
    calc
      _ ≤ 4 * (50 * n ^ 12 * d * B5 + 2 * n ^ 10 * Λ ^ 2 * d * B6) +
          16 * (KQ * d) + 2 * (KD * d) := by
        exact add_le_add (add_le_add hspace (le_refl _)) (le_refl _)
      _ = (200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 +
          16 * KQ + 2 * KD) * d := by ring
  have hG : normSq0S (I := I) (g₁ t) x 4 G ≤ KG * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
    let Rg : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
      lowerTri (I := I)
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
        (riemannOp (metricCov (I := I) (g₂ t)) x)
    let Hg : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
      lowerTri (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x) V₂
    have hGsplit : G = (2 : Real) • Rg - Hg := rfl
    have hRg0 := lowerTriSq_le (I := I) (g₁ t)
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
      (riemannOp (metricCov (I := I) (g₂ t)) x)
    rw [lowerRm_cross (I := I) (g₁ t) (g₂ t) x] at hRg0
    have hRicDiff := ricciSlabLe (I := I) g₁ g₂ t x
    have hCross0 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4
          (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
            (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hRicUpper0 : 0 ≤ n ^ 4 * d := mul_nonneg (pow_nonneg hn 4) hd
    have hprodR :
        normSq0S (I := I) (g₁ t) x 2
              (metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₁ t) x 4
              (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
                (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤
          (n ^ 4 * d) * BP :=
      mul_le_mul hRicDiff (hBP t hIcc x) hCross0 hRicUpper0
    have hRg :
        normSq0S (I := I) (g₁ t) x 4 Rg ≤ n ^ 10 * BP * d := by
      refine hRg0.trans ?_
      calc
        _ ≤ n ^ 6 * ((n ^ 4 * d) * BP) :=
          mul_le_mul_of_nonneg_left hprodR (pow_nonneg hn 6)
        _ = n ^ 10 * BP * d := by ring
    have h2Rg_eq :
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) =
          4 * normSq0S (I := I) (g₁ t) x 4 Rg := by
      calc
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) =
            (2 : Real) ^ 2 * normSq0S (I := I) (g₁ t) x 4 Rg :=
          Tensor0SBundle.normSq0S_smul (I := I) (g₁ t) (2 : Real) Rg
        _ = 4 * normSq0S (I := I) (g₁ t) x 4 Rg := by norm_num
    have h2Rg :
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) ≤
          4 * (n ^ 10 * BP * d) := by
      rw [h2Rg_eq]
      exact mul_le_mul_of_nonneg_left hRg (by norm_num)
    have hNabla2 :
        normSq0S (I := I) (g₂ t) x 6
            (metricNabla0S (I := I) (g₂ t)
              (metricNabla0S (I := I) (g₂ t) (fuTf (I := I) g₂ t)) x) ≤
          B6g2 := by
      simpa only [fuTf, metricRm04] using hB6g2 t hIcc x
    have hRm2 :
        normSq0S (I := I) (g₂ t) x 4 (fuTf (I := I) g₂ t x) ≤ BR2g2 := by
      simpa only [fuTf_apply, metricRm04At] using hBR2g2 t hIcc x
    have hRm20 :
        0 ≤ normSq0S (I := I) (g₂ t) x 4 (fuTf (I := I) g₂ t x) :=
      normSq0S_nonneg (I := I) (g₂ t) x 4 _
    have hRm2sq :
        normSq0S (I := I) (g₂ t) x 4 (fuTf (I := I) g₂ t x) ^ 2 ≤
          BR2g2 ^ 2 := by
      nlinarith
    have hRicRm :
        normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤
          BRic2g2 * BR2g2 := by
      have hRm2' :
          normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤
            BR2g2 := by
        simpa only [fuTf_apply] using hRm2
      exact mul_le_mul (hBRic2g2 t hIcc x) hRm2'
        (normSq0S_nonneg (I := I) (g₂ t) x 4 _) hBRic2g20
    have hSpeed0 := uhlSpeedSq_le (I := I) (g₂ t) (fuTf (I := I) g₂ t) x
    have hSpeed :
        normSq0S (I := I) (g₂ t) x 4
            (uhlSpeed04 (I := I) (g₂ t) (fuTf (I := I) g₂ t) x) ≤
          BSpeed := by
      have hS1 :
          8 * n ^ 6 *
              normSq0S (I := I) (g₂ t) x 6
                (metricNabla0S (I := I) (g₂ t)
                  (metricNabla0S (I := I) (g₂ t) (fuTf (I := I) g₂ t)) x) ≤
            8 * n ^ 6 * B6g2 :=
        mul_le_mul_of_nonneg_left hNabla2
          (mul_nonneg (by norm_num) (pow_nonneg hn 6))
      have hS2 :
          512 * n ^ 14 *
              normSq0S (I := I) (g₂ t) x 4 (fuTf (I := I) g₂ t x) ^ 2 ≤
            512 * n ^ 14 * BR2g2 ^ 2 :=
        mul_le_mul_of_nonneg_left hRm2sq
          (mul_nonneg (by norm_num) (pow_nonneg hn 14))
      have hS3 :
          72 * n ^ 6 *
              (normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
                normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x)) ≤
            72 * n ^ 6 * (BRic2g2 * BR2g2) :=
        mul_le_mul_of_nonneg_left hRicRm
          (mul_nonneg (by norm_num) (pow_nonneg hn 6))
      have hSpeed0' :
          normSq0S (I := I) (g₂ t) x 4
              (uhlSpeed04 (I := I) (g₂ t) (fuTf (I := I) g₂ t) x) ≤
            8 * n ^ 6 *
                normSq0S (I := I) (g₂ t) x 6
                  (metricNabla0S (I := I) (g₂ t)
                    (metricNabla0S (I := I) (g₂ t) (fuTf (I := I) g₂ t)) x) +
              512 * n ^ 14 *
                  normSq0S (I := I) (g₂ t) x 4 (fuTf (I := I) g₂ t x) ^ 2 +
                72 * n ^ 6 *
                  (normSq0S (I := I) (g₂ t) x 2
                      (metricRicciAt (I := I) (g₂ t) x) *
                    normSq0S (I := I) (g₂ t) x 4
                      (metricRm04At (I := I) (g₂ t) x)) := by
        simpa only [n] using hSpeed0
      refine hSpeed0'.trans ?_
      dsimp only [BSpeed]
      exact add_le_add (add_le_add hS1 hS2) hS3
    have hBSpeed0 : 0 ≤ BSpeed := by
      dsimp only [BSpeed]
      positivity
    have hVlow :
        lowerTri (I := I) (metricTensorField (I := I) (g₂ t) x) V₂ =
          uhlSpeed04 (I := I) (g₂ t) (fuTf (I := I) g₂ t) x := by
      simpa only [V₂] using fuSpeed_low (I := I) g₂ t x
    have hswap := lowerTriSwapSq_le (I := I) (g₁ t) (g₂ t) V₂ hCe
      (hEquiv t hIcc x)
    rw [hVlow] at hswap
    have hSpeedMetric :
        normSq0S (I := I) (g₂ t) x 4
              (uhlSpeed04 (I := I) (g₂ t) (fuTf (I := I) g₂ t) x) *
            metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          BSpeed * d :=
      mul_le_mul hSpeed hmetric hmetric0 hBSpeed0
    have hHg : normSq0S (I := I) (g₁ t) x 4 Hg ≤
        Ce ^ 6 * n ^ 6 * BSpeed * d := by
      refine hswap.trans ?_
      calc
        _ ≤ Ce ^ 6 * n ^ 6 * (BSpeed * d) :=
          mul_le_mul_of_nonneg_left hSpeedMetric
            (mul_nonneg (pow_nonneg (le_trans (by norm_num) hCe) 6) (pow_nonneg hn 6))
        _ = Ce ^ 6 * n ^ 6 * BSpeed * d := by ring
    rw [hGsplit]
    refine (normSq0S_sub_le (I := I) (g₁ t) x 4 ((2 : Real) • Rg) Hg).trans ?_
    dsimp only [KG]
    calc
      _ ≤ 2 * (4 * (n ^ 10 * BP * d)) +
          2 * (Ce ^ 6 * n ^ 6 * BSpeed * d) :=
        add_le_add
          (mul_le_mul_of_nonneg_left h2Rg (by norm_num))
          (mul_le_mul_of_nonneg_left hHg (by norm_num))
      _ = (8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed) * d := by ring
  have hPfield :
      P = CovariantDerivative.rm04Section (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) := by
    refine DFunLike.ext _ _ fun y => ?_
    simpa only [P, CovariantDerivative.rm04Section_apply] using
      fuP_eq (I := I) g₁ g₂ t y
  have hL : normSq0S (I := I) (g₁ t) x 4 L ≤ KL * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hDeriv :
        normSq0S (I := I) (g₁ t) x 6
            (metricNabla0S (I := I) (g₁ t)
              (metricNabla0S (I := I) (g₁ t) P) x) ≤
          BP2 := by
      rw [hPfield]
      exact hBP2 t hIcc x
    have hLap0 := roughLapSq_le (I := I) (s := 4) (g₁ t) P x
    have hLap :
        normSq0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) P x) ≤
          n ^ 6 * BP2 := by
      refine hLap0.trans ?_
      simpa only [n] using
        mul_le_mul_of_nonneg_left hDeriv (pow_nonneg hn 6)
    have hLapUpper0 : 0 ≤ n ^ 6 * BP2 :=
      mul_nonneg (pow_nonneg hn 6) hBP20
    have hprod :
        normSq0S (I := I) (g₁ t) x 4
              (roughLap0SField (I := I) (g₁ t) P x) *
            metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          (n ^ 6 * BP2) * d :=
      mul_le_mul hLap hmetric hmetric0 hLapUpper0
    have hDef0 := reLowerDefSq_le (I := I) (s := 3) (g₁ t) (g₂ t)
      (roughLap0SField (I := I) (g₁ t) P) x
    have hDef :
        normSq0S (I := I) (g₁ t) x 4 L ≤
          n ^ 6 *
            (normSq0S (I := I) (g₁ t) x 4
                (roughLap0SField (I := I) (g₁ t) P x) *
              metricDiffSq (I := I) (g₁ t) (g₂ t) x) := by
      simpa only [L, ContMDiffSection.coe_sub, Pi.sub_apply, n] using hDef0
    refine hDef.trans ?_
    dsimp only [KL]
    calc
      _ ≤ n ^ 6 * ((n ^ 6 * BP2) * d) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg hn 6)
      _ = n ^ 12 * BP2 * d := by ring
  have hT : normSq0S (I := I) (g₁ t) x 4 T ≤ KT * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hconn :
        connDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using connDiffSq_le_dens (I := I) g₁ g₂ t x
    have hMetricField0 :
        0 ≤ normSq0S (I := I) (g₁ t) x 2
          (metricTensorField (I := I) (g₂ t) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hGradP :
        normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) P x) ≤ BP1 := by
      rw [hPfield]
      exact hBP1 t hIcc x
    have hFluxProd :
        connDiffSq (I := I) (g₁ t) (g₂ t) x *
            normSq0S (I := I) (g₁ t) x 2
              (metricTensorField (I := I) (g₂ t) x) ≤
          d * Bg :=
      mul_le_mul hconn (hBg t hIcc x) hMetricField0 hd
    have hFlux0 := fluxNormSq_le (I := I) (s := 2) (g₁ t) (g₂ t)
      (metricTensorField (I := I) (g₂ t)) x
    have hFlux : normSq0S (I := I) (g₁ t) x 3 (K x) ≤
        4 * n ^ 3 * Bg * d := by
      dsimp only [K]
      refine hFlux0.trans ?_
      calc
        _ = (2 : Real) ^ 2 * n ^ 3 *
            (connDiffSq (I := I) (g₁ t) (g₂ t) x *
              normSq0S (I := I) (g₁ t) x 2
                (metricTensorField (I := I) (g₂ t) x)) := by ring
        _ ≤ (2 : Real) ^ 2 * n ^ 3 * (d * Bg) :=
          mul_le_mul_of_nonneg_left hFluxProd
            (mul_nonneg (sq_nonneg (2 : Real)) (pow_nonneg hn 3))
        _ = 4 * n ^ 3 * Bg * d := by ring
    have hFluxNorm0 : 0 ≤ normSq0S (I := I) (g₁ t) x 3 (K x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 3 _
    have hPairProd :
        normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) P x) *
            normSq0S (I := I) (g₁ t) x 3 (K x) ≤
          BP1 * (4 * n ^ 3 * Bg * d) :=
      mul_le_mul hGradP hFlux hFluxNorm0 hBP10
    have hPair0 := reLowerPairSq_le (I := I) (s := 4) (g₁ t)
      (metricNabla0S (I := I) (g₁ t) P) K x
    have hPair :
        normSq0S (I := I) (g₁ t) x 6
            (reLowerPair (I := I) (g₁ t)
              (metricNabla0S (I := I) (g₁ t) P) K x) ≤
          4 * n ^ 11 * BP1 * Bg * d := by
      refine hPair0.trans ?_
      calc
        _ ≤ n ^ 8 * (BP1 * (4 * n ^ 3 * Bg * d)) :=
          mul_le_mul_of_nonneg_left hPairProd (pow_nonneg hn 8)
        _ = 4 * n ^ 11 * BP1 * Bg * d := by ring
    have hTrace0 := traceNormSq_le (I := I) (s := 4) (g₁ t) x
      (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P) K x)
    have hTrace :
        normSq0S (I := I) (g₁ t) x 4 T ≤
          n ^ 6 *
            normSq0S (I := I) (g₁ t) x 6
              (reLowerPair (I := I) (g₁ t)
                (metricNabla0S (I := I) (g₁ t) P) K x) := by
      simpa only [T, metricTraceFirstTwoField_apply, n] using hTrace0
    refine hTrace.trans ?_
    dsimp only [KT]
    calc
      _ ≤ n ^ 6 * (4 * n ^ 11 * BP1 * Bg * d) :=
        mul_le_mul_of_nonneg_left hPair (pow_nonneg hn 6)
      _ = 4 * n ^ 17 * BP1 * Bg * d := by ring
  have hAB := normSq0S_add_le (I := I) (g₁ t) x 4 R0 G
  have hABC := normSq0S_sub_le (I := I) (g₁ t) x 4 (R0 + G) L
  have hABCD := normSq0S_sub_le (I := I) (g₁ t) x 4 ((R0 + G) - L) T
  change normSq0S (I := I) (g₁ t) x 4 (((R0 + G) - L) - T) ≤ C_rem * d
  calc
    normSq0S (I := I) (g₁ t) x 4 (((R0 + G) - L) - T) ≤
        2 * normSq0S (I := I) (g₁ t) x 4 ((R0 + G) - L) +
          2 * normSq0S (I := I) (g₁ t) x 4 T := hABCD
    _ ≤ 8 * normSq0S (I := I) (g₁ t) x 4 R0 +
          8 * normSq0S (I := I) (g₁ t) x 4 G +
          4 * normSq0S (I := I) (g₁ t) x 4 L +
          2 * normSq0S (I := I) (g₁ t) x 4 T := by
      nlinarith [hAB, hABC]
    _ ≤ 8 * (KR0 * d) + 8 * (KG * d) + 4 * (KL * d) + 2 * (KT * d) := by
      nlinarith [hR0, hG, hL, hT]
    _ = C_rem * d := by
      dsimp only [C_rem]
      ring

/-- **The `adotLe` field of `ForwardUniqueSlab` at the constructed carrier.**

The four background constants of `connDiffDot_normSq_le` are supplied on the closed subslab
by `ricciSlabSup`, `nablaRicSlabSup`, and `metricCompSlab`.  Its component inputs are the
canonical chart-frame inverse and `∇Ric` families: `fuGamma` supplies the Christoffel
derivatives, `connDiffVec_hasDerivAt` turns them into the invariant connection-difference
derivative, and `nablaRicReal_frame` identifies the explicit `chartNablaRic` components with
the intrinsic covariant derivatives. -/
theorem fuAdotSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {c : Real} (hc : c ∈ Ioo a b) :
    ∃ C_A : Real, ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 3
          (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) t x) ≤
        C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x)) := by
  have hsub : Icc a c ⊆ Ico a b := fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h1smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hres₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (h2smooth x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  obtain ⟨Λric, hΛric0, hΛric⟩ := ricciSlabSup (I := I) g₁ g₁ hres₁ hres₁
  obtain ⟨Λ, hΛ0, hΛ⟩ := metricCompSlab (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨B₁, hB₁0, hB₁⟩ := nablaRicSlabSup (I := I) g₁ g₂ hres₁ hres₂
  obtain ⟨B₃, hB₃0, hB₃⟩ := ricciSlabSup (I := I) g₁ g₂ hres₁ hres₂
  let K : Real := 2 * (200 * ((Module.finrank Real E : Real) ^ 6 + 1))
  let L : Real := (1 + Λ) ^ 2 * (B₁ + B₃)
  let C_A : Real := max (8 * Λric + K * L) K
  refine ⟨C_A, fun t ht x => ?_⟩
  have hIcc : t ∈ Icc a c := Ioo_subset_Icc_self ht
  let frame := chartFrame I x
  let hframe := chartFrame_isFrame I x
  have hu : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := chartFrame_mem I x
  let Ric₁ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t))
  let Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t))
  have hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y := by
    intro y
    exact CovariantDerivative.ricciSection_apply (I := I) (metricCov (I := I) (g₁ t))
      (metricCov_smooth (I := I) (g₁ t)) y
  have hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y := by
    intro y
    exact CovariantDerivative.ricciSection_apply (I := I) (metricCov (I := I) (g₂ t))
      (metricCov_smooth (I := I) (g₂ t)) y
  have hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) (fuSfield (I := I) g₁ g₂ t) :=
    fun y => fuSfield_apply (I := I) g₁ g₂ t y
  have hgInv₁ : MetricInverseInBasis_gen (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j => chartFrameInv (I := I) g₁ x t x i j) := by
    have hlocal := localFrameInv_real (I := I) (D := refD)
      (solOfMetric (I := I) (D := refD) g₁)
      (chartFrame I x) (chartFrame_isFrameTop I x)
    simpa [MetricInverseInBasis_gen, InvMetricLocal, chartFrameInv, metricCompInFrame,
      frame, hframe] using hlocal t x hx
  have hgInv₂ : MetricInverseInBasis_gen (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j => chartFrameInv (I := I) g₂ x t x i j) := by
    have hlocal := localFrameInv_real (I := I) (D := refD)
      (solOfMetric (I := I) (D := refD) g₂)
      (chartFrame I x) (chartFrame_isFrameTop I x)
    simpa [MetricInverseInBasis_gen, InvMetricLocal, chartFrameInv, metricCompInFrame,
      frame, hframe] using hlocal t x hx
  have hNR₁ : ∀ d i j : Fin (Module.finrank Real E),
      chartNablaRic (I := I) g₁ x t x d i j =
        component0S (I := I) (hframe.toBasisAt hx)
          (metricNabla0S (I := I) (g₁ t) Ric₁ x)
          (fun s : Fin 3 => if s = 0 then d else if s = 1 then i else j) := by
    intro d i j
    have hreal := nablaRicReal_frame (I := I) (solOfMetric (I := I) (D := refD) g₁) t
      (chartFrame I x) hframe hu hx d i j
    have hslots :
        (fun s : Fin 3 =>
          (hframe.toBasisAt hx) (if s = 0 then d else if s = 1 then i else j)) =
          DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (chartFrame I x d x) (chartFrame I x i x) (chartFrame I x j x) := by
      funext s
      fin_cases s <;>
        simp [DifferentialGeometry.Integral.Connection.vec3]
    rw [component0S_apply, hslots, metricNabla0S_apply]
    simpa [chartNablaRic, Ric₁, nablaRicComp, solOfMetric, SolutionOn.family,
      SolutionOn.ricci, SolutionFamily.connection, SolutionFamily.ricci, metricRicci,
      metricCov, frame, hframe] using hreal.symm
  have hNR₂ : ∀ d i j : Fin (Module.finrank Real E),
      chartNablaRic (I := I) g₂ x t x d i j =
        component0S (I := I) (hframe.toBasisAt hx)
          (metricNabla0S (I := I) (g₂ t) Ric₂ x)
          (fun s : Fin 3 => if s = 0 then d else if s = 1 then i else j) := by
    intro d i j
    have hreal := nablaRicReal_frame (I := I) (solOfMetric (I := I) (D := refD) g₂) t
      (chartFrame I x) hframe hu hx d i j
    have hslots :
        (fun s : Fin 3 =>
          (hframe.toBasisAt hx) (if s = 0 then d else if s = 1 then i else j)) =
          DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (chartFrame I x d x) (chartFrame I x i x) (chartFrame I x j x) := by
      funext s
      fin_cases s <;>
        simp [DifferentialGeometry.Integral.Connection.vec3]
    rw [component0S_apply, hslots, metricNabla0S_apply]
    simpa [chartNablaRic, Ric₂, nablaRicComp, solOfMetric, SolutionOn.family,
      SolutionOn.ricci, SolutionFamily.connection, SolutionFamily.ricci, metricRicci,
      metricCov, frame, hframe] using hreal.symm
  have hΓcoeff := fuGamma (I := I) g₁ g₂ hab h1smooth h2smooth h1pde h2pde
    t ⟨ht.1, lt_trans ht.2 hc.2⟩ x
  have hΓ : ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
            (chartNablaRic (I := I) g₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
            (chartNablaRic (I := I) g₂ x) t x i j k) t := by
    intro i j k
    have hval :
        hframe.coeff k x
            ((fuAvec (I := I) g₁ g₂ t x (frame j x)) (frame i x)) =
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
              (chartNablaRic (I := I) g₁ x) t x i j k -
            christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
              (chartNablaRic (I := I) g₂ x) t x i j k := by
      simpa [fuAvec, christoffelDiffSpeed, frame, hframe] using
        (coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) hx
          (fun i j k =>
            christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
                (chartNablaRic (I := I) g₁ x) t x i j k -
              christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
                (chartNablaRic (I := I) g₂ x) t x i j k) i j k)
    simpa only [frame, hframe, hval] using hΓcoeff i j k
  have hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((fuAvec (I := I) g₁ g₂ t x Y) X) t :=
    fun X Y => connDiffVec_hasDerivAt (I := I) g₁ g₂ frame hframe hu hx
      (fuAvec (I := I) g₁ g₂ t) hΓcoeff X Y
  have hmain := connDiffDot_normSq_le (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂ t)
    frame hframe hu hx (fuSfield (I := I) g₁ g₂ t) hS Ric₁ Ric₂ hRic₁ hRic₂
    (chartFrameInv (I := I) g₁ x) (chartFrameInv (I := I) g₂ x) hgInv₁ hgInv₂
    (chartNablaRic (I := I) g₁ x) (chartNablaRic (I := I) g₂ x) hNR₁ hNR₂ hΓ hA
    (hΛric t hIcc x) hΛ0 (hΛ t hIcc x) (hB₁ t hIcc x) (hB₃ t hIcc x)
  have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x :=
    by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have hden0 : 0 ≤ forwardUniqueDensity (I := I) g₁ g₂ t x :=
    density_nonneg (I := I) g₁ g₂ t x
  have hdiss0 : 0 ≤ normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x) :=
    normSq0S_nonneg (I := I) (g₁ t) x 5 _
  have hpair : metricDiffSq (I := I) (g₁ t) (g₂ t) x +
      connDiffSq (I := I) (g₁ t) (g₂ t) x ≤
        forwardUniqueDensity (I := I) g₁ g₂ t x := by
    rw [forwardUniqueDensity]
    exact le_add_of_nonneg_right (by
      rw [rmDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 4 _)
  have hconn : connDiffSq (I := I) (g₁ t) (g₂ t) x ≤
      forwardUniqueDensity (I := I) g₁ g₂ t x :=
    (le_add_of_nonneg_left hmetric0).trans hpair
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (sq_nonneg _) (add_nonneg hB₁0 hB₃0)
  have hfirst :
      8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x ≤
        8 * Λric * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    mul_le_mul_of_nonneg_left hconn (mul_nonneg (by positivity) hΛric0)
  have hsecond :
      K * (nablaRmDiffSq (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x +
          L * (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
            connDiffSq (I := I) (g₁ t) (g₂ t) x)) ≤
        K * (normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x) +
          L * forwardUniqueDensity (I := I) g₁ g₂ t x) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    rw [nablaRmDiffSq, nablaRmDiff]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpair hL0)
  calc
    normSq0S (I := I) (g₁ t) x 3
        (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) t x) ≤
        8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x +
          K * (nablaRmDiffSq (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x +
            L * (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connDiffSq (I := I) (g₁ t) (g₂ t) x)) := by
      simpa [connSpeed, K, L, mul_assoc] using hmain
    _ ≤ 8 * Λric * forwardUniqueDensity (I := I) g₁ g₂ t x +
          K * (normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x) +
            L * forwardUniqueDensity (I := I) g₁ g₂ t x) :=
      add_le_add hfirst hsecond
    _ = (8 * Λric + K * L) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          K * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x) := by ring
    _ ≤ C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          C_A * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hden0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hdiss0)
    _ = C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) (fuSfield (I := I) g₁ g₂ t) x)) := by ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`hbounds` at the constructed carriers, with all six estimates produced internally.**

The chart-Gram regularity and Ricci-flow equations supply the closed-subslab background
bounds used by `fuFluxSlab`, `fuVolSlab`, `fuReactSlab`, `fuRemSlab`, and `fuAdotSlab`;
`ricciSlabLe` supplies the remaining universal curvature coefficient. -/
theorem fuSlab_of_gram (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t) :
    ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem : Real,
      ForwardUniqueSlab (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂))
        (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂)
        a c C_A C_R C_Ric C_V C_U C_rem := by
  intro c hc
  obtain ⟨C_U, hU⟩ := fuFluxSlab (I := I) g₁ g₂ h1smooth h2smooth hc
  obtain ⟨C_V, _, hV⟩ := fuVolSlab (I := I) g₁ h1smooth h1pde hc
  obtain ⟨C_R, _, hR⟩ := fuReactSlab (I := I) g₁ g₂ h1smooth h1pde hc
  obtain ⟨C_rem, hrem'⟩ := fuRemSlab (I := I) g₁ g₂ h1smooth h2smooth hc
  obtain ⟨C_A, hadot'⟩ :=
    fuAdotSlab (I := I) g₁ g₂ (lt_trans hc.1 hc.2)
      h1smooth h2smooth h1pde h2pde hc
  exact ⟨C_A, C_R, (Module.finrank Real E : Real) ^ 4, C_V, C_U, C_rem,
    { fluxLe := hU
      remLe := hrem'
      reactLe := hR
      ricciLe := fun t _ x => ricciSlabLe (I := I) g₁ g₂ t x
      adotLe := hadot'
      volLe := hV }⟩

end SlabFields

/-! ## The residual bundle, assembled

`fuInputs_of_gram` builds `ForwardUniqueInputs` at the constructed carriers from black box
(B)'s own fields plus **two** named residual hypotheses.  Everything else — the three evolution
members, the realization member, the seven density-regularity members, and the three
bare-pointwise integrability members — is discharged here. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The standing bundle of the (B) endgame, at the constructed carriers.**

From (B)'s own fields (`hjointᵢ`, `hpdeᵢ`) together with two residual inputs:

* `hbounds` — K4's six slab-uniform pointwise estimates, per compact subslab;
* `hedge` — continuity of the Kotschwar energy at the *single* closed initial time `a`.

Nothing else remains: `gamma`/`rm`/`sdec` come from the tail Uhlenbeck and Christoffel
producers, `car` is by construction, the density-regularity members come from
`ForwardUniqueDensReg.lean`, the three bare-pointwise integrability members come from
`fuPairInt`/`fuRestInt`/`fuRemInt`, and the interior half of `energyCont` comes from
`fuEnergyDeriv`. -/
theorem fuInputs_of_gram (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    (hbounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem : Real,
      ForwardUniqueSlab (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂))
        (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂)
        a c C_A C_R C_Ric C_V C_U C_rem)
    (hedge : ContinuousWithinAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) a) :
    ForwardUniqueInputs (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) (fuSvec (I := I) g₁ g₂)
      (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂) a b := by
  have hS₁ := fuIsSol (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := fuIsSol (I := I) g₂ hab hjoint₂ hpde₂
  exact
    { gamma := fuGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      rm := fuRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂
      car := fun _ _ x => fuSfield_apply (I := I) g₁ g₂ _ x
      sdec := fuSdec (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂
      bounds := hbounds
      dens := dens_jointContMDiffOn (I := I) g₁ g₂ (fuGramIoo (I := I) g₁ hjoint₁)
        (fuGramIoo (I := I) g₂ hjoint₂)
      energyCont := fuEnergyCont (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ hedge
      densInt := fun t _ => (dcont_idens (I := I) g₁ g₂ t).2
      densCont := fun t _ => (dcont_idens (I := I) g₁ g₂ t).1
      restInt := fuRestInt (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      pairInt := fuPairInt (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      lapInt := fun t _ => ilap_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t)
      divInt := fun t _ =>
        idiv_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) (fuUflux (I := I) g₁ g₂ t)
      remInt := fuRemInt (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      nabInt := fun t _ =>
        inab_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) (fuUflux (I := I) g₁ g₂ t)
      disInt := fun t _ => idis_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) }

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Forward uniqueness from black box (B)'s own fields, modulo two named residual inputs.**

This is `ricci_flow_forward_unique`'s statement with exactly the residual list of
`fuInputs_of_gram` added: the slab-uniform pointwise bounds, and continuity of the Kotschwar
energy at the single initial time.  Instantiating it is the whole content of the endpoint. -/
theorem forward_unique_of_gram (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    (h0 : g₁ a = g₂ a)
    (hbounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem : Real,
      ForwardUniqueSlab (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂))
        (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂)
        a c C_A C_R C_Ric C_V C_U C_rem)
    (hedge : ContinuousWithinAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) a) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t :=
  forward_unique_of_inputs (I := I) g₁ g₂ hab (fuAvec (I := I) g₁ g₂) (fuSvec (I := I) g₁ g₂)
    (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂)
    h1smooth h1cont h2smooth h2cont h1pde h2pde h0
    (fuInputs_of_gram (I := I) g₁ g₂ hab h1smooth h2smooth h1pde h2pde hbounds hedge)

end DifferentialGeometry.PDE.RicciFlow

end
