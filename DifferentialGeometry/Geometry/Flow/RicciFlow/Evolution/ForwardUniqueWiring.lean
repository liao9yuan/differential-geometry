import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSdec
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueDensReg
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04ProducerTail

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
  `disInt`, inside `fuInputs_of_gram`, from `ForwardUniqueDensReg.lean`.

## What is NOT discharged here

`bounds` (the six slab-uniform pointwise estimates), `energyCont`, and the three integrability
members `pairInt`, `restInt`, `remInt` that pair a bare pointwise family.  They are named,
with their frontier, in `fuInputs_of_gram`'s hypothesis list and in `ForwardUniqueWiring.md`.
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

/-! ## The residual bundle, assembled

`fuInputs_of_gram` builds `ForwardUniqueInputs` at the constructed carriers from black box
(B)'s own fields plus **five** named residual hypotheses in three families.  Everything else —
the three evolution members, the realization member, and the seven density-regularity members
— is discharged here. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The standing bundle of the (B) endgame, at the constructed carriers.**

From (B)'s own fields (`hjointᵢ`, `hpdeᵢ`) together with four residual inputs:

* `hbounds` — K4's six slab-uniform pointwise estimates, per compact subslab;
* `henergy` — continuity of the Kotschwar energy up to the closed initial edge;
* `hpair`, `hrest`, `hrem` — the three integrability slots whose integrand pairs a bare
  pointwise speed family.

Nothing else remains: `gamma`/`rm`/`sdec` come from the tail Uhlenbeck and Christoffel
producers, `car` is by construction, and the density-regularity members come from
`ForwardUniqueDensReg.lean`. -/
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
    (henergy : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b))
    (hpair : ∀ t ∈ Ioo a b, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4
        (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hrest : ∀ t ∈ Ioo a b, Integrable
      (fun x => rateRest (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)) t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hrem : ∀ t ∈ Ioo a b, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x)
        (fuSfield (I := I) g₁ g₂ t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    ForwardUniqueInputs (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂) (fuSvec (I := I) g₁ g₂)
      (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂) a b := by
  have hS₁ := fuIsSol (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := fuIsSol (I := I) g₂ hab hjoint₂ hpde₂
  have hgramIoo₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
    (hjoint₁ x₀ i j).mono (Set.prod_mono_left Ioo_subset_Ico_self)
  have hgramIoo₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
    (hjoint₂ x₀ i j).mono (Set.prod_mono_left Ioo_subset_Ico_self)
  exact
    { gamma := fuGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂
      rm := fuRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂
      car := fun _ _ x => fuSfield_apply (I := I) g₁ g₂ _ x
      sdec := fuSdec (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂
      bounds := hbounds
      dens := dens_jointContMDiffOn (I := I) g₁ g₂ hgramIoo₁ hgramIoo₂
      energyCont := henergy
      densInt := fun t _ => (dcont_idens (I := I) g₁ g₂ t).2
      densCont := fun t _ => (dcont_idens (I := I) g₁ g₂ t).1
      restInt := hrest
      pairInt := hpair
      lapInt := fun t _ => ilap_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t)
      divInt := fun t _ =>
        idiv_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) (fuUflux (I := I) g₁ g₂ t)
      remInt := hrem
      nabInt := fun t _ =>
        inab_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) (fuUflux (I := I) g₁ g₂ t)
      disInt := fun t _ => idis_integrable (I := I) g₁ t (fuSfield (I := I) g₁ g₂ t) }

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Forward uniqueness from black box (B)'s own fields, modulo six named residual inputs.**

This is `ricci_flow_forward_unique`'s statement with exactly the residual list of
`fuInputs_of_gram` added; instantiating it is the whole content of the endpoint. -/
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
    (henergy : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b))
    (hpair : ∀ t ∈ Ioo a b, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4
        (rmSpeed (I := I) g₁ g₂ (fuSvec (I := I) g₁ g₂) t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hrest : ∀ t ∈ Ioo a b, Integrable
      (fun x => rateRest (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ (fuAvec (I := I) g₁ g₂)) t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hrem : ∀ t ∈ Ioo a b, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (fuRem (I := I) g₁ g₂ t x)
        (fuSfield (I := I) g₁ g₂ t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t :=
  forward_unique_of_inputs (I := I) g₁ g₂ hab (fuAvec (I := I) g₁ g₂) (fuSvec (I := I) g₁ g₂)
    (fuSfield (I := I) g₁ g₂) (fuUflux (I := I) g₁ g₂) (fuRem (I := I) g₁ g₂)
    h1smooth h1cont h2smooth h2cont h1pde h2pde h0
    (fuInputs_of_gram (I := I) g₁ g₂ hab h1smooth h2smooth h1pde h2pde
      hbounds henergy hpair hrest hrem)

end DifferentialGeometry.PDE.RicciFlow

end
