import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step B honest inputs (S6 / `lbl418`, and `lbl395`)

This file collects the book-external honest inputs that Step B consumes at the
model-coordinate level.

## S6 / `lbl418` — derivatives of `exp⁻¹`

The Jacobi/Rauch-comparison input for Step B: uniform `C^p` bounds for the
normal-coordinate transition maps `normalChart_y ∘ exp_x : E → E` on chart overlaps
(MSM135 §`lbl-2103`, "derivatives of `exp⁻¹`").  This is the rebuild of the former
`GeometricInputs.lean` S6 section on the NATIVE normal-coordinate API
(`Geometry.Riemannian.expMapDiffeo` / `normalChartAt`), replacing
the dangling `RicciFlower.Coordinates.NormalChartData` reference.

The field `exp_inv_deriv` is the deep external comparison-geometry theorem (the book
cites it; proving it from §5 `S1–S5` is optional later work).  Note the native
`expMapDiffeo` source is *some* open neighbourhood of `0`; widening the charts to the
full `λ`-ball scale (so the bounds apply on the Step A covering balls) is part of the
`lbl383` item-3 frontier, not of this input.

## `lbl395` — normal-coordinate metric bounds

MSM135 Chapter 4 Proposition `lbl395` (Hamilton [H6] Corollary 4.12): in normal
coordinates, `|∇^ℓ Rm| ≤ C_ℓ` forces `½δ ≤ g ≤ 2δ` and uniform bounds on all partial
derivatives of `g`.  This is taken as an honest input now (Planner Ruling Q1); the
native Jacobi/Grönwall discharge is the optional `B0NormalCoordBounds.md` route.

The pulled-back metric is realized concretely as `normalCoordMetric`, the model-space
bilinear-form map `E → (E →L[ℝ] E →L[ℝ] ℝ)`, mirroring `Diffeomorph.pullbackInner`.
The input `NormalCoordMetricBoundInput` records, constants-first, the Euclidean
equivalence and all-orders derivative bounds *only on the relevant normal-coordinate
ball*.  It deliberately does NOT claim total `Set.univ` (`IsometryDerivBounds`)
control; the partial-domain bridge is reserved for the later B-loc brick.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The model-coordinate transition map `normalChart_y ∘ exp_x : E → E` of one
pointed Riemannian manifold, built from the native normal-coordinate charts.  Outside
the meaningful domain the partial diffeomorphisms return junk values; the derivative
bounds below are therefore stated only on the chart overlap. -/
noncomputable def normalTransition
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M) : E → E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  fun z =>
    normalChartAt (I := I) X.metric y
      (expMapDiffeo (I := I) X.metric x z)

/-- Derivative bound for one normal-coordinate transition map, on the chart overlap
**below a scale cap `r₁`**: the evaluation point `z` lies in the `min r₁ (C²-radius of x)`
ball, and its image lies in the `min r₁ (C²-radius of y)` normal ball of `y`.

The scale cap is the book's own domain (MSM135 `lbl418` proves the bounds for
`x, y ∈ B(p, r₁)`, `r₁ ≤ min{inj(p)/4, c/√C₀}`).  An uncapped version quantified over
the whole chart overlap is over-strong: chart sources are not scale-controlled, and in
negatively curved members `d(exp_x)` grows exponentially with the radius, so transition
derivatives are not uniformly bounded far out. -/
def NormalTransitionDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M)
    (r₁ : Real) (p : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  forall z : E,
    ‖z‖ < min r₁ (expMapC2Radius (I := I) X.metric x) ->
    z ∈ (expMapDiffeo (I := I) X.metric x).source ->
      expMapDiffeo (I := I) X.metric x z ∈
          (fun v : E => (expMap (I := I) X.metric y
            (show TangentSpace I y from v) : X.M)) ''
            Metric.ball (0 : E) (min r₁ (expMapC2Radius (I := I) X.metric y)) ->
      expMapDiffeo (I := I) X.metric x z ∈
          (normalChartAt (I := I) X.metric y).source ->
        ‖iteratedFDeriv Real p (normalTransition (I := I) X x y) z‖ <= C

/-- MSM135 Chapter 4, section `lbl-2103` (S6 / `lbl418`): Jacobi/Rauch comparison
bounds for derivatives of the normal-coordinate transition maps `exp_y⁻¹ ∘ exp_x`,
valid below the comparison scale `r₁` (the book's `r₁ ≤ min{inj/4, c/√C₀}`).

The field `exp_inv_deriv` is the deep external theorem, consumed by Steps B/C. -/
structure ExpInverseDerivBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  /-- The comparison scale below which the transition-derivative bounds hold. -/
  r₁ : Real
  r₁_pos : 0 < r₁
  derivC : Nat -> Real
  derivC_nonneg : forall p : Nat, 0 <= derivC p
  /-- Consumed by Steps B/C: uniform `C^p` bounds for the normal-coordinate
  transition map on the overlap of two normal charts, below the scale `r₁`. -/
  exp_inv_deriv :
    forall k p : Nat, forall x y : (X.obj k).M,
      NormalTransitionDerivBound (I := I) (X.obj k) x y r₁ p (derivC p)

namespace ExpInverseDerivBoundInput

/-- Reindex the normal-transition derivative input along a subsequence. -/
def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : ExpInverseDerivBoundInput (I := I) X) (f : Nat -> Nat) :
    ExpInverseDerivBoundInput (I := I) (X.subseq f) where
  r₁ := h.r₁
  r₁_pos := h.r₁_pos
  derivC := h.derivC
  derivC_nonneg := h.derivC_nonneg
  exp_inv_deriv := by
    intro k p x y
    simpa [PointedRiemannianSeq.subseq] using h.exp_inv_deriv (f k) p x y

end ExpInverseDerivBoundInput

/-! ## `lbl395` normal-coordinate metric bounds (honest input) -/

/-- The model-coordinate **pulled-back normal-coordinate metric**
`(H_x)^* g : E → (E →L[ℝ] E →L[ℝ] ℝ)` of one pointed Riemannian manifold, where
`H_x := expMapDiffeo g x : E → M` is the exponential-side normal-coordinate
parametrization at `x`.  At `z : E` it is the continuous bilinear form
`(u, v) ↦ g_{H_x z}(d(H_x)_z u, d(H_x)_z v)`, built from the manifold derivative
`mfderiv` of `H_x` in both slots, in the slot-composition shape of
`Diffeomorph.pullbackInner`.  Outside the normal-coordinate domain the derivative is
junk; the bounds below are therefore stated only on the relevant ball. -/
noncomputable def normalCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E -> (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  fun z =>
    let D : E →L[Real] TangentSpace I (expMapDiffeo (I := I) Y.metric x z) :=
      mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)).comp D)

/-- **Comparison/smoothness of the realized parametrization** (frontier-1 producer, step 1).
On a ball where forward `expMap` is `C∞` and inside the chart source, the realized
normal-coordinate parametrization `expMapDiffeo` — only a `PartialDiffeomorph … 1` — is in
fact `ContMDiffOn ⊤`, because it agrees there with the now-`C∞` `expMap`
(`expMap_contMDiffAt_infty_of_norm_lt` + `expMapDiffeo_apply_eq` + `ContMDiffOn.congr`).
This discharges the `C¹`-vs-`C∞` mismatch the hard-stop flagged. -/
theorem expMapDiffeo_contMDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContMDiffOn 𝓘(Real, E) I ∞
        (fun w => expMapDiffeo (I := I) Y.metric x w)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hforward⟩ :=
    expMap_contMDiffAt_infty_of_norm_lt (I := I) Y.metric x
  refine ⟨δ, hδ, ?_⟩
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
    intro w hw
    have hwδ : ‖w‖ < δ := by
      have := hw.1; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    exact (hforward w hwδ).contMDiffWithinAt
  exact hexp.congr (fun w hw => expMapDiffeo_apply_eq (I := I) Y.metric x hw.2)

/-- **Scalar evaluation of `normalCoordMetric`** (frontier-1 producer, step 2): the pulled-back
metric applied to two vectors is `g` at `expMapDiffeo z` on the two pushed-forward vectors —
the model-coordinate analogue of `Diffeomorph.pullbackInner_eval`. -/
theorem normalCoordMetric_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y x z v w =
      Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [normalCoordMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

/-- **Pushforward section smoothness** (frontier-1 producer, step 3): for forward `f =
expMapDiffeo` which is `C∞` on an open `U`, the bundle section `z ↦ ⟨f z, d f_z v⟩` of `TM`
(over the base map `f`) is `ContMDiffOn`.  Obtained from
`ContMDiffOn.contMDiffOn_tangentMapWithin` (the within tangent map of `f`) composed with the
constant tangent section `z ↦ ⟨z, v⟩` of `TE` (`tangentBundleModelSpaceHomeomorph.symm`), plus
`mfderivWithin = mfderiv` on the open set `U`. -/
private theorem expMapDiffeo_pushforward_section_contMDiffOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {U : Set E}
    (hU : IsOpen U)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) U)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E)) ∞
      (fun z => TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
        (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)) U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  -- the within tangent map of `f` is `C∞` on the preimage of `U`
  have htm := hf.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn
  -- constant tangent section `z ↦ ⟨z, v⟩` of `TE`, via the model-space homeomorphism
  have hσ : ContMDiff 𝓘(Real, E) (𝓘(Real, E)).tangent ∞
      (fun z : E => (TotalSpace.mk' E z v : TangentBundle 𝓘(Real, E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => v)).mpr contDiff_const
  -- compose: `tangentMapWithin f U` after the constant section, on `U`
  have hcomp : ContMDiffOn 𝓘(Real, E) I.tangent ∞
      (fun z => tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
        (TotalSpace.mk' E z v)) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun z hz => hz)
  refine hcomp.congr ?_
  intro z hz
  have hmf : mfderivWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U z
      = mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z :=
    mfderivWithin_of_isOpen hU hz
  change TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
      (expMapDiffeo (I := I) Y.metric x z)
      (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
      = tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
          (TotalSpace.mk' E z v)
  dsimp only [tangentMapWithin]
  rw [hmf]

set_option synthInstance.maxHeartbeats 800000 in
/-- **Generic-domain B-metric smoothness** (the reusable core): on any open set `S ⊆ E`
on which the realized parametrization `expMapDiffeo` is `C∞`, the pulled-back
normal-coordinate metric `normalCoordMetric Y x` is `ContDiffOn ℝ ⊤`.  The opaque-radius and
named-radius producers below specialize `S`.  Built from the pushforward sections +
`ContMDiffOn.clm_bundle_apply₂` (the bilinear bundle apply) + the finite-dimensional
`contDiffOn_clm_apply` reduction. -/
theorem normalCoordMetric_contDiffOn_of_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {S : Set E}
    (hU : IsOpen S)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) S) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) S := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  -- scalar smoothness `z ↦ g(f z)(d f_z v, d f_z w)` for fixed `v, w`
  have hscalar : ∀ v w : E, ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w))
      S := by
    intro v w
    have hg : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun z => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : Y.M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)))
        S :=
      Y.metric.contMDiff.comp_contMDiffOn hf
    have hv := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf v
    have hw := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf w
    have htotal : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, Real)) ∞
        (fun z => TotalSpace.mk' Real (E := Bundle.Trivial Y.M Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)))
        S :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := fun b : Y.M => TangentSpace I b) (E₂ := fun b : Y.M => TangentSpace I b)
        (E₃ := fun _ : Y.M => Real)
        (b := fun z => expMapDiffeo (I := I) Y.metric x z)
        (ψ := fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z))
        (v := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (w := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)
        hg hv hw
    intro z hz
    have h_at := htotal z hz
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.2
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  rw [← contMDiffOn_iff_contDiffOn]
  exact (hscalar v w).congr (fun z _ => normalCoordMetric_apply (I := I) Y x z v w)

set_option synthInstance.maxHeartbeats 800000 in
/-- **B-metric smoothness producer** (frontier-1, S6/`lbl395`): the model-coordinate
normal-coordinate pulled-back metric `normalCoordMetric Y x` is `ContDiffOn ℝ ⊤` on a uniform
ball `ball 0 δ ∩ source` where forward `expMap` is `C∞`.  This discharges the `hsmooth`
hypothesis of `exists_metricLimit_normalCoord` for a fixed `β`.  Built from
`expMapDiffeo_contMDiffOn_ball` + the pushforward sections + `ContMDiffOn.clm_bundle_apply₂`
(the bilinear bundle apply) + the finite-dimensional `contDiffOn_clm_apply` reduction. -/
theorem normalCoordMetric_contDiffOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hf⟩ := expMapDiffeo_contMDiffOn_ball (I := I) Y x
  exact ⟨δ, hδ, normalCoordMetric_contDiffOn_of_smooth (I := I) Y x
    (Metric.isOpen_ball.inter (expMapDiffeo (I := I) Y.metric x).open_source) hf⟩

/-- **B-metric smoothness producer, pure-ball form** (the smallest domain/radius lemma for
the fixed-`U` wrapper).  Combining `normalCoordMetric_contDiffOn` (`C∞` on `ball 0 δ ∩ source`)
with a positive model ball inside the chart source (`source` is open and contains `0`), the
pulled-back normal-coordinate metric is `C∞` on a single `Metric.ball 0 r`.  This is the clean
consumable shape matching `NormalCoordMetricBoundInput.radius` (no `∩ source` wrinkle).

The per-point `r` here is still an **opaque existential** (`min` of the `expMap`-smoothness
radius `δ` and the ball-in-source radius), with no uniform positive lower bound across the
sequence; supplying that uniform lower bound is the remaining frontier recorded in
`StepBLocalMetrics.md` (it requires anchoring the `∞`-smoothness radius to a Step-A-controlled
geometric scale — a smoothness-layer input, not domain bookkeeping). -/
theorem normalCoordMetric_contDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) (Metric.ball (0 : E) r) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hsm⟩ := normalCoordMetric_contDiffOn (I := I) Y x
  obtain ⟨r₀, hr₀, hsub⟩ :=
    Metric.isOpen_iff.mp (expMapDiffeo (I := I) Y.metric x).open_source 0
      (zero_mem_expMapDiffeo_source (I := I) Y.metric x)
  refine ⟨min δ r₀, lt_min hδ hr₀, hsm.mono fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine ⟨Metric.mem_ball.mpr ?_, hsub (Metric.mem_ball.mpr ?_)⟩
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_right _ _)

/-- **Realized parametrization `C∞` on the named geometric ball.**  On
`Metric.ball 0 (expMapC2Radius Y.metric x)` the realized normal-coordinate parametrization
`expMapDiffeo` — only a `PartialDiffeomorph … 1` — is `ContMDiffOn ⊤`, because it agrees there
with the now-`C∞` forward `expMap` (`expMap_contMDiffAt_infty_of_norm_lt_radius` +
`expMapDiffeo_apply_eq` + `ContMDiffOn.congr`), the ball being inside the chart source by
the fourth component of `expMapC2Radius` (`mem_expMapDiffeo_source_of_norm_lt_radius`). -/
theorem expMapDiffeo_contMDiffOn_expBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) I ∞
      (fun w => expMapDiffeo (I := I) Y.metric x w)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) Y.metric x hw).contMDiffWithinAt
  refine hexp.congr (fun w hw => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact expMapDiffeo_apply_eq (I := I) Y.metric x
    (mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hw)

/-- **B-metric smoothness producer, named-radius pure-ball form.**  The pulled-back
normal-coordinate metric `normalCoordMetric Y x` is `ContDiffOn ℝ ⊤` on the named ball
`Metric.ball 0 (expMapC2Radius Y.metric x)` — the exposed geometric radius that Step-A
controls from below (so a single `U` works across the sequence).  This strengthens
`normalCoordMetric_contDiffOn_ball` by anchoring the opaque smoothness radius to the named
geometric scale, discharging the frontier flagged in `StepBLocalMetrics.md`. -/
theorem normalCoordMetric_contDiffOn_expBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact normalCoordMetric_contDiffOn_of_smooth (I := I) Y x Metric.isOpen_ball
    (expMapDiffeo_contMDiffOn_expBall (I := I) Y x)

/-- **`hsmooth` reduction for the fixed-`U` wrapper.**  Given a fixed open `U` contained in
every term's named smoothness ball `ball 0 (expMapC2Radius (X.obj k).metric (c k))`, the
pulled-back metrics are uniformly `ContDiffOn ℝ ⊤` on `U` — exactly the `hsmooth` hypothesis
of `exists_metricLimit_normalCoord`.  This reduces `hsmooth` to the single geometric
containment `hsub`, i.e. to a uniform lower bound on `expMapC2Radius` across the sequence (the
remaining Step-A wiring frontier). -/
theorem contDiffOn_normalCoordMetric_of_subset_expBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (c : ∀ k : ℕ, (X.obj k).M) {U : Set E}
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric (c k))) :
    ∀ k, ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) (X.obj k) (c k)) U :=
  fun k => (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj k) (c k)).mono (hsub k)

/-- Local Euclidean equivalence of the pulled-back normal-coordinate metric on `U`:
`½‖v‖² ≤ g(z)(v,v) ≤ 2‖v‖²` for every `z ∈ U` and `v` — the quadratic-form form of
the book's `½(δ_ij) ≤ (g_ij) ≤ 2(δ_ij)`. -/
def NormalCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (U : Set E) :
    Prop :=
  forall z : E, z ∈ U -> forall v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 <= normalCoordMetric (I := I) Y x z v v ∧
      normalCoordMetric (I := I) Y x z v v <= 2 * ‖v‖ ^ 2

-- `iteratedFDeriv` over the nested operator-norm space `E →L[ℝ] E →L[ℝ] ℝ` with
-- `InnerProductSpace ℝ E` in scope needs the project-standard extended (terminating)
-- instance-synthesis budget.
set_option synthInstance.maxHeartbeats 800000 in
/-- Uniform `C^p` Euclidean derivative bound for the pulled-back normal-coordinate
metric on `U`: `‖∇ᵖ g‖ ≤ C` for every `z ∈ U` (`∇` the Euclidean iterated Fréchet
derivative). -/
def NormalCoordMetricDerivBound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) : Prop :=
  forall z : E, z ∈ U ->
    ‖iteratedFDeriv Real p (normalCoordMetric (I := I) Y x) z‖ <= C

/-- MSM135 Chapter 4 Proposition `lbl395` (Hamilton [H6] Corollary 4.12), as the
book-external honest input for Step B: in normal coordinates, `|∇^ℓ Rm| ≤ C_ℓ`
forces uniform Euclidean control of the pulled-back metrics.

For each term `k` of the sequence and each chart center `x`, on the
normal-coordinate ball `Metric.ball 0 (radius k x)`:

* `metric_equiv` — the pulled-back metric is uniformly Euclidean-equivalent
  (`½δ ≤ g ≤ 2δ`);
* `metric_deriv` — every Euclidean iterated derivative of order `p` is bounded by the
  uniform constant `metricC p`.

The constants `metricC` are listed first and are uniform over `k` and `x` (the book's
`C̃_ℓ` depend only on `n`, `inj`, and the curvature bounds, all uniform across the
cover); the per-center `radius` only records *where* the bounds apply.  The control is
**local** to the normal-coordinate ball: this input does not claim total `Set.univ`
control — the partial-domain bridge to `IsometryDerivBounds` is the later B-loc
brick. -/
structure NormalCoordMetricBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  /-- The per-center normal-coordinate radius `min{c₁/√C₀, r₀}` of `lbl395` (book
  scale), recording where the bounds below hold. -/
  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x
  /-- Uniform Euclidean equivalence `½δ ≤ g ≤ 2δ` of the pulled-back normal-coordinate
  metric on the relevant ball. -/
  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))
  /-- Uniform all-orders Euclidean derivative bounds for the pulled-back metric on the
  relevant ball, with `metricC p` independent of `k` and `x`. -/
  metric_deriv :
    forall (k p : Nat) (x : (X.obj k).M),
      NormalCoordMetricDerivBound (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x)) p (metricC p)

namespace NormalCoordMetricBoundInput

/-- Reindex the normal-coordinate metric bound input along a subsequence. -/
def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) (f : Nat -> Nat) :
    NormalCoordMetricBoundInput (I := I) (X.subseq f) where
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => h.radius (f k) x
  radius_pos := by
    intro k x
    exact h.radius_pos (f k) x
  metric_equiv := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using h.metric_equiv (f k) x
  metric_deriv := by
    intro k p x
    simpa [PointedRiemannianSeq.subseq] using h.metric_deriv (f k) p x

end NormalCoordMetricBoundInput

/-! ## `C∞` normal chart inverse (B-trans transition-map smoothness)

`normalChartAt` carries only `C¹` smoothness in the library
(`NormalCoordinates.normalChartAt_contMDiffOn`), because its realizing `PartialDiffeomorph`
was built at order 1.  Now that the forward exponential is `C∞` on a uniform ball
(`expMap_contMDiffAt_infty_of_norm_lt_radius`), the chart inverse is `C∞` by the inverse
function theorem.  This cannot be a bump of `LocalDiffeomorphism.lean` (the `C∞` forward fact
is downstream of it, so importing it there is an import cycle), so the Banach IFT is re-run
here, downstream of both `OffZero` and `NormalCoordinates`, pointwise over the ball (a single
IFT at the centre is not enough: `ContDiffAt ∞` does not give `ContDiffOn ∞` on a nbhd —
`ContDiffAt.contDiffOn` needs `n = ω`).  See `StepBTransition.md`. -/

section NormalChartInftySmooth

open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- **`normalChartAt` is `C∞` at every image point of the smoothness ball.**  For
`‖v₀‖ < expMapC2Radius g p`, the normal chart `normalChartAt g p` is `ContMDiffAt … ∞` at the
image point `expMap g p v₀`.  Proved by the Banach inverse function theorem at `∞` applied to
`extChartAt (expMap g p v₀) ∘ expMap g p` (its derivative at `v₀` is invertible: `expMap` is a
local diffeomorphism on the ball and `extChartAt`'s differential at its centre is invertible),
identifying the produced local inverse with `normalChartAt g p` near the image point. -/
theorem normalChartAt_contMDiffAt_infty
    (g : SmoothRiemannianMetric I M) (p : M) {v₀ : E}
    (hv₀ : ‖v₀‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      (expMap (I := I) g p (show TangentSpace I p from v₀)) := by
  classical
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set fexp : E → M := fun v => (expMap (I := I) g p (show TangentSpace I p from v)) with hfexp
  set q : M := fexp v₀ with hq
  set χ : M → E := ⇑(extChartAt I q) with hχ
  -- forward map `C∞` at `v₀`
  have hf_cd : ContMDiffAt 𝓘(ℝ, E) I ∞ fexp v₀ :=
    expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p hv₀
  -- forward map is a `C¹` local diffeomorphism at `v₀`
  have hmem_ball : v₀ ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₀
  have hf_diffeo : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 fexp v₀ :=
    exp_isLocalDiffeomorphOn_ball (I := I) g p (le_refl _) ⟨v₀, hmem_ball⟩
  -- the two factor differentials are invertible, hence so is the composite
  have hD1_inv : (mfderiv 𝓘(ℝ, E) I fexp v₀).IsInvertible :=
    ⟨hf_diffeo.mfderivToContinuousLinearEquiv one_ne_zero,
      hf_diffeo.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
  have hD2_inv : (mfderiv I 𝓘(ℝ, E) χ q).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source q)
  -- composite `F = χ ∘ fexp` is `C∞` at `v₀`
  have hχ_cd : ContMDiffAt I 𝓘(ℝ, E) ∞ χ q := contMDiffAt_extChartAt (I := I) (x := q)
  have hF_cd : ContDiffAt ℝ ∞ (χ ∘ fexp) v₀ := (hχ_cd.comp v₀ hf_cd).contDiffAt
  have h1 : HasMFDerivAt 𝓘(ℝ, E) I fexp v₀ (mfderiv 𝓘(ℝ, E) I fexp v₀) :=
    (hf_cd.mdifferentiableAt hne).hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, E) χ q (mfderiv I 𝓘(ℝ, E) χ q) :=
    (hχ_cd.mdifferentiableAt hne).hasMFDerivAt
  have hF_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (χ ∘ fexp) v₀
      ((mfderiv I 𝓘(ℝ, E) χ q).comp (mfderiv 𝓘(ℝ, E) I fexp v₀)) := h2.comp v₀ h1
  -- view the differential as an `E →L E` Fréchet derivative; it is invertible, so it is an
  -- `E ≃L E` (this dodges the `TangentSpace 𝓘(ℝ,E) (χ q) = E` defeq friction in `↑e`)
  have hF_fderiv0 := hasMFDerivAt_iff_hasFDerivAt.mp hF_mfd
  have hfd_inv : (fderiv ℝ (χ ∘ fexp) v₀).IsInvertible := by
    rw [hF_fderiv0.fderiv]; exact hD2_inv.comp hD1_inv
  obtain ⟨e, he⟩ := hfd_inv
  have hF_fderiv : HasFDerivAt (χ ∘ fexp) (e : E →L[ℝ] E) v₀ := by
    rw [he]; exact hF_fderiv0.differentiableAt.hasFDerivAt
  -- IFT at `∞`: the local inverse of `F` is `C∞` at `F v₀ = χ q`
  have hinv := hF_cd.to_localInverse hF_fderiv hne
  -- the IFT homeomorph; its `.symm` is the local inverse
  set Φ : OpenPartialHomeomorph E E :=
    hF_cd.toOpenPartialHomeomorph (χ ∘ fexp) hF_fderiv hne with hΦ
  have hloc_eq : hF_cd.localInverse hF_fderiv hne = Φ.symm := rfl
  rw [hloc_eq] at hinv
  -- key memberships
  have hv₀_Φsrc : v₀ ∈ Φ.source :=
    hF_cd.mem_toOpenPartialHomeomorph_source hF_fderiv hne
  have hv₀_src : v₀ ∈ (expMapDiffeo (I := I) g p).source := by
    have h := ball_subset_normalChartAt_target (I := I) g p hv₀
    rwa [normalChartAt_target_eq] at h
  have hq_tgt : q ∈ (expMapDiffeo (I := I) g p).target := by
    have hev : expMapDiffeo (I := I) g p v₀ = q := by
      rw [expMapDiffeo_apply_eq (I := I) g p hv₀_src]
    rw [← hev]; exact (expMapDiffeo (I := I) g p).map_source hv₀_src
  -- `Φ.symm ∘ χ` is `C∞` at `q`
  have hsymm_cm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ.symm (χ q) :=
    (contMDiffAt_iff_contDiffAt).mpr hinv
  have hcomp : ContMDiffAt I 𝓘(ℝ, E) ∞ (Φ.symm ∘ χ) q := hsymm_cm.comp q hχ_cd
  -- they agree on the open set `target ∩ symm⁻¹(Φ.source)`, a neighbourhood of `q`
  have hΦcoe : (Φ : E → E) = χ ∘ fexp :=
    hF_cd.toOpenPartialHomeomorph_coe hF_fderiv hne
  have hncq : normalChartAt (I := I) g p q = v₀ := by
    have hv₀_nctgt : v₀ ∈ (normalChartAt (I := I) g p).target := by
      rw [normalChartAt_target_eq]; exact hv₀_src
    have hq_eq : q = (normalChartAt (I := I) g p).symm v₀ := by
      rw [normalChartAt_symm_apply (I := I) g p hv₀_nctgt]
    rw [hq_eq]; exact normalChartAt_right_inv (I := I) g p hv₀_nctgt
  have hq_src : q ∈ (normalChartAt (I := I) g p).source := by
    rw [normalChartAt_source_eq]; exact hq_tgt
  have heqEv : normalChartAt (I := I) g p =ᶠ[nhds q] (Φ.symm ∘ χ) := by
    have hUopen : IsOpen ((normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source) :=
      ((normalChartAt_contMDiffOn (I := I) g p).continuousOn).isOpen_inter_preimage
        (normalChartAt (I := I) g p).open_source Φ.open_source
    have hqU : q ∈ (normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source :=
      ⟨hq_src, by rw [Set.mem_preimage, hncq]; exact hv₀_Φsrc⟩
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hqU) (fun q' hq' => ?_)
    obtain ⟨hq'_src, hq'_pre⟩ := hq'
    rw [Set.mem_preimage] at hq'_pre
    set v' := normalChartAt (I := I) g p q' with hv'def
    have hv'_symmsrc : v' ∈ (normalChartAt (I := I) g p).symm.source :=
      (normalChartAt (I := I) g p).map_source hq'_src
    have hfv' : fexp v' = q' := by
      show (expMap (I := I) g p (show TangentSpace I p from v') : M) = q'
      rw [← normalChartAt_symm_apply (I := I) g p hv'_symmsrc]
      exact normalChartAt_left_inv (I := I) g p hq'_src
    have hΦv' : Φ v' = χ q' := by
      have hc : (χ ∘ fexp) v' = χ q' := by rw [Function.comp_apply, hfv']
      rw [hΦcoe]; exact hc
    show normalChartAt (I := I) g p q' = (Φ.symm ∘ χ) q'
    rw [Function.comp_apply, ← hΦv', Φ.left_inv hq'_pre]
  exact hcomp.congr_of_eventuallyEq heqEv

/-- **`normalChartAt` is `C∞` on the image of the smoothness ball** (`ContMDiffOn` form of
`normalChartAt_contMDiffAt_infty`): the normal chart at `p` is `C∞` on the normal-coordinate
neighbourhood `expMap g p '' (ball 0 (expMapC2Radius g p))`. -/
theorem normalChartAt_contMDiffOn_infty
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) g p)) := by
  rintro q ⟨v₀, hv₀ball, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv₀ball
  exact (normalChartAt_contMDiffAt_infty (I := I) g p hv₀ball).contMDiffWithinAt

end NormalChartInftySmooth

end HCGCompactness
end DifferentialGeometry
