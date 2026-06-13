import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.StepAInputs

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

/-- Derivative bound for one normal-coordinate transition map on the chart overlap. -/
def NormalTransitionDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M)
    (p : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  forall z : E,
    z ∈ (expMapDiffeo (I := I) X.metric x).source ->
      expMapDiffeo (I := I) X.metric x z ∈
          (normalChartAt (I := I) X.metric y).source ->
        ‖iteratedFDeriv Real p (normalTransition (I := I) X x y) z‖ <= C

/-- MSM135 Chapter 4, section `lbl-2103` (S6 / `lbl418`): Jacobi/Rauch comparison
bounds for derivatives of the normal-coordinate transition maps `exp_y⁻¹ ∘ exp_x`.

The field `exp_inv_deriv` is the deep external theorem, consumed by Steps B/C. -/
structure ExpInverseDerivBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  derivC : Nat -> Real
  derivC_nonneg : forall p : Nat, 0 <= derivC p
  /-- Consumed by Steps B/C: uniform `C^p` bounds for the normal-coordinate
  transition map on the overlap of two normal charts. -/
  exp_inv_deriv :
    forall k p : Nat, forall x y : (X.obj k).M,
      NormalTransitionDerivBound (I := I) (X.obj k) x y p (derivC p)

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
  refine ⟨δ, hδ, ?_⟩
  have hU : IsOpen (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) :=
    Metric.isOpen_ball.inter (expMapDiffeo (I := I) Y.metric x).open_source
  -- scalar smoothness `z ↦ g(f z)(d f_z v, d f_z w)` for fixed `v, w`
  have hscalar : ∀ v w : E, ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w))
      (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
    intro v w
    have hg : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun z => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : Y.M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)))
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) :=
      Y.metric.contMDiff.comp_contMDiffOn hf
    have hv := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf v
    have hw := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf w
    have htotal : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, Real)) ∞
        (fun z => TotalSpace.mk' Real (E := Bundle.Trivial Y.M Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)))
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) :=
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
  -- reduce the `E →L E →L ℝ`-valued map to scalar entries, then convert model↔model
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  rw [← contMDiffOn_iff_contDiffOn]
  exact (hscalar v w).congr (fun z _ => normalCoordMetric_apply (I := I) Y x z v w)

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

end HCGCompactness
end DifferentialGeometry
