import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Analysis.ODE.FlowC1Continuous
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option linter.unusedSectionVars false

/-!
# Joint `C^1` regularity of the chart-coordinate geodesic flow

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete finite-dimensional inner-product space `E`, the
chart-coordinate phase-space form of the geodesic equation reads
$$\dot x = v, \qquad \dot v = -\Gamma_\alpha(v, v)(x),$$
on `E × E`, where `x ∈ E` is the chart image of the foot point under
`extChartAt I α` and `v ∈ E` is the velocity in the chart-`α` frame.
This is autonomous and `C^∞` on `interior (extChartAt I α).target ×ˢ univ`.

By smoothly cutting off the right-hand side outside a small ball centred
at any base phase-space point `z₀ = (extChartAt I α p, v₀)`, we obtain a
globally `C^∞` vector field on `E × E` that agrees with the chart-fixed
geodesic field on a neighbourhood of `z₀`. The Banach-space flow theorem
then produces a local flow of the cutoff field; the generic joint-`C^1`
upgrade gives `C^1` smoothness of the flow on an open neighbourhood of
`(z₀, 0)`.

## Main definitions

* `chartPhaseVF g α : E × E → E × E` — the chart-coordinate phase-space
  vector field `(x, v) ↦ (v, -Γ_α(v, v)(x))`.

* `chartPhaseVFCutoff g α z₀ b : E × E → E × E` — the globally `C^∞`
  cutoff version, multiplying `chartPhaseVF g α` pointwise by a
  `ContDiffBump` centred at `z₀`.

* `chartPhaseVFTime g α z₀ b : ℝ → (E × E) → E × E` — the trivial
  time-padding, used to feed the generic Banach-space flow theorem.

## Main theorems

* `chartPhaseVF_contDiffOn` — `C^∞` regularity of `chartPhaseVF g α` on
  `interior (extChartAt I α).target ×ˢ univ`.

* `chartPhaseVFCutoff_contDiff` — global `C^∞` regularity of the cutoff
  vector field on `E × E`, provided the bump's outer support sits inside
  the chart-target interior product.

* `chartPhaseVFCutoff_eq_of_mem_closedBall` — the cutoff agrees with the
  original vector field on the inner closed ball of the bump.

* `exists_chartPhase_isLocalFlow` — existence of a Picard–Lindelöf local
  flow of the cutoff field around any base point with chart-target
  interior first coordinate.

* `exists_chartPhase_contDiffOn_isLocalFlow` — the headline: there exist
  a `ContDiffBump`, a local flow `Φ` of the cutoff field, and strictly
  smaller open neighbourhoods of `(z₀, 0)` on which `Φ` is jointly
  `C^1` (via the generic flow theorem of
  `DifferentialGeometry.Analysis.ODE.FlowC1Continuous`).

## What this file does *not* do

* It does not lift the chart-coordinate flow back to a `TM`-valued
  geodesic flow. That requires composing with the trivialisation of
  `T(TM)` at `⟨α, 0⟩` and identifying the result with the existing
  maximal-geodesic curve from `MaximalInterval.lean`. The identification
  uses Mathlib-style ODE uniqueness arguments and is left to a follow-up
  step.

* It does not define the exponential map. With the chart-coordinate flow
  available, the exponential map can be built as `Φ(z, 1)` after the
  lift back to `TM`, again as a follow-up step.

The local flow is `C^1`, hence the present file delivers the
*unconditional `C^1`* regularity of the chart-coordinate geodesic flow.
`C^k` regularity for `k ≥ 2` would follow from the (conditional) higher
inductive scaffolding in `Analysis/ODE/FlowCk.lean`; this is deferred.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Chart-coordinate phase-space vector field

The chart-coordinate phase-space geodesic vector field on `E × E`. The
first component is the velocity `v` (linear in the state, smooth), and
the second component is the negation of the Christoffel contraction of
`v` with itself at the chart image `x`. Smoothness in `(x, v)` on
`interior (extChartAt I α).target ×ˢ univ` follows from
`chartChristoffel_contDiffOn_interior`.

This is the autonomous Banach-space form of the chart-fixed geodesic
vector field. Compared to `geodesicVectorFieldChart g α`, the present
form lives directly on `E × E` and is the natural input to the generic
flow theorems of `DifferentialGeometry.Analysis.ODE.FlowC1Continuous`. -/

/-- The chart-coordinate phase-space geodesic vector field on `E × E`. -/
def chartPhaseVF (g : SmoothRiemannianMetric I M) (α : M) : E × E → E × E :=
  fun z => (z.2, - chartChristoffelContraction (I := I) g α z.2 z.2 z.1)

@[simp] lemma chartPhaseVF_apply (g : SmoothRiemannianMetric I M) (α : M)
    (z : E × E) :
    chartPhaseVF (I := I) g α z =
      (z.2, - chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl

@[simp] lemma chartPhaseVF_mk (g : SmoothRiemannianMetric I M) (α : M)
    (x v : E) :
    chartPhaseVF (I := I) g α (x, v) =
      (v, - chartChristoffelContraction (I := I) g α v v x) := rfl

/-! ### Smoothness of the chart-coordinate phase-space vector field

We work under `[I.Boundaryless]`, which gives
`extChartAt_target_subset_interior_of_boundaryless` and hence smoothness
of `chartChristoffel` on the chart-target interior. -/

variable [I.Boundaryless]

/-- The scalar coefficient
`(x, v) ↦ ∑_{ij} Γ^k_{ij}(x) · chartCoord i v · chartCoord j v`
is `C^∞` on `interior (extChartAt I α).target ×ˢ univ`. -/
lemma chartChristoffelContraction_scalarCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i z.2 *
            chartCoord (E := E) j z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  classical
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun j _ => ?_)
  have hΓ : ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffel (I := I) g α i j k z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
    have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j k
    have hfst : ContDiff ℝ ∞ (Prod.fst : E × E → E) := contDiff_fst
    have hmapsto : MapsTo (Prod.fst : E × E → E)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
        (interior (extChartAt I α).target) :=
      fun _ hp => hp.1
    exact hbase.comp hfst.contDiffOn hmapsto
  have hCLM_i : ContDiff ℝ ∞ (((chartModelBasis E).coord i).toContinuousLinearMap) :=
    ((chartModelBasis E).coord i).toContinuousLinearMap.contDiff
  have hCLM_j : ContDiff ℝ ∞ (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    ((chartModelBasis E).coord j).toContinuousLinearMap.contDiff
  have hsnd : ContDiff ℝ ∞ (Prod.snd : E × E → E) := contDiff_snd
  have hci : ContDiffOn ℝ ∞
      (fun z : E × E => chartCoord (E := E) i z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (hCLM_i.comp hsnd).contDiffOn
  have hcj : ContDiffOn ℝ ∞
      (fun z : E × E => chartCoord (E := E) j z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (hCLM_j.comp hsnd).contDiffOn
  exact (hΓ.mul hci).mul hcj

/-- The chart-coordinate Christoffel contraction `Γ_α(v, v)(x)`, viewed
as a function on `E × E`, is `C^∞` on `interior (extChartAt I α).target ×ˢ univ`. -/
lemma chartChristoffelContraction_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum (fun k _ => ?_)
  have hscalar :=
    chartChristoffelContraction_scalarCoeff_contDiffOn (I := I) g α k
  have hconst : ContDiffOn ℝ ∞
      (fun _ : E × E => (chartModelBasis E) k)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    contDiffOn_const
  exact hscalar.smul hconst

/-- **Smoothness of the chart-coordinate phase-space geodesic vector field.**
The right-hand side of the chart-coordinate geodesic ODE is `C^∞` on
`interior (extChartAt I α).target ×ˢ univ`. -/
theorem chartPhaseVF_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  have hfst : ContDiffOn ℝ ∞ (fun z : E × E => z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    contDiff_snd.contDiffOn
  have hΓ : ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    chartChristoffelContraction_contDiffOn (I := I) g α
  exact hfst.prodMk hΓ.neg

/-! ## Cutoff to make the vector field globally smooth

`exists_isLocalFlow_of_contDiffOn_univ` requires the field to be `C^1` on
all of `ℝ × (E × E)`. We multiply `chartPhaseVF g α` by a `ContDiffBump`
centred at a chosen base point `z₀` whose outer ball sits inside
`interior _.target ×ˢ univ`. The result is globally `C^∞` on `E × E`,
equals `chartPhaseVF g α` on the inner closed ball, and is identically
zero outside the outer closed ball. -/

/-- The cutoff phase-space vector field: `chartPhaseVF g α` multiplied
pointwise by the smooth bump `b`. -/
def chartPhaseVFCutoff (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) : E × E → E × E :=
  fun z => b z • chartPhaseVF (I := I) g α z

@[simp] lemma chartPhaseVFCutoff_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) (z : E × E) :
    chartPhaseVFCutoff (I := I) g α z₀ b z =
      b z • chartPhaseVF (I := I) g α z := rfl

/-- On the inner closed ball, the cutoff equals the original vector field. -/
lemma chartPhaseVFCutoff_eq_of_mem_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) {z : E × E}
    (hz : z ∈ Metric.closedBall z₀ b.rIn) :
    chartPhaseVFCutoff (I := I) g α z₀ b z = chartPhaseVF (I := I) g α z := by
  have hb1 : b z = 1 := b.one_of_mem_closedBall hz
  simp [chartPhaseVFCutoff_apply, hb1]

/-- **Global smoothness of the cutoff vector field.** If the bump's outer
closed ball is contained in `interior (extChartAt I α).target ×ˢ univ`,
the cutoff vector field is `C^∞` on all of `E × E`. -/
theorem chartPhaseVFCutoff_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Metric.closedBall z₀ b.rOut
  · -- Inside the closed ball: product of a smooth bump and a smooth field.
    have hz_open : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
      hb_sub hz
    have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ
        (Set.univ : Set E)) :=
      isOpen_interior.prod isOpen_univ
    have hVF_at : ContDiffAt ℝ ∞ (chartPhaseVF (I := I) g α) z :=
      (chartPhaseVF_contDiffOn (I := I) g α).contDiffAt
        (hopen.mem_nhds hz_open)
    have hb_at : ContDiffAt ℝ ∞ (fun z => (b : E × E → ℝ) z) z :=
      b.contDiff.contDiffAt
    exact hb_at.smul hVF_at
  · -- Outside the closed ball: `b = 0` on a neighbourhood.
    rw [Metric.mem_closedBall] at hz
    have hdist : b.rOut < dist z z₀ := not_le.mp hz
    have hopen : IsOpen {w : E × E | b.rOut < dist w z₀} := by
      have hcont : Continuous (fun w : E × E => dist w z₀) :=
        continuous_id.dist continuous_const
      exact hcont.isOpen_preimage _ isOpen_Ioi
    have hmem : z ∈ {w : E × E | b.rOut < dist w z₀} := hdist
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : E × E => (0 : E × E))
      contDiffAt_const ?_
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    intro w hw
    have hw' : b.rOut < dist w z₀ := hw
    have hb0 : (b : E × E → ℝ) w = 0 :=
      b.zero_of_le_dist (le_of_lt hw')
    simp [chartPhaseVFCutoff_apply, hb0]

/-! ## Time-padded reframing for the Banach-space flow theorem

The chart-coordinate phase-space ODE is autonomous, but the generic flow
theorem in `DifferentialGeometry.Analysis.ODE.FlowC1` is stated for
time-dependent vector fields. We pad with a trivial time argument. -/

/-- The time-padded cutoff vector field. -/
def chartPhaseVFTime (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) : ℝ → (E × E) → E × E :=
  fun _ z => chartPhaseVFCutoff (I := I) g α z₀ b z

@[simp] lemma chartPhaseVFTime_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) (t : ℝ) (z : E × E) :
    chartPhaseVFTime (I := I) g α z₀ b t z =
      chartPhaseVFCutoff (I := I) g α z₀ b z := rfl

lemma uncurry_chartPhaseVFTime_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) :
    Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b) =
      fun p : ℝ × (E × E) => chartPhaseVFCutoff (I := I) g α z₀ b p.2 := by
  funext p; rfl

/-- The uncurried time-padded cutoff vector field is `C^∞` on `ℝ × (E × E)`. -/
lemma chartPhaseVFTime_uncurry_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiff ℝ ∞ (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) := by
  rw [uncurry_chartPhaseVFTime_eq]
  have hVF : ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) :=
    chartPhaseVFCutoff_contDiff (I := I) g α z₀ b hb_sub
  exact hVF.comp contDiff_snd

/-- The uncurried time-padded cutoff vector field is `C^1` on
`Set.univ : Set (ℝ × (E × E))`, the regularity required by the generic
local-flow theorem. -/
lemma chartPhaseVFTime_uncurry_contDiffOn_univ_one
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiffOn ℝ 1 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b))
      (Set.univ : Set (ℝ × (E × E))) := by
  have h := chartPhaseVFTime_uncurry_contDiff (I := I) g α z₀ b hb_sub
  have h1 : ContDiff ℝ 1 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) :=
    h.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact h1.contDiffOn

/-! ## Existence of a base-point bump -/

/-- Given a base phase-space point `(x₀, v₀)` with `x₀ ∈ interior _.target`,
there exists a `ContDiffBump` at `(x₀, v₀)` whose outer closed ball is
contained in `interior (extChartAt I α).target ×ˢ univ`. -/
lemma exists_contDiffBump_subset_chart_interior
    (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ b : ContDiffBump ((x₀, v₀) : E × E),
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp
    (isOpen_interior.mem_nhds hx₀)
  refine ⟨{ rIn := ε / 4, rOut := ε / 2,
            rIn_pos := by positivity,
            rIn_lt_rOut := by linarith }, ?_⟩
  intro p hp
  refine ⟨?_, Set.mem_univ _⟩
  rw [Metric.mem_closedBall, Prod.dist_eq] at hp
  have hfst : dist p.1 x₀ ≤ ε / 2 := le_trans (le_max_left _ _) hp
  have hfst_lt : dist p.1 x₀ < ε := lt_of_le_of_lt hfst (by linarith)
  exact hε_sub (Metric.mem_ball.mpr hfst_lt)

/-! ## Banach-space local flow of the cutoff vector field -/

/-- **Existence of a local flow of the cutoff field.** For any base
phase-space point `(x₀, v₀)` with `x₀` in the chart-target interior, there
exists a `ContDiffBump` cutoff `b` and a Picard–Lindelöf local flow `Φ`
of the time-padded cutoff vector field around `((x₀, v₀), 0)`. -/
theorem exists_chartPhase_isLocalFlow
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ := by
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨r, ε, hr, hε, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  refine ⟨b, r, ε, Φ, hr, hε, hb_sub, ?_⟩
  have heq1 : (0 : ℝ) - ε = -ε := by ring
  have heq2 : (0 : ℝ) + ε = ε := by ring
  rw [heq1, heq2] at hΦ
  exact hΦ

/-! ## Joint `C^1` regularity of the local flow

We apply `contDiffOn_flow_of_isLocalFlow` to the cutoff field. The key
input is a uniform bound `M` on the operator norm of the partial Fréchet
derivative along an orbit; we obtain it by compactness from the global
continuity of `fderiv (chartPhaseVFTime ... t)` on `E × E`.

Because the cutoff field has compact support contained in
`closedBall z₀ b.rOut`, its Fréchet derivative also has compact support
in that ball, and is *bounded uniformly on `E × E`*. This gives a global
upper bound `M` that can serve as the input to the joint-`C^1` theorem
without needing to track orbit positions. -/

/-- The fderiv of the cutoff vector field is bounded uniformly on `E × E`:
since the cutoff has compact support, so does its derivative. This is a
key technical fact for applying the joint-`C^1` upgrade. -/
lemma exists_bound_fderiv_chartPhaseVFCutoff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : E × E,
      ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z‖ ≤ M := by
  classical
  -- Outside `closedBall z₀ b.rOut`, the cutoff is identically zero on an open
  -- neighbourhood, hence its derivative is zero.
  -- Inside `closedBall z₀ b.rOut + 1` (compact), the derivative is continuous,
  -- hence bounded on the compact set.
  have hVF_cd : ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) :=
    chartPhaseVFCutoff_contDiff (I := I) g α z₀ b hb_sub
  have hfderiv_cont : Continuous
      (fun z => fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z) := by
    -- `ContDiff ℝ ∞ f → Continuous (fderiv ℝ f)` since ∞ ≠ 0.
    exact hVF_cd.continuous_fderiv (by
      intro h
      exact absurd h (by decide))
  -- Define `R := b.rOut + 1` (strictly larger than the support's outer radius).
  set R : ℝ := b.rOut + 1 with hR_def
  have hR_pos : 0 < R := by have := b.rOut_pos; linarith
  have hcompact : IsCompact (Metric.closedBall z₀ R) := isCompact_closedBall _ _
  have hnonempty : (Metric.closedBall z₀ R).Nonempty := ⟨z₀, Metric.mem_closedBall_self hR_pos.le⟩
  have hfd_cont_on : ContinuousOn
      (fun z => ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z‖)
      (Metric.closedBall z₀ R) :=
    (continuous_norm.comp hfderiv_cont).continuousOn
  rcases hcompact.exists_isMaxOn hnonempty hfd_cont_on with ⟨zmax, _, hzmax_max⟩
  set Mglob : ℝ := ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) zmax‖ with hMglob_def
  have hMglob_nn : 0 ≤ Mglob := norm_nonneg _
  refine ⟨Mglob, hMglob_nn, ?_⟩
  intro z
  by_cases hz_in : z ∈ Metric.closedBall z₀ R
  · exact hzmax_max hz_in
  · -- Outside `closedBall z₀ R`, in particular `dist z z₀ > R > b.rOut`, so the cutoff
    -- vanishes on a neighbourhood, hence its derivative is zero.
    rw [Metric.mem_closedBall] at hz_in
    have hR_lt : R < dist z z₀ := not_le.mp hz_in
    have hdist_gt : b.rOut < dist z z₀ := by linarith
    -- Build an open set on which `chartPhaseVFCutoff = 0`.
    have hopen : IsOpen {w : E × E | b.rOut < dist w z₀} := by
      have hcont : Continuous (fun w : E × E => dist w z₀) :=
        continuous_id.dist continuous_const
      exact hcont.isOpen_preimage _ isOpen_Ioi
    have hmem : z ∈ {w : E × E | b.rOut < dist w z₀} := hdist_gt
    have hev : chartPhaseVFCutoff (I := I) g α z₀ b =ᶠ[𝓝 z] (fun _ => (0 : E × E)) := by
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro w hw
      have hw' : b.rOut < dist w z₀ := hw
      have hb0 : (b : E × E → ℝ) w = 0 := b.zero_of_le_dist (le_of_lt hw')
      simp [chartPhaseVFCutoff_apply, hb0]
    have hfd_eq : fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z =
        fderiv ℝ (fun _ : E × E => (0 : E × E)) z :=
      Filter.EventuallyEq.fderiv_eq hev
    have hfd_zero : fderiv ℝ (fun _ : E × E => (0 : E × E)) z = 0 := by
      change fderiv ℝ (0 : E × E → E × E) z = 0
      rw [fderiv_zero]; rfl
    rw [hfd_eq, hfd_zero]
    rw [norm_zero]
    exact hMglob_nn

/-- **Joint `C^1` regularity of the cutoff-flow.**

For every base phase-space point `(x₀, v₀)` with `x₀ ∈ interior (extChartAt I α).target`,
there exist a `ContDiffBump` `b`, a phase-space radius `0 < ρ`, a time
radius `0 < T`, and a map `Φ : (E × E) × ℝ → E × E` such that:

* `Φ` is jointly `C^1` on `ball (x₀, v₀) ρ ×ˢ Ioo (-T) T`;
* `Φ((x₀, v₀), 0) = (x₀, v₀)`;
* the underlying flow is a Picard–Lindelöf local flow of the cutoff
  vector field `chartPhaseVFCutoff g α (x₀, v₀) b`.

On the inner closed ball of `b`, the cutoff agrees with the genuine
chart-coordinate phase-space geodesic vector field
`chartPhaseVF g α`, so the flow there solves the chart-coordinate
geodesic ODE. -/
theorem exists_chartPhase_contDiffOn_isLocalFlow
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  -- Step 1: build the bump and the local flow.
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  -- Step 2: extract a global bound M on the partial Fréchet derivative.
  obtain ⟨Mglob, hMglob_nn, hMglob_bound⟩ :=
    exists_bound_fderiv_chartPhaseVFCutoff (I := I) g α (x₀, v₀) b hb_sub
  -- For any t, fderiv of `chartPhaseVFTime ... t` equals fderiv of the cutoff.
  have hfderiv_eq : ∀ (τ : ℝ) (z : E × E),
      fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) z =
        fderiv ℝ (chartPhaseVFCutoff (I := I) g α (x₀, v₀) b) z := by
    intro τ z
    rfl
  -- Step 3: choose strictly nested parameters.
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1))) with hTcap_def
  have hTcap_pos : 0 < Tcap := by
    apply lt_min hεN
    apply div_pos one_pos
    positivity
  set T_out : ℝ := Tcap / 2 with hT_out_def
  set T_mid : ℝ := Tcap / 4 with hT_mid_def
  set T : ℝ := Tcap / 8 with hT_def
  have hT_pos : 0 < T := by positivity
  have hT_lt_mid : T < T_mid := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    have hpos : 0 < εN := hεN
    have hcap_le : Tcap ≤ εN := min_le_left _ _
    change Tcap / 2 ≤ εN; linarith
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have hpos_den : (0 : ℝ) < 2 * (Mglob + 1) := by positivity
      have hstep : Tcap / 4 ≤ (1 / (2 * (Mglob + 1))) / 4 := by linarith
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith [heq ▸ hstep]
    have hMplus_pos : (0 : ℝ) < Mglob + 1 := by linarith
    have hMplus8_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    have hbound_aux : Mglob / (8 * (Mglob + 1)) ≤ 1 / 8 := by
      have hnum : Mglob * 8 ≤ 1 * (8 * (Mglob + 1)) := by nlinarith [hMglob_nn]
      have := (div_le_div_iff_of_pos_left (a := (1 : ℝ)) (by norm_num)
        hMplus8_pos (by norm_num : (0 : ℝ) < 8))
      -- Fallback: just nlinarith on the goal directly.
      rw [div_le_iff₀ hMplus8_pos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hMglob_nn]
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) := by
            apply mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := hbound_aux
      _ < 1 := by norm_num
  have hsub_T_out : Set.Icc ((0 : ℝ) - T_out) (0 + T_out) ⊆
      Set.Icc ((0 : ℝ) - εN) (0 + εN) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · linarith [ht.1, hT_out_le_eps]
    · linarith [ht.2, hT_out_le_eps]
  -- Phase-space parameters: ρ_out = rN/2, ρ_mid = rN/4, ρ = rN/8, r' = rN/8.
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩ with hρ_out_def
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩ with hρ_mid_def
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hr'_def
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  -- A-bound: holds globally on E × E by `hMglob_bound`.
  have hA_bd : ∀ x ∈ Metric.closedBall ((x₀, v₀) : E × E) (ρ_out : ℝ),
      ∀ τ ∈ Set.Icc (0 - T_out) (0 + T_out),
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) (Φ ⟨x, τ⟩)‖
        ≤ Mglob := by
    intro x _ τ _
    rw [hfderiv_eq]
    exact hMglob_bound _
  -- Apply `contDiffOn_flow_of_isLocalFlow`.
  have hCDOn :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_flow_of_isLocalFlow
      hΦ hC1 hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Now rewrite the parameters: ball z₀ ρ × Ioo (0-T) (0+T) = ball z₀ ρ × Ioo (-T) T.
  have hball_eq : (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (0 - T) (0 + T) =
      (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (-T) T := by
    congr 1
    ext t
    simp only [Set.mem_Ioo, zero_sub, zero_add]
  rw [hball_eq] at hCDOn
  -- Initial condition Φ((x₀, v₀), 0) = (x₀, v₀): from `apply_initial`.
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  refine ⟨b, (ρ : ℝ), T, Φ, hρ_pos, hT_pos, hb_sub, hCDOn, hinitial⟩

/-! ## Sibling: combined joint `C^1` and `IsLocalFlow` packaging

The proof of `exists_chartPhase_contDiffOn_isLocalFlow` constructs `Φ`
via `exists_isLocalFlow_of_contDiffOn_univ`, so the same `Φ` is both a
Picard–Lindelöf local flow on a larger radius `(rN, εN)` and jointly
`C^1` on a strict open neighbourhood `ball ρ × Ioo (-T) T` of
`((x₀, v₀), 0)`. We expose both predicates on the same `Φ`. -/

/-- **Combined joint-`C^1` and `IsLocalFlow` packaging.** For every base
phase-space point `(x₀, v₀)` with `x₀` in the chart-target interior,
there exist a `ContDiffBump` `b`, Picard–Lindelöf radii `(r, ε)`, a
joint-`C^1` radius `(ρ, T)`, and a map `Φ : (E × E) × ℝ → E × E` that is
both an `IsLocalFlow` of the time-padded cutoff field
`chartPhaseVFTime g α (x₀, v₀) b` (on the larger Picard radius) and
jointly `C^1` on `ball ((x₀, v₀)) ρ × Ioo (-T) T`. -/
theorem exists_chartPhase_contDiffOn_isLocalFlow_combined
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  -- Mirror the proof of `exists_chartPhase_contDiffOn_isLocalFlow` but
  -- expose the IsLocalFlow predicate as well.
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  obtain ⟨Mglob, hMglob_nn, hMglob_bound⟩ :=
    exists_bound_fderiv_chartPhaseVFCutoff (I := I) g α (x₀, v₀) b hb_sub
  have hfderiv_eq : ∀ (τ : ℝ) (z : E × E),
      fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) z =
        fderiv ℝ (chartPhaseVFCutoff (I := I) g α (x₀, v₀) b) z := by
    intro τ z; rfl
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1))) with hTcap_def
  have hTcap_pos : 0 < Tcap := by
    apply lt_min hεN
    apply div_pos one_pos
    positivity
  set T_out : ℝ := Tcap / 2 with hT_out_def
  set T_mid : ℝ := Tcap / 4 with hT_mid_def
  set T : ℝ := Tcap / 8 with hT_def
  have hT_pos : 0 < T := by positivity
  have hT_lt_mid : T < T_mid := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    have hpos : 0 < εN := hεN
    have hcap_le : Tcap ≤ εN := min_le_left _ _
    change Tcap / 2 ≤ εN; linarith
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have hpos_den : (0 : ℝ) < 2 * (Mglob + 1) := by positivity
      have hstep : Tcap / 4 ≤ (1 / (2 * (Mglob + 1))) / 4 := by linarith
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith [heq ▸ hstep]
    have hMplus_pos : (0 : ℝ) < Mglob + 1 := by linarith
    have hMplus8_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    have hbound_aux : Mglob / (8 * (Mglob + 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ hMplus8_pos, div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hMglob_nn]
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) := by
            apply mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := hbound_aux
      _ < 1 := by norm_num
  have hsub_T_out : Set.Icc ((0 : ℝ) - T_out) (0 + T_out) ⊆
      Set.Icc ((0 : ℝ) - εN) (0 + εN) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · linarith [ht.1, hT_out_le_eps]
    · linarith [ht.2, hT_out_le_eps]
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩ with hρ_out_def
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩ with hρ_mid_def
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hr'_def
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hA_bd : ∀ x ∈ Metric.closedBall ((x₀, v₀) : E × E) (ρ_out : ℝ),
      ∀ τ ∈ Set.Icc (0 - T_out) (0 + T_out),
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) (Φ ⟨x, τ⟩)‖
        ≤ Mglob := by
    intro x _ τ _
    rw [hfderiv_eq]
    exact hMglob_bound _
  have hCDOn :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_flow_of_isLocalFlow
      hΦ hC1 hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hball_eq : (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (0 - T) (0 + T) =
      (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (-T) T := by
    congr 1
    ext t
    simp only [Set.mem_Ioo, zero_sub, zero_add]
  rw [hball_eq] at hCDOn
  -- IsLocalFlow's `tmin = 0 - εN = -εN` after rewriting; match the
  -- `(-ε) ε` form by rewriting the IsLocalFlow time parameters.
  have heq1 : (0 : ℝ) - εN = -εN := by ring
  have heq2 : (0 : ℝ) + εN = εN := by ring
  have hΦ' : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) rN (-εN) εN Φ := by
    have := hΦ
    rw [heq1, heq2] at this
    exact this
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ'.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  exact ⟨b, rN, εN, (ρ : ℝ), T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hΦ', hCDOn, hinitial⟩

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
