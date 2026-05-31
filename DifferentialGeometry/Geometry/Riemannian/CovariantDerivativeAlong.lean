import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartTransition

set_option linter.unusedSectionVars false

/-!
# The intrinsic covariant derivative along a curve

For a smooth Riemannian metric `g` on a smooth manifold `M`, a curve
`γ : ℝ → M`, and a section `V` along `γ` (a dependent function
`V : ∀ t, TangentSpace I (γ t)`), this file defines the **intrinsic**
covariant derivative `(∇_t V)(t) ∈ T_{γ(t)} M`.

The construction pins the canonical chart at the *foot* `γ t` (the value
of the curve at the very time at which the derivative is taken). Because
no chart is chosen by hand — the chart is dictated by the point `γ t` —
the resulting operator is intrinsic. The output is a bundle vector in
`T_{γ(t)} M`; the model-space `E`-coordinate representation is only ever
used *inside* the single fixed foot-chart at `γ t`, which sidesteps the
basepoint discontinuity of the chart transition Jacobian.

## Construction

Concretely:

1. Represent the section `V` in the chart at `γ t`: for each `s`,
   `(triv_{γt})·.continuousLinearMapAt ℝ (γ s) (V s) : E` is the
   chart-`(γ t)`-coordinate of the vector `V s ∈ T_{γ(s)} M`.
2. Apply the chart-local covariant derivative
   `chartCovDerivAlong g (γ t) γ` (from `AlongCurve`) to this
   `E`-valued section, at the time `t`.
3. Map the resulting model-fibre vector back into `T_{γ(t)} M` by the
   inverse trivialisation `symmL ℝ (γ t)`.

## Main results

* `covDerivAlong` — the definition.
* `covDerivAlong_chartCoord` — the chart-`(γ t)`-coordinate of
  `covDerivAlong g γ V t` is `chartCovDerivAlong g (γ t) γ (chartRep V) t`,
  i.e. the `symmL`/`continuousLinearMapAt` round-trip is the identity at
  the foot `γ t` (which lies in its own chart's base set).
* `covDerivAlong_zero`, `covDerivAlong_add`, `covDerivAlong_smul`,
  `covDerivAlong_smulFun` — ℝ-linearity in `V` (with the Leibniz rule for
  the scalar-function multiple), under the natural differentiability
  hypotheses on the chart-`(γ t)`-coordinate representations.
* `covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt` — **the
  keystone velocity equivalence**: for a `C^∞` curve `γ`, the intrinsic
  covariant derivative of the velocity field `t ↦ dγ_t(1)` vanishes at `t`
  iff `γ` satisfies the chart-coordinate geodesic equation at `t`.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace CovariantDerivativeAlong

/-! ## The chart-`(γ t)`-coordinate representation of a section -/

/-- The chart-`(γ t)`-coordinate representation of a section `V` along
`γ`, *pinned at the foot `γ t`*: for each `s`, this is the model-fibre
vector `(triv_{γ t})·.continuousLinearMapAt ℝ (γ s) (V s) : E`, the
chart-`(γ t)`-coordinate of `V s ∈ T_{γ(s)} M`.

This is a function of the *evaluation time* `t` (which fixes the chart)
and the *running parameter* `s` (along which one differentiates). At
`s = t` it returns the chart-`(γ t)`-coordinate of `V t` in its own
chart, where the trivialisation round-trip is the identity. -/
def chartRepAt (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ → E :=
  fun s => (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (V s)

@[simp] lemma chartRepAt_apply (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t s : ℝ) :
    chartRepAt (I := I) γ V t s =
      (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s) (V s) := rfl

/-- At the foot `γ t`, the chart-`(γ t)`-coordinate of `V t` recovers
`V t` after the inverse trivialisation: `symmL ℝ (γ t) (chartRepAt γ V t t) = V t`.
This holds because `γ t` lies in the base set of `trivializationAt E (TangentSpace I) (γ t)`. -/
lemma symmL_chartRepAt_self (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        (chartRepAt (I := I) γ V t t) = V t := by
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  exact (trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt
    (R := ℝ) hmem (V t)

/-! ## Total-space (bundle-topology) continuity of an along-curve section

A section `V` along `γ` packages into a `TangentBundle I M`-valued map
`t ↦ ⟨γ t, V t⟩` (`TotalSpace.mk' E (γ t) (V t)`). Its continuity into the
total space is governed by Mathlib's fibre-bundle continuity criterion
`FiberBundle.continuousWithinAt_totalSpace`: continuity of the base curve
`γ` together with continuity of the *fibre coordinate read in the
trivialisation pinned at the foot `γ x₀`*. On the open set where `γ t` lands
in the base set of that trivialisation, the fibre coordinate is exactly the
chart-`(γ x₀)`-coordinate representation `chartRepAt γ V x₀`, whose
differentiability at the diagonal point `x₀` supplies the needed pointwise
continuity. (The bundle topology is independent of the choice of fibre norm,
so the `TangentSpace`-norm diamond does not interfere with this continuity.) -/

/-- **Total-space continuity at a point (within a set).** For a curve `γ`
that is continuous within `s` at `x₀`, and a section `V` along `γ` whose
pinned chart-`(γ x₀)`-coordinate representation `chartRepAt γ V x₀` is
differentiable at `x₀`, the bundle-valued map `t ↦ ⟨γ t, V t⟩` is
`ContinuousWithinAt` into `TangentBundle I M` at `x₀`.

The proof goes through `FiberBundle.continuousWithinAt_totalSpace`: the base
component is `hγ`; the fibre component coincides, eventually within `s` near
`x₀` (where `γ t` lies in the base set of the trivialisation at `γ x₀`), with
`chartRepAt γ V x₀`, which is continuous at `x₀` because it is differentiable
there. -/
theorem sectionAlongCurve_continuousWithinAt_totalSpace
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ} {x₀ : ℝ}
    (hx₀ : x₀ ∈ s)
    (hγ : ContinuousWithinAt γ s x₀)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V x₀) x₀) :
    ContinuousWithinAt
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s x₀ := by
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hγ, ?_⟩
  -- the foot at `x₀` lies in the base set of its own trivialisation
  have hbase₀ : γ x₀ ∈ (trivializationAt E (TangentSpace I) (γ x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ x₀)
  -- the base set is open
  have hopen : IsOpen (trivializationAt E (TangentSpace I) (γ x₀)).baseSet :=
    (trivializationAt E (TangentSpace I) (γ x₀)).open_baseSet
  -- eventually within `s` near `x₀`, `γ t` lands in the base set
  have hpre : γ ⁻¹' (trivializationAt E (TangentSpace I) (γ x₀)).baseSet ∈ 𝓝[s] x₀ :=
    hγ.preimage_mem_nhdsWithin (hopen.mem_nhds hbase₀)
  -- there the fibre coordinate is exactly the pinned chart-`(γ x₀)`-coordinate
  have heq :
      (fun t => ((trivializationAt E (TangentSpace I) (γ x₀))
        (TotalSpace.mk' E (γ t) (V t))).2)
        =ᶠ[𝓝[s] x₀] chartRepAt (I := I) γ V x₀ := by
    filter_upwards [hpre] with t ht
    rw [chartRepAt_apply]
    rw [(trivializationAt E (TangentSpace I) (γ x₀)).continuousLinearMapAt_apply (R := ℝ)]
    rw [(trivializationAt E (TangentSpace I) (γ x₀)).coe_linearMapAt_of_mem ht]
  -- the chart-representation is continuous at `x₀` (differentiable ⟹ continuous)
  have hcont : ContinuousWithinAt (chartRepAt (I := I) γ V x₀) s x₀ :=
    hV.continuousAt.continuousWithinAt
  exact hcont.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hx₀)

/-- **Total-space continuity on a set.** For a curve `γ` continuous on `s`
and a section `V` along `γ` whose pinned chart-`(γ t)`-coordinate
representations `chartRepAt γ V t` are differentiable at every `t ∈ s`, the
bundle-valued map `t ↦ ⟨γ t, V t⟩` is `ContinuousOn s` into
`TangentBundle I M`. This is the pointwise lemma quantified over `s`. -/
theorem sectionAlongCurve_continuousOn_totalSpace
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ}
    (hγ : ContinuousOn γ s)
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    ContinuousOn
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s := by
  intro x₀ hx₀
  exact sectionAlongCurve_continuousWithinAt_totalSpace (I := I) γ V hx₀
    (hγ x₀ hx₀) (hV x₀ hx₀)

/-- **Total-space continuity on a set, from `C¹` smoothness of the curve.**
A convenience wrapper for `sectionAlongCurve_continuousOn_totalSpace` that
extracts the base continuity from `ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s`. -/
theorem sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    ContinuousOn
      (fun t => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) s :=
  sectionAlongCurve_continuousOn_totalSpace (I := I) γ V hγ.continuousOn hV

/-! ## The intrinsic covariant derivative along a curve -/

/-- The intrinsic covariant derivative of a section `V` along `γ` at time
`t`, valued in `T_{γ(t)} M`. The chart at the foot `γ t` is pinned, `V`
is represented in that chart by `chartRepAt γ V t`, the chart-local
covariant derivative `chartCovDerivAlong g (γ t) γ` is applied at the
time `t`, and the result is mapped back into the fibre by the inverse
trivialisation `symmL ℝ (γ t)`. -/
def covDerivAlong (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
    (chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t)

@[simp] lemma covDerivAlong_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ V t =
      (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        (chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t) := rfl

/-- **Chart-`(γ t)`-coordinate of the intrinsic covariant derivative.**
Applying the forward chart-`(γ t)`-coordinate map (the trivialisation's
`continuousLinearMapAt` at the foot `γ t`) to `covDerivAlong g γ V t`
returns exactly the chart-local covariant derivative
`chartCovDerivAlong g (γ t) γ (chartRepAt γ V t) t`. This is the
"round-trip is the identity at the foot" identity: `γ t` lies in the base
set of its own trivialisation, so `continuousLinearMapAt ∘ symmL = id`
there. -/
lemma covDerivAlong_chartCoord (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlong (I := I) g γ V t) =
      chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t := by
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  rw [covDerivAlong_def]
  exact (trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt_symmL
    (R := ℝ) hmem _

/-- `covDerivAlong` is `0` iff its chart-`(γ t)`-coordinate
`chartCovDerivAlong g (γ t) γ (chartRepAt γ V t) t` is `0`. Forward
direction: apply the (injective on the base set) forward chart map; the
round-trip identity `covDerivAlong_chartCoord` turns `covDerivAlong = 0`
into `chartCovDerivAlong = 0`. Backward direction: `symmL` of `0` is `0`. -/
lemma covDerivAlong_eq_zero_iff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ V t = 0 ↔
      chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t = 0 := by
  constructor
  · intro h
    have := covDerivAlong_chartCoord (I := I) g γ V t
    rw [h, map_zero] at this
    exact this.symm
  · intro h
    rw [covDerivAlong_def, h, map_zero]

/-! ## ℝ-linearity in the section argument

The chart-`(γ t)`-coordinate representation `chartRepAt` is fibrewise
ℝ-linear, and `chartCovDerivAlong` is ℝ-linear in its section argument
(under the appropriate differentiability of the chart representations,
needed for the additivity of `deriv`). Composing with the linear `symmL`
yields the linearity of `covDerivAlong`. -/

/-- The zero section has vanishing covariant derivative. -/
@[simp] lemma covDerivAlong_zero (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    covDerivAlong (I := I) g γ (fun s => (0 : TangentSpace I (γ s))) t = 0 := by
  -- `chartRepAt γ 0 t` is the zero function: each fibre CLM sends `0 ↦ 0`.
  have hrep : chartRepAt (I := I) γ (fun s => (0 : TangentSpace I (γ s))) t = fun _ => (0 : E) := by
    funext s
    simp [chartRepAt]
  rw [covDerivAlong_def, hrep]
  -- `chartCovDerivAlong g (γt) γ 0 t = deriv 0 t + Γ(u't, 0)(ut) = 0`.
  rw [chartCovDerivAlong_def]
  rw [ChartChristoffel.contraction_zero_right]
  rw [deriv_const', add_zero]
  -- `symmL` is a continuous linear map, so it sends `0` to `0`.
  exact map_zero _

/-- The chart-`(γ t)`-coordinate representation of a pointwise sum is the
sum of the representations. -/
lemma chartRepAt_add (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => V s + W s) t =
      fun s => chartRepAt (I := I) γ V t s + chartRepAt (I := I) γ W t s := by
  funext s
  simp [chartRepAt, map_add]

/-- The chart-`(γ t)`-coordinate representation of a real-scalar multiple
is the scalar multiple of the representation. -/
lemma chartRepAt_smul (γ : ℝ → M) (c : ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => c • V s) t =
      fun s => c • chartRepAt (I := I) γ V t s := by
  funext s
  simp [chartRepAt, map_smul]

/-- The chart-`(γ t)`-coordinate representation of a scalar-function
multiple `s ↦ f s • V s` is `s ↦ f s • chartRepAt γ V t s`. -/
lemma chartRepAt_smulFun (γ : ℝ → M) (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => f s • V s) t =
      fun s => f s • chartRepAt (I := I) γ V t s := by
  funext s
  simp [chartRepAt, map_smul]

/-- **Additivity in the section argument.** If the chart-`(γ t)`-coordinate
representations of `V` and `W` are both differentiable at `t`, then the
covariant derivative of the pointwise sum is the sum of the covariant
derivatives. The differentiability hypotheses are the genuine
"both sections vary differentiably (in chart coordinates)" assumptions
that make `deriv (X + Y) t = deriv X t + deriv Y t` valid. -/
theorem covDerivAlong_add (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t) :
    covDerivAlong (I := I) g γ (fun s => V s + W s) t =
      covDerivAlong (I := I) g γ V t + covDerivAlong (I := I) g γ W t := by
  rw [covDerivAlong_def, covDerivAlong_def, covDerivAlong_def]
  rw [← map_add]
  congr 1
  rw [chartRepAt_add]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  -- `deriv (X + Y) t = deriv X t + deriv Y t`; `Γ(u't, X t + Y t) = Γ(..,X t) + Γ(..,Y t)`.
  rw [deriv_fun_add hV hW]
  rw [ChartChristoffel.contraction_add_right]
  abel

/-- **Real-scalar homogeneity in the section argument.** The covariant
derivative of `s ↦ c • V s` is `c • covDerivAlong g γ V t`. No
differentiability hypothesis is needed: `deriv (c • X) t = c • deriv X t`
holds unconditionally. -/
theorem covDerivAlong_smul (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (c : ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlong (I := I) g γ (fun s => c • V s) t =
      c • covDerivAlong (I := I) g γ V t := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  rw [chartRepAt_smul]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [deriv_fun_const_smul_field]
  rw [ChartChristoffel.contraction_smul_right]
  rw [smul_add]

/-- **Leibniz rule for a scalar-function multiple.** If the chart-`(γ t)`-
coordinate representation of `V` and the scalar function `f` are both
differentiable at `t`, then
`covDerivAlong g γ (f • V) t = f' t • V t + f t • covDerivAlong g γ V t`.
The first summand uses the *derivative of `f` at `t`* times the value
`V t` (recovered by the round-trip `symmL`), the second the value `f t`
times the covariant derivative of `V`. -/
theorem covDerivAlong_smulFun (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    covDerivAlong (I := I) g γ (fun s => f s • V s) t =
      (deriv f t) • V t + f t • covDerivAlong (I := I) g γ V t := by
  rw [covDerivAlong_def, covDerivAlong_def]
  -- Right-hand side: `(deriv f t) • V t + f t • symmL (...)`.
  -- Recover `V t = symmL (chartRepAt γ V t t)`.
  rw [← symmL_chartRepAt_self (I := I) γ V t]
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  rw [chartRepAt_smulFun]
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  -- `deriv (fun s => f s • X s) t = deriv f t • X t + f t • deriv X t` via `HasDerivAt`.
  have hderivSmul :
      deriv (fun s => f s • chartRepAt (I := I) γ V t s) t =
        f t • deriv (chartRepAt (I := I) γ V t) t + deriv f t • chartRepAt (I := I) γ V t t :=
    (hf.hasDerivAt.smul hV.hasDerivAt).deriv
  rw [hderivSmul]
  -- `Γ(u't, f t • X t) = f t • Γ(u't, X t)`.
  rw [ChartChristoffel.contraction_smul_right]
  -- assemble both sides.
  rw [smul_add]
  abel

/-! ## Smoothness of the chart trajectory and the velocity representation

For the keystone velocity equivalence we need: the chart-`(γ t)`-pullback
`u := chartCurve (γ t) γ = chartLocalCurve γ t` is `C^∞` on the open set
`U := γ ⁻¹' (chartAt H (γ t)).source`; and the chart-`(γ t)`-coordinate
representation of the velocity field equals `deriv u` near `t`. -/

/-- The open parameter set on which the chart `γ t` "sees" the curve.
Expressed through `extChartAt I (γ t)` so that the model `I` is part of
the signature; its source coincides with `(chartAt H (γ t)).source`. -/
private def chartTime (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (t : ℝ) : Set ℝ :=
  γ ⁻¹' (extChartAt I (γ t)).source

private lemma chartTime_isOpen {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    IsOpen (chartTime I γ t) := by
  have hsrc : IsOpen (extChartAt I (γ t)).source := isOpen_extChartAt_source (I := I) (γ t)
  exact hγ.continuous.isOpen_preimage _ hsrc

private lemma mem_chartTime_self (γ : ℝ → M) (t : ℝ) : t ∈ chartTime I γ t := by
  rw [chartTime, mem_preimage, extChartAt_source]
  exact mem_chart_source H (γ t)

private lemma chartTime_eq_chartSource (γ : ℝ → M) (t : ℝ) :
    chartTime I γ t = γ ⁻¹' (chartAt H (γ t)).source := by
  rw [chartTime, extChartAt_source]

/-- The chart-`(γ t)`-pullback `chartCurve (γ t) γ = extChartAt I (γ t) ∘ γ`
is `C^∞` (`ContDiffOn ℝ ∞`) on the open set `chartTime γ t`. -/
private lemma contDiffOn_chartCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    ContDiffOn ℝ ∞ (chartCurve (I := I) (γ t) γ) (chartTime I γ t) := by
  have h_comp_mdiff :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I (γ t)) ∘ γ) (chartTime I γ t) := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I (γ t)) (chartAt H (γ t)).source :=
      contMDiffOn_extChartAt (I := I) (n := ∞) (x := γ t)
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (chartTime I γ t) := hγ.contMDiffOn
    have hmaps : MapsTo γ (chartTime I γ t) (chartAt H (γ t)).source := by
      intro s hs
      rw [chartTime, mem_preimage, extChartAt_source] at hs
      exact hs
    exact hφ.comp hγU hmaps
  -- `chartCurve (γ t) γ = extChartAt I (γ t) ∘ γ` by definition.
  have hfun : (chartCurve (I := I) (γ t) γ) = ((extChartAt I (γ t)) ∘ γ) := rfl
  rw [hfun]
  exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff

/-- The chart trajectory is `ContDiffAt ℝ ∞` at `t`. -/
lemma contDiffAt_chartCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    ContDiffAt ℝ ∞ (chartCurve (I := I) (γ t) γ) t :=
  (contDiffOn_chartCurve (I := I) hγ t).contDiffAt
    ((chartTime_isOpen (I := I) hγ t).mem_nhds (mem_chartTime_self (I := I) γ t))

/-- On `chartTime γ t`, the chart-`(γ t)`-coordinate of the velocity field
`s ↦ mfderiv γ s 1` coincides with `deriv (chartCurve (γ t) γ)`. This is
the chain-rule identity `chartCoord_mfderiv_along_curve_eq_fderiv`
specialised to the chart at `γ t`, together with
`fderiv (extChartAt I (γ t) ∘ γ) s 1 = deriv (chartCurve (γ t) γ) s`. -/
private lemma velocity_chartRep_eqOn {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    EqOn (chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t)
      (deriv (chartCurve (I := I) (γ t) γ)) (chartTime I γ t) := by
  intro s hs
  -- `hs : γ s ∈ (chartAt H (γ t)).source` (after unfolding `chartTime`).
  have hs' : γ s ∈ (chartAt H (γ t)).source := by
    rw [chartTime, mem_preimage, extChartAt_source] at hs
    exact hs
  -- `chartRepAt ... t s = continuousLinearMapAt ℝ (γ s) (mfderiv γ s 1)`.
  rw [chartRepAt_apply]
  -- chain-rule identity: the chart-`(γ t)`-coordinate equals `fderiv (extChartAt I (γ t) ∘ γ) s 1`.
  rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M)
    (γ := γ) hγ (γ t) (t := s) hs']
  -- `fderiv (extChartAt I (γ t) ∘ γ) s 1 = deriv (chartCurve (γ t) γ) s`: both sides are
  -- definitionally `deriv (fun s => extChartAt I (γ t) (γ s)) s` (via `fderiv_apply_one_eq_deriv`,
  -- which is `rfl`, and `chartCurve (γ t) γ = extChartAt I (γ t) ∘ γ`).
  rfl

/-- The velocity field's chart-`(γ t)`-coordinate representation agrees
with `deriv (chartCurve (γ t) γ)` *eventually near `t`* (the open set
`chartTime γ t` is a neighbourhood of `t`). -/
private lemma velocity_chartRep_eventuallyEq {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t
      =ᶠ[𝓝 t] deriv (chartCurve (I := I) (γ t) γ) :=
  (velocity_chartRep_eqOn (I := I) hγ t).eventuallyEq_of_mem
    ((chartTime_isOpen (I := I) hγ t).mem_nhds (mem_chartTime_self (I := I) γ t))

/-! ## The keystone velocity equivalence

The intrinsic covariant derivative of the velocity field vanishes at `t`
iff `γ` satisfies the chart-coordinate geodesic equation at `t`. -/

/-- **Velocity equivalence (keystone).** For a `C^∞` curve `γ : ℝ → M`, the
intrinsic covariant derivative of the velocity field `s ↦ dγ_s(1)`
vanishes at `t` iff `γ` satisfies the chart-coordinate geodesic equation
at `t` (the predicate `HasGeodesicEquationAt`).

The minimal differentiability hypothesis is `ContMDiff 𝓘(ℝ, ℝ) I ∞ γ`
(space-only `C^∞` smoothness of the one-dimensional curve). This is the
exact regularity under which the chart-`(γ t)`-coordinate of the velocity
is the chain-rule `fderiv` (via `chartCoord_mfderiv_along_curve_eq_fderiv`)
and the chart pullback `chartCurve (γ t) γ` is twice continuously
differentiable near `t`. -/
theorem covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 ↔
      HasGeodesicEquationAt (I := I) g γ t := by
  classical
  -- Abbreviations.
  set u : ℝ → E := chartCurve (I := I) (γ t) γ with hu_def
  set rep : ℝ → E :=
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t with hrep_def
  -- The chart trajectory is `C^∞` at `t`.
  have hu_cdiff : ContDiffAt ℝ ∞ u t := contDiffAt_chartCurve (I := I) hγ t
  -- `u` is `C^∞` on the open set `chartTime γ t` (a neighbourhood of `t`).
  have hU_open : IsOpen (chartTime I γ t) := chartTime_isOpen (I := I) hγ t
  have ht_mem : t ∈ chartTime I γ t := mem_chartTime_self (I := I) γ t
  have hU_nhds : chartTime I γ t ∈ 𝓝 t := hU_open.mem_nhds ht_mem
  have hu_cdiffOn : ContDiffOn ℝ ∞ u (chartTime I γ t) :=
    contDiffOn_chartCurve (I := I) hγ t
  -- `deriv u` is `C^∞` on `chartTime γ t`; in particular differentiable there.
  have hderiv_u_cdiffOn : ContDiffOn ℝ ∞ (deriv u) (chartTime I γ t) :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
  -- `u` differentiable at `t`, so `HasDerivAt u (deriv u t) t`.
  have hu_diffAt : DifferentiableAt ℝ u t := hu_cdiff.differentiableAt (by simp)
  have hu_hasDerivAt : HasDerivAt u (deriv u t) t := hu_diffAt.hasDerivAt
  -- `u` differentiable on `chartTime γ t`, so `∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s`.
  have hu_diffOn : DifferentiableOn ℝ u (chartTime I γ t) :=
    hu_cdiffOn.differentiableOn (by simp)
  have hu_eventually_hasDerivAt :
      ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s := by
    filter_upwards [hU_nhds] with s hs
    exact ((hu_diffOn s hs).differentiableAt (hU_open.mem_nhds hs)).hasDerivAt
  -- `deriv u` differentiable at `t`, so `HasDerivAt (deriv u) (deriv (deriv u) t) t`.
  have hderiv_u_diffAt : DifferentiableAt ℝ (deriv u) t :=
    (hderiv_u_cdiffOn.differentiableOn (by simp) t ht_mem).differentiableAt hU_nhds
  have hderiv_u_hasDerivAt : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hderiv_u_diffAt.hasDerivAt
  -- The velocity chart-rep equals `deriv u` eventually near `t`.
  have hrep_eq : rep =ᶠ[𝓝 t] deriv u := velocity_chartRep_eventuallyEq (I := I) hγ t
  -- Value at `t`: `rep t = deriv u t`.
  have hrep_t : rep t = deriv u t := hrep_eq.eq_of_nhds
  -- `deriv rep t = deriv (deriv u) t`.
  have hderiv_rep_t : deriv rep t = deriv (deriv u) t := hrep_eq.deriv_eq
  -- The chart-`(γ t)`-coordinate covariant derivative computed explicitly:
  --   chartCovDerivAlong g (γ t) γ rep t
  --     = deriv rep t + Γ(deriv u t, rep t)(u t)
  --     = deriv (deriv u) t + Γ(deriv u t, deriv u t)(u t).
  have hchart :
      chartCovDerivAlong (I := I) g (γ t) γ rep t =
        deriv (deriv u) t +
          chartChristoffelContraction (I := I) g (γ t) (deriv u t) (deriv u t)
            (extChartAt I (γ t) (γ t)) := by
    rw [chartCovDerivAlong_def]
    -- `chartCurve (γ t) γ = u` and `chartCurve (γ t) γ t = extChartAt I (γ t) (γ t)`.
    rw [hderiv_rep_t, hrep_t]
    -- `chartCurve (γ t) γ t = u t = extChartAt I (γ t) (γ t)`; `deriv (chartCurve (γt) γ) t = deriv u t`.
    rfl
  -- Reduce `covDerivAlong = 0` to `chartCovDerivAlong = 0`.
  rw [covDerivAlong_eq_zero_iff (I := I) g γ
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t]
  -- The chart-rep used inside `covDerivAlong_eq_zero_iff` is exactly `rep`.
  change chartCovDerivAlong (I := I) g (γ t) γ rep t = 0 ↔ HasGeodesicEquationAt (I := I) g γ t
  rw [hchart]
  constructor
  · -- `deriv (deriv u) t + Γ(deriv u t, deriv u t)(u t) = 0 → HasGeodesicEquationAt`.
    intro heq
    refine ⟨deriv u t, deriv (deriv u) t, ?_, ?_, ?_, ?_⟩
    · -- `HasDerivAt (chartLocalCurve γ t) (deriv u t) t`; `chartLocalCurve γ t = u`.
      exact hu_hasDerivAt
    · -- `∀ᶠ s in 𝓝 t, HasDerivAt (chartLocalCurve γ t) (deriv (chartLocalCurve γ t) s) s`.
      exact hu_eventually_hasDerivAt
    · -- `HasDerivAt (deriv (chartLocalCurve γ t)) (deriv (deriv u) t) t`.
      exact hderiv_u_hasDerivAt
    · -- The geodesic identity.
      exact heq
  · -- `HasGeodesicEquationAt → deriv (deriv u) t + Γ(deriv u t, deriv u t)(u t) = 0`.
    intro hgeo
    obtain ⟨v, a, hv, _hev, ha, hid⟩ := hgeo
    -- `chartLocalCurve γ t = u`, so `v = deriv u t` and `a = deriv (deriv u) t`.
    have hv_eq : v = deriv u t := by
      have : HasDerivAt u v t := hv
      exact this.deriv.symm ▸ rfl
    have ha_eq : a = deriv (deriv u) t := by
      have : HasDerivAt (deriv u) a t := ha
      exact this.deriv.symm ▸ rfl
    -- Rewrite the geodesic identity using these.
    rw [← hv_eq, ← ha_eq]
    -- `extChartAt I (γ t) (γ t) = u t`; `hid : a + Γ(v, v)(extChartAt I (γt) (γt)) = 0`.
    exact hid

/-- **`C²`-form velocity equivalence (backward direction).** For a curve `γ`
that is `ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t` (twice continuously differentiable at `t`
in the manifold sense), if `γ` satisfies the chart-coordinate geodesic equation
at `t` (`HasGeodesicEquationAt`), then the intrinsic covariant derivative of the
velocity field `s ↦ dγ_s(1)` vanishes at `t`.

This is the `C²`-relaxed backward direction of
`covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt`. The full iff is stated
under `ContMDiff 𝓘(ℝ, ℝ) I ∞ γ`, but the geodesic-implies-zero direction needs
only `C²` regularity: the chart trajectory `chartCurve (γ t) γ` is `ContDiffOn 2`
on an open neighbourhood of `t` (where `γ` is `C²` and lands in the chart source),
hence its first derivative is `C¹` and the eventual `HasDerivAt` clauses hold; the
velocity chart-representation equals `deriv (chartCurve (γ t) γ)` near `t` via the
`MDifferentiableAt`-level chain-rule bridge
`chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt`. This is the form
consumed by second-order variational arguments where the central curve is only
twice continuously differentiable (e.g. the radial geodesic variation behind
Gauss's lemma, whose velocity field is `C²` but not known to be `C^∞`). -/
theorem covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    (hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : HasGeodesicEquationAt (I := I) g γ t) :
    covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 := by
  classical
  set u : ℝ → E := chartCurve (I := I) (γ t) γ with hu_def
  set rep : ℝ → E :=
    chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t with hrep_def
  -- Eventual `C²` of `γ` near `t` (uses `IsManifold I 2 M`, auto from `IsManifold I ∞ M`).
  have hev_c2 : ∀ᶠ s in 𝓝 t, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγ2
  -- The chart-source preimage is a neighbourhood of `t` (`γ` continuous at `t`).
  have hev_src : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source := by
    have : (chartAt H (γ t)).source ∈ 𝓝 (γ t) :=
      (chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t))
    exact hγ2.continuousAt.preimage_mem_nhds this
  -- Combine into an open set `U ∋ t` carrying both properties.
  obtain ⟨U, hU_sub, hU_open, ht_U⟩ := eventually_nhds_iff.mp (hev_c2.and hev_src)
  have hUsub_c2 : ∀ s ∈ U, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ s := fun s hs => (hU_sub s hs).1
  have hUsub_src : ∀ s ∈ U, γ s ∈ (chartAt H (γ t)).source := fun s hs => (hU_sub s hs).2
  have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds ht_U
  -- `u = chartCurve (γ t) γ` is `ContDiffOn 2` on `U`.
  have hu_cdiffOn : ContDiffOn ℝ 2 u U := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t)) ∘ γ) U := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) 2 (extChartAt I (γ t)) (chartAt H (γ t)).source :=
        contMDiffOn_extChartAt (I := I) (n := 2) (x := γ t)
      have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ U := fun s hs => (hUsub_c2 s hs).contMDiffWithinAt
      have hmaps : MapsTo γ U (chartAt H (γ t)).source := fun s hs => hUsub_src s hs
      exact hφ.comp hγU hmaps
    have hfun : u = ((extChartAt I (γ t)) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  -- `deriv u` is `ContDiffOn 1` on `U`; in particular differentiable on `U`.
  have hderiv_u_cdiffOn : ContDiffOn ℝ 1 (deriv u) U :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by norm_num)
  have hu_diffAt : DifferentiableAt ℝ u t :=
    (hu_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hu_hasDerivAt : HasDerivAt u (deriv u t) t := hu_diffAt.hasDerivAt
  have hu_diffOn : DifferentiableOn ℝ u U := hu_cdiffOn.differentiableOn (by norm_num)
  have hu_eventually_hasDerivAt : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u s) s := by
    filter_upwards [hU_nhds] with s hs
    exact ((hu_diffOn s hs).differentiableAt (hU_open.mem_nhds hs)).hasDerivAt
  have hderiv_u_diffAt : DifferentiableAt ℝ (deriv u) t :=
    (hderiv_u_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hderiv_u_hasDerivAt : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hderiv_u_diffAt.hasDerivAt
  -- The velocity chart-rep equals `deriv u` on `U` (via the `MDifferentiableAt`
  -- chart-`(γ t)`-coordinate chain rule).
  have hrep_eqOn : EqOn rep (deriv u) U := by
    intro s hs
    have hs_src : γ s ∈ (chartAt H (γ t)).source := hUsub_src s hs
    have hs_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
      (hUsub_c2 s hs).mdifferentiableAt (by decide)
    rw [hrep_def, chartRepAt_apply]
    rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) hs_mdiff (γ t) (t := s) hs_src]
    rfl
  have hrep_eq : rep =ᶠ[𝓝 t] deriv u := hrep_eqOn.eventuallyEq_of_mem hU_nhds
  have hrep_t : rep t = deriv u t := hrep_eq.eq_of_nhds
  have hderiv_rep_t : deriv rep t = deriv (deriv u) t := hrep_eq.deriv_eq
  -- The chart-`(γ t)`-coordinate covariant derivative computed explicitly.
  have hchart :
      chartCovDerivAlong (I := I) g (γ t) γ rep t =
        deriv (deriv u) t +
          chartChristoffelContraction (I := I) g (γ t) (deriv u t) (deriv u t)
            (extChartAt I (γ t) (γ t)) := by
    rw [chartCovDerivAlong_def]
    rw [hderiv_rep_t, hrep_t]
    rfl
  -- Reduce `covDerivAlong = 0` to `chartCovDerivAlong = 0` and apply the geodesic identity.
  rw [covDerivAlong_eq_zero_iff (I := I) g γ
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t]
  change chartCovDerivAlong (I := I) g (γ t) γ rep t = 0
  rw [hchart]
  obtain ⟨v, a, hv, _hev, ha, hid⟩ := hgeo
  -- `chartLocalCurve γ t = u`, so `v = deriv u t` and `a = deriv (deriv u) t`.
  have hv_eq : v = deriv u t := by
    have : HasDerivAt u v t := hv
    exact this.deriv.symm ▸ rfl
  have ha_eq : a = deriv (deriv u) t := by
    have : HasDerivAt (deriv u) a t := ha
    exact this.deriv.symm ▸ rfl
  rw [← hv_eq, ← ha_eq]
  exact hid

/-! ## Chart-foot invariance of the intrinsic covariant derivative

The intrinsic covariant derivative `covDerivAlong g γ V t` is defined by
pinning the *canonical* foot chart `chartAt H (γ t)`. The lemma
`covDerivAlong_chart_foot_invariance` below shows that *any* chart `β`
whose source contains the foot `γ t` computes the same fibre vector:
represent `V` in chart `β` (via the `β`-trivialisation), apply the
chart-`β` covariant derivative `chartCovDerivAlong g β γ (·) t`, and map
the model-fibre result back into `T_{γ(t)} M` by the inverse `β`-
trivialisation; the answer is `covDerivAlong g γ V t`.

The proof reads everything in the *canonical foot chart* `α := γ t`
(coordinates), where `covDerivAlong_chartCoord` is the identity. The
chart-`β` covariant derivative pushes through the reverse chart-transition
Jacobian `chartTransitionAt β α`; expanding the chart-`β` Christoffel
contraction with the transformation law
`chartChristoffelContraction_transform` produces an inhomogeneous
second-derivative correction `chartTransitionSecondDerivCorrection` that
*exactly cancels* the non-tensorial mismatch coming from differentiating
the foot-dependent transition Jacobian applied to the section
(`fderiv_chartTransitionAt_apply_eq_pushCorrection` plus the mutual-inverse
Jacobian collapse `chartTransitionAt_comp_chartTransitionAt'`). -/

/-- The chart-`β`-coordinate representation of a section `V` along `γ`,
*pinned at the basepoint `β`* (rather than at the moving foot `γ t`): for
each `s`, the model-fibre vector
`(triv_β)·.continuousLinearMapAt ℝ (γ s) (V s) : E`, the chart-`β`
coordinate of `V s ∈ T_{γ(s)} M`. With `β = γ t` it agrees with
`chartRepAt γ V t`. -/
def chartRepAtBase (β : M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) : ℝ → E :=
  fun s => (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s) (V s)

@[simp] lemma chartRepAtBase_apply (β : M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (s : ℝ) :
    chartRepAtBase (I := I) β γ V s =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s) (V s) := rfl

/-- With basepoint `β = γ t`, the pinned-foot chart representation
`chartRepAt γ V t` and the general `chartRepAtBase (γ t) γ V` coincide. -/
lemma chartRepAtBase_foot (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartRepAtBase (I := I) (γ t) γ V = chartRepAt (I := I) γ V t := rfl

/-- **Trivialisation composite is the chart-transition Jacobian.** For two
basepoints `α β : M` and a manifold point `b` in both chart sources, the
chart-`β` trivialisation coordinate of the inverse chart-`α` trivialisation
of `v` equals the chart-transition Jacobian `chartTransitionAt α β` at the
chart-`α` image of `b`, applied to `v`. (Bundle `coordChange` composition
law combined with the boundaryless identification
`fderivWithin (range I) = fderiv`.) -/
private theorem trivCoord_comp_symmL_eq_transition [I.Boundaryless]
    (α β : M) {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
      chartTransitionAt (I := I) α β (extChartAt I α b) v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hβ,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hα]
  have hb_self : b ∈ (chartAt H b).source := mem_chart_source H b
  have hmem : b ∈ (tangentBundleCore I M).baseSet (achart H α)
      ∩ (tangentBundleCore I M).baseSet (achart H b)
      ∩ (tangentBundleCore I M).baseSet (achart H β) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hα
    · rw [tangentBundleCore_baseSet]; exact hb_self
    · rw [tangentBundleCore_baseSet]; exact hβ
  have hcomp := (tangentBundleCore I M).coordChange_comp
    (achart H α) (achart H b) (achart H β) b hmem v
  have hcc : ((tangentBundleCore I M).coordChange (achart H α) (achart H β) b) v =
      chartTransitionAt (I := I) α β (extChartAt I α b) v := by
    change tangentCoordChange I α β b v = _
    rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
    have hrange : (Set.range I : Set E) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I)
    rw [hrange, fderivWithin_univ]
  rw [← hcc]
  exact hcomp

/-- **Chart-foot invariance of the intrinsic covariant derivative.** For a
`C^∞` curve `γ`, a section `V` along `γ` whose canonical foot-chart
representation `chartRepAt γ V t` is differentiable at `t`, and *any*
basepoint `β` whose chart source contains the foot `γ t`, the chart-`β`
recipe for the covariant derivative — transport `V` into chart-`β`
coordinates (`chartRepAtBase β γ V`), take the chart-`β` covariant
derivative `chartCovDerivAlong g β γ (·) t`, push the result back into the
fibre by the inverse `β`-trivialisation `symmL ℝ (γ t)` — returns exactly
the canonical intrinsic value `covDerivAlong g γ V t`.

The differentiability hypothesis `hV` is the genuine "the section varies
differentiably in chart coordinates at `t`" assumption (the same one under
which `covDerivAlong_add` and friends are stated); it is not a restatement
of the conclusion. The smoothness `hγ` of the curve supplies the chart
trajectory's `HasDerivAt` and the eventual two-source membership that make
the chart-transition chain rule valid near `t`. -/
theorem covDerivAlong_chart_foot_invariance [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
        (chartCovDerivAlong (I := I) g β γ (chartRepAtBase (I := I) β γ V) t) =
      covDerivAlong (I := I) g γ V t := by
  classical
  -- The canonical foot chart `α := γ t`; the foot lies in its own chart source.
  set α : M := γ t with hα_def
  have hα : γ t ∈ (chartAt H α).source := mem_chart_source H (γ t)
  -- Chart-coordinate abbreviations.
  set uα : ℝ → E := chartCurve (I := I) α γ with huα_def
  set x : E := extChartAt I α (γ t) with hx_def
  have hxut : uα t = x := by rw [huα_def, chartCurve_def, hx_def]
  -- The reverse transition Jacobian `A`, the forward `J`, and the foot image `xβ`.
  set xβ : E := chartTransitionMap (I := I) α β x with hxβ_def
  -- The foot is in `chartTransitionSource α β`.
  have hsrc : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hα hβ
  -- Foot-image identities: `xβ = extChartAt I β (γ t) = chartCurve β γ t`.
  have hxβ_eq : xβ = extChartAt I β (γ t) := by
    rw [hxβ_def, hx_def, chartTransitionMap_apply_extChartAt (I := I) α β hα]
  have hxβ_curve : xβ = chartCurve (I := I) β γ t := by rw [hxβ_eq, chartCurve_def]
  -- The canonical foot-chart representation, and the chart-`β` representation.
  set repα : ℝ → E := chartRepAt (I := I) γ V t with hrepα_def
  set repβ : ℝ → E := chartRepAtBase (I := I) β γ V with hrepβ_def
  -- `HasDerivAt` for the chart-α trajectory and the foot-chart representation.
  have huα_hd : HasDerivAt uα (deriv uα t) t :=
    ((contDiffAt_chartCurve (I := I) hγ t).differentiableAt (by simp)).hasDerivAt
  have hrepα_hd : HasDerivAt repα (deriv repα t) t := hV.hasDerivAt
  -- An open neighbourhood `U ∋ t` on which `γ` stays in both chart sources.
  set U : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) with hU_def
  have hU_open : IsOpen U :=
    ((chartAt H α).open_source.inter (chartAt H β).open_source).preimage hγ.continuous
  have htU : t ∈ U := ⟨hα, hβ⟩
  have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds htU
  -- On `U`, `repβ s = chartTransitionAt α β (uα s) (repα s)` (the same tangent
  -- vector, read in chart-β coordinates, is the transition push of its chart-α
  -- coordinate).
  have hrepβ_eq : repβ =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) α β (uα s) (repα s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsα, hsβ⟩ := hs
    have hbridge :
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ s)
            ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s))) =
          chartTransitionAt (I := I) α β (extChartAt I α (γ s))
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s)) :=
      trivCoord_comp_symmL_eq_transition (I := I) α β hsα hsβ _
    -- `symmL ∘ continuousLinearMapAt = id` at the base point `γ s`.
    have hround :
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s) (V s)) =
          V s := by
      have hmem : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hsα
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hmem (V s)
    rw [hround] at hbridge
    rw [hrepβ_def, chartRepAtBase_apply]
    rw [hrepα_def, chartRepAt_apply]
    rw [huα_def, chartCurve_def]
    exact hbridge
  -- The value at `t`: `repβ t = chartTransitionAt α β x (repα t)`.
  have hrepβ_t : repβ t = chartTransitionAt (I := I) α β x (repα t) := by
    have := hrepβ_eq.eq_of_nhds
    rw [this, hxut]
  -- Chart-β trajectory is the transition push of the chart-α trajectory near `t`.
  have huβ_eq : chartCurve (I := I) β γ =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α β (uα s)) := by
    filter_upwards [hU_nhds] with s hs
    obtain ⟨hsα, _⟩ := hs
    rw [chartCurve_def, huα_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α β hsα).symm
  -- `HasDerivAt` of the chart-β trajectory: `deriv uβ t = J (deriv uα t)`.
  have hTdiff : DifferentiableAt ℝ (chartTransitionMap (I := I) α β) x :=
    chartTransitionMap_differentiableAt (I := I) α β hsrc
  have huβ_hd : HasDerivAt (chartCurve (I := I) β γ)
      (chartTransitionAt (I := I) α β x (deriv uα t)) t := by
    have hcomp : HasDerivAt
        (fun s => chartTransitionMap (I := I) α β (uα s))
        (chartTransitionAt (I := I) α β x (deriv uα t)) t := by
      have hc : HasDerivAt (chartTransitionMap (I := I) α β ∘ uα)
          ((fderiv ℝ (chartTransitionMap (I := I) α β) (uα t)) (deriv uα t)) t :=
        hTdiff.hasFDerivAt.comp_hasDerivAt t huα_hd
      -- `uα t = x` (defeq); `chartTransitionAt α β x = fderiv (chartTransitionMap α β) x`.
      rw [chartTransitionAt_def]
      exact hc
    exact hcomp.congr_of_eventuallyEq huβ_eq
  have hderiv_uβ : deriv (chartCurve (I := I) β γ) t =
      chartTransitionAt (I := I) α β x (deriv uα t) := huβ_hd.deriv
  -- `HasDerivAt` of the chart-β representation via the CLM-application rule.
  have hAdiff : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E)) x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
      chartTransitionSource_isOpen (I := I) α β
    exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
      (h_open.mem_nhds hsrc)).differentiableAt (by simp)
  have hcA : HasDerivAt
      (fun s => (chartTransitionAt (I := I) α β (uα s) : E →L[ℝ] E))
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) t :=
    -- `uα t = x` definitionally, so the `comp` derivative matches.
    hAdiff.hasFDerivAt.comp_hasDerivAt t huα_hd
  have hrepβ_hd : HasDerivAt repβ
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
        + chartTransitionAt (I := I) α β x (deriv repα t)) t := by
    have hbase : HasDerivAt (fun s => chartTransitionAt (I := I) α β (uα s) (repα s))
        (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
          + chartTransitionAt (I := I) α β x (deriv repα t)) t :=
      -- `uα t = x` definitionally; `clm_apply` value matches up to that defeq.
      hcA.clm_apply hrepα_hd
    exact hbase.congr_of_eventuallyEq hrepβ_eq
  have hderiv_repβ : deriv repβ t =
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t)
        + chartTransitionAt (I := I) α β x (deriv repα t) := hrepβ_hd.deriv
  -- The foot lies in the base set of its own (chart-α) trivialisation.
  have hmemα : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hα
  -- The RHS is, by definition, the inverse chart-α trivialisation of the chart-α
  -- covariant derivative `chartCovDerivAlong g α γ repα t` (since `α = γ t`).
  rw [covDerivAlong_def]
  -- Re-express the LHS as `symmL_α ∘ continuousLinearMapAt_α` of itself (round trip
  -- at the foot), reducing the goal to a chart-α coordinate equality in `E`.
  rw [← (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
    (R := ℝ) hmemα
    ((trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
      (chartCovDerivAlong (I := I) g β γ repβ t))]
  congr 1
  -- The forward chart-α coordinate of `symmL_β` is `chartTransitionAt β α xβ`.
  have hAcoord :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t)
          ((trivializationAt E (TangentSpace I) β).symmL ℝ (γ t)
            (chartCovDerivAlong (I := I) g β γ repβ t)) =
        chartTransitionAt (I := I) β α xβ
          (chartCovDerivAlong (I := I) g β γ repβ t) := by
    rw [trivCoord_comp_symmL_eq_transition (I := I) β α hβ hα
      (chartCovDerivAlong (I := I) g β γ repβ t)]
    rw [hxβ_eq]
  rw [hAcoord]
  -- Set `A := chartTransitionAt β α xβ` and expand the chart-β covariant derivative.
  set A : E →L[ℝ] E := chartTransitionAt (I := I) β α xβ with hA_def
  rw [chartCovDerivAlong_def]
  -- `A` is linear: distribute over the sum.
  rw [map_add]
  -- The chart-β curve value at `t` is `xβ`.
  have huβ_t : chartCurve (I := I) β γ t = xβ := hxβ_curve.symm
  rw [hderiv_repβ, hderiv_uβ, hrepβ_t, huβ_t]
  -- Collapse `A ∘ chartTransitionAt α β x = id` (mutual-inverse Jacobian at the foot).
  have hinv : (A.comp (chartTransitionAt (I := I) α β x)) = ContinuousLinearMap.id ℝ E := by
    rw [hA_def, hxβ_def]
    exact chartTransitionAt_comp_chartTransitionAt (I := I) α β hsrc
  have hcollapse : ∀ z : E, A (chartTransitionAt (I := I) α β x z) = z := by
    intro z
    have := congrArg (fun L : E →L[ℝ] E => L z) hinv
    simpa [ContinuousLinearMap.comp_apply] using this
  -- The foot-slot derivative of the transition Jacobian = forward push of `D²T`.
  have hfoot :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (deriv uα t)) (repα t) =
        chartTransitionAt (I := I) α β x
          (chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x) :=
    fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α β hsrc (deriv uα t) (repα t)
  -- Apply `A` to the first summand and collapse.
  rw [map_add, hfoot, hcollapse, hcollapse]
  -- The chart-Christoffel transformation law at the foot `γ t` (outer α, inner β).
  have htransform :
      chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x =
        chartTransitionAt (I := I) β α xβ
            (chartChristoffelContraction (I := I) g β
              (chartTransitionAt (I := I) α β x (deriv uα t))
              (chartTransitionAt (I := I) α β x (repα t)) xβ)
          + chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x := by
    have hxx : x = extChartAt I α (γ t) := hx_def
    rw [hxx]
    have h := chartChristoffelContraction_transform (I := I) g α β hα hβ
      (deriv uα t) (repα t)
    rw [← hxx, ← hxβ_def] at h
    exact h
  -- Now assemble: the two `D²T` terms cancel.
  -- LHS (after `map_add`, `hfoot`, `hcollapse`):
  --   D²T + deriv repα t + A(Γ_β(J v, J w)(xβ))
  -- and `A(Γ_β(...)) = Γ_α(v, w)(x) - D²T` by `htransform`.
  rw [show chartTransitionAt (I := I) β α xβ
        (chartChristoffelContraction (I := I) g β
          (chartTransitionAt (I := I) α β x (deriv uα t))
          (chartTransitionAt (I := I) α β x (repα t)) xβ)
      = chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x
          - chartTransitionSecondDerivCorrection (I := I) α β (deriv uα t) (repα t) x by
    rw [htransform]; abel]
  -- The RHS (`chartCovDerivAlong g α γ repα t`) expanded in `repα`, `uα`, `x`.
  have hRHS : chartCovDerivAlong (I := I) g α γ repα t =
      deriv repα t + chartChristoffelContraction (I := I) g α (deriv uα t) (repα t) x := by
    rw [chartCovDerivAlong_def, ← huα_def, hxut]
  rw [hRHS]
  -- The two `D²T` corrections cancel; the remaining terms match.
  abel

end CovariantDerivativeAlong

end Riemannian
end Geometry
end DifferentialGeometry

end
