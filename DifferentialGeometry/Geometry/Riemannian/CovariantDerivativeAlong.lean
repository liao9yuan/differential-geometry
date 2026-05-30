import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation

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
private lemma contDiffAt_chartCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
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

end CovariantDerivativeAlong

end Riemannian
end Geometry
end DifferentialGeometry

end
