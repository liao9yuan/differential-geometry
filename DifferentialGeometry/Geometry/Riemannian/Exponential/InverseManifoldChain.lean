import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartFlowToTangentLift
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

set_option linter.unusedSectionVars false

/-!
# Manifold integral-curve property of `chartFlowOrbitLift` on the full uniform interval

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the manifold lift
`F_v := chartFlowOrbitLift Φ p v` of the chart-pushed flow orbit
(constructed in `Exponential/ChartFlowToTangentLift.lean`) is — under
the chart-target-interior confinement and chart-phase ODE hypotheses
supplied by the uniform existence interval — a local integral curve of
the chart-fixed geodesic vector field `geodesicVectorFieldChart g p` at
**every** point of the open interval `Ioo (-T) T`.

This upgrades the "integral curve at `0`" property from
`Exponential/ChartFlowToTangentLift.lean` to "integral curve on the
full uniform interval", which is the manifold-side ingredient required
by the downstream uniform-uniqueness step.

## Strategy

The argument is local at every interior point `s₀ ∈ Ioo (-T) T`.

1. **Chart-of-`TM` chain at a fixed base point `⟨p, 0⟩`.** We prove that,
   for any local integral curve `f` of `geodesicVectorFieldChart g p` at
   `s₀` with `(f s₀).proj ∈ (chartAt H p).source`, the chart-pushed
   curve at the *fixed* zero-section base point `⟨p, 0⟩`,
   ```
   c_p(s) := extChartAt I.tangent ⟨p, 0⟩ (f s),
   ```
   satisfies the chart-phase ODE
   `HasDerivAt c_p (chartPhaseVF g p (c_p s)) s` on a neighbourhood of
   `s₀`. The proof mirrors the Mathlib lemma
   `IsMIntegralCurveAt.eventually_hasDerivAt`, but with the chart at the
   running base point `f s₀` replaced by the chart at the *fixed* point
   `⟨p, 0⟩`. The replacement is valid because the chart-of-`TM` only
   depends on the projection and the projection of `f s` remains in the
   chart-`p` source on a neighbourhood of `s₀`.

2. **Picard–Lindelöf local lift at `s₀`.** At each `s₀ ∈ Ioo (-T) T`,
   Mathlib's Picard–Lindelöf theorem produces a curve
   `g_loc : ℝ → TangentBundle I M` with `g_loc s₀ = F_v s₀` and
   `IsMIntegralCurveAt g_loc (gvf...) s₀`. The smoothness hypothesis
   needed is `(F_v s₀).proj ∈ (chartAt H p).source`, which holds from
   `chartAt_source_of_extChartAt_tangent_zero_symm` applied to the
   orbit's chart-target-interior confinement.

3. **Chart-coordinate ODE uniqueness against the orbit.** Both the
   curve `c_p ∘ g_loc` (from step 1) and the orbit
   `c(s) := Φ((x₀, v), s)` solve the chart-phase ODE on a neighbourhood
   of `s₀`. They take the same value at `s = s₀`: at the curve side,
   `c_p (g_loc s₀) = c_p (F_v s₀) = c s₀` (by construction of `F_v`).
   By `chartPhaseVF_orbit_uniqueness`, they agree on a neighbourhood of
   `s₀`. Inverting the chart-of-`TM` at `⟨p, 0⟩` yields
   `g_loc =ᶠ[𝓝 s₀] F_v`.

4. **Transfer of the integral-curve property.** From `g_loc =ᶠ[𝓝 s₀] F_v`
   and `IsMIntegralCurveAt g_loc (gvf...) s₀`, transfer the property to
   `F_v` via `HasMFDerivAt.congr_of_eventuallyEq`.

## Main results

* `eventually_hasDerivAt_chartPhaseVF_at_zero_section` — the chart-of-
  `TM`-at-`⟨p, 0⟩` form of the chart-phase ODE for any local integral
  curve of `geodesicVectorFieldChart g p` whose projection at the base
  time lies in the chart-`p` source.

* `chartFlowOrbitLift_isMIntegralCurveAt_of_mem_Ioo` — for each
  `s₀ ∈ Ioo (-T) T` and `v ∈ ball (0 : E) ρ`, the lift `F_v` is a local
  integral curve of `geodesicVectorFieldChart g p` at `s₀`.

* `chartFlowOrbitLift_isMIntegralCurveOn_Ioo` — the headline:
  `F_v` is `IsMIntegralCurveOn (geodesicVectorFieldChart g p) (Ioo (-T) T)`.

* `exists_chartFlowOrbitLift_isMIntegralCurveOn_Ioo_data` — packaged
  existence form: there exist a chart-pushed flow `Φ` and uniform
  radii `(ρ, T) > 0` such that for every `v ∈ ball (0 : E) ρ`, all
  R.D.1 data plus the `IsMIntegralCurveOn` of `F_v` on `Ioo (-T) T`
  hold.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Chart-phase ODE at a fixed zero-section base point

The Mathlib lemma `IsMIntegralCurveAt.eventually_hasDerivAt` expresses
the derivative of a manifold-valued integral curve in the chart at the
running base point `f t₀`. The chart-of-`TM` only depends on the
projection (`extChartAt_tangent_eq_at_proj`), so when the projection of
`f s₀` lies in the chart-`α` source we can equivalently express the
chart-pushed derivative at the *fixed* zero-section point `⟨α, 0⟩`.

We mirror the Mathlib proof, substituting the fixed chart base. The
identification of the derivative with `chartPhaseVF g α` then follows
from the chain `tangentCoordChange ⟶ geodesicVectorFieldChartFiber ⟶
chartPhaseVF` already in `ChartPushVFEq.lean`. -/

section ChartPhaseAtZeroSection

variable [I.Boundaryless]

set_option backward.isDefEq.respectTransparency false in
/-- **Chart-`⟨α, 0⟩`-pushed derivative of a local integral curve.** For
a curve `f : ℝ → TangentBundle I M` that is a local integral curve of
`geodesicVectorFieldChart g α` at `s₀`, and whose projection at `s₀`
lies in the chart-`α` source, the chart-pushed curve at the fixed
zero-section base `⟨α, 0⟩`,
`s ↦ extChartAt I.tangent ⟨α, 0⟩ (f s)`, satisfies the genuine
chart-phase ODE on a neighbourhood of `s₀`. -/
theorem eventually_hasDerivAt_chartPhaseVF_at_zero_section
    {g : SmoothRiemannianMetric I M} {α : M} {s₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hα_src : (f s₀).proj ∈ (chartAt H α).source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) s₀) :
    ∀ᶠ s in 𝓝 s₀,
      HasDerivAt
        (fun s' : ℝ => extChartAt I.tangent
          (⟨α, (0 : E)⟩ : TangentBundle I M) (f s'))
        (chartPhaseVF (I := I) g α
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s))) s := by
  classical
  -- The chart-of-`TM` at `⟨α, 0⟩` is a partial homeomorph whose source
  -- contains `f s` iff `(f s).proj ∈ (chartAt H α).source`.
  set q₀ : TangentBundle I M := (⟨α, (0 : E)⟩ : TangentBundle I M) with hq₀_def
  -- Eventually `(f s).proj ∈ (chartAt H α).source`.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f s₀ := hf.continuousAt
  have hcomp0 : ContinuousAt (fun s => (f s).proj) s₀ :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_nhds : (chartAt H α).source ∈ 𝓝 ((f s₀).proj) :=
    hα_open.mem_nhds hα_src
  have hsrc_nhds : (fun s : ℝ => (f s).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 s₀ :=
    hcomp0.preimage_mem_nhds hα_nhds
  -- `IsMIntegralCurveAt` gives `HasMFDerivAt f s _` eventually.
  -- Combine with the chart-source-preimage to get the eventually statement.
  filter_upwards [hf, hsrc_nhds] with s hHas hs_src
  -- `hs_src : (f s).proj ∈ (chartAt H α).source`.
  -- Membership of `f s` in chart-of-`TM`-at-`⟨α, 0⟩` source.
  have hf_chsrc : f s ∈ (chartAt (ModelProd H E) q₀).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α (f s)).mpr hs_src
  have hf_extsrc : f s ∈ (extChartAt I.tangent q₀).source := by
    rw [extChartAt_source]; exact hf_chsrc
  -- Mirror Mathlib's proof of `IsMIntegralCurveAt.eventually_hasDerivAt`,
  -- with the running chart base `γ t₀` replaced by the fixed `q₀ := ⟨α, 0⟩`.
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp s (hasMFDerivAt_extChartAt (I := I.tangent) hf_chsrc)
    hHas).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hf_chsrc]
  -- Goal: `(smulRight 1 (tangentCoordChange I.tangent (f s) q₀ (f s) (gvf g α (f s)))) (1 a)
  --        = (toSpanSingleton ℝ (chartPhaseVF g α (extChartAt I.tangent q₀ (f s)))) (1 a)`.
  -- Unfold `q₀ = ⟨α, 0⟩` to enable the chart-of-`TM` identifications.
  rw [hq₀_def]
  -- Simplify both CLM applications to `a • v` (`1 a = a` and both forms reduce).
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
  congr 1
  -- Show both sides equal `geodesicVectorFieldChartFiber g α (f s)`.
  trans (geodesicVectorFieldChartFiber (I := I) g α (f s))
  · exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f s) hs_src
  · symm
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hs_src]
    rfl

end ChartPhaseAtZeroSection

/-! ## Local integral curve at a generic time `s₀`

For each `s₀ ∈ Ioo (-T) T`, the lift `F_v := chartFlowOrbitLift Φ p v`
agrees, near `s₀`, with a local Picard–Lindelöf integral curve of
`geodesicVectorFieldChart g p` at `s₀`. The agreement is proved by
chart-coordinate ODE uniqueness in the fixed chart at `⟨p, 0⟩`. -/

section LocalLiftAtsZero

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Local existence of a tangent-bundle integral curve at a given
phase-space point.** For any `q : TangentBundle I M` whose projection
lies in `(chartAt H α).source`, and any base time `s₀ : ℝ`, there exists
a curve `g_loc : ℝ → TangentBundle I M` with `g_loc s₀ = q` and
`IsMIntegralCurveAt g_loc (gvf...) s₀`. -/
private lemma exists_local_lift_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {q : TangentBundle I M}
    (hq : q.proj ∈ (chartAt H α).source) (s₀ : ℝ) :
    ∃ g_loc : ℝ → TangentBundle I M,
      g_loc s₀ = q ∧
      IsMIntegralCurveAt g_loc (geodesicVectorFieldChart (I := I) g α) s₀ := by
  classical
  -- Smoothness of the chart-fixed geodesic VF at `q`.
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g α w⟩ :
          TangentBundle I.tangent (TangentBundle I M))) q :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g α (p₀ := q) hq
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g α w⟩ :
          TangentBundle I.tangent (TangentBundle I M))) q :=
    hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (t₀ := s₀) (x₀ := q) hsmooth1

/-- **Identification of the local lift with `F_v` near `s₀`.** Under the
chart-target-interior confinement of the orbit and the chart-phase ODE
on the orbit at `s₀`, the local lift `g_loc` agrees with the manifold
lift `F_v` on a neighbourhood of `s₀`.

The agreement is proved by applying `chartPhaseVF_orbit_uniqueness` to
the chart-coordinate curve `c_p ∘ g_loc` (from
`eventually_hasDerivAt_chartPhaseVF_at_zero_section`) and the orbit
`c(s) := Φ((x₀, v), s)`, both of which solve the chart-phase ODE near
`s₀` with matching values at `s₀`. -/
private lemma local_lift_eventuallyEq_chartFlowOrbitLift
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {Φ : (E × E) × ℝ → E × E} {s₀ : ℝ}
    (hΦ_target_s₀ : Φ (((extChartAt I p p, v) : E × E), s₀) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_chart_phase : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    {g_loc : ℝ → TangentBundle I M}
    (hg_loc_s₀ : g_loc s₀ = chartFlowOrbitLift (I := I) Φ p v s₀)
    (hg_loc_int : IsMIntegralCurveAt g_loc
      (geodesicVectorFieldChart (I := I) g p) s₀) :
    g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLift (I := I) Φ p v := by
  classical
  -- `(F_v s₀).proj ∈ (chartAt H p).source` from chart-target-interior of orbit.
  have hF_s₀_src : (chartFlowOrbitLift (I := I) Φ p v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLift_proj_mem_chartAt_source (I := I) p v s₀ hΦ_target_s₀
  -- Same for `g_loc s₀`.
  have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H p).source := by
    rw [hg_loc_s₀]; exact hF_s₀_src
  -- Chart-`⟨p, 0⟩`-pushed derivative of `g_loc` near `s₀`.
  have hd_gloc :=
    eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
      (g := g) (α := p) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
  -- We define the two chart-coord candidate solutions.
  -- c₁(τ) := extChartAt I.tangent ⟨p, 0⟩ (g_loc (s₀ + τ)).
  -- c₂(τ) := Φ((x₀, v), s₀ + τ).
  -- Both solve the chart-phase ODE near τ = 0 with matching value at τ = 0.
  set c₁ : ℝ → E × E := fun τ : ℝ =>
    extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) with hc₁_def
  set c₂ : ℝ → E × E := fun τ : ℝ =>
    Φ (((extChartAt I p p, v) : E × E), s₀ + τ) with hc₂_def
  -- z₀ := common value at τ = 0.
  set z₀ : E × E := Φ (((extChartAt I p p, v) : E × E), s₀) with hz₀_def
  have hz₀_interior : z₀ ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := hΦ_target_s₀
  -- c₂ 0 = z₀.
  have hc₂_zero : c₂ 0 = z₀ := by
    change Φ (((extChartAt I p p, v) : E × E), s₀ + 0) =
      Φ (((extChartAt I p p, v) : E × E), s₀)
    rw [add_zero]
  -- c₁ 0 = z₀: from g_loc s₀ = F_v s₀ and chartFlowOrbitLift's defining
  -- inverse-chart identity, `extChartAt I.tangent ⟨p, 0⟩ (F_v s₀) = (Φ orbit) s₀`.
  have hc₁_zero : c₁ 0 = z₀ := by
    change extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + 0)) =
      Φ (((extChartAt I p p, v) : E × E), s₀)
    rw [add_zero, hg_loc_s₀]
    -- Goal: extChartAt I.tangent ⟨p, 0⟩ (F_v s₀) = Φ((x₀, v), s₀).
    unfold chartFlowOrbitLift
    exact extChartAt_tangent_zero_apply_symm (I := I) p hΦ_target_s₀
  -- c₂ satisfies chart-phase ODE near 0 (via time-shift of hΦ_chart_phase).
  have hd_c₂ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g p (c₂ τ)) τ ∧
      c₂ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have htranslate : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
      have h1 : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) := h1
      simpa using this
    have hev := htranslate.eventually hΦ_chart_phase
    filter_upwards [hev] with τ hτ
    obtain ⟨hτD, hτT⟩ := hτ
    refine ⟨?_, hτT⟩
    -- hτD : HasDerivAt (fun s' => Φ((x₀, v), s')) (chartPhaseVF g p (Φ((x₀, v), s₀+τ))) (s₀+τ).
    -- We want: HasDerivAt c₂ (chartPhaseVF g p (c₂ τ)) τ.
    -- c₂ τ = Φ((x₀, v), s₀+τ) and c₂ is the composition with τ ↦ s₀+τ.
    have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add s₀
    have hcomp := hτD.scomp τ h_shift
    -- hcomp : HasDerivAt ((fun s' => Φ((x₀, v), s')) ∘ (fun τ => s₀ + τ))
    --         (1 • chartPhaseVF g p (Φ((x₀, v), s₀+τ))) τ
    simp only [one_smul] at hcomp
    convert hcomp using 1
  -- c₁ satisfies chart-phase ODE near 0 (via time-shift of hd_gloc).
  have hd_c₁ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g p (c₁ τ)) τ ∧
      c₁ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    -- We need to combine the chart-phase derivative for g_loc (at base time s₀)
    -- with chart-target interior containment, which we'll deduce from continuity.
    -- Continuity of c₁ at 0 + value at 0 = z₀ ∈ interior * univ.
    have hπ_cont : Continuous
        (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    -- c₁ continuous near 0 (chart-of-TM is continuous on chart source).
    -- We need eventual chart-target-interior of c₁.
    -- c₁ τ = extChartAt I.tangent ⟨p, 0⟩ (g_loc (s₀+τ)). This lies in target =
    -- (extChartAt I p).target ∩ ... ×ˢ univ. For "interior of target", we
    -- need (c₁ τ).1 ∈ interior (extChartAt I p).target.
    -- By extChartAt_target_subset_interior_of_boundaryless under [I.Boundaryless].
    have hc₁_target_int : ∀ᶠ τ in 𝓝 (0 : ℝ),
        c₁ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      -- We need (g_loc (s₀+τ)).proj ∈ (chartAt H p).source eventually.
      have hcomp : ContinuousAt (fun τ : ℝ => (g_loc (s₀ + τ)).proj) 0 := by
        have h_shift : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
          (continuous_const.add continuous_id).continuousAt
        have h_gloc_at : ContinuousAt g_loc (s₀ + 0) := by
          rw [add_zero]; exact hg_loc_int.continuousAt
        exact hπ_cont.continuousAt.comp (h_gloc_at.comp h_shift)
      have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
      have hp_nhds : (chartAt H p).source ∈ 𝓝 ((g_loc s₀).proj) := by
        apply hp_open.mem_nhds
        rw [hg_loc_s₀]; exact hF_s₀_src
      have hval0 : (g_loc (s₀ + 0)).proj = (g_loc s₀).proj := by
        rw [add_zero]
      have hpre : (fun τ : ℝ => (g_loc (s₀ + τ)).proj) ⁻¹'
          (chartAt H p).source ∈ 𝓝 (0 : ℝ) := by
        apply hcomp.preimage_mem_nhds
        rw [hval0]; exact hp_nhds
      filter_upwards [hpre] with τ hτ
      -- (g_loc (s₀+τ)).proj ∈ chart source ⟹ c₁ τ ∈ interior target ×ˢ univ.
      have hpair :
          extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) =
            (extChartAt I p (g_loc (s₀ + τ)).proj,
              chartFiberCoord (I := I) p (g_loc (s₀ + τ))) :=
        extChartAt_tangent_zero_apply_chartFiber (I := I) p hτ
      refine ⟨?_, Set.mem_univ _⟩
      show (c₁ τ).1 ∈ _
      have h_c₁_val : c₁ τ =
          (extChartAt I p (g_loc (s₀ + τ)).proj,
            chartFiberCoord (I := I) p (g_loc (s₀ + τ))) := hpair
      rw [h_c₁_val]
      change extChartAt I p (g_loc (s₀ + τ)).proj ∈ _
      -- extChartAt I p (g_loc (s₀+τ)).proj ∈ interior target via boundarylessness.
      have h_extsrc : (g_loc (s₀ + τ)).proj ∈ (extChartAt I p).source := by
        rw [extChartAt_source]; exact hτ
      have h_target : extChartAt I p (g_loc (s₀ + τ)).proj ∈ (extChartAt I p).target :=
        (extChartAt I p).map_source h_extsrc
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
    -- Chart-phase derivative of c₁ via time-shift.
    have htranslate : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
      have h1 : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) := h1
      simpa using this
    have hd_gloc_shift := htranslate.eventually hd_gloc
    filter_upwards [hd_gloc_shift, hc₁_target_int] with τ hτD hτT
    refine ⟨?_, hτT⟩
    -- hτD : HasDerivAt (fun s' => extChartAt I.tangent ⟨p, 0⟩ (g_loc s'))
    --        (chartPhaseVF g p (extChartAt I.tangent ⟨p, 0⟩ (g_loc (s₀+τ)))) (s₀+τ).
    -- Want: HasDerivAt c₁ (chartPhaseVF g p (c₁ τ)) τ.
    have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add s₀
    have hcomp := hτD.scomp τ h_shift
    simp only [one_smul] at hcomp
    convert hcomp using 1
  -- Apply `chartPhaseVF_orbit_uniqueness` to c₁, c₂.
  have hc_eq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
      (c₁ := c₁) (c₂ := c₂) (z₀ := z₀) hz₀_interior hc₁_zero hc₂_zero hd_c₁ hd_c₂
  -- Translate `hc_eq` (in τ at 0) into `g_loc =ᶠ F_v` (in s at s₀).
  -- For τ near 0, c₁ τ = c₂ τ, which when inverted gives g_loc(s₀+τ) = F_v(s₀+τ).
  -- We need to convert the eventually-equality at 0 in τ to the equality at s₀ in s.
  have htranslate_inv : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
    have h1 : ContinuousAt (fun s : ℝ => s - s₀) s₀ :=
      (continuous_id.sub continuous_const).continuousAt
    have : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) := h1
    simpa using this
  -- Apply: pull back hc_eq via τ ↦ s - s₀.
  have hc_eq_in_s : ∀ᶠ s in 𝓝 s₀, c₁ (s - s₀) = c₂ (s - s₀) := htranslate_inv.eventually hc_eq
  -- We also need the chart-target-interior of the orbit eventually near s₀.
  -- and (g_loc s).proj ∈ chart-p source eventually near s₀.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H p).source := by
    have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
      hπ_cont.continuousAt.comp hg_loc_int.continuousAt
    have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
    apply hcomp.preimage_mem_nhds
    rw [show (g_loc s₀).proj = (chartFlowOrbitLift (I := I) Φ p v s₀).proj
      from by rw [hg_loc_s₀]]
    exact hp_open.mem_nhds hF_s₀_src
  -- Orbit chart-target-interior near s₀ (only need it).
  have hΦ_target_ev : ∀ᶠ s in 𝓝 s₀,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hΦ_chart_phase] with s hs
    exact hs.2
  -- Combine the three filters.
  filter_upwards [hc_eq_in_s, hgloc_proj_src, hΦ_target_ev] with s hs_c_eq hs_gloc_src hs_orbit_t
  -- We want g_loc s = F_v s.
  -- We have hs_c_eq : c₁ (s - s₀) = c₂ (s - s₀).
  -- c₁ (s - s₀) = extChartAt I.tangent ⟨p, 0⟩ (g_loc (s₀ + (s - s₀)))
  --             = extChartAt I.tangent ⟨p, 0⟩ (g_loc s).
  -- c₂ (s - s₀) = Φ((x₀, v), s).
  -- So extChartAt I.tangent ⟨p, 0⟩ (g_loc s) = Φ((x₀, v), s).
  have hs_ext_eq :
      extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) =
        Φ (((extChartAt I p p, v) : E × E), s) := by
    have h₁ : c₁ (s - s₀) =
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) := by
      simp [hc₁_def, add_sub_cancel]
    have h₂ : c₂ (s - s₀) = Φ (((extChartAt I p p, v) : E × E), s) := by
      simp [hc₂_def, add_sub_cancel]
    rw [← h₁, hs_c_eq, h₂]
  -- Apply (.symm) to both sides at `Φ((x₀, v), s) ∈ target`.
  have h_F_v_eq :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (Φ (((extChartAt I p p, v) : E × E), s)) =
      chartFlowOrbitLift (I := I) Φ p v s := rfl
  -- g_loc s ∈ source of chart-of-TM-at-⟨p, 0⟩.
  have hgloc_chsrc : g_loc s ∈
      (chartAt (ModelProd H E) (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) p (g_loc s)).mpr hs_gloc_src
  have hgloc_extsrc : g_loc s ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hgloc_chsrc
  have hleft :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s)) = g_loc s :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv hgloc_extsrc
  rw [← hleft, hs_ext_eq]
  rfl

end LocalLiftAtsZero

/-! ## Headline: integral curve at every point of the uniform interval -/

section IntegralCurveOnIoo

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **`F_v` is a local integral curve at every `s₀ ∈ Ioo (-T) T`.** Under
the chart-target-interior confinement of the orbit on `Icc (-T) T` and
the chart-phase ODE on `Ioo (-T) T`, the manifold lift
`F_v := chartFlowOrbitLift Φ p v` is `IsMIntegralCurveAt
(geodesicVectorFieldChart g p) s₀` at every interior point `s₀`. -/
theorem chartFlowOrbitLift_isMIntegralCurveAt_of_mem_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) {T : ℝ}
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-T) T) :
    IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) s₀ := by
  classical
  -- Get the local Picard-Lindelöf lift at `F_v s₀`.
  have hF_s₀_src : (chartFlowOrbitLift (I := I) Φ p v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLift_proj_mem_chartAt_source (I := I) p v s₀
      (hΦ_target_Icc s₀ (Set.Ioo_subset_Icc_self hs₀))
  obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
    exists_local_lift_at (I := I) (g := g) (α := p) (q := chartFlowOrbitLift (I := I) Φ p v s₀)
      hF_s₀_src s₀
  -- Build the chart-phase ODE eventually-near-`s₀` hypothesis from `Ioo (-T) T`.
  have hΦ_chart_phase : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 s₀ := isOpen_Ioo.mem_nhds hs₀
    filter_upwards [hIoo_nhds] with s hs
    refine ⟨hΦ_phase_Ioo s hs, ?_⟩
    exact hΦ_target_Icc s (Set.Ioo_subset_Icc_self hs)
  -- Apply the eventually-equality lemma.
  have h_eq : g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLift (I := I) Φ p v :=
    local_lift_eventuallyEq_chartFlowOrbitLift (I := I) (g := g) (p := p) (v := v)
      (Φ := Φ) (s₀ := s₀)
      (hΦ_target_Icc s₀ (Set.Ioo_subset_Icc_self hs₀)) hΦ_chart_phase
      hg_loc_s₀ hg_loc_int
  -- Transfer IsMIntegralCurveAt g_loc ... s₀ to F_v via the eventual equality.
  rw [IsMIntegralCurveAt] at hg_loc_int ⊢
  filter_upwards [hg_loc_int, h_eq, h_eq.eventually_nhds] with s hs_int hs_eq hs_eq_nhds
  -- Goal: HasMFDerivAt% F_v s (smulRight 1 (gvf g p (F_v s))).
  -- hs_int gives this for g_loc. Use hs_eq : g_loc s = F_v s.
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with x hx
  exact hx.symm

/-- **Headline: `F_v` is an `IsMIntegralCurveOn` on `Ioo (-T) T`.** -/
theorem chartFlowOrbitLift_isMIntegralCurveOn_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) {T : ℝ}
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s) :
    IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T) := by
  apply IsMIntegralCurveAt.isMIntegralCurveOn
  intro s₀ hs₀
  exact chartFlowOrbitLift_isMIntegralCurveAt_of_mem_Ioo (I := I) g p v
    hΦ_target_Icc hΦ_phase_Ioo hs₀

end IntegralCurveOnIoo

/-! ## Headline R.D.3.a packaging

We combine the R.D.1 uniform data with the integral-curve-on-`Ioo`
property into a single existential packaging. -/

section HeadlineRD3a

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Headline R.D.3.a — `F_v` is an integral curve on the full uniform
interval, uniformly in `v`.** There exist a chart-pushed flow
`Φ : (E × E) × ℝ → E × E` and uniform radii `(ρ, T) > 0` such that, for
every `v ∈ Metric.ball (0 : E) ρ`:

* all R.D.1 manifold-lift data is available on `Ioo (-T) T`;
* the chart-coordinate orbit satisfies the genuine chart-phase ODE on
  `Ioo (-T) T`;
* the manifold lift `F_v := chartFlowOrbitLift Φ p v` starts at
  `⟨p, v⟩` at `s = 0`;
* **`F_v` is an `IsMIntegralCurveOn` of `geodesicVectorFieldChart g p`
  on the entire `Ioo (-T) T`** (the upgrade from R.D.1's
  `IsMIntegralCurveAt … 0`). -/
theorem exists_chartFlowOrbitLift_isMIntegralCurveOn_Ioo_data
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        chartFlowOrbitLift (I := I) Φ p v 0 =
          (⟨p, v⟩ : TangentBundle I M)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T)) := by
  classical
  -- Invoke R.D.1's uniform data.
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0,
    _hF_proj, _hF_chartPush, _hF_int⟩ :=
    exists_chartFlowOrbitLift_data_uniform (I := I) (g := g) (p := p)
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0, ?_⟩
  intro v hv
  exact chartFlowOrbitLift_isMIntegralCurveOn_Ioo (I := I) g p v
    (hΦ_target v hv) (hΦ_phase v hv)

end HeadlineRD3a

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
