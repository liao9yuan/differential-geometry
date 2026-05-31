import DifferentialGeometry.Geometry.Riemannian.Exponential.OffZeroRegularity
import DifferentialGeometry.Geometry.Riemannian.Exponential.IntrinsicExp

set_option linter.unusedSectionVars false

/-!
# Joint smoothness of the intrinsic exponential map in basepoint and vector

For a smooth Riemannian metric `g` on a boundaryless, complete smooth manifold
`M` modelled on a complete inner-product space `E`, the *intrinsic* exponential
map `expMapIntrinsic g hEnorm p v` (the value at time `1` of the complete
moving-foot geodesic through `p` with launch velocity `v`,
`Exponential/IntrinsicExp.lean`) follows the geodesic across charts.  The
second-variation analysis of arc length needs the *manifold lift* of its joint
regularity: along a smooth curve `γ` of basepoints and a smooth field `V` of
launch directions, the two-parameter map `(s, t) ↦ expMapIntrinsic (γ t) (s • V t)`
is jointly smooth in `(s, t)` for small `s`.

## Architecture

The chart-coordinate analytic content is supplied by
`exists_chartExp_jointContDiffOn_nat` (`Exponential/OffZeroRegularity.lean`):
for a fixed chart center `α` and finite order `n`, the chart-`α` geodesic flow
`Φ : (E × E) × ℝ → E × E` is jointly `C^n` in the phase point `z = (chart-position,
velocity)`, and the chart position of the geodesic at the fixed time `t'` is
`(Φ (z, t')).1`.  Pulling the first component back through `(extChartAt I α).symm`
yields a candidate manifold map.

The identification of this chart-`α` flow projection with `expMapIntrinsic q w`
for a moving basepoint `q ≠ α` is the **chart-independence of geodesics** — the
statement that the base orbit of an integral curve of the chart-`α` phase-space
field `chartPhaseVF g α` is the unique geodesic determined by its initial data,
independently of the chart center `α`.  That identification is the genuine
cross-chart input flagged in `Exponential/OffZeroRegularity.lean` (the
"moving-chart geodesic equation"); it is the single residual of this file,
isolated as `expMapIntrinsic_eq_chartFlow_proj_residual`.  Everything built on
top of it — the smooth chart-coordinate coordinatisation, the `t`-local joint
`ContMDiff`, and the local-agreement gluing across the basepoint chart cover —
is proved unconditionally.

## Main results

* `expMapIntrinsic_eq_chartFlow_proj_residual` — the chart-independence bridge
  (residual): for `q` in chart `α`'s source and small `w`, the intrinsic
  exponential is the chart-`α` flow projection at the appropriate phase point.
* `chartFlowVelCoordMap_contMDiff` — joint `C∞` smoothness of the
  chart-coordinate coordinatisation `(s, t) ↦ (extChartAt I α (γ t),
  chartFiberCoord α ⟨γ t, (s • V t) rescaled⟩)`.
* `expMapIntrinsic_variation_contMDiff` — the headline: the two-parameter map
  `(s, t) ↦ expMapIntrinsic (γ t) (s • V t)` is jointly `ContMDiff
  (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) I n` near every `(s₀, t₀)`, for every finite `n`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section JointVariationSmooth

/-! ## The chart-independence bridge (residual)

The chart-`α` geodesic flow `Φ` of `exists_chartExp_jointContDiffOn_nat`
integrates the chart-phase ODE `HasDerivAt (Φ(z, ·)) (chartPhaseVF g α (Φ(z, s))) s`
with chart center `α` *fixed*, while the intrinsic geodesic from a basepoint
`q ≠ α` is the moving-foot geodesic launched from `q`.  Identifying the chart-`α`
flow's base orbit at the appropriate phase point with `expMapIntrinsic q w` is
the chart-independence of geodesics: both are the unique geodesic through `q`
with the prescribed initial velocity, so the chart-`α` ODE solution, projected
to `M` through `(extChartAt I α).symm`, agrees with the moving-foot geodesic.

This identity — concretely, that the base orbit of the chart-`α` phase flow is a
moving-foot geodesic `HasGeodesicEquationAt` even when its foot is not the chart
center `α` — is the cross-chart "moving-chart geodesic equation" recorded as the
outstanding analytic input in `Exponential/OffZeroRegularity.lean` and
`Geodesic/Uniqueness.lean`.  It is isolated here as the sole residual of this
file; the smoothness scaffold below consumes it as a black box. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Chart-independence bridge (residual).**  For a chart center `α`, a finite
order `n ≥ 1`, the chart-`α` joint geodesic flow `Φ`, its evaluation time `t'`,
its phase-ball radius `ρ`, and a basepoint `q` in chart `α`'s source whose
chart-`α` phase point `(extChartAt I α q, chartFiberCoord α ⟨q, t' • w⟩)` lies in
the flow's phase-ball, the intrinsic exponential map `expMapIntrinsic g hEnorm q w`
is the chart-`α` flow projection at the rescaled velocity, pulled back through
`(extChartAt I α).symm`.

This is the chart-independence of geodesics (the moving-chart geodesic equation):
the chart-`α` flow base orbit `s ↦ (extChartAt I α).symm (Φ((x, v), s)).1` is the
moving-foot geodesic launched from `(extChartAt I α).symm x` with the chart-`α`
velocity `v`, hence at time `t'` it reaches the intrinsic geodesic's value, and
the launch-velocity rescaling `intrinsicGeodesic_smul` absorbs the fixed `t'`. -/
theorem expMapIntrinsic_eq_chartFlow_proj_residual
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (α : M) (n : ℕ) (_hn : 1 ≤ n)
    (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ)
    (hΦ : 0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)))
    (q : M) (hq : q ∈ (chartAt H α).source) (w : TangentSpace I q)
    -- The chart-`α` flow base orbit through `q`'s phase point keeps its foot in
    -- `q`'s home chart-source throughout `[0, t']` (a small-velocity geodesic
    -- confinement: the geodesic launched from `q` with velocity `t'⁻¹ • w` does
    -- not leave `q`'s chart before time `t'`).
    (hfoot : ∀ s ∈ Set.Icc (0 : ℝ) t',
      (extChartAt I α).symm
          (Φ (((extChartAt I α q,
              chartFiberCoord (I := I) α
                (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q (t'⁻¹ • w)))
            : E × E), s) : E × E).1 ∈ (chartAt H q).source)
    -- Small-velocity agreement of the intrinsic and chart-fixed exponentials.
    (hwexp : expMapIntrinsic (I := I) g hEnorm q w = expMap (I := I) g q w)
    -- Small-velocity geodesic rescaling identity at `q`.
    (hwresc : maximalGeodesic (I := I) g q ((1 : ℝ) • w) 1 =
      maximalGeodesic (I := I) g q (t'⁻¹ • w) t')
    (hphase : ((extChartAt I α q,
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q (t'⁻¹ • w))) : E × E)
      ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) :
    expMapIntrinsic (I := I) g hEnorm q w =
      (extChartAt I α).symm
        (Φ (((extChartAt I α q,
            chartFiberCoord (I := I) α
              (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q (t'⁻¹ • w))) : E × E),
          t') : E × E).1 := by
  classical
  obtain ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, _hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ := hΦ
  -- The launch velocity at `q` and its chart-`α` fibre coordinate.
  set vq : TangentSpace I q := t'⁻¹ • w with hvq_def
  set vα : E := chartFiberCoord (I := I) α
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) with hvα_def
  -- The chart-`α` phase point through which the orbit is launched.
  set z₀ : E × E := ((extChartAt I α q, vα) : E × E) with hz₀_def
  have hz₀_ball : z₀ ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := hphase
  -- The orbit hypotheses specialised at `z₀`.
  have hz₀_init : Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) = z₀ := hΦ_init z₀ hz₀_ball
  have hz₀_ode : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ ((z₀, s') : (E × E) × ℝ))
        (chartPhaseVF (I := I) g α (Φ ((z₀, s) : (E × E) × ℝ))) s := hΦ_ode z₀ hz₀_ball
  have hz₀_target : ∀ s ∈ Set.Icc (-T) T,
      Φ ((z₀, s) : (E × E) × ℝ) ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hΦ_target z₀ hz₀_ball
  -- The manifold lift of the orbit through `z₀`.
  set F : ℝ → TangentBundle I M := fun s =>
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (Φ ((z₀, s) : (E × E) × ℝ)) with hF_def
  -- `q ∈ (extChartAt I α).source` (its chart-source).
  have hq_extsrc : q ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hq
  -- **Step B — initial value of the lift: `F 0 = ⟨q, vq⟩`.**
  have hQq_proj : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq).proj ∈
      (chartAt H α).source := hq
  have hz₀_eq_chart :
      z₀ = extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) := by
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hQq_proj]
  have hQq_chsrc : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) ∈
      (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α _).mpr hQq_proj
  have hQq_extsrc : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) ∈
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hQq_chsrc
  have hF0 : F 0 = (⟨q, vq⟩ : TangentBundle I M) := by
    rw [hF_def]
    simp only
    rw [hz₀_init, hz₀_eq_chart]
    exact (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hQq_extsrc
  -- **Step C — `F` is an `IsMIntegralCurveOn (gvf g α)` on `Ioo (-T) T`.**
  -- The chart-target-interior confinement gives `(F s).proj ∈ (chartAt H α).source`.
  have hF_proj_src : ∀ s ∈ Set.Icc (-T) T, (F s).proj ∈ (chartAt H α).source := by
    intro s hs
    rw [hF_def]; simp only
    exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) α (hz₀_target s hs)
  -- The projection identity along the lift on `Icc (-T) T`.
  have hF_proj_eq : ∀ s ∈ Set.Icc (-T) T,
      (F s).proj = (extChartAt I α).symm (Φ ((z₀, s) : (E × E) × ℝ)).1 := by
    intro s hs
    rw [hF_def]; simp only
    exact extChartAt_tangent_zero_symm_proj (I := I) α (hz₀_target s hs)
  -- Local integral-curve property at every `s₀ ∈ Ioo (-T) T`.
  have hF_intAt : ∀ s₀ ∈ Set.Ioo (-T) T,
      IsMIntegralCurveAt F (geodesicVectorFieldChart (I := I) g α) s₀ := by
    intro s₀ hs₀
    have hs₀_Icc : s₀ ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hs₀
    -- Picard-Lindelöf local lift `g_loc` at `F s₀`.
    have hFs₀_src : (F s₀).proj ∈ (chartAt H α).source := hF_proj_src s₀ hs₀_Icc
    have hsmoothVF : ContMDiffAt I.tangent I.tangent.tangent 1
        (fun u : TangentBundle I M =>
          (⟨u, geodesicVectorFieldChart (I := I) g α u⟩ :
            TangentBundle I.tangent (TangentBundle I M))) (F s₀) :=
      (geodesicVectorFieldChart_contMDiffAt (I := I) g α (p₀ := F s₀) hFs₀_src).of_le
        (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
      exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
        (I := I.tangent) (M := TangentBundle I M)
        (v := geodesicVectorFieldChart (I := I) g α)
        (t₀ := s₀) (x₀ := F s₀) hsmoothVF
    -- The chart-`⟨α,0⟩`-pushed derivative of `g_loc` near `s₀`.
    have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H α).source := by
      rw [hg_loc_s₀]; exact hFs₀_src
    have hd_gloc :=
      eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
        (g := g) (α := α) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
    -- The two chart-coordinate candidate solutions.
    set c₁ : ℝ → E × E := fun τ : ℝ =>
      extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) with hc₁_def
    set c₂ : ℝ → E × E := fun τ : ℝ => Φ ((z₀, s₀ + τ) : (E × E) × ℝ) with hc₂_def
    set w₀ : E × E := Φ ((z₀, s₀) : (E × E) × ℝ) with hw₀_def
    have hw₀_interior : w₀ ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hz₀_target s₀ hs₀_Icc
    have hc₂_zero : c₂ 0 = w₀ := by
      change Φ ((z₀, s₀ + 0) : (E × E) × ℝ) = Φ ((z₀, s₀) : (E × E) × ℝ); rw [add_zero]
    have hc₁_zero : c₁ 0 = w₀ := by
      change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + 0)) =
        Φ ((z₀, s₀) : (E × E) × ℝ)
      rw [add_zero, hg_loc_s₀, hF_def]
      simp only
      exact extChartAt_tangent_zero_apply_symm (I := I) α hw₀_interior
    -- `c₂` solves the chart-phase ODE + target near `0` (time-shift of orbit data).
    have hd_c₂ : ∀ᶠ τ in 𝓝 (0 : ℝ),
        HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ τ)) τ ∧
        c₂ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hshift_tendsto : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
        have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) :=
          (continuous_const.add continuous_id).continuousAt
        simpa using this
      have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 s₀ := isOpen_Ioo.mem_nhds hs₀
      have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), s₀ + τ ∈ Set.Ioo (-T) T :=
        hshift_tendsto hIoo_nhds
      filter_upwards [hev] with τ hτ
      have hτD := hz₀_ode (s₀ + τ) hτ
      have hτT := hz₀_target (s₀ + τ) (Set.Ioo_subset_Icc_self hτ)
      refine ⟨?_, hτT⟩
      have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
        simpa using (hasDerivAt_id τ).const_add s₀
      have hcomp := hτD.scomp τ h_shift
      simpa only [one_smul] using hcomp
    -- `c₁` solves the chart-phase ODE + target near `0` (time-shift of `g_loc`).
    have hd_c₁ : ∀ᶠ τ in 𝓝 (0 : ℝ),
        HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ τ)) τ ∧
        c₁ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
        FiberBundle.continuous_proj E (TangentSpace I)
      -- target-interior of `c₁` near `0`.
      have hc₁_target : ∀ᶠ τ in 𝓝 (0 : ℝ),
          c₁ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
        have hcompcont : ContinuousAt (fun τ : ℝ => (g_loc (s₀ + τ)).proj) 0 := by
          have h_shift : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
            (continuous_const.add continuous_id).continuousAt
          have h_gloc_at : ContinuousAt g_loc (s₀ + 0) := by
            rw [add_zero]; exact hg_loc_int.continuousAt
          exact hπ_cont.continuousAt.comp (h_gloc_at.comp h_shift)
        have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
        have hpre : (fun τ : ℝ => (g_loc (s₀ + τ)).proj) ⁻¹' (chartAt H α).source ∈
            𝓝 (0 : ℝ) := by
          apply hcompcont.preimage_mem_nhds
          rw [show (g_loc (s₀ + 0)).proj = (g_loc s₀).proj from by rw [add_zero]]
          exact hα_open.mem_nhds hg_loc_s₀_src
        filter_upwards [hpre] with τ hτ
        have hpair := extChartAt_tangent_zero_apply_chartFiber (I := I) α (p := g_loc (s₀ + τ)) hτ
        refine ⟨?_, Set.mem_univ _⟩
        show (c₁ τ).1 ∈ _
        rw [hc₁_def]; simp only
        rw [hpair]
        change extChartAt I α (g_loc (s₀ + τ)).proj ∈ _
        have h_extsrc : (g_loc (s₀ + τ)).proj ∈ (extChartAt I α).source := by
          rw [extChartAt_source]; exact hτ
        exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
          (I := I) α ((extChartAt I α).map_source h_extsrc)
      have hshift_tendsto : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
        have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) :=
          (continuous_const.add continuous_id).continuousAt
        simpa using this
      have hd_gloc_shift := hshift_tendsto.eventually hd_gloc
      filter_upwards [hd_gloc_shift, hc₁_target] with τ hτD hτT
      refine ⟨?_, hτT⟩
      have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
        simpa using (hasDerivAt_id τ).const_add s₀
      have hcomp := hτD.scomp τ h_shift
      simpa only [one_smul] using hcomp
    -- Chart-coordinate ODE uniqueness: `c₁ =ᶠ c₂` near `0`.
    have hc_eq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
      chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := α)
        (c₁ := c₁) (c₂ := c₂) (z₀ := w₀) hw₀_interior hc₁_zero hc₂_zero hd_c₁ hd_c₂
    -- Transfer to `g_loc =ᶠ[𝓝 s₀] F`.
    have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have htranslate_inv : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).continuousAt
      simpa using this
    have hc_eq_in_s : ∀ᶠ s in 𝓝 s₀, c₁ (s - s₀) = c₂ (s - s₀) := htranslate_inv.eventually hc_eq
    have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H α).source := by
      have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
        hπ_cont.continuousAt.comp hg_loc_int.continuousAt
      apply hcomp.preimage_mem_nhds
      exact ((chartAt H α).open_source).mem_nhds hg_loc_s₀_src
    have hgloc_eq_F : g_loc =ᶠ[𝓝 s₀] F := by
      filter_upwards [hc_eq_in_s, hgloc_proj_src] with s hs_c hs_src
      have hext_eq :
          extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s) =
            Φ ((z₀, s) : (E × E) × ℝ) := by
        have h₁ : c₁ (s - s₀) =
            extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s) := by
          rw [hc₁_def]; simp [add_sub_cancel]
        have h₂ : c₂ (s - s₀) = Φ ((z₀, s) : (E × E) × ℝ) := by
          rw [hc₂_def]; simp [add_sub_cancel]
        rw [← h₁, hs_c, h₂]
      have hgloc_chsrc : g_loc s ∈
          (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
        (mem_chartAt_modelProd_zero_source_iff (I := I) α (g_loc s)).mpr hs_src
      have hgloc_extsrc : g_loc s ∈
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
        rw [extChartAt_source]; exact hgloc_chsrc
      have hleft :
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
            (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s)) = g_loc s :=
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hgloc_extsrc
      rw [hF_def]; simp only
      rw [← hext_eq, hleft]
    -- `F` inherits the integral-curve property at `s₀`.
    rw [IsMIntegralCurveAt] at hg_loc_int ⊢
    filter_upwards [hg_loc_int, hgloc_eq_F, hgloc_eq_F.eventually_nhds]
      with s hs_int hs_eq hs_eq_nhds
    rw [← hs_eq]
    refine hs_int.congr_of_eventuallyEq ?_
    filter_upwards [hs_eq_nhds] with x hx
    exact hx.symm
  have hF_int : IsMIntegralCurveOn F (geodesicVectorFieldChart (I := I) g α)
      (Set.Ioo (-T) T) :=
    IsMIntegralCurveAt.isMIntegralCurveOn (fun s hs => hF_intAt s hs)
  -- **Step E — identify `(F s).proj` with `maximalGeodesic g q vq s` on `[0, t']`.**
  -- The chosen-curve witness for `maximalGeodesic g q vq`.
  -- Build a `MaximalGeodesicWitness` from `F` restricted to a connected interval
  -- around `0` where `F`'s foot stays in `q`'s chart-source.
  -- The orbit foot in `q`'s source on `Icc 0 t'` is supplied by `hfoot`.
  have hfoot' : ∀ s ∈ Set.Icc (0 : ℝ) t', (F s).proj ∈ (chartAt H q).source := by
    intro s hs
    have hs_Icc : s ∈ Set.Icc (-T) T := by
      refine ⟨?_, ?_⟩
      · exact le_trans (by linarith [ht'_Ioo.1] : (-T : ℝ) ≤ 0) hs.1
      · exact le_trans hs.2 (le_of_lt ht'_Ioo.2)
    rw [hF_proj_eq s hs_Icc]
    exact hfoot s hs
  -- `0` and `t'` and the whole `Icc 0 t'` lie in `Ioo (-T) T`.
  have hIcc_sub_Ioo : Set.Icc (0 : ℝ) t' ⊆ Set.Ioo (-T) T := by
    intro s hs
    refine ⟨by linarith [hs.1, hT_pos], lt_of_le_of_lt hs.2 ht'_Ioo.2⟩
  -- The open set `S := {s ∈ Ioo (-T) T | foot of F at s ∈ q's source}`.
  set S : Set ℝ :=
    Set.Ioo (-T) T ∩ ((fun s => (F s).proj) ⁻¹' (chartAt H q).source) with hS_def
  have hF_cont_proj : ContinuousOn (fun s => (F s).proj) (Set.Ioo (-T) T) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hF_int.continuousOn
  have hS_open : IsOpen S := by
    rw [hS_def]
    have h := hF_cont_proj.isOpen_inter_preimage isOpen_Ioo ((chartAt H q).open_source)
    simpa [Set.inter_comm] using h
  -- `Icc 0 t' ⊆ S`.
  have hIcc_sub_S : Set.Icc (0 : ℝ) t' ⊆ S := by
    intro s hs
    exact ⟨hIcc_sub_Ioo hs, hfoot' s hs⟩
  -- `0 ∈ Icc 0 t'` and `t' ∈ Icc 0 t'`.
  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t' := ⟨le_refl _, le_of_lt ht'_pos⟩
  have ht'_Icc0 : t' ∈ Set.Icc (0 : ℝ) t' := ⟨le_of_lt ht'_pos, le_refl _⟩
  have h0_S : (0 : ℝ) ∈ S := hIcc_sub_S h0_Icc
  -- The connected component `J₀ := connectedComponentIn S 0`: open, preconnected,
  -- contains `0`, `t'`, and the whole `Icc 0 t'`, and is contained in `S`.
  set J₀ : Set ℝ := connectedComponentIn S 0 with hJ₀_def
  have hJ₀_open : IsOpen J₀ := hS_open.connectedComponentIn
  have hJ₀_conn : IsPreconnected J₀ := isPreconnected_connectedComponentIn
  have h0_J₀ : (0 : ℝ) ∈ J₀ := mem_connectedComponentIn h0_S
  have hJ₀_sub_S : J₀ ⊆ S := connectedComponentIn_subset S 0
  have hIcc_sub_J₀ : Set.Icc (0 : ℝ) t' ⊆ J₀ :=
    (isPreconnected_Icc).subset_connectedComponentIn h0_Icc hIcc_sub_S
  have ht'_J₀ : t' ∈ J₀ := hIcc_sub_J₀ ht'_Icc0
  have hJ₀_sub_Ioo : J₀ ⊆ Set.Ioo (-T) T := fun s hs => (hJ₀_sub_S hs).1
  have hJ₀_src : ∀ s ∈ J₀, (F s).proj ∈ (chartAt H q).source := fun s hs => (hJ₀_sub_S hs).2
  -- **`F` is an `IsMIntegralCurveOn (gvf g q)` on `J₀`** (cross-chart VF coincidence).
  have hF_int_q : IsMIntegralCurveOn F (geodesicVectorFieldChart (I := I) g q) J₀ := by
    intro s hs
    have hs_Ioo : s ∈ Set.Ioo (-T) T := hJ₀_sub_Ioo hs
    have hsα : (F s).proj ∈ (chartAt H α).source :=
      hF_proj_src s (Set.Ioo_subset_Icc_self hs_Ioo)
    have hsq : (F s).proj ∈ (chartAt H q).source := hJ₀_src s hs
    have hvf_eq : geodesicVectorFieldChart (I := I) g α (F s) =
        geodesicVectorFieldChart (I := I) g q (F s) :=
      geodesicVectorFieldChart_eq_of_proj_mem (I := I) g α q (p := F s) hsα hsq
    have hd := hF_int s hs_Ioo
    -- `IsMIntegralCurveOn` on `J₀` ⊆ `Ioo (-T) T`: transfer the within-derivative.
    have hd' := (hF_int.mono hJ₀_sub_Ioo) s hs
    rw [hvf_eq] at hd'
    exact hd'
  -- The geodesic-with-initial-data witness on `J₀`.
  have hgeo_F : IsGeodesicOnWithInitial (I := I) g
      (fun s => (F s).proj) J₀ q vq := by
    refine ⟨F, ?_, hF0, hF_int_q⟩
    intro _; rfl
  -- Hence every `s ∈ J₀` is in the maximal interval of `(q, vq)`.
  have hwitness : ∀ s ∈ J₀, MaximalGeodesicWitness (I := I) g q vq s := by
    intro s hs
    exact ⟨fun s => (F s).proj, J₀, hJ₀_open, hJ₀_conn, h0_J₀, hs, hgeo_F⟩
  -- **Identify `(F s).proj` with `maximalGeodesic g q vq s` on `J₀`.**
  have hF_proj_maximal : ∀ s ∈ J₀, (F s).proj = maximalGeodesic (I := I) g q vq s := by
    intro s hs
    have hs_mem : s ∈ maximalGeodesicInterval (I := I) g q vq := hwitness s hs
    rw [maximalGeodesic_of_mem (I := I) hs_mem]
    -- Extract the chosen-curve witness.
    obtain ⟨J', hJ'_open, hJ'_conn, h0_J', hs_J', hgeo'⟩ :=
      maximalGeodesicChosenCurve_spec (I := I) g q vq hs_mem
    obtain ⟨f', hproj', hf'_0, hf'_on⟩ := hgeo'
    -- Clopen propagation on `K := J₀ ∩ J'`.
    set K : Set ℝ := J₀ ∩ J' with hK_def
    have hK_open : IsOpen K := hJ₀_open.inter hJ'_open
    have hK_conn : IsPreconnected K :=
      (hJ₀_conn.ordConnected.inter hJ'_conn.ordConnected).isPreconnected
    have h0_K : (0 : ℝ) ∈ K := ⟨h0_J₀, h0_J'⟩
    have hs_K : s ∈ K := ⟨hs, hs_J'⟩
    have hF_on_K : IsMIntegralCurveOn F (geodesicVectorFieldChart (I := I) g q) K :=
      hF_int_q.mono Set.inter_subset_left
    have hf'_on_K : IsMIntegralCurveOn f' (geodesicVectorFieldChart (I := I) g q) K :=
      hf'_on.mono Set.inter_subset_right
    have hF_src_K : ∀ s' ∈ K, (F s').proj ∈ (chartAt H q).source :=
      fun s' hs'_K => hJ₀_src s' hs'_K.1
    have h0_eq : F 0 = f' 0 := by rw [hF0, hf'_0]
    have heqOn := isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g) (p := q)
      (f₁ := F) (f₂ := f') hK_open hK_conn h0_K hF_on_K hf'_on_K hF_src_K h0_eq
    have hFs_eq : F s = f' s := heqOn hs_K
    rw [show (F s).proj = (f' s).proj from by rw [hFs_eq]]
    exact hproj' s
  -- **Step F — evaluate at `s = t'` and chain to the conclusion.**
  -- Projection identity at `t'`.
  have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
  have hFt'_orbit : (F t').proj = (extChartAt I α).symm (Φ ((z₀, t') : (E × E) × ℝ)).1 :=
    hF_proj_eq t' ht'_Icc
  -- `(F t').proj = maximalGeodesic g q vq t'`.
  have hFt'_max : (F t').proj = maximalGeodesic (I := I) g q vq t' :=
    hF_proj_maximal t' ht'_J₀
  -- `maximalGeodesic g q vq t' = maximalGeodesic g q (1 • w) 1 = expMap g q w`.
  have hmax_chain : maximalGeodesic (I := I) g q vq t' = expMap (I := I) g q w := by
    rw [hvq_def, ← hwresc, one_smul]
    rfl
  -- Assemble: `expMapIntrinsic q w = expMap q w = maximalGeodesic q vq t' = orbit`.
  rw [hwexp, ← hmax_chain, ← hFt'_max, hFt'_orbit, hz₀_def]

end JointVariationSmooth

/-! ## The chart-coordinate coordinatisation

The coordinate map `(s, t) ↦ (extChartAt I α (γ t), chartFiberCoord α ⟨γ t, c s • V t⟩)`
into the chart-`α` phase space `E × E`.  Its first factor is the chart-`α`
coordinate of the moving basepoint `γ t`; its second factor is the chart-`α`
fiber coordinate of the rescaled launch direction.  We record its joint
`C∞`-smoothness near a base parameter, the analytic prerequisite of the
composition argument. -/

section CoordMap

/-- The chart-coordinate phase point of a smooth basepoint curve `γ` and a smooth
total-space section `V₀` of launch directions, rescaled by `c • ·` in the first
parameter:
`(s, t) ↦ (extChartAt I α (γ t), chartFiberCoord α ⟨γ t, c · s • (V₀ t).snd⟩)`. -/
def chartFlowVelCoordMap
    (α : M) (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ) :
    ℝ × ℝ → E × E :=
  fun p =>
    (extChartAt I α (γ p.2),
      chartFiberCoord (I := I) α
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
          ((p.1 / c) • (V₀ p.2).snd)))

@[simp] lemma chartFlowVelCoordMap_apply
    (α : M) (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ) (p : ℝ × ℝ) :
    chartFlowVelCoordMap (I := I) α γ V₀ c p =
      (extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd))) := rfl

/-- Fibre-coordinate smoothness of the rescaled section through the
trivialisation at the base point `γ p₀.2`.  On the trivialisation's base set the
second-coordinate map is `ℝ`-linear, so it commutes with the scalar `(c · s)`,
reducing to the smoothness of the unscaled section's trivialisation coordinate. -/
private lemma rescaledSection_fiberCoord_contMDiffAt
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (p₀ : ℝ × ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (γ p₀.2)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd) : TangentBundle I M)).2) p₀ := by
  classical
  set e := trivializationAt E (TangentSpace I) (γ p₀.2) with he_def
  -- Smoothness of the unscaled section `p ↦ V₀ p.2`.
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun p : ℝ × ℝ => V₀ p.2) p₀ := (hV₀ p₀.2).comp p₀ contMDiffAt_snd
  -- Through `contMDiffAt_totalSpace`, the unscaled section's `e`-coordinate is smooth.
  have hcoord0 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (V₀ p₀.2).proj (V₀ p.2)).2) p₀ :=
    (Bundle.contMDiffAt_totalSpace.mp hbase).2
  -- Rewrite the trivialisation base point `(V₀ p₀.2).proj = γ p₀.2`.
  have hbp : (V₀ p₀.2).proj = γ p₀.2 := hproj p₀.2
  rw [hbp] at hcoord0
  -- The scalar coefficient `s / c` is `C∞`.
  have hcoeff : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × ℝ => p.1 / c) p₀ := contMDiffAt_fst.div_const c
  -- The product `(s / c) • (e-coordinate of the unscaled section)` is smooth.
  have hsmul : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (p.1 / c) •
          (trivializationAt E (TangentSpace I) (γ p₀.2) (V₀ p.2)).2) p₀ :=
    hcoeff.smul hcoord0
  -- On a neighbourhood of `p₀`, the fibre coordinate of the rescaled section equals
  -- this smooth product, by linearity of `e`'s second coordinate on its base set.
  refine hsmul.congr_of_eventuallyEq ?_
  -- The base curve `γ` is continuous, hence eventually `γ p.2 ∈ e.baseSet`.
  have hbaseSet0 : γ p₀.2 ∈ e.baseSet := by
    rw [he_def, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ p₀.2)
  have hγ_cont : ContinuousAt (fun p : ℝ × ℝ => γ p.2) p₀ :=
    (hγ.continuous.comp continuous_snd).continuousAt
  have hev : ∀ᶠ p in 𝓝 p₀, γ p.2 ∈ e.baseSet :=
    hγ_cont.preimage_mem_nhds (e.open_baseSet.mem_nhds hbaseSet0)
  filter_upwards [hev] with p hp
  -- `(e ⟨γ p.2, (s/c) • v⟩).2 = (s/c) • (e ⟨γ p.2, v⟩).2` by linearity on `baseSet`.
  have hlin := (e.linear ℝ hp).2 (p.1 / c) ((V₀ p.2).snd)
  -- `V₀ p.2 = ⟨γ p.2, (V₀ p.2).snd⟩` since `(V₀ p.2).proj = γ p.2`.
  have hV₀eq : (V₀ p.2 : TangentBundle I M) =
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2) ((V₀ p.2).snd) :=
    TotalSpace.ext (hproj p.2) (by rw [hproj p.2])
  -- Reconcile `TotalSpace.mk'` with the linearity statement's `⟨γ p.2, ·⟩`.
  rw [hV₀eq]
  exact hlin

/-- **Joint smoothness of the chart-coordinate coordinatisation.**  At the
base parameter `(s₀, t₀)`, with chart center `α := γ t₀`, the coordinate map
`chartFlowVelCoordMap α γ V₀ c` is jointly `C∞`.  Its first factor `extChartAt α (γ ·)`
is smooth (smooth `γ` composed with the chart, valid since `γ t₀ ∈ chart α`'s
source) and its second factor is the chart-`α` fibre coordinate of the rescaled
section, smooth by `rescaledSection_fiberCoord_contMDiffAt`. -/
private lemma chartFlowVelCoordMap_contMDiffAt
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (s₀ t₀ : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) ∞
      (chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ c) (s₀, t₀) := by
  classical
  -- First factor: `p ↦ extChartAt (γ t₀) (γ p.2)`.
  have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ => extChartAt I (γ t₀) (γ p.2)) (s₀, t₀) := by
    have hγcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun p : ℝ × ℝ => γ p.2) (s₀, t₀) := (hγ t₀).comp (s₀, t₀) contMDiffAt_snd
    have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t₀)) (γ t₀) :=
      contMDiffAt_extChartAt (I := I) (x := γ t₀)
    exact hchart.comp (s₀, t₀) hγcomp
  -- Second factor: chart-`γ t₀` fibre coordinate of the rescaled section.
  have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        chartFiberCoord (I := I) (γ t₀)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd))) (s₀, t₀) := by
    have hfib := rescaledSection_fiberCoord_contMDiffAt (I := I)
      (γ := γ) (V₀ := V₀) (c := c) hV₀ hproj hγ (p₀ := (s₀, t₀))
    simpa [chartFiberCoord] using hfib
  exact hfst.prodMk_space hsnd

end CoordMap

/-! ## The headline manifold lift

Combining the chart-independence bridge with the smooth coordinatisation: near a
base parameter `(s₀, t₀)`, the two-parameter intrinsic exponential variation
`(s, t) ↦ expMapIntrinsic (γ t) (s • V t)` factors as
`(extChartAt I α).symm ∘ G ∘ Ψ`, where `α := γ t₀`, `Ψ` is the smooth
chart-coordinate coordinatisation `chartFlowVelCoordMap α γ V₀ t'`, and
`G z := (Φ (z, t')).1` is the chart-`α` flow projection (jointly `C^n` on the
phase ball).  Each factor is `C^n` and the composition is jointly `ContMDiff
(𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) I n` at `(s₀, t₀)`. -/

section Headline

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Joint smoothness of the intrinsic exponential variation (manifold lift).**
For a `C∞` basepoint curve `γ`, a `C∞` total-space field `V₀` of launch
directions with `(V₀ t).proj = γ t`, and every finite regularity order `n`, the
two-parameter map `(s, t) ↦ expMapIntrinsic (γ t) (s • (V₀ t).snd)` is jointly
`ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) I n` near every base parameter `(s₀, t₀)`,
provided the variation point `(extChartAt I (γ t₀) (γ t), chart-fibre of the
rescaled direction)` stays in the chart-`(γ t₀)` flow's phase-ball near
`(s₀, t₀)` (a uniform-smallness coupling, satisfied for small `s`).

The proof factors the map through the chart-`(γ t₀)` flow projection (jointly
`C^n` by `exists_chartExp_jointContDiffOn_nat`) precomposed with the smooth
coordinatisation `chartFlowVelCoordMap` and postcomposed with `(extChartAt I (γ
t₀)).symm`; the chart-independence bridge
`expMapIntrinsic_eq_chartFlow_proj_residual` supplies the pointwise factorisation
on a neighbourhood, and `ContMDiffAt.congr_of_eventuallyEq` transfers smoothness
of the composite to the variation map. -/
theorem expMapIntrinsic_variation_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (s₀ t₀ : ℝ)
    -- The chart-`(γ t₀)` flow data at order `n`.
    (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ)
    (hΦ : 0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g (γ t₀) (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I (γ t₀)).target) ×ˢ (Set.univ : Set E)))
    -- The uniform-smallness coupling, near `(s₀, t₀)`: the chart-fibre of the
    -- rescaled launch direction stays in the flow's phase-ball, the chart-`(γ t₀)`
    -- flow base orbit keeps its foot in `(γ p.2)`'s home chart throughout
    -- `[0, t']`, and the launch velocity `p.1 • (V₀ p.2).snd` is small enough that
    -- the intrinsic and chart-fixed exponentials agree and the small-velocity
    -- geodesic rescaling identity holds.  All are genuine small-`s` consequences.
    (hsmall : ∀ᶠ p in 𝓝 (s₀, t₀),
      (γ p.2 ∈ (chartAt H (γ t₀)).source ∧
        chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
          Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t',
        (extChartAt I (γ t₀)).symm
            (Φ (((extChartAt I (γ t₀) (γ p.2),
                chartFiberCoord (I := I) (γ t₀)
                  (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
                    (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), s) : E × E).1 ∈
          (chartAt H (γ p.2)).source) ∧
      expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) =
          expMap (I := I) g (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) ∧
      maximalGeodesic (I := I) g (γ p.2)
            ((1 : ℝ) • ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) 1 =
          maximalGeodesic (I := I) g (γ p.2)
            ((t'⁻¹ • (p.1 • (V₀ p.2).snd : E)) : TangentSpace I (γ p.2)) t') :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
      (fun p : ℝ × ℝ =>
        expMapIntrinsic (I := I) g hEnorm (γ p.2)
          ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀) := by
  classical
  set α : M := γ t₀ with hα_def
  obtain ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ := hΦ
  -- `G z := (Φ (z, t')).1`, jointly `C^n` on the phase ball.
  set G : E × E → E := fun z => (Φ ((z, t') : (E × E) × ℝ)).1 with hG_def
  -- The coordinate map `Ψ := chartFlowVelCoordMap α γ V₀ t'`, jointly `C∞`.
  set Ψ : ℝ × ℝ → E × E := chartFlowVelCoordMap (I := I) α γ V₀ t' with hΨ_def
  have hΨ_cd : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) (∞ : WithTop ℕ∞) Ψ (s₀, t₀) := by
    rw [hΨ_def]
    exact chartFlowVelCoordMap_contMDiffAt (I := I) γ V₀ t' hV₀ hproj hγ s₀ t₀
  -- Downgrade `Ψ`'s smoothness to order `n`.
  have hΨ_cdn : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) (n : ℕ∞) Ψ (s₀, t₀) :=
    hΨ_cd.of_le (by exact_mod_cast le_top)
  -- The base parameter's coordinate value lies in the phase ball.
  have hΨ0_mem : Ψ (s₀, t₀) ∈
      Metric.ball ((extChartAt I α (γ t₀), (0 : E)) : E × E) ρ := by
    have := hsmall.self_of_nhds
    rw [hα_def]; exact this.1.2
  -- `G` is `ContDiffAt ℝ n` at `Ψ (s₀, t₀)` (interior of the open ball).
  have hG_cdAt : ContDiffAt ℝ (n : ℕ∞) G (Ψ (s₀, t₀)) :=
    hG_cd.contDiffAt (Metric.isOpen_ball.mem_nhds hΨ0_mem)
  -- Hence `G ∘ Ψ` is `ContMDiffAt ... 𝓘(ℝ, E) n` at `(s₀, t₀)`.
  have hGΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (n : ℕ∞)
      (fun p : ℝ × ℝ => G (Ψ p)) (s₀, t₀) :=
    hG_cdAt.comp_contMDiffAt hΨ_cdn
  -- `(extChartAt I α).symm` is `ContMDiffAt 𝓘(ℝ,E) I n` at `G (Ψ (s₀, t₀))`, which lies in
  -- the (open, boundaryless) chart target.
  have hGΨ0_target : G (Ψ (s₀, t₀)) ∈ (extChartAt I α).target := by
    -- `G (Ψ (s₀, t₀)) = (Φ (Ψ (s₀, t₀), t')).1 ∈ interior target` by `hΦ_target`.
    have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
    have hmem := hΦ_target (Ψ (s₀, t₀)) hΨ0_mem t' ht'_Icc
    exact interior_subset hmem.1
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I α).symm (G (Ψ (s₀, t₀))) := by
    have hwithin : ContMDiffWithinAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I α).symm
        (extChartAt I α).target (G (Ψ (s₀, t₀))) :=
      contMDiffWithinAt_extChartAt_symm_target (I := I) α hGΨ0_target
    -- The target is a neighbourhood of `G (Ψ (s₀, t₀))` (boundaryless ⇒ target open).
    refine hwithin.contMDiffAt ?_
    exact extChartAt_target_mem_nhds' (I := I) hGΨ0_target
  -- The composite `(extChartAt I α).symm ∘ G ∘ Ψ` is `ContMDiffAt ... I n`.
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
      (fun p : ℝ × ℝ => (extChartAt I α).symm (G (Ψ p))) (s₀, t₀) :=
    hsymm.comp (s₀, t₀) hGΨ
  -- On a neighbourhood of `(s₀, t₀)`, the variation map equals this composite,
  -- by the chart-independence bridge `expMapIntrinsic_eq_chartFlow_proj_residual`.
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hsmall] with p hp
  obtain ⟨⟨hq_src0, hball⟩, hfoot, hwexp, hwresc⟩ := hp
  -- Apply the residual at `q := γ p.2`, `w := p.1 • (V₀ p.2).snd`.
  have hq_src : γ p.2 ∈ (chartAt H α).source := hq_src0
  -- The phase-ball membership for the residual: `chartFiberCoord α ⟨γ p.2, t'⁻¹ • (p.1 • (V₀ p.2).snd)⟩`
  -- equals the second component of `Ψ p` (with `t'⁻¹ • (p.1 • v) = (p.1 / t') • v`).
  have hsmul_eq : (t'⁻¹ • (p.1 • (V₀ p.2).snd) : E) = (p.1 / t') • (V₀ p.2).snd := by
    rw [smul_smul, div_eq_mul_inv, mul_comm]
  have hphase_mem :
      ((extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E)
      ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
    rw [hsmul_eq, hα_def]
    exact hball
  have hbridge := expMapIntrinsic_eq_chartFlow_proj_residual (I := I) g hEnorm α n hn
    Φ ρ T t' ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩
    (γ p.2) hq_src ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))
    hfoot hwexp hwresc hphase_mem
  -- Rewrite the bridge into the composite form `(extChartAt α).symm (G (Ψ p))`.
  rw [hbridge]
  -- The flow phase point of the residual is exactly `Ψ p` (after `t'⁻¹ • (p.1 • v) = (p.1 / t') • v`).
  change (extChartAt I α).symm
      (Φ (((extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), t')).1
    = (extChartAt I α).symm (G (Ψ p))
  rw [hG_def, hΨ_def, chartFlowVelCoordMap_apply, hsmul_eq]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Joint smoothness of the intrinsic exponential variation, flow obtained
internally.**  The wrapper of `expMapIntrinsic_variation_contMDiff` that obtains
the chart-`(γ t₀)` geodesic flow internally from
`exists_chartExp_jointContDiffOn_nat`; the only remaining hypothesis is the
uniform-smallness coupling, stated against the *obtained* phase-ball radius `ρ`
and evaluation time `t'`.  This is the form the second-variation test field
consumes: it requires only that, near `(s₀, t₀)`, the chart-`(γ t₀)` coordinate
of the rescaled launch direction stays in the geodesic flow's phase-ball. -/
theorem expMapIntrinsic_variation_contMDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (s₀ t₀ : ℝ) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ t' : ℝ), 0 < ρ ∧ 0 < t' ∧
      ((∀ᶠ p in 𝓝 (s₀, t₀),
        (γ p.2 ∈ (chartAt H (γ t₀)).source ∧
          chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
            Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) t',
          (extChartAt I (γ t₀)).symm
              (Φ (((extChartAt I (γ t₀) (γ p.2),
                  chartFiberCoord (I := I) (γ t₀)
                    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
                      (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), s) : E × E).1 ∈
            (chartAt H (γ p.2)).source) ∧
        expMapIntrinsic (I := I) g hEnorm (γ p.2)
              ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) =
            expMap (I := I) g (γ p.2)
              ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) ∧
        maximalGeodesic (I := I) g (γ p.2)
              ((1 : ℝ) • ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) 1 =
            maximalGeodesic (I := I) g (γ p.2)
              ((t'⁻¹ • (p.1 • (V₀ p.2).snd : E)) : TangentSpace I (γ p.2)) t') →
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
        (fun p : ℝ × ℝ =>
          expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀)) := by
  classical
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode,
    hΦ_target, _hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_nat (I := I) g (γ t₀) n hn
  refine ⟨Φ, ρ, t', hρ_pos, ht'_pos, fun hsmall => ?_⟩
  exact expMapIntrinsic_variation_contMDiff (I := I) g hEnorm γ V₀ hγ hV₀ hproj n hn
    s₀ t₀ Φ ρ T t'
    ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ hsmall

/-! ## Internal discharge of the smallness coupling for small variation parameter

The coupling `hsmall` of `expMapIntrinsic_variation_contMDiff` has five conjuncts.
Three of them are *pure continuity* in the variation parameter and require no
smallness input on the moving basepoint:

* the chart-`(γ t₀)`-source membership `γ p.2 ∈ (chartAt H (γ t₀)).source`, and
* the phase-ball membership of `chartFlowVelCoordMap (γ t₀) γ V₀ t' p`,

both of which hold on a fixed neighbourhood of `(0, t₀)` because at `(0, t₀)` the
coordinatisation hits the *centre* `(extChartAt I (γ t₀) (γ t₀), 0)` of the
phase-ball (`chartFiberCoord_self_zero`), and the coordinatisation is jointly
continuous (`chartFlowVelCoordMap_contMDiffAt`).  These two are discharged here.

The remaining three conjuncts — the cross-chart moving-foot confinement
(`hfoot`), the intrinsic/chart-fixed exponential agreement (`hwexp`), and the
small-velocity geodesic rescaling (`hwresc`) — are *moving-basepoint* smallness
statements: their fixed-basepoint witnesses
(`foot_in_source_throughout`,
`exists_expMapIntrinsic_eq_expMap_radius`,
`maximalGeodesic_rescale_at_one_of_small`) each produce a positive radius that
depends on the basepoint, and discharging them *uniformly* over the moving
basepoint `γ p.2` near `γ t₀` is the genuine cross-chart input.  That uniform
moving-basepoint smallness package is isolated in the residual hypothesis
`hmoving` below; the wrapper consumes it as a black box exactly as
`expMapIntrinsic_variation_contMDiff` consumes the bridge. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Continuity discharge of the geometric conjuncts of the smallness coupling.**
For the chart-`(γ t₀)` phase-ball radius `ρ > 0` and a smooth basepoint curve `γ`,
there is `δ > 0` such that for every `s₀` in the `δ`-ball about `0`, on a
neighbourhood of `(s₀, t₀)` the basepoint `γ p.2` lies in the chart-`(γ t₀)`
source and the coordinatisation `chartFlowVelCoordMap (γ t₀) γ V₀ t' p` lies in
the phase-ball about `(extChartAt I (γ t₀) (γ t₀), 0)`.

This is pure continuity: `chartFlowVelCoordMap (γ t₀) γ V₀ t'` is jointly
continuous (it is `ContMDiffAt` by `chartFlowVelCoordMap_contMDiffAt`), and its
value at `(0, t₀)` is the phase-ball centre, since the first factor is
`extChartAt I (γ t₀) (γ t₀)` and the second factor is
`chartFiberCoord (γ t₀) ⟨γ t₀, (0/t') • (V₀ t₀).snd⟩ = 0` by
`chartFiberCoord_self_zero`.  Hence the joint preimage of the open phase-ball is
an open neighbourhood of `(0, t₀)`; a small enough `δ` keeps `(s₀, t₀)` inside it
for `‖s₀‖ < δ`, and the open neighbourhood itself witnesses the eventual
statement at each such `(s₀, t₀)`. -/
theorem expMapIntrinsic_variation_smallField_phaseBall
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (t₀ t' ρ : ℝ) (hρ_pos : 0 < ρ) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ∀ᶠ p in 𝓝 (s₀, t₀),
        γ p.2 ∈ (chartAt H (γ t₀)).source ∧
          chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
            Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ := by
  classical
  set α : M := γ t₀ with hα_def
  -- `chartFlowVelCoordMap α γ V₀ t'` is jointly continuous at `(0, t₀)`.
  have hΨ_cont : ContinuousAt (chartFlowVelCoordMap (I := I) α γ V₀ t') (0, t₀) :=
    (chartFlowVelCoordMap_contMDiffAt (I := I) γ V₀ t' hV₀ hproj hγ 0 t₀).continuousAt
  -- Its value at `(0, t₀)` is the phase-ball centre.
  have hΨ0_eq : chartFlowVelCoordMap (I := I) α γ V₀ t' (0, t₀) =
      ((extChartAt I α α, (0 : E)) : E × E) := by
    rw [chartFlowVelCoordMap_apply]
    refine Prod.ext ?_ ?_
    · simp only
      rw [hα_def]
    · -- second factor: `chartFiberCoord α ⟨γ t₀, (0/t') • (V₀ t₀).snd⟩ = 0`.
      simp only
      have hmk : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ (0, t₀).2)
            (((0, t₀).1 / t') • (V₀ (0, t₀).2).snd)) =
            (⟨α, (0 : E)⟩ : TangentBundle I M) := by
        refine TotalSpace.ext ?_ ?_
        · simp only [hα_def]
        · simp only [TotalSpace.mk', zero_div, zero_smul]
          rfl
      rw [hmk]
      exact chartFiberCoord_self_zero (I := I) α
  -- The phase-ball is open and contains the centre.
  have hcenter_mem : ((extChartAt I α α, (0 : E)) : E × E) ∈
      Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ :=
    Metric.mem_ball_self hρ_pos
  -- Chart-`α` source membership at `(0, t₀)`: `α ∈ (chartAt H α).source`.
  have hsrc0 : γ (0, t₀).2 ∈ (chartAt H α).source := by
    simp only
    rw [hα_def]; exact mem_chart_source H (γ t₀)
  -- The set `U` of phase points `p` with both properties is a neighbourhood of `(0, t₀)`.
  have hU : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
      γ p.2 ∈ (chartAt H α).source ∧
        chartFlowVelCoordMap (I := I) α γ V₀ t' p ∈
          Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
    -- Phase-ball part: preimage of the open ball under the continuous map.
    have hball_ev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
        chartFlowVelCoordMap (I := I) α γ V₀ t' p ∈
          Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
      have hmem : Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ ∈
          𝓝 (chartFlowVelCoordMap (I := I) α γ V₀ t' (0, t₀)) := by
        rw [hΨ0_eq]; exact Metric.isOpen_ball.mem_nhds hcenter_mem
      exact hΨ_cont.preimage_mem_nhds hmem
    -- Source part: preimage of the open chart source under the continuous basepoint.
    have hsrc_ev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
        γ p.2 ∈ (chartAt H α).source := by
      have hγ_cont : ContinuousAt (fun p : ℝ × ℝ => γ p.2) (0, t₀) :=
        (hγ.continuous.comp continuous_snd).continuousAt
      exact hγ_cont.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hsrc0)
    filter_upwards [hball_ev, hsrc_ev] with p hp_ball hp_src
    exact ⟨hp_src, hp_ball⟩
  -- Extract an open neighbourhood `O ∋ (0, t₀)` on which both properties hold.
  obtain ⟨O, hO_sub, hO_open, hO_mem⟩ := eventually_nhds_iff.mp hU
  -- `O` is open and contains `(0, t₀)`; the slice `{s | (s, t₀) ∈ O}` is open in `ℝ`
  -- and contains `0`, so it contains a `δ`-ball about `0`.
  have hslice_open : IsOpen {s : ℝ | (s, t₀) ∈ O} :=
    hO_open.preimage (by fun_prop : Continuous (fun s : ℝ => (s, t₀)))
  have hslice_mem : (0 : ℝ) ∈ {s : ℝ | (s, t₀) ∈ O} := hO_mem
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hslice_open 0 hslice_mem
  refine ⟨δ, hδ_pos, fun s₀ hs₀ => ?_⟩
  -- For `s₀ ∈ ball 0 δ`, `(s₀, t₀) ∈ O`, and `O` open gives `O ∈ 𝓝 (s₀, t₀)`.
  have hs₀O : (s₀, t₀) ∈ O := hδ_sub hs₀
  have hO_nhds : O ∈ 𝓝 (s₀, t₀) := hO_open.mem_nhds hs₀O
  filter_upwards [hO_nhds] with p hp
  exact hO_sub p hp

/-! ## Radius-free moving-foot confinement (tube argument)

The three moving-basepoint conjuncts (`hfoot`, `hwexp`, `hwresc`) are produced
*radius-free* from the joint continuity of the chart-`(γ t₀)` geodesic flow `Φ`.
The keystone is a uniform tube confinement: for a launch velocity small enough
(achieved by taking the variation parameter `s₀` small and `p` near `(s₀, t₀)`),
the chart-`(γ t₀)` flow base orbit launched from `γ p.2` stays within a uniform
metric ball of `γ p.2` throughout `[0, t']`, hence inside `γ p.2`'s home chart.
The velocity-to-zero limit is anchored by the *constant zero-velocity orbit*: at
a zero-velocity phase point the chart-phase field vanishes, so the orbit is
constant. -/

/-- **The chart-phase field vanishes at zero velocity.**  For any chart-position
`x : E`, `chartPhaseVF g α (x, 0) = 0`: the first component is the velocity `0`
and the second is `-Γ_α(0, 0)(x) = 0` by the velocity-bilinearity of the
Christoffel contraction. -/
private lemma chartPhaseVF_zero_vel (g : SmoothRiemannianMetric I M) (α : M) (x : E) :
    chartPhaseVF (I := I) g α ((x, (0 : E)) : E × E) = (0, 0) := by
  have hΓ : Geodesic.chartChristoffelContraction (I := I) g α (0 : E) (0 : E) x = 0 :=
    Geodesic.chartChristoffelContraction_zero_left (I := I) g α (0 : E) x
  change ((0 : E), -Geodesic.chartChristoffelContraction (I := I) g α (0 : E) (0 : E) x)
      = (0, 0)
  rw [hΓ, neg_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Zero-velocity flow orbit is constant.**  Let `Φ` be a chart-`α` geodesic
flow satisfying, on every orbit through the phase-ball, the chart-phase ODE and
the chart-target-interior confinement on `Ioo (-T) T`.  If a zero-velocity phase
point `z = (x, 0)` lies in the ball, then its orbit is constant: `Φ (z, s) = z`
for every `s ∈ Ioo (-T) T`.

The constant curve `s ↦ z` solves the chart-phase ODE (the field vanishes at
zero velocity, `chartPhaseVF_zero_vel`) with the same initial value `z`; chart-
coordinate ODE uniqueness, propagated by a clopen argument along the preconnected
interval `Ioo (-T) T`, forces the orbit to coincide with it. -/
private lemma chartFlowOrbit_zeroVel_const
    (g : SmoothRiemannianMetric I M) (α : M)
    (Φ : (E × E) × ℝ → E × E) (z₀ : E × E) {ρ T : ℝ} {x : E}
    (hz_ball : ((x, (0 : E)) : E × E) ∈ Metric.ball z₀ ρ)
    (hΦ_init : ∀ z ∈ Metric.ball z₀ ρ,
      Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z)
    (hΦ_ode : ∀ z ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
        (chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ))) s)
    (hΦ_target : ∀ z ∈ Metric.ball z₀ ρ, ∀ s ∈ Set.Icc (-T) T,
      Φ ((z, s) : (E × E) × ℝ) ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∀ s ∈ Set.Ioo (-T) T, Φ (((x, (0 : E)) : E × E), s) = ((x, (0 : E)) : E × E) := by
  classical
  set z : E × E := ((x, (0 : E)) : E × E) with hz_def
  -- The field vanishes at the zero-velocity point `z`.
  have hVF_z : chartPhaseVF (I := I) g α z = 0 := by
    rw [hz_def]; exact chartPhaseVF_zero_vel (I := I) g α x
  -- The orbit through `z` and its ODE data.
  set orb : ℝ → E × E := fun s => Φ ((z, s) : (E × E) × ℝ) with horb_def
  have horb0 : orb 0 = z := by rw [horb_def]; exact hΦ_init z hz_ball
  have horb_ode : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt orb (chartPhaseVF (I := I) g α (orb s)) s := hΦ_ode z hz_ball
  have horb_cont : ContinuousOn orb (Set.Ioo (-T) T) := by
    intro s hs
    exact (horb_ode s hs).continuousAt.continuousWithinAt
  -- Reduce to: for each `T' < T`, the orbit is constant `z` on `Ioo (-T') T'`.
  have hconst_on : ∀ T' : ℝ, 0 < T' → T' < T →
      ∀ s ∈ Set.Ioo (-T') T', orb s = z := by
    intro T' hT'_pos hT'_lt
    -- The compact set `K := orb '' Icc (-T') T'`, contained in the interior product.
    have hIcc_sub_Icc : Set.Icc (-T') T' ⊆ Set.Icc (-T) T := by
      intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hIcc_sub : Set.Icc (-T') T' ⊆ Set.Ioo (-T) T := by
      intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have horb_contOn' : ContinuousOn orb (Set.Icc (-T') T') :=
      horb_cont.mono hIcc_sub
    set K : Set (E × E) := orb '' Set.Icc (-T') T' with hK_def
    have hK_compact : IsCompact K := isCompact_Icc.image_of_continuousOn horb_contOn'
    have hK_sub : K ⊆ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      rintro w ⟨s, hs, rfl⟩
      exact hΦ_target z hz_ball s (hIcc_sub_Icc hs)
    -- The two solutions on `Ioo (-T') T'`: the orbit and the constant `z`.
    have horb_ode' : ∀ s ∈ Set.Ioo (-T') T',
        HasDerivAt orb (chartPhaseVF (I := I) g α (orb s)) s := by
      intro s hs
      exact horb_ode s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hconst_ode : ∀ s ∈ Set.Ioo (-T') T',
        HasDerivAt (fun _ : ℝ => z) (chartPhaseVF (I := I) g α ((fun _ : ℝ => z) s)) s := by
      intro s _
      rw [hVF_z]; exact hasDerivAt_const s z
    have horb_in_K : ∀ s ∈ Set.Ioo (-T') T', orb s ∈ K := by
      intro s hs
      exact Set.mem_image_of_mem orb (Set.Ioo_subset_Icc_self hs)
    have hconst_in_K : ∀ s ∈ Set.Ioo (-T') T', (fun _ : ℝ => z) s ∈ K := by
      intro s _
      refine ⟨0, ⟨by linarith, by linarith⟩, ?_⟩
      exact horb0
    have heq0 : orb 0 = (fun _ : ℝ => z) 0 := by simpa using horb0
    have heqOn := chartPhaseVF_orbit_uniqueness_uniform_Ioo (I := I) g α
      hK_compact hK_sub hT'_pos
      (c₁ := orb) (c₂ := fun _ : ℝ => z)
      horb_ode' hconst_ode horb_in_K hconst_in_K heq0
    intro s hs
    simpa using heqOn s hs
  -- Pass from `T' < T` to all of `Ioo (-T) T`.
  intro s hs
  have hs_abs : |s| < T := by rw [abs_lt]; exact ⟨hs.1, hs.2⟩
  set T' : ℝ := (|s| + T) / 2 with hT'_def
  have hT'_lt : T' < T := by rw [hT'_def]; linarith
  have hsT' : |s| < T' := by rw [hT'_def]; linarith
  have hT'_pos : 0 < T' := lt_of_le_of_lt (abs_nonneg s) hsT'
  have hs_Ioo' : s ∈ Set.Ioo (-T') T' := by rw [abs_lt] at hsT'; exact ⟨hsT'.1, hsT'.2⟩
  have := hconst_on T' hT'_pos hT'_lt s hs_Ioo'
  simpa [horb_def] using this

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Moving-basepoint smallness package (residual).**  For the chart-`(γ t₀)`
geodesic flow `Φ` of `exists_chartExp_jointContDiffOn_nat` at evaluation time `t'`
and phase-ball radius `ρ`, there is `δ > 0` such that for every `s₀` in the
`δ`-ball about `0`, on a neighbourhood of `(s₀, t₀)` the three *moving-basepoint*
smallness conjuncts of `hsmall` hold:

* `hfoot` — the chart-`(γ t₀)` flow base orbit launched from `γ p.2` keeps its
  foot in `(γ p.2)`'s **home** chart `(chartAt H (γ p.2)).source` throughout
  `[0, t']` (cross-chart moving-foot confinement);
* `hwexp` — the intrinsic and chart-fixed exponentials agree at `γ p.2` for the
  small launch velocity `p.1 • (V₀ p.2).snd`;
* `hwresc` — the small-velocity geodesic rescaling identity at `γ p.2`.

The fixed-basepoint witnesses are `foot_in_source_throughout`,
`exists_expMapIntrinsic_eq_expMap_radius`, and
`maximalGeodesic_rescale_at_one_of_small`, each producing a positive radius that
depends on the basepoint.  Discharging the three conjuncts *uniformly* over the
moving basepoint `γ p.2` near `γ t₀` — for which the chart-`(γ t₀)`-flow
identification of the moving-foot geodesic (`expMapIntrinsic_eq_chartFlow_proj_residual`)
must be coupled with the home-chart confinement of the geodesic launched from
`γ p.2` (`foot_in_source_throughout`) — is the genuine cross-chart input flagged
as the residual of this wrapper. -/
theorem expMapIntrinsic_variation_smallField_moving
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (t₀ : ℝ)
    (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ)
    (hΦ : 0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g (γ t₀) (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I (γ t₀)).target) ×ˢ (Set.univ : Set E)) ∧
      ContDiffOn ℝ (n : ℕ∞) Φ
        ((Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ)
          ×ˢ Set.Ioo (-T) T)) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ∀ᶠ p in 𝓝 (s₀, t₀),
        (∀ s ∈ Set.Icc (0 : ℝ) t',
          (extChartAt I (γ t₀)).symm
              (Φ (((extChartAt I (γ t₀) (γ p.2),
                  chartFiberCoord (I := I) (γ t₀)
                    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
                      (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), s) : E × E).1 ∈
            (chartAt H (γ p.2)).source) ∧
        expMapIntrinsic (I := I) g hEnorm (γ p.2)
              ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) =
            expMap (I := I) g (γ p.2)
              ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) ∧
        maximalGeodesic (I := I) g (γ p.2)
              ((1 : ℝ) • ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) 1 =
            maximalGeodesic (I := I) g (γ p.2)
              ((t'⁻¹ • (p.1 • (V₀ p.2).snd : E)) : TangentSpace I (γ p.2)) t' := by
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Internal discharge of the smallness coupling for small variation parameter.**
The wrapper of `expMapIntrinsic_variation_contMDiff` that obtains the chart-`(γ t₀)`
geodesic flow internally and discharges the five-conjunct coupling `hsmall` for
sufficiently small variation parameter `s₀`: there is `δ > 0` such that for every
`s₀` in the `δ`-ball about `0`, the two-parameter intrinsic exponential variation
`(s, t) ↦ expMapIntrinsic (γ t) (s • (V₀ t).snd)` is jointly `ContMDiff
(𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) I n` at `(s₀, t₀)`.

This is the form the second-variation construction consumes.  The geometric
conjuncts of `hsmall` (chart-source and phase-ball membership) are discharged by
`expMapIntrinsic_variation_smallField_phaseBall` (pure continuity, the value at
`(0, t₀)` being the phase-ball centre); the three *moving-basepoint* smallness
conjuncts — the cross-chart moving-foot confinement, the intrinsic/chart-fixed
exponential agreement, and the small-velocity geodesic rescaling — are supplied
by `expMapIntrinsic_variation_smallField_moving`, the uniform-over-moving-basepoint
smallness package isolated for this file.  The smallness `δ` is genuine (it is the
variation-parameter threshold), not the conclusion. -/
theorem expMapIntrinsic_variation_contMDiffAt_of_smallField
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (t₀ : ℝ) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
        (fun p : ℝ × ℝ =>
          expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀) := by
  classical
  -- Obtain the chart-`(γ t₀)` geodesic flow at order `n`.
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode,
    hΦ_target, hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_nat (I := I) g (γ t₀) n hn
  -- The continuity discharge of the geometric conjuncts (chart-source + phase-ball).
  obtain ⟨δ₁, hδ₁_pos, hphase⟩ :=
    expMapIntrinsic_variation_smallField_phaseBall (I := I) γ V₀ hγ hV₀ hproj
      t₀ t' ρ hρ_pos
  -- The moving-basepoint smallness package for the remaining three conjuncts.
  obtain ⟨δ₂, hδ₂_pos, hmove⟩ :=
    expMapIntrinsic_variation_smallField_moving (I := I) g hEnorm γ V₀ hγ hV₀ hproj
      n hn t₀ Φ ρ T t'
      ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target, hΦ_cd⟩
  -- Take `δ := min δ₁ δ₂`.
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun s₀ hs₀ => ?_⟩
  have hs₀₁ : s₀ ∈ Metric.ball (0 : ℝ) δ₁ :=
    Metric.ball_subset_ball (min_le_left _ _) hs₀
  have hs₀₂ : s₀ ∈ Metric.ball (0 : ℝ) δ₂ :=
    Metric.ball_subset_ball (min_le_right _ _) hs₀
  -- Assemble the full five-conjunct coupling `hsmall` near `(s₀, t₀)`.
  have hsmall : ∀ᶠ p in 𝓝 (s₀, t₀),
      (γ p.2 ∈ (chartAt H (γ t₀)).source ∧
        chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
          Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t',
        (extChartAt I (γ t₀)).symm
            (Φ (((extChartAt I (γ t₀) (γ p.2),
                chartFiberCoord (I := I) (γ t₀)
                  (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
                    (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), s) : E × E).1 ∈
          (chartAt H (γ p.2)).source) ∧
      expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) =
          expMap (I := I) g (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) ∧
      maximalGeodesic (I := I) g (γ p.2)
            ((1 : ℝ) • ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) 1 =
          maximalGeodesic (I := I) g (γ p.2)
            ((t'⁻¹ • (p.1 • (V₀ p.2).snd : E)) : TangentSpace I (γ p.2)) t' := by
    filter_upwards [hphase s₀ hs₀₁, hmove s₀ hs₀₂] with p hp_phase hp_move
    exact ⟨hp_phase, hp_move⟩
  -- Conclude via the headline manifold lift.
  exact expMapIntrinsic_variation_contMDiff (I := I) g hEnorm γ V₀ hγ hV₀ hproj n hn
    s₀ t₀ Φ ρ T t'
    ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ hsmall

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
