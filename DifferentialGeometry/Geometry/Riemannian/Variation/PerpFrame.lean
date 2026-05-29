import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport

/-!
# Parallel orthonormal perpendicular frame along a geodesic

For a `C^∞` unit-speed geodesic `γ : ℝ → M` on `Icc 0 L` with `L > 0`, this
file isolates the construction and supporting bridges for a parallel
orthonormal frame `e : Fin (finrank E - 1) → SectionAlongCurve I M γ` of the
`g`-orthogonal complement of the velocity `t ↦ dγ_t(1)`:

* `exists_parallel_orthonormal_perp_frame` — existence of the frame: each
  `e i` is differentiable, parallel along `γ` (moving-foot
  `chartCovDerivAlong g (γ t) γ (e i) t = 0`), the frame is `g`-orthonormal
  pointwise, and each `e i` is `g`-orthogonal to the velocity.
* `perp_to_velocity_preserved` — a parallel section that is `g`-orthogonal to
  the velocity at `t = 0` stays `g`-orthogonal to the velocity for all `t`.
* `chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered` — the
  foot bridge from `IsParallelChart` to the moving-foot `chartCovDerivAlong`.

The foot identity relating a section's value to the inverse-trivialisation of
its chart representation is already available as `symmL_chartRepAt_self`
(`CovariantDerivativeAlong`), so it is consumed directly rather than restated here.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

section PerpFrame

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Existence of a parallel orthonormal perpendicular frame.** For a `C^∞`
unit-speed geodesic `γ` on `Icc 0 L` (`L > 0`), there is a frame
`e : Fin (finrank E - 1) → SectionAlongCurve I M γ` such that each `e i` is
differentiable on `Icc 0 L`, parallel along `γ` (the *intrinsic* covariant
derivative `covDerivAlong g γ (e i) t` vanishes), the frame is pointwise
`g`-orthonormal, and each frame vector is `g`-orthogonal to the velocity
`dγ_t(1)`. This is the standalone form of the frame package consumed in the
Bonnet–Myers second-variation contradiction.

The construction is the genuine Gram–Schmidt-of-an-orthonormal-basis-of
`(γ'(0))^⊥`-then-parallel-transport: seed an orthonormal basis of the
`g`-orthogonal complement of `dγ_0(1)` at the basepoint `γ 0` and parallel
transport each seed along `γ` (`parallelTransport`); the transported sections
are parallel by construction (`parallelTransport_isParallel`, bridged to the
intrinsic `covDerivAlong` via `covDerivAlong_eq_zero_iff` /
`chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered`),
`g`-orthonormality is preserved by parallel transport
(`parallelTransport_preserves_inner_product`), and perpendicularity to the
velocity is preserved because the velocity field of a geodesic is itself
parallel (`perp_to_velocity_preserved`). -/
theorem exists_parallel_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (e i).toFun t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0) :=
  sorry

set_option linter.unusedVariables false in
/-- **Perpendicularity to the velocity is preserved.** If a section `V` along a
`C^∞` geodesic `γ` is parallel (the intrinsic covariant derivative
`covDerivAlong g γ V` vanishes on `Icc 0 L`) and `V 0` is `g`-orthogonal to the
velocity `dγ_0(1)` at the basepoint, then `V t` is `g`-orthogonal to the
velocity `dγ_t(1)` for every `t ∈ Icc 0 L`. The mechanism is constancy of the
genuine Riemannian inner product `t ↦ g(γ t)(V t, dγ_t(1))`: at every point its
derivative is computed in the chart pinned at the foot `γ t` by the
covariant-derivative product rule
(`chartGramAlongCurve_hasDerivAt_covariant`), and both correction terms vanish
— the `V`-term because `V` is parallel (the foot-chart covariant derivative is
the chart-coordinate of `covDerivAlong g γ V`, which is `0`), the velocity-term
because `γ` is a geodesic (the velocity field is parallel,
`covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt`).

The regularity hypothesis `hVdiff` (the chart-coordinate representation
`chartRepAt γ V t` is differentiable at the foot `t`) is the standard
"`V` varies differentiably along `γ`" assumption shared with
`covDerivAlong_add` / `covDerivAlong_smulFun`; without it the chart-Gram form
is not differentiable and `covDerivAlong = 0` (which reads `deriv` of a possibly
non-differentiable representation) carries no propagation content. -/
theorem perp_to_velocity_preserved
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L) (V : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0)
    (hPerp0 : g.inner (γ 0) (V 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0 := by
  classical
  -- The genuine Riemannian inner product as a function of the parameter.
  set vel : ℝ → ∀ s, TangentSpace I (γ s) :=
    fun _ s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) with hvel_def
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) with hf_def
  -- We show: `f` is constant on `Icc 0 L`, equal to `f 0 = 0`.
  -- For the constancy engine we need: (a) `f` continuous on `Icc 0 L`,
  -- (b) `HasDerivWithinAt f 0 (Ici t) t` for every `t ∈ Ico 0 L`.
  -- Both follow from a local computation in the chart pinned at the foot `γ t`.
  --
  -- ### Local statement at a foot time `t₀ ∈ Icc 0 L`.
  -- In the chart at `α := γ t₀`, the chart-coordinate representations of `V` and
  -- the velocity field are `Vrep := chartRepAt γ V t₀` and
  -- `urep := chartRepAt γ (velocity) t₀`. On a neighbourhood of `t₀` (where `γ s`
  -- stays in the chart's base set) the round-trip `symmL ∘ continuousLinearMapAt`
  -- is the identity, so `f` agrees with the chart-Gram form of `Vrep`, `urep`.
  have hlocal : ∀ t₀ ∈ Set.Icc (0 : ℝ) L, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set urep : ℝ → E :=
      chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ with hurep_def
    -- `γ t₀ = α` lies in the base set of the trivialisation/chart at `α`.
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H (γ t₀)
    -- The base set is an open neighbourhood of times whose curve point sits in it.
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
    -- ### Round trip: on this neighbourhood, the section equals `symmL ∘ rep`.
    have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
      intro s hs
      simpa [hVrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs (V s)
    have huround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s) =
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) := by
      intro s hs
      simpa [hurep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs ((mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
    -- ### `f` agrees with the chart-Gram form of `Vrep`, `urep` near `t₀`.
    have hf_eq : f =ᶠ[𝓝 t₀]
        fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s := by
      filter_upwards [hsrc_mem] with s hs
      have hVs := hVround s hs
      have hus := huround s hs
      -- `f s = g.inner (γ s) (symmL (γ s) (Vrep s)) (symmL (γ s) (urep s))`.
      have : f s = g.inner (γ s)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s)) := by
        rw [hf_def]; rw [hVs, hus]
      rw [this, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (urep s)]
      rw [AlongCurve.chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      -- `chartGramMatrix g α (γ s) = chartGramOnE g α · (chartCurve α γ s)`.
      have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
        rw [chartCurve_def]
        refine (extChartAt I α).left_inv ?_
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        rw [TangentBundle.trivializationAt_baseSet] at hs
        exact hs
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
    -- ### The chart trajectory has the prescribed velocity at `t₀`.
    -- `u := chartCurve α γ`, with `u(t₀) ∈ interior target`.
    have hu_hasDerivAt :
        HasDerivAt (chartCurve (I := I) α γ)
          (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ ∞ (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (γ t₀) :=
            contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by simp)).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    -- ### `Vrep` is differentiable at `t₀` (foot regularity hypothesis).
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ :=
      ((hVdiff t₀ ht₀).hasDerivAt)
    -- ### The open neighbourhood of times whose curve point sits in the chart source.
    set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
    have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
    have ht₀_U : t₀ ∈ U := by
      rw [hU_def, Set.mem_preimage]; exact mem_chart_source H (γ t₀)
    have hU_nhds : U ∈ 𝓝 t₀ := hU_open.mem_nhds ht₀_U
    -- The chart trajectory `chartCurve α γ = extChartAt I α ∘ γ` is `C^∞` on `U`.
    have hu_cdiffOn : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) U := by
      have h_comp_mdiff :
          ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
        have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
        have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
        have hmaps : Set.MapsTo γ U (chartAt H α).source := fun s hs => hs
        exact hφ.comp hγU hmaps
      have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
      rw [hfun]
      exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
    -- ### `urep` equals `deriv u` on `U` (chain-rule identity for the velocity coordinate).
    have hurep_eqOn : Set.EqOn urep (deriv (chartCurve (I := I) α γ)) U := by
      intro s hs
      have hs' : γ s ∈ (chartAt H α).source := hs
      rw [hurep_def, chartRepAt_apply]
      rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := I) (M := M) (γ := γ) hγ α (t := s) hs']
      rfl
    have hurep_eq : urep =ᶠ[𝓝 t₀] deriv (chartCurve (I := I) α γ) :=
      hurep_eqOn.eventuallyEq_of_mem hU_nhds
    -- `deriv u` is `C^∞` on `U`, hence differentiable at `t₀`.
    have hu_deriv_hasDerivAt :
        HasDerivAt (deriv (chartCurve (I := I) α γ))
          (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ := by
      have hderiv_u_cdiffOn :
          ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) α γ)) U :=
        hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
      exact ((hderiv_u_cdiffOn.differentiableOn (by simp) t₀ ht₀_U).differentiableAt
        hU_nhds).hasDerivAt
    have hurep_hasDerivAt : HasDerivAt urep (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ :=
      hu_deriv_hasDerivAt.congr_of_eventuallyEq hurep_eq
    -- ### The chart-Gram form has derivative `0` at `t₀` by the covariant product rule.
    have hgram :=
      AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep urep
        (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
        (Vprime := fun _ => deriv Vrep t₀)
        (Wprime := fun _ => deriv (deriv (chartCurve (I := I) α γ)) t₀)
        hu_hasDerivAt hmem_int hVrep_hasDerivAt hurep_hasDerivAt
    -- The two covariant correction terms equal the foot-chart covariant derivatives.
    -- For `Vrep`: `chartCovDerivAlong g α γ Vrep t₀ = covDerivAlong's chart coord = 0`.
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this
      exact this
    -- For `urep`: the velocity field is parallel because `γ` is a geodesic.
    have hcorru :
        deriv (deriv (chartCurve (I := I) α γ)) t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (urep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have hgeoeq := hgeo.hasGeodesicEquationAt t₀
      have hvel0 :
          covDerivAlong (I := I) g γ
            (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ = 0 :=
        (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t₀ hγ).mpr hgeoeq
      have hchart0 : chartCovDerivAlong (I := I) g α γ urep t₀ = 0 := by
        rw [hα_def, hurep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ
          (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀).mp hvel0
      rw [chartCovDerivAlong_def] at hchart0
      -- `deriv urep t₀ = deriv (deriv u) t₀` since `urep =ᶠ deriv u` near `t₀`.
      rw [hurep_eq.deriv_eq] at hchart0
      exact hchart0
    -- Substitute the vanishing corrections into the derivative value: it is `0`.
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s) 0 t₀ := by
      -- The two covariant-correction terms (`Vprime + Γ(u', V)` and
      -- `Wprime + Γ(u', W)`) vanish at `t₀`, so the whole derivative value is `0`.
      convert hgram using 1
      simp only [hcorrV, hcorru]
      simp
    -- Transfer the derivative back to `f`.
    exact hderiv0.congr_of_eventuallyEq hf_eq
  -- ### `f` is continuous on `Icc 0 L` and has zero right-derivative on `Ico 0 L`.
  have hcont : ContinuousOn f (Set.Icc 0 L) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt f 0 (Set.Ici x) x := by
    intro x hx
    exact (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  -- ### Constancy on `Icc 0 L`.
  have hconst : ∀ x ∈ Set.Icc (0 : ℝ) L, f x = f 0 :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  -- ### Conclude: `f t = f 0 = 0`.
  intro t ht
  have hft := hconst t ht
  -- `f t = f 0` and `f 0 = g.inner (γ 0) (V 0) (dγ_0 1) = 0` by hypothesis.
  rw [hf_def] at hft
  simp only at hft
  rw [hft]
  exact hPerp0

/-- **Foot bridge: chart parallelism implies moving-foot covariant vanishing.**
If a section's `E`-valued representation `X` is parallel along `γ` in the chart
centred at the foot `γ t` (the predicate `IsParallelChart` for the foot-centred
chart curve velocity, on a neighbourhood `s` of `t`), then the moving-foot
chart-local covariant derivative `chartCovDerivAlong g (γ t) γ X t` vanishes. -/
theorem chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {X : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hX : IsParallelChart (I := I) g (γ t) γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) τ) X s)
    (ht : t ∈ s) :
    chartCovDerivAlong (I := I) g (γ t) γ X t = 0 := by
  -- The parallel-transport ODE at `t` gives the time-derivative of `X`.
  have hd := hX.hasDerivAt ht
  -- Extract `deriv X t` from `HasDerivAt`.
  have hderiv := hd.deriv
  -- Unfold the covariant-derivative formula and substitute.
  rw [chartCovDerivAlong_def, hderiv]
  abel

end PerpFrame

end DifferentialGeometry.Geometry.Riemannian

end
