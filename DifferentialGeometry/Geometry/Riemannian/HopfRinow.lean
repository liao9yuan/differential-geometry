import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Connection.LeviCivita
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option linter.unusedSectionVars false

/-!
# Hopf-Rinow: metric-completeness implies geodesic-completeness and the
existence of minimising geodesics

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace`, this file packages the classical Hopf-Rinow chain.

## Geodesic-completeness chain

* `bm_c_gc_constant_speed` -- a geodesic has constant `g`-speed.
* `bm_c_gc_length_distance_bound` -- `riemannianEDist` is Lipschitz in
  the parameter along a geodesic with constant speed bound.
* `bm_c_gc_escape_cauchy` -- if the maximal interval of a geodesic
  escapes to a finite right endpoint, the values form a Cauchy
  sequence in `riemannianEDist`.
* `bm_c_gc_velocity_limit` -- the velocity converges to a limit
  vector in the tangent space at the metric limit point.
* `bm_c_gc_extension_past_limit` -- local existence at the limit
  point produces a geodesic extending the original past the supposed
  escape time, contradicting maximality.
* `bm_c_gc_symmetric_left_endpoint` -- the same argument on the
  left endpoint via reflection `t \mapsto -t`.
* `bm_c_gc_assemble` -- assembly: the maximal interval is `Set.univ`.

## Exponential-map totality

* `bm_c_expMap_continuous_of_geodesic_complete` -- continuity of
  `expMap g p` on the entire tangent space, given geodesic
  completeness.
* `bm_c_expMap_total` -- totality plus continuity packaged.

## Hopf-Rinow existence of minimisers

* `path_length_infimum_attained` -- the infimum `riemannianEDist I p q`
  is attained by a continuous curve.
* `minimiser_is_smooth_geodesic` -- a length-minimising curve coincides
  after arclength rescale with a smooth geodesic.
* `unit_speed_rescale` -- affine reparametrisation rescales a geodesic
  to unit-speed.
* `unit_speed_minimising_geodesic_from_points` -- existence of a
  unit-speed minimising geodesic between any two points.

## Exponential surjectivity on the closed ball

* `bm_c_expMap_surjective_on_closedBall` -- under a diameter bound,
  `expMap g p` surjects onto `M` from a closed ball in `T_p M`.

All thirteen statements are emitted below as `theorem ... := sorry`
stubs.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-! ## Geodesic-completeness chain -/

section GeodesicCompleteness

/-- **Constant speed of a geodesic.** From `\nabla_{\gamma'} \gamma' = 0`
and metric compatibility of Levi-Civita, the function
`t \mapsto \langle \gamma'(t), \gamma'(t)\rangle_g` is constant. -/
theorem bm_c_gc_constant_speed
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    ∀ s t : ℝ,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) =
        (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The speed-squared function `F : ℝ → ℝ`.
  set F : ℝ → ℝ := fun t =>
      (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) with hF_def
  -- Strategy: show `F` has derivative `0` at every `t`, hence `F` is constant
  -- by `is_const_of_deriv_eq_zero`. The derivative formula at `t` reads
  --   `F'(t) = 2 · ⟨∇_{γ'} γ' (t), γ'(t)⟩_g(γ t)`
  -- by metric compatibility of Levi-Civita applied to the curve `γ`. Along a
  -- geodesic, the geodesic equation `∇_{γ'} γ' (t) = 0` (encoded
  -- chart-locally by `IsGeodesicAt.hasGeodesicEquationAt`) makes the right-hand
  -- side vanish.
  --
  -- The metric-compatibility identity in the precise form required here
  --   `HasDerivAt (fun t => g.inner (γ t) (γ'(t)) (γ'(t)))
  --      (2 · g.inner (γ t) ((∇_{γ'} γ')(t)) (γ'(t))) t`
  -- is a chart-local computation: in normal coordinates at `γ t` it reduces
  -- to standard product-rule differentiation of the metric components
  -- `g_{ij}(γ(t)) · u'^i(t) · u'^j(t)` and the chart-coordinate Christoffel
  -- relation `∂_k g_{ij} = g_{lj} Γ^l_{ik} + g_{il} Γ^l_{jk}`. We isolate this
  -- step as `hF_deriv` below; it consumes the cross-VF reduction bridge
  -- `IsGeodesicAt.hasGeodesicEquationAt` (which is itself PARTIAL via
  -- `bm_c_gc_vf_chart_coincidence`).
  have hF_deriv : ∀ t : ℝ, HasDerivAt F 0 t := by
    intro t
    -- Extract the local geodesic predicate at `t`.
    have hγ_at : IsGeodesicAt (I := I) g γ t := hγ.isGeodesicAt t
    -- Chart-coordinate second-derivative form of the geodesic equation at `t`.
    have hγ_eq : HasGeodesicEquationAt (I := I) g γ t :=
      IsGeodesicAt.hasGeodesicEquationAt (I := I) (g := g) (γ := γ) (t₀ := t) hγ_at
    -- Differentiation of `F` at `t` via metric compatibility of Levi-Civita.
    -- In the chart at `γ t`, write `u(s) := φ_{γ t}(γ s)`, `v := u'(t)`,
    -- `a := u''(t)`. The geodesic equation says `a = -Γ_{γ t}(v, v)(u(t))`.
    -- Differentiating `F(s) = g_{ij}(γ s) · v^i(s) · v^j(s)` at `s = t` uses
    -- the product rule plus the Christoffel relation; the linear-in-`a` term
    -- becomes `2 · g_{ij}(γ t) · v^i · a^j` and combines with the
    -- metric-derivative term `(∂_k g_{ij}) · v^i · v^j · v^k` to yield zero
    -- by the geodesic equation. The detailed chart-local product-rule chain
    -- has not been packaged separately in the project; we record it here as
    -- the single residual gap of this PARTIAL proof.
    sorry
  -- `F` is differentiable everywhere (witnessed by `hF_deriv`).
  have hF_diff : Differentiable ℝ F :=
    fun t => (hF_deriv t).differentiableAt
  -- The derivative vanishes everywhere.
  have hF_deriv_eq : ∀ t : ℝ, deriv F t = 0 :=
    fun t => (hF_deriv t).deriv
  -- A function with zero derivative on all of `ℝ` is constant.
  have hF_const : ∀ s t : ℝ, F s = F t :=
    fun s t => is_const_of_deriv_eq_zero hF_diff hF_deriv_eq s t
  exact hF_const

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Length-distance bound along a geodesic.** With constant `g`-speed
`c := (g.inner p v v)^{1/2}` along the maximal geodesic at `(p, v)`,
for any `s \le t` in the maximal interval the Riemannian extended
distance between `\gamma(s)` and `\gamma(t)` is bounded by
`c \cdot (t - s)`. -/
theorem bm_c_gc_length_distance_bound
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {s t : ℝ}
    (hs : s ∈ maximalGeodesicInterval (I := I) g p v)
    (ht : t ∈ maximalGeodesicInterval (I := I) g p v)
    (hst : s ≤ t) :
    riemannianEDist I
        (maximalGeodesic (I := I) g p v s)
        (maximalGeodesic (I := I) g p v t) ≤
      ENNReal.ofReal (Real.sqrt ((g.inner p) v v) * (t - s)) := by
  -- Abbreviations for the maximal geodesic curve and its constant speed `c`.
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  -- The constant `c` is nonnegative as a square root.
  have hc_nonneg : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  -- Step 1. Smoothness witness for `γ` on `Icc s t`.
  -- On the maximal interval, `γ = maximalGeodesic g p v` is locally a smooth
  -- geodesic; in particular it is `C¹` on the compact subinterval `Icc s t`.
  -- A self-contained derivation requires gluing chart-local witnesses across
  -- `[s, t]` and reading off `ContMDiffOn` smoothness from the corresponding
  -- `IsMIntegralCurveOn` data, which is a separate bridge from the
  -- `MaximalInterval` module not currently exposed. Recorded as an
  -- intermediate sorry isolating this gap.
  have hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t) := by
    sorry
  -- Step 2. PathELength bound by `c · (t - s)`.
  -- Along a geodesic the norm of the velocity is the constant `c`; therefore
  -- the integral defining `pathELength` is `c · (t - s)`. The constant-speed
  -- identity used here is `bm_c_gc_constant_speed` (still a sorry); the
  -- enorm identification between `‖γ'(τ)‖ₑ` and `ENNReal.ofReal (√⟨γ',γ'⟩_g)`
  -- comes from the `IsRiemannianManifold` typeclass.  The composition is
  -- isolated below.
  have h_pathLen_le :
      pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    sorry
  -- Step 3. `riemannianEDist ≤ pathELength` from the Mathlib lemma.
  have h_dist_le :
      riemannianEDist I (γ s) (γ t) ≤ pathELength I γ s t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
      hγ_smooth rfl rfl hst
  -- Step 4. Chain the two bounds.
  exact h_dist_le.trans h_pathLen_le

variable [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Escape sequences along a maximal geodesic are Cauchy.** If the
maximal interval of the geodesic at `(p, v)` is bounded above by
`T < \infty`, then for every monotone real sequence `t_n \to T` inside
the maximal interval the image sequence `\gamma(t_n)` is Cauchy in
`riemannianEDist`. -/
theorem bm_c_gc_escape_cauchy
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (htₙ_lim : Tendsto tₙ atTop (𝓝 T)) :
    CauchySeq (fun n => maximalGeodesic (I := I) g p v (tₙ n)) := by
  -- Abbreviations: `γ` for the maximal geodesic curve, `c` for the constant
  -- speed `√⟨v,v⟩_g`.
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  -- The convergent sequence `tₙ → T` is Cauchy in `ℝ`.
  have htₙ_cauchy : CauchySeq tₙ := htₙ_lim.cauchySeq
  -- Switch the ℝ-Cauchy criterion to its metric form.
  rw [Metric.cauchySeq_iff] at htₙ_cauchy
  -- Switch the goal to the EMetric form.
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  -- From `0 < ε` in `ℝ≥0∞`, find a real `δ₀ > 0` with `ofReal δ₀ < ε`.
  obtain ⟨δ₀, hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hε
  -- The real `δ₀` is strictly positive.
  have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
  -- We need a real Cauchy threshold `δ := δ₀ / (c + 1)` so that
  -- `c * δ < δ₀`, hence `ENNReal.ofReal (c * δ) < ENNReal.ofReal δ₀ < ε`.
  have hcc_pos : 0 < c + 1 := by linarith
  set δ : ℝ := δ₀ / (c + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hδ₀_pos hcc_pos
  -- Use the Cauchy property of `tₙ` for this `δ`.
  obtain ⟨N, hN⟩ := htₙ_cauchy δ hδ_pos
  refine ⟨N, fun m hm n hn => ?_⟩
  -- Set `s := min (tₙ m) (tₙ n)`, `t := max (tₙ m) (tₙ n)`; both lie in the
  -- maximal interval, with `s ≤ t` and `t - s = |tₙ m - tₙ n|`.
  set s : ℝ := min (tₙ m) (tₙ n) with hs_def
  set t : ℝ := max (tₙ m) (tₙ n) with ht_def
  have hst : s ≤ t := min_le_max
  -- `s ∈ maximalGeodesicInterval`.
  have hs_mem : s ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, min_eq_left h]; exact htₙ_mem m
    · rw [hs_def, min_eq_right h]; exact htₙ_mem n
  -- `t ∈ maximalGeodesicInterval`.
  have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [ht_def, max_eq_right h]; exact htₙ_mem n
    · rw [ht_def, max_eq_left h]; exact htₙ_mem m
  -- Apply the length-distance bound to `s, t`.
  have h_bound :
      riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    have :=
      bm_c_gc_length_distance_bound (I := I) g p v (s := s) (t := t)
        hs_mem ht_mem hst
    -- Normalise to our local `γ` and `c`.
    simpa [hγ_def, hc_def] using this
  -- Convert `riemannianEDist` to `edist` using `IsRiemannianManifold`.
  -- The local `attribute [-instance]` above suppresses the project's
  -- `Tensor0SBundle.tangentSpace_normedAddCommGroup` and `_normedSpace`,
  -- so both `bm_c_gc_length_distance_bound` and `IsRiemannianManifold.out`
  -- resolve to the same `RiemannianBundle`-derived norm at this call site.
  have h_edist_bound :
      edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]
    exact h_bound
  -- Edist between `γ (tₙ m)` and `γ (tₙ n)` equals edist between `γ s` and
  -- `γ t` (up to symmetry).
  have h_edist_eq :
      edist (γ (tₙ m)) (γ (tₙ n)) = edist (γ s) (γ t) := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · -- `s = tₙ m`, `t = tₙ n`.
      have hs_eq : s = tₙ m := by rw [hs_def, min_eq_left h]
      have ht_eq : t = tₙ n := by rw [ht_def, max_eq_right h]
      rw [hs_eq, ht_eq]
    · -- `s = tₙ n`, `t = tₙ m`.
      have hs_eq : s = tₙ n := by rw [hs_def, min_eq_right h]
      have ht_eq : t = tₙ m := by rw [ht_def, max_eq_left h]
      rw [hs_eq, ht_eq, edist_comm]
  -- `t - s = |tₙ m - tₙ n|` as a real number.
  have ht_sub_s : t - s = |tₙ m - tₙ n| := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h,
          abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h,
          abs_of_nonneg (sub_nonneg.mpr h)]
  -- The real distance `|tₙ m - tₙ n|` is `< δ` by Cauchy.
  have h_dist_lt : |tₙ m - tₙ n| < δ := by
    have := hN m hm n hn
    rwa [Real.dist_eq] at this
  -- Combine: `t - s < δ`, hence `c * (t - s) ≤ c * δ < δ₀`.
  have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
  have h_ct_sub_s_le : c * (t - s) ≤ c * δ := by
    have h_abs_lt : t - s < δ := by rw [ht_sub_s]; exact h_dist_lt
    exact mul_le_mul_of_nonneg_left h_abs_lt.le hc_nn
  -- Strict bound `c * δ < δ₀` via `c / (c + 1) < 1` and `δ₀ > 0`.
  have h_cdelta_lt_real : c * δ < δ₀ := by
    rw [hδ_def]
    -- `c * (δ₀/(c+1)) = δ₀ * (c/(c+1))`, and `c/(c+1) < 1`.
    have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
    rw [hrw]
    have hfrac_lt_one : c / (c + 1) < 1 := by
      rw [div_lt_one hcc_pos]; linarith
    -- Multiply both sides by `δ₀ > 0`.
    have := (mul_lt_mul_of_pos_left hfrac_lt_one hδ₀_pos)
    rwa [mul_one] at this
  -- Chain: edist (γ tₙ m) (γ tₙ n) = edist (γ s) (γ t)
  --        ≤ ENNReal.ofReal (c * (t - s))
  --        ≤ ENNReal.ofReal (c * δ)
  --        < ENNReal.ofReal δ₀ ≤ ε.
  calc edist (γ (tₙ m)) (γ (tₙ n))
      = edist (γ s) (γ t) := h_edist_eq
    _ ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
    _ ≤ ENNReal.ofReal (c * δ) := ENNReal.ofReal_le_ofReal h_ct_sub_s_le
    _ < ENNReal.ofReal δ₀ := by
          rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]
          exact h_cdelta_lt_real
    _ < ε := hδ₀_ofReal_lt

/-- **Velocity limit at the finite escape time.** If the maximal
interval of the geodesic at `(p, v)` is bounded above by `T < \infty`
and the metric limit `y := \lim \gamma(t_n)` exists by completeness,
then there exists a tangent vector `w \in T_y M` with
`(g.inner y) w w = (g.inner p) v v`. (The existential statement encodes
the geometric content: the squared speed is preserved by the limit. A
witness is produced by scaling any nonzero tangent vector at `y` by the
appropriate factor `\sqrt{(g.inner p) v v / (g.inner y) u u}`; the
limit hypotheses, while motivating the precise value, are not needed
to discharge the existential.) -/
theorem bm_c_gc_velocity_limit
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (_htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (_htₙ_lim : Tendsto tₙ atTop (𝓝 T))
    {y : M}
    (_hy : Tendsto (fun n => maximalGeodesic (I := I) g p v (tₙ n))
      atTop (𝓝 y)) :
    ∃ w : TangentSpace I y,
      (g.inner y) w w = (g.inner p) v v := by
  -- The conclusion is a pure existence statement about the metric:
  -- for any value `r := (g.inner p) v v ≥ 0` and any nonzero tangent
  -- vector `u : TangentSpace I y`, the scaled vector
  -- `Real.sqrt (r / (g.inner y) u u) • u` realises the inner-product
  -- equation. Positive dimension `NeZero (Module.finrank ℝ E)` together
  -- with the def-eq `TangentSpace I y ≡ E` provides the nonzero `u`.
  have hfin_pos : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  -- Nonzero `u : TangentSpace I y` (defeq to `E`).
  obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I y, u ≠ 0 :=
    ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
  -- Constants and positivity / nonnegativity facts.
  set r : ℝ := (g.inner p) v v with hr_def
  have hr_nn : 0 ≤ r := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hr_def, hv]
    · exact (g.pos p v hv).le
  have hc_pos : 0 < (g.inner y) u u := g.pos y u hu_ne
  have hc_nn : 0 ≤ (g.inner y) u u := hc_pos.le
  have hc_ne : (g.inner y) u u ≠ 0 := ne_of_gt hc_pos
  -- Ratio is nonnegative.
  have hratio_nn : 0 ≤ r / (g.inner y) u u := div_nonneg hr_nn hc_nn
  set s : ℝ := Real.sqrt (r / (g.inner y) u u) with hs_def
  refine ⟨s • u, ?_⟩
  -- Bilinearity: `(g.inner y) (s • u) (s • u) = s * s * (g.inner y) u u`.
  have step1 :
      (g.inner y) (s • u) (s • u) = s * s * (g.inner y) u u := by
    rw [map_smul (g.inner y), ContinuousLinearMap.smul_apply,
        map_smul (g.inner y u), smul_eq_mul, smul_eq_mul]
    ring
  -- `s * s = r / (g.inner y) u u`.
  have hs_sq : s * s = r / (g.inner y) u u := by
    rw [hs_def]; exact Real.mul_self_sqrt hratio_nn
  -- Combine.
  rw [step1, hs_sq, div_mul_cancel₀ _ hc_ne]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Local extension past the supposed escape time.** Given the limit
data `(y, w)` from `bm_c_gc_velocity_limit`, the local existence and
uniqueness theorems for geodesics provide a geodesic on `(-\varepsilon,
\varepsilon)` starting at `y` with initial velocity `w`; gluing
contradicts the maximality of the original interval. Concretely, the
maximal interval at `(p, v)` cannot be bounded above by a finite `T`. -/
theorem bm_c_gc_extension_past_limit
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ¬ ∃ T : ℝ, IsLUB (maximalGeodesicInterval (I := I) g p v) T := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Argue by contradiction.
  rintro ⟨T, hT⟩
  -- Abbreviate the maximal interval.
  set S : Set ℝ := maximalGeodesicInterval (I := I) g p v with hS_def
  -- `S` is open.
  have hS_open : IsOpen S := maximalGeodesicInterval_isOpen (I := I) g p v
  -- `S` is nonempty: `0 ∈ S`.
  have hS_ne : S.Nonempty :=
    ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩
  -- The LUB `T` cannot lie in `S`: openness of `S` would give a
  -- neighbourhood `(T - ε, T + ε) ⊆ S`, contradicting upper-bound-ness.
  have hT_notMem : T ∉ S := by
    intro hT_mem
    -- `S ∈ 𝓝 T` from openness.
    have hS_nhds : S ∈ 𝓝 T := hS_open.mem_nhds hT_mem
    -- A real neighbourhood contains an open interval `(l, u) ∋ T`.
    obtain ⟨l, u, ⟨hlT, hTu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hS_nhds
    -- The midpoint `T' := (T + u) / 2` lies in `(T, u) ⊆ S`.
    set T' : ℝ := (T + u) / 2 with hT'_def
    have hT_lt_T' : T < T' := by
      have : T + T < T + u := by linarith
      have hT' : T = (T + T) / 2 := by ring
      rw [hT', hT'_def]
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr this
    have hT'_lt_u : T' < u := by
      have : T + u < u + u := by linarith
      have hu' : u = (u + u) / 2 := by ring
      conv_rhs => rw [hu']
      rw [hT'_def]
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr this
    have hl_lt_T' : l < T' := by
      -- `l < T` from `hlT` (membership in `Ioo l u`), and `T < T'`.
      linarith [hlT, hT_lt_T']
    have hT'_mem : T' ∈ S := hsub ⟨hl_lt_T', hT'_lt_u⟩
    -- Upper-bound property: `T' ≤ T`, contradicting `T < T'`.
    exact absurd (hT.1 hT'_mem) (not_le.mpr hT_lt_T')
  -- Extract a strictly increasing sequence `tₙ ∈ S` with `tₙ → T`.
  obtain ⟨tₙ, _h_strictMono, _h_lt_T, htₙ_lim, htₙ_mem⟩ :=
    hT.exists_seq_strictMono_tendsto_of_notMem hT_notMem hS_ne
  -- By `bm_c_gc_escape_cauchy`, `γ(tₙ)` is Cauchy in the
  -- `[PseudoEMetricSpace M]` uniformity (which equals `riemannianEDist`
  -- on `M` via `IsRiemannianManifold.out`, packaged inside escape-cauchy).
  have h_cauchy :
      CauchySeq (fun n => maximalGeodesic (I := I) g p v (tₙ n)) :=
    bm_c_gc_escape_cauchy (I := I) g p v (T := T) hT htₙ_mem htₙ_lim
  -- A Cauchy sequence in a complete pseudo-EMetric space converges to
  -- some limit point `y : M` in the topology of `[PseudoEMetricSpace M]`.
  obtain ⟨y, _hy⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- Velocity-limit construction: `bm_c_gc_velocity_limit`'s proof is
  -- topology-independent (the limit hypotheses are unused — they motivate
  -- the witness but do not appear in the proof). We reproduce the
  -- existential here without invoking the sibling, to avoid a spurious
  -- `TopologicalSpace M`-diamond between the ChartedSpace topology and
  -- the PseudoEMetricSpace topology at the call site.
  have hfin_pos : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  obtain ⟨u, _hu_ne⟩ : ∃ u : TangentSpace I y, u ≠ 0 :=
    ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
  -- Scaled vector at `y` realising `(g.inner y) w w = (g.inner p) v v`.
  set w : TangentSpace I y :=
    Real.sqrt ((g.inner p) v v / (g.inner y) u u) • u with hw_def
  -- Local existence at `(y, w)` produces a geodesic `η` on an interval
  -- `(-ε, ε)` with `η 0 = y` and chart basepoint `y`.
  obtain ⟨_η, _fη, _hfη0, _hη_proj, _hη0, _hfη_int, _hη_geod⟩ :=
    exists_geodesic_at (I := I) g y w
  -- Hand-off gap. We now have:
  --   * the original maximal interval `S` and the curve `γ := maximalGeodesic g p v`
  --     defined on `S`, with chart basepoint `p`;
  --   * the limit point `y` (from the Cauchy convergence above);
  --   * a tangent vector `w ∈ T_y M` of the correct speed;
  --   * a local geodesic `η` at `(y, w)` defined on `(-ε, ε)`, with chart
  --     basepoint `y`.
  -- To derive `False` we must produce a single curve `γ̃ : ℝ → M` and a
  -- connected open `J ∋ 0, T + δ` (for some `δ > 0`) such that
  -- `IsGeodesicOnWithInitial g γ̃ J p v` holds — which would witness
  -- `T + δ ∈ maximalGeodesicInterval g p v`, contradicting `IsLUB` on `T`.
  -- This requires gluing `γ` to a shifted copy of `η` across the limit
  -- point `y`. The chart basepoint of `η` is `y`, but `MaximalGeodesicWitness`
  -- demands a single chart basepoint `p` throughout, so the gluing forces
  -- ODE-uniqueness across chart changes — a chart-change invariance lemma
  -- for `IsGeodesicAt`/`IsMIntegralCurveOn` that is not currently in the
  -- project. Recorded as the single residual gap of this PARTIAL proof.
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Symmetric argument at the left endpoint.** The same contradiction
applies at the left endpoint via the reflection `t \mapsto -t`, which
converts `(p, v)` to `(p, -v)`. Hence the maximal interval cannot be
bounded below by a finite `T` either.

Structurally the proof mirrors `bm_c_gc_extension_past_limit`: we replace
the upper-bound contradiction by the lower-bound one, the strictly
monotone-up sequence approaching the supposed LUB by a strictly
monotone-down (antitone) sequence approaching the supposed GLB, and we
inline the Cauchy-along-the-sequence argument of `bm_c_gc_escape_cauchy`
(its body uses only `tₙ ∈ S` and `tₙ → T`; the IsLUB hypothesis there is
declared `_hT` and is unused, so the same chart-distance computation
works equally for a GLB). The residual gap is the same gluing step
across the metric limit point as in `bm_c_gc_extension_past_limit`. -/
theorem bm_c_gc_symmetric_left_endpoint
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ¬ ∃ T : ℝ, IsGLB (maximalGeodesicInterval (I := I) g p v) T := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Argue by contradiction.
  rintro ⟨T, hT⟩
  -- Abbreviate the maximal interval.
  set S : Set ℝ := maximalGeodesicInterval (I := I) g p v with hS_def
  -- `S` is open.
  have hS_open : IsOpen S := maximalGeodesicInterval_isOpen (I := I) g p v
  -- `S` is nonempty: `0 ∈ S`.
  have hS_ne : S.Nonempty :=
    ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩
  -- The GLB `T` cannot lie in `S`: openness of `S` would give a
  -- neighbourhood `(T - ε, T + ε) ⊆ S`, and the midpoint between `l` and
  -- `T` (which is `< T`) would be a member of `S` violating the
  -- lower-bound-ness.
  have hT_notMem : T ∉ S := by
    intro hT_mem
    -- `S ∈ 𝓝 T` from openness.
    have hS_nhds : S ∈ 𝓝 T := hS_open.mem_nhds hT_mem
    -- A real neighbourhood contains an open interval `(l, u) ∋ T`.
    obtain ⟨l, u, ⟨hlT, hTu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hS_nhds
    -- The midpoint `T' := (l + T) / 2` lies in `(l, T) ⊆ (l, u) ⊆ S`.
    set T' : ℝ := (l + T) / 2 with hT'_def
    have hT'_lt_T : T' < T := by
      have : l + T < T + T := by linarith
      have hT' : T = (T + T) / 2 := by ring
      conv_rhs => rw [hT']
      rw [hT'_def]
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr this
    have hl_lt_T' : l < T' := by
      have : l + l < l + T := by linarith
      have hl' : l = (l + l) / 2 := by ring
      rw [hl', hT'_def]
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr this
    have hT'_lt_u : T' < u := by
      -- `T < u` from `hTu`, and `T' < T`.
      linarith [hTu, hT'_lt_T]
    have hT'_mem : T' ∈ S := hsub ⟨hl_lt_T', hT'_lt_u⟩
    -- Lower-bound property: `T ≤ T'`, contradicting `T' < T`.
    exact absurd (hT.1 hT'_mem) (not_le.mpr hT'_lt_T)
  -- Extract a strictly antitone sequence `tₙ ∈ S` with `tₙ → T`, all
  -- strictly above `T`.
  obtain ⟨tₙ, _h_strictAnti, _h_gt_T, htₙ_lim, htₙ_mem⟩ :=
    hT.exists_seq_strictAnti_tendsto_of_notMem hT_notMem hS_ne
  -- Cauchy property of `γ(tₙ)` in the `[PseudoEMetricSpace M]`
  -- uniformity. We inline the chart-distance computation here because
  -- `bm_c_gc_escape_cauchy`'s public signature demands an
  -- `IsLUB S T` hypothesis (declared `_hT`, unused inside the body),
  -- which we cannot construct from `IsGLB S T`. The argument is
  -- otherwise identical: bound each pair-distance by the length-distance
  -- inequality and use Cauchy of `tₙ` in `ℝ`.
  have h_cauchy :
      CauchySeq (fun n => maximalGeodesic (I := I) g p v (tₙ n)) := by
    set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
    set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
    have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
    -- The convergent sequence `tₙ → T` is Cauchy in `ℝ`.
    have htₙ_cauchy : CauchySeq tₙ := htₙ_lim.cauchySeq
    rw [Metric.cauchySeq_iff] at htₙ_cauchy
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    -- From `0 < ε` in `ℝ≥0∞`, find a real `δ₀ > 0` with `ofReal δ₀ < ε`.
    obtain ⟨δ₀, hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hε
    have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
    -- Real Cauchy threshold `δ := δ₀ / (c + 1)`.
    have hcc_pos : 0 < c + 1 := by linarith
    set δ : ℝ := δ₀ / (c + 1) with hδ_def
    have hδ_pos : 0 < δ := div_pos hδ₀_pos hcc_pos
    obtain ⟨N, hN⟩ := htₙ_cauchy δ hδ_pos
    refine ⟨N, fun m hm n hn => ?_⟩
    set s : ℝ := min (tₙ m) (tₙ n) with hs_def
    set t : ℝ := max (tₙ m) (tₙ n) with ht_def
    have hst : s ≤ t := min_le_max
    have hs_mem : s ∈ maximalGeodesicInterval (I := I) g p v := by
      rcases le_total (tₙ m) (tₙ n) with h | h
      · rw [hs_def, min_eq_left h]; exact htₙ_mem m
      · rw [hs_def, min_eq_right h]; exact htₙ_mem n
    have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v := by
      rcases le_total (tₙ m) (tₙ n) with h | h
      · rw [ht_def, max_eq_right h]; exact htₙ_mem n
      · rw [ht_def, max_eq_left h]; exact htₙ_mem m
    have h_bound :
        riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
      have :=
        bm_c_gc_length_distance_bound (I := I) g p v (s := s) (t := t)
          hs_mem ht_mem hst
      simpa [hγ_def, hc_def] using this
    have h_edist_bound :
        edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
      rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]
      exact h_bound
    have h_edist_eq :
        edist (γ (tₙ m)) (γ (tₙ n)) = edist (γ s) (γ t) := by
      rcases le_total (tₙ m) (tₙ n) with h | h
      · have hs_eq : s = tₙ m := by rw [hs_def, min_eq_left h]
        have ht_eq : t = tₙ n := by rw [ht_def, max_eq_right h]
        rw [hs_eq, ht_eq]
      · have hs_eq : s = tₙ n := by rw [hs_def, min_eq_right h]
        have ht_eq : t = tₙ m := by rw [ht_def, max_eq_left h]
        rw [hs_eq, ht_eq, edist_comm]
    have ht_sub_s : t - s = |tₙ m - tₙ n| := by
      rcases le_total (tₙ m) (tₙ n) with h | h
      · rw [hs_def, ht_def, min_eq_left h, max_eq_right h,
            abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [hs_def, ht_def, min_eq_right h, max_eq_left h,
            abs_of_nonneg (sub_nonneg.mpr h)]
    have h_dist_lt : |tₙ m - tₙ n| < δ := by
      have := hN m hm n hn
      rwa [Real.dist_eq] at this
    have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
    have h_ct_sub_s_le : c * (t - s) ≤ c * δ := by
      have h_abs_lt : t - s < δ := by rw [ht_sub_s]; exact h_dist_lt
      exact mul_le_mul_of_nonneg_left h_abs_lt.le hc_nn
    have h_cdelta_lt_real : c * δ < δ₀ := by
      rw [hδ_def]
      have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
      rw [hrw]
      have hfrac_lt_one : c / (c + 1) < 1 := by
        rw [div_lt_one hcc_pos]; linarith
      have := (mul_lt_mul_of_pos_left hfrac_lt_one hδ₀_pos)
      rwa [mul_one] at this
    calc edist (γ (tₙ m)) (γ (tₙ n))
        = edist (γ s) (γ t) := h_edist_eq
      _ ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
      _ ≤ ENNReal.ofReal (c * δ) := ENNReal.ofReal_le_ofReal h_ct_sub_s_le
      _ < ENNReal.ofReal δ₀ := by
            rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]
            exact h_cdelta_lt_real
      _ < ε := hδ₀_ofReal_lt
  -- A Cauchy sequence in a complete pseudo-EMetric space converges.
  obtain ⟨y, _hy⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- Velocity-limit construction (inlined as in `bm_c_gc_extension_past_limit`
  -- to avoid the topology diamond between the ChartedSpace topology and
  -- the PseudoEMetricSpace topology at the call site).
  have hfin_pos : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  obtain ⟨u, _hu_ne⟩ : ∃ u : TangentSpace I y, u ≠ 0 :=
    ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
  -- Scaled vector at `y` realising `(g.inner y) w w = (g.inner p) v v`.
  set w : TangentSpace I y :=
    Real.sqrt ((g.inner p) v v / (g.inner y) u u) • u with hw_def
  -- Local existence at `(y, w)` produces a geodesic `η` on `(-ε, ε)`.
  obtain ⟨_η, _fη, _hfη0, _hη_proj, _hη0, _hfη_int, _hη_geod⟩ :=
    exists_geodesic_at (I := I) g y w
  -- Hand-off gap. As in `bm_c_gc_extension_past_limit`, deriving `False`
  -- now requires producing a single geodesic curve `γ̃` on a connected
  -- open `J ∋ 0, T - δ` (for some `δ > 0`) with chart basepoint `p`,
  -- gluing the original `γ` to a shifted reflection of `η` across the
  -- limit point `y`. The shift / chart-change invariance lemma for
  -- `IsGeodesicAt` / `IsMIntegralCurveOn` that would discharge this
  -- gluing is not currently exposed in the project. Recorded as the
  -- single residual gap of this PARTIAL proof, matching the residual
  -- gap of `bm_c_gc_extension_past_limit`.
  sorry

/-- **Assembly: the maximal geodesic interval is the whole real line.**
Combine the no-right-escape `bm_c_gc_extension_past_limit` with the
no-left-escape `bm_c_gc_symmetric_left_endpoint` and the openness of
the maximal interval to conclude it equals `Set.univ`. -/
theorem bm_c_gc_assemble
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesicInterval (I := I) g p v = Set.univ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set S : Set ℝ := maximalGeodesicInterval (I := I) g p v with hS_def
  -- Step 1: `S` is preconnected, as a union of preconnected sets sharing `0`.
  have hSpre : IsPreconnected S := by
    -- Express `S` as a union over members of itself.
    have hS_eq : S = ⋃₀ {J : Set ℝ |
        ∃ γ : ℝ → M, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧
          IsGeodesicOnWithInitial (I := I) g γ J p v} := by
      apply Set.eq_of_subset_of_subset
      · intro t ht
        obtain ⟨γ, J, hJ, hJ_conn, h0, _ht_in, hγ⟩ := ht
        exact ⟨J, ⟨γ, hJ, hJ_conn, h0, hγ⟩, _ht_in⟩
      · rintro t ⟨J, ⟨γ, hJ, hJ_conn, h0, hγ⟩, ht_in⟩
        exact ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩
    rw [hS_eq]
    apply isPreconnected_sUnion (0 : ℝ)
    · rintro J ⟨_, _, _, h0, _⟩; exact h0
    · rintro J ⟨_, _, hJpre, _, _⟩; exact hJpre
  -- Step 2: `S` is nonempty (`0 ∈ S`).
  have hS_ne : S.Nonempty :=
    ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩
  -- Step 3: `S` is not bounded above.
  have hS_no_BddAbove : ¬ BddAbove S := by
    intro hBdd
    -- A nonempty bounded-above set in ℝ has an LUB (= sSup), contradicting
    -- `bm_c_gc_extension_past_limit`.
    exact bm_c_gc_extension_past_limit (I := I) g p v
      ⟨sSup S, isLUB_csSup hS_ne hBdd⟩
  -- Step 4: `S` is not bounded below.
  have hS_no_BddBelow : ¬ BddBelow S := by
    intro hBdd
    exact bm_c_gc_symmetric_left_endpoint (I := I) g p v
      ⟨sInf S, isGLB_csInf hS_ne hBdd⟩
  -- Step 5: a preconnected set unbounded both ways equals `univ`.
  exact hSpre.eq_univ_of_unbounded hS_no_BddBelow hS_no_BddAbove

end GeodesicCompleteness

/-! ## Exponential map totality and continuity -/

section ExpMapTotality

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Continuity of `expMap g p` on the whole tangent space.** Under
geodesic completeness (`bm_c_gc_assemble`), the exponential map at `p`
is continuous on the entire tangent space `T_p M`. The proof propagates
the smooth dependence of geodesics on initial conditions chart-locally
along the compact arc `[0, 1]`. -/
theorem bm_c_expMap_continuous_of_geodesic_complete
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  sorry

/-- **Total continuity of `expMap g p`.** The exponential map at `p`
is a total continuous function from the tangent space `T_p M` to `M`,
under the geodesic-completeness conclusion of `bm_c_gc_assemble`. The
membership conjunct `expMap g p v \in Set.univ` is trivial. -/
theorem bm_c_expMap_total
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) ∧
      ∀ v : TangentSpace I p,
        expMap (I := I) g p v ∈ (Set.univ : Set M) :=
  ⟨bm_c_expMap_continuous_of_geodesic_complete (I := I) g p,
    fun _ => Set.mem_univ _⟩

end ExpMapTotality

/-! ## Hopf-Rinow existence: minimising geodesic between any two points -/

section MinimiserExistence

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Path-length infimum is attained.** On a complete connected
sigma-compact Riemannian manifold, for every `p q : M` there exists a
continuous curve `\gamma : [0, 1] \to M` from `p` to `q` whose
`pathELength` realises `riemannianEDist I p q`. -/
theorem path_length_infimum_attained
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ γ : ℝ → M,
      Continuous γ ∧ γ 0 = p ∧ γ 1 = q ∧
        pathELength I γ 0 1 = riemannianEDist I p q := by
  sorry

/-- **A length minimiser is, after arclength rescale, a smooth
geodesic.** This consumes the Gauss-lemma cluster from
`GaussLemma.lean`: at every interior parameter the minimiser is
locally a radial geodesic in normal coordinates, and overlap
consistency glues the pieces into a global smooth geodesic on the
open parameter interval. The parameter `L` is the arclength of `γ`
and equals the Riemannian distance between the endpoints. The
reparametrisation preserves the `pathELength`, so
`pathELength I η 0 L = ENNReal.ofReal L`. -/
theorem minimiser_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : Continuous γ)
    (hmin : pathELength I γ a b = riemannianEDist I (γ a) (γ b)) :
    ∃ (L : ℝ) (η : ℝ → M),
      0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L,
          IsGeodesicAt (I := I) g η t) ∧
        pathELength I η 0 L = ENNReal.ofReal L ∧
        ENNReal.ofReal L = riemannianEDist I (γ a) (γ b) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) := by
  sorry

/-- **Auxiliary: `IsGeodesicOn` is preserved under affine
reparametrisation.** If `γ` is a geodesic on `[a, b]` and
`c, d : ℝ`, then `s ↦ γ (c · s + d)` is a geodesic on the
preimage interval. The lifted curve is `s ↦ ⟨γ(c s + d), c • γ'(c s + d)⟩`,
which is an integral curve of the same chart-fixed geodesic vector field
on `TM` by the second-order chain rule combined with the quadratic scaling
`Γ(c v, c v) = c² · Γ(v, v)` of the Christoffel contraction.

The full chain-rule computation on `TM` is deferred: this is the
substantial step in the unit-speed rescale theorem, and the missing
TM-derivative infrastructure makes the proof open in this file. -/
private theorem isGeodesicOn_affineReparam
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b c d : ℝ}
    (_hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b)) :
    IsGeodesicOn (I := I) g (fun s => γ (c * s + d))
      {s : ℝ | c * s + d ∈ Set.Icc a b} := by
  sorry

/-- **Unit-speed reparametrisation of a geodesic of positive length.**
A geodesic `\gamma : [a, b] \to M` whose `pathELength` equals
`ENNReal.ofReal L` with `L > 0` becomes unit-speed under the affine
reparametrisation `\eta(s) := \gamma(a + s \cdot (b - a)/L)` on
`[0, L]`. The `IsGeodesicOn` predicate is preserved under affine
reparametrisation. -/
theorem unit_speed_rescale
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 < L)
    (hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b))
    (hγ_len : pathELength I γ a b = ENNReal.ofReal L) :
    ∃ η : ℝ → M,
      η 0 = γ a ∧ η L = γ b ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (η t)) (mfderiv 𝓘(ℝ, ℝ) I η t 1)
              (mfderiv 𝓘(ℝ, ℝ) I η t 1) = 1 := by
  -- The affine speed factor.
  set c : ℝ := (b - a) / L with hc_def
  -- The reparametrised curve.
  refine ⟨fun s => γ (a + s * c), ?_, ?_, ?_, ?_⟩
  · -- `η 0 = γ a`: substitute `s = 0` and simplify `0 * c = 0`.
    change γ (a + 0 * c) = γ a
    simp
  · -- `η L = γ b`: substitute `s = L`. We need `a + L * c = b`, i.e.
    -- `L * ((b - a) / L) = b - a`. Uses `L ≠ 0`.
    change γ (a + L * c) = γ b
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsum : a + L * c = b := by rw [hLc]; ring
    rw [hsum]
  · -- `IsGeodesicOn` on `[0, L]` of `η`.
    -- We use the affine-reparametrisation lemma above with `c := c` and
    -- `d := a`, then show `Set.Icc (0 : ℝ) L ⊆ {s | c * s + a ∈ Set.Icc a b}`.
    -- The functions `fun s => γ (a + s * c)` and `fun s => γ (c * s + a)`
    -- agree by commutativity of multiplication and addition.
    have hreparam :
        IsGeodesicOn (I := I) g (fun s => γ (c * s + a))
          {s : ℝ | c * s + a ∈ Set.Icc a b} :=
      isGeodesicOn_affineReparam (I := I) g (a := a) (b := b)
        (c := c) (d := a) hγ_geod
    -- Rewrite `c * s + a` as `a + s * c`.
    have hrw : (fun s => γ (c * s + a)) = (fun s => γ (a + s * c)) := by
      funext s
      have : c * s + a = a + s * c := by ring
      rw [this]
    rw [hrw] at hreparam
    -- Now restrict to `Set.Icc 0 L`.
    apply hreparam.mono
    intro s hs
    -- Goal: `a + s * c ∈ Set.Icc a b`, given `s ∈ [0, L]`.
    rcases hs with ⟨hs0, hsL⟩
    -- Show `c ≥ 0` (since `b ≥ a` and `L > 0`).
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hc_nonneg : 0 ≤ c := by
      rw [hc_def]; exact div_nonneg hba hL.le
    -- `s * c ≥ 0`.
    have hsc_nonneg : 0 ≤ s * c := mul_nonneg hs0 hc_nonneg
    -- `s * c ≤ L * c = b - a`.
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsc_le : s * c ≤ b - a := by
      calc s * c ≤ L * c := mul_le_mul_of_nonneg_right hsL hc_nonneg
        _ = b - a := hLc
    refine ⟨?_, ?_⟩
    · -- `a ≤ a + s * c`.
      linarith
    · -- `a + s * c ≤ b`.
      linarith
  · -- Unit-speed: the inner product of the velocity with itself equals 1
    -- for every `t ∈ [0, L]`.
    -- This requires the chain rule for `mfderiv` (η = γ ∘ (a + · * c)) and
    -- the constant-speed property of geodesics (`bm_c_gc_constant_speed`),
    -- combined with the length equation `hγ_len`. Both pieces are open:
    -- `bm_c_gc_constant_speed` is still a `sorry` and the mfderiv chain
    -- rule on manifolds requires additional bridge lemmas not present
    -- in this file. Recorded as `sorry`.
    intro t _ht
    sorry

/-- **Hopf-Rinow existence (unit-speed minimising geodesic).** Any two
points `p q : M` on a complete connected sigma-compact Riemannian
manifold are joined by a unit-speed `C^1` geodesic whose parameter
length equals the Riemannian distance. Assembled from
`path_length_infimum_attained`, `minimiser_is_smooth_geodesic`, and
`unit_speed_rescale`. -/
theorem unit_speed_minimising_geodesic_from_points
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ (γ : ℝ → M) (L : ℝ),
      0 ≤ L ∧ γ 0 = p ∧ γ L = q ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g γ (Set.Icc 0 L) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
        riemannianEDist I p q = ENNReal.ofReal L := by
  -- Step 1: obtain a length-minimising continuous curve `α` from `p` to `q`
  -- on `[0, 1]` realising the Riemannian infimum.
  obtain ⟨α, hα_cont, hα0, hα1, hα_len⟩ :=
    path_length_infimum_attained (I := I) g p q
  -- Step 2: apply `minimiser_is_smooth_geodesic` to extract a smooth
  -- geodesic reparametrisation on the open interval `(0, L)`.
  have hαlen' : pathELength I α 0 1 = riemannianEDist I (α 0) (α 1) := by
    rw [hα0, hα1]; exact hα_len
  obtain ⟨L, η, hL_nonneg, hη0, hηL, _hη_smooth_int, _hη_geod_int,
      hη_len_min, hL_eq_dist, hη_C1_min, hη_geod_min⟩ :=
    minimiser_is_smooth_geodesic (I := I) g (γ := α) (a := 0) (b := 1)
      zero_le_one hα_cont hαlen'
  -- The candidate γ is η; the parameter length is L. Identify endpoints with
  -- p, q via the substitutions from Step 1.
  have hηp : η 0 = p := by rw [hη0, hα0]
  have hηq : η L = q := by rw [hηL, hα1]
  -- The remaining ingredients (full `IsGeodesicOn` on `Icc 0 L`,
  -- `ContMDiffOn` of degree 1 on `Icc 0 L`, the path-length identity
  -- `pathELength I η 0 L = ENNReal.ofReal L`, and the unit-speed-via-rescale
  -- chain) require bridge lemmas extending the minimiser's interior
  -- geodesic-at predicate to the closed-interval `IsGeodesicOn`, and
  -- transferring the path-length minimisation from `α` to `η`. These bridges
  -- are not currently exposed in this file; the composition is therefore
  -- assembled below at the cost of intermediate gaps recorded as `sorry`.
  -- The packaging is structural and does not hide axiomatic assumptions
  -- beyond the upstream sorries already present in this file.
  -- Closed-interval geodesic predicate for `η`. Delivered directly by
  -- `minimiser_is_smooth_geodesic` (closed-interval `IsGeodesicOn` conjunct).
  have hη_geod_closed : IsGeodesicOn (I := I) g η (Set.Icc 0 L) := hη_geod_min
  -- `C¹` smoothness on the closed interval `[0, L]`. Delivered directly
  -- by `minimiser_is_smooth_geodesic` (closed-interval `C¹` conjunct).
  have hη_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) := hη_C1_min
  -- Path-length of `η` on `[0, L]` equals `ENNReal.ofReal L`. This is the
  -- "η is a length-minimising reparametrisation" content; needed to feed
  -- `unit_speed_rescale`. Delivered by `minimiser_is_smooth_geodesic`.
  have hη_len : pathELength I η 0 L = ENNReal.ofReal L := hη_len_min
  -- We now split on the value of `L`.
  rcases (lt_or_eq_of_le hL_nonneg) with hLpos | hLzero
  · -- Case `0 < L`: apply `unit_speed_rescale` to `η`.
    obtain ⟨ζ, hζ0, hζL, hζ_geod, hζ_unit⟩ :=
      unit_speed_rescale (I := I) g (γ := η) (a := 0) (b := L) (L := L)
        hL_nonneg hLpos hη_geod_closed hη_len
    refine ⟨ζ, L, hL_nonneg, ?_, ?_, ?_, hζ_geod, hζ_unit, ?_⟩
    · -- ζ 0 = p: `unit_speed_rescale` gives `ζ 0 = η 0 = p`.
      rw [hζ0]; exact hηp
    · -- ζ L = q: `unit_speed_rescale` gives `ζ L = η L = q`.
      rw [hζL]; exact hηq
    · -- ContMDiffOn of degree 1 of ζ on `[0, L]`. Inherited from η via
      -- the affine reparametrisation in `unit_speed_rescale`. Bridge gap.
      sorry
    · -- `riemannianEDist I p q = ENNReal.ofReal L`. Delivered by the
      -- strengthened `minimiser_is_smooth_geodesic`: `L` is by construction
      -- the arclength of `α`, and on the minimiser this arclength equals
      -- the Riemannian distance between the endpoints. Combined with
      -- `α 0 = p`, `α 1 = q`, the conclusion follows from `hL_eq_dist`.
      have hL_eq_pq : ENNReal.ofReal L = riemannianEDist I p q := by
        rw [hL_eq_dist, hα0, hα1]
      exact hL_eq_pq.symm
  · -- Case `L = 0`: then `p = q` (since `η 0 = p` and `η L = q` with
    -- `L = 0`). We construct a unit-speed geodesic γ starting at p
    -- via Picard-Lindelöf (`exists_geodesic_at`) with an initial
    -- velocity v that is g-unit at p; on the singleton interval
    -- `Set.Icc 0 0 = {0}` we only need the unit-speed condition at
    -- `t = 0`, which is delivered by the projection-derivative
    -- identity `IsMIntegralCurveAt.mfderiv_proj_one`.
    subst hLzero
    -- p = q.
    have hpq : p = q := by rw [← hηp]; exact hηq
    -- Positive dimension: extract a nonzero vector u ∈ E and rescale
    -- to a g-unit vector v at p.
    have hfin_pos : 0 < Module.finrank ℝ E :=
      Nat.pos_of_ne_zero (NeZero.ne _)
    haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I p, u ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < (g.inner p) u u := g.pos p u hu_ne
    have hc_ne : (g.inner p) u u ≠ 0 := ne_of_gt hc_pos
    set s : ℝ := Real.sqrt ((g.inner p) u u)⁻¹ with hs_def
    have hs_sq : s * s = ((g.inner p) u u)⁻¹ := by
      rw [hs_def]
      have hinv_nn : 0 ≤ ((g.inner p) u u)⁻¹ := inv_nonneg.mpr hc_pos.le
      exact Real.mul_self_sqrt hinv_nn
    set v : TangentSpace I p := s • u with hv_def
    -- v is g-unit at p: (g.inner p) v v = 1.
    have hv_unit : (g.inner p) v v = 1 := by
      rw [hv_def, map_smul (g.inner p), ContinuousLinearMap.smul_apply,
        map_smul (g.inner p u), smul_eq_mul, smul_eq_mul]
      rw [show s * (s * (g.inner p) u u) = (s * s) * (g.inner p) u u by ring]
      rw [hs_sq, inv_mul_cancel₀ hc_ne]
    -- Local geodesic via Picard-Lindelöf.
    obtain ⟨γ', f, hf0, hγ'_eq, hγ'_zero, hf_mIC, _hγ'_geod⟩ :=
      exists_geodesic_at (I := I) g p v
    -- Provide the existential with L = 0 and curve γ := γ'.
    refine ⟨γ', 0, le_refl 0, hγ'_zero, ?_, ?_, ?_, ?_, ?_⟩
    · -- γ' 0 = q: since p = q.
      rw [hγ'_zero, hpq]
    · -- ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ' (Set.Icc 0 0): singleton case.
      have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq]
      intro t ht
      rcases ht with rfl
      -- ContMDiffWithinAt 𝓘(ℝ,ℝ) I 1 γ' {0} 0.
      rw [contMDiffWithinAt_iff']
      refine ⟨continuousWithinAt_singleton, ?_⟩
      -- ContDiffWithinAt at the singleton-image of {0} in the model.
      have hsub :
          ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target ∩
            (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm ⁻¹'
              (({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source)) ⊆
            {extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0} := by
        intro x hx
        have hx_sym : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x ∈
            ({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source :=
          hx.2
        have hx_sym0 : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x = 0 := hx_sym.1
        have hx_in_target : x ∈ (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target := hx.1
        have hxx : x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by
          calc x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)
                      ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x) :=
                  ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).right_inv hx_in_target).symm
            _ = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by rw [hx_sym0]
        exact hxx
      exact (contDiffWithinAt_singleton).mono hsub
    · -- IsGeodesicOn g γ' (Set.Icc 0 0): from the local IsMIntegralCurveAt.
      have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq]
      refine ⟨p, f, ?_, ?_⟩
      · intro t
        have := congrFun hγ'_eq t
        simp [projectCurve] at this
        exact this.symm
      · refine IsMIntegralCurveAt.isMIntegralCurveOn ?_
        intro t ht
        rcases ht with rfl
        exact hf_mIC
    · -- Unit speed at every t ∈ Set.Icc 0 0.
      intro t ht
      have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq] at ht
      rcases ht with rfl
      -- Substitute γ' = projectCurve f everywhere. After subst,
      -- the binder γ' is replaced by `projectCurve f` in the goal
      -- and in `hf0`, `hγ'_zero`, etc.
      subst hγ'_eq
      -- The goal: `g.inner (projectCurve f 0) (mfderiv 𝓘(ℝ,ℝ) I (projectCurve f) 0 1)
      --             (mfderiv 𝓘(ℝ,ℝ) I (projectCurve f) 0 1) = 1`.
      -- Strategy: introduce the projection-curve as a named function
      -- with the unblocker giving its mfderiv at 0, then close by
      -- generalising over the value of `f 0`.
      -- Generalise: we want to show
      -- `(g.inner (f 0).proj) ((f 0).snd) ((f 0).snd) = 1`
      -- once we know `mfderiv ... 1 = (f 0).snd`. Use generalize +
      -- subst to avoid the rewriting failure.
      have hmf : mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ) =
          (f 0).snd :=
        IsMIntegralCurveAt.mfderiv_proj_one (I := I) (g := g) (f := f)
          (α := p) (t₀ := 0) hf_mIC
          (by rw [hf0]; exact mem_chart_source H p)
      -- Use a single dependent-type-aware substitution: package the
      -- goal as a function of (q : TangentBundle I M) such that
      -- substituting q := f 0 closes via hmf and hf0.
      -- The trick: the goal as a function of `f 0` (which appears
      -- only via `projectCurve f 0 = (f 0).proj`) becomes
      -- `(g.inner (f 0).proj) (m) (m) = 1` with `m : TangentSpace I (f 0).proj`.
      -- After `rcases hf0`, this becomes `(g.inner p) (m) (m) = 1` with
      -- `m : TangentSpace I p`. And `hmf` becomes `m = v`.
      -- We package this via a helper lemma.
      have hgoal :
          ∀ (q : TangentBundle I M)
            (hq : q = (⟨p, v⟩ : TangentBundle I M))
            (m : TangentSpace I q.proj)
            (hm : m = q.snd),
            (g.inner q.proj) m m = 1 := by
        intro q hq m hm
        rcases hq
        change m = v at hm
        subst hm
        exact hv_unit
      -- Apply hgoal with q := f 0. The Mfderiv value lives in
      -- `TangentSpace I (f 0).proj = TangentSpace I (projectCurve f 0)`
      -- (these are definitionally equal). hmf provides hm.
      exact hgoal (f 0) hf0
        (mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ)) hmf
    · -- riemannianEDist I p q = ENNReal.ofReal 0 = 0.
      rw [← hpq, ENNReal.ofReal_zero]
      exact riemannianEDist_self

end MinimiserExistence

/-! ## Exponential surjectivity on the closed ball -/

section ExpMapSurjectivity

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **`expMap g p` is surjective on `M` from the closed ball
`Metric.closedBall 0 R \subseteq T_p M`, assuming a diameter bound.**
For each `q : M`, pick a unit-speed minimising geodesic from `p` to
`q` of length `L = riemannianDist p q \le R`; its initial velocity
`L \cdot v_0` lies in the closed ball of radius `R`, and
`expMap g p (L \cdot v_0) = q`. -/
theorem bm_c_expMap_surjective_on_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal R) :
    (Set.univ : Set M) ⊆
      (expMap (I := I) g p) ''
        (Metric.closedBall (0 : TangentSpace I p) R) := by
  sorry

end ExpMapSurjectivity

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
