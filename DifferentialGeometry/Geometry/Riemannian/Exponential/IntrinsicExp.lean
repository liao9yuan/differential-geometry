import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.TangentNormDiamond

set_option linter.unusedSectionVars false

/-!
# The intrinsic exponential map of a complete Riemannian manifold

The chart-fixed exponential map `expMap g p v = maximalGeodesic g p v 1`
(`Exponential/Definition.lean`) follows the geodesic spray written in the single
chart at `p`.  That object is junk once the geodesic leaves `(chartAt H p).source`,
so on a multi-chart manifold `expMap g p v` reverts to `p` for large `v`.

For the metric-geometry program (e.g. the compactness/diameter theorems) one needs
the *intrinsic* exponential map: the value at `t = 1` of the **complete** geodesic
through `p` with initial velocity `v`, where "complete" means defined on all of `ℝ`
via the moving-foot geodesic predicate `IsGeodesic` (chart-independent).

## Main objects

* `exists_complete_geodesic_at_velocity` — existence of a two-sided complete
  geodesic `Γ : ℝ → M` with `Γ 0 = p` and launch velocity `v`.  Built from the
  local seed `exists_isGeodesicOn_Ioo_at_velocity` and the metric-completeness
  forward/backward extension `isGeodesicOn_Ici_of_complete`.
* `intrinsicGeodesic g p v : ℝ → M` — the chosen complete geodesic.
* `expMapIntrinsic g p v : M := intrinsicGeodesic g p v 1` — the intrinsic
  exponential map.

## Status of this file

The forward/backward completeness extension engine
`HopfRinow.isGeodesicOn_Ici_of_complete` is seeded by a geodesic on a
*left-unbounded* interval `Iio b₀`.  The local seed
`exists_isGeodesicOn_Ioo_at_velocity` only produces a geodesic on a *bounded*
interval `Ioo (-δ) δ`.  Bridging the two — an `Ioo`-seeded completeness engine,
or equivalently a two-sided complete-extension producer — is the single missing
analytic input recorded as the residual of
`exists_complete_geodesic_at_velocity` below.  The downstream definitions and
their specification lemmas are stated against that existential so that, once it
is discharged, the intrinsic exponential map is available with no further work.
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

/-! ## Two-sided geodesic completeness at a prescribed launch velocity

Throughout this section every declaration carries the completeness context
`[PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]` together
with `[IsContinuousRiemannianBundle E (fun x ↦ TangentSpace I x)]`.  The latter
binder, and the fibrewise `g`-inner product it depends on, can only be
synthesised once the project's competing fibre-norm instances
`Tensor0SBundle.tangentSpace_normedAddCommGroup` /
`Tensor0SBundle.tangentSpace_normedSpace` are locally removed (otherwise the
norm diamond hides the `RiemannianBundle`-derived inner product); hence the
`attribute [-instance] … in` prefix on every such declaration, mirroring the
pattern used throughout `HopfRinow`.
-/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Velocity enorm bound from a squared-speed bound (the norm-diamond bridge).**
Given the ambient fibre-norm — square-root inner-product compatibility
`hEnorm : ‖·‖ₑ = ENNReal.ofReal (√(g.inner …))` (the same structural fact threaded
throughout the Hopf-Rinow / Bonnet-Myers pipeline as an explicit hypothesis), a
squared `g`-speed bound `g.inner x w w ≤ c²` (with `c ≥ 0`) yields the fibre
enorm bound `‖w‖ₑ ≤ ENNReal.ofReal c`. -/
private lemma velocity_enorm_le_of_speedSq_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {x : M} {w : TangentSpace I x} {c : ℝ}
    (hc : 0 ≤ c) (hle : g.inner x w w ≤ c ^ 2) :
    ‖w‖ₑ ≤ ENNReal.ofReal c := by
  rw [hEnorm x w]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `√(g.inner x w w) ≤ √(c²) = c`.
  calc Real.sqrt (g.inner x w w) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hle
    _ = c := by rw [Real.sqrt_sq hc]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`hreg` data for a constant-speed geodesic extending a seed.**  Given a
local seed `η` (a geodesic on `Ioo a₀ δ`, continuous there) whose squared speed
at the launch time `0` is `g.inner (η 0) (η'(0)) (η'(0)) ≤ c²` (with `c ≥ 0`),
and the ambient fibre-norm — square-root inner-product compatibility `hEnorm`,
every geodesic `γ` on `Ioo a₀ b` that is continuous there and agrees with `η` on
the agreement window has constant `g`-speed `≤ c²`, is `C¹`, and has its velocity
enorm bounded by `c`.  This is exactly the per-extension analytic record
`isGeodesicOn_Ici_of_complete_Ioo` consumes. -/
private lemma isGeodesicOn_hreg_record
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {η γ : ℝ → M} {a₀ δ b c : ℝ}
    (ha₀ : a₀ < 0) (hδ : 0 < δ) (hc_nonneg : 0 ≤ c)
    (hηspeed : (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) ≤ c ^ 2)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b))
    (hγ_cont : ContinuousOn γ (Set.Ioo a₀ b)) (hb : 0 < b)
    (hagree : ∀ t, a₀ < t → t < δ → t < b → γ t = η t) :
    ∃ c : ℝ, 0 ≤ c ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a₀ b) ∧
      (∀ τ ∈ Set.Ioo a₀ b, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal c) ∧
      (∀ s ∈ Set.Ioo a₀ b, (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2) := by
  -- The agreement window `(a₀, min δ b)` is an open neighbourhood of `0` on which
  -- `γ = η`, so `γ` and `η` share value and velocity at `0`.
  have hagree_nhds : γ =ᶠ[nhds (0 : ℝ)] η := by
    have hwin_open : IsOpen (Set.Ioo a₀ (min δ b)) := isOpen_Ioo
    have hwin_mem : (0 : ℝ) ∈ Set.Ioo a₀ (min δ b) := ⟨ha₀, lt_min hδ hb⟩
    refine Filter.eventually_of_mem (hwin_open.mem_nhds hwin_mem) ?_
    intro t ht
    exact hagree t ht.1 (lt_of_lt_of_le ht.2 (min_le_left _ _))
      (lt_of_lt_of_le ht.2 (min_le_right _ _))
  have hγ0 : γ 0 = η 0 := hagree_nhds.eq_of_nhds
  have hmfderiv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 = mfderiv 𝓘(ℝ, ℝ) I η 0 :=
    hagree_nhds.mfderiv_eq
  -- `C¹` regularity of `γ` on the open set `Ioo a₀ b`.
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a₀ b) :=
    HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_Ioo hγ hγ_cont
  -- The squared speed is constant `= g.inner (η 0) (η'(0)) (η'(0)) ≤ c²`
  -- throughout `Ioo a₀ b`.
  have hspeedSq : ∀ s ∈ Set.Ioo a₀ b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        ≤ c ^ 2 := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Ioo a₀ b := ⟨ha₀, hb⟩
    -- `Icc (min 0 s) (max 0 s) ⊆ Ioo a₀ b` by order-connectedness.
    have hIcc : Set.Icc (min 0 s) (max 0 s) ⊆ Set.Ioo a₀ b := by
      have hmin : min (0 : ℝ) s ∈ Set.Ioo a₀ b := by
        rcases le_total (0 : ℝ) s with h | h
        · rwa [min_eq_left h]
        · rwa [min_eq_right h]
      have hmax : max (0 : ℝ) s ∈ Set.Ioo a₀ b := by
        rcases le_total (0 : ℝ) s with h | h
        · rwa [max_eq_right h]
        · rwa [max_eq_left h]
      exact (Set.ordConnected_Ioo).out hmin hmax
    have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := 0) (t₁ := s)
      isOpen_Ioo hγ hγ_C1 hIcc
    -- Speed at `s` equals speed at `0` (constant speed); at `0` it equals the
    -- seed's launch speed `≤ c²`.
    rw [← hconst, hγ0, hmfderiv0]
    exact hηspeed
  refine ⟨c, hc_nonneg, hγ_C1, ?_, hspeedSq⟩
  -- Enorm bound from the squared-speed bound via the norm-diamond bridge.
  intro τ hτ
  exact velocity_enorm_le_of_speedSq_le (I := I) g hEnorm hc_nonneg (hspeedSq τ hτ)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Two-sided geodesic completeness.**  On a complete Riemannian manifold,
for every base point `p` and tangent vector `v : T_p M` there is a geodesic
`Γ : ℝ → M` defined on all of `ℝ` with `Γ 0 = p` and launch velocity `v`
(`mfderiv Γ 0 1 = v`).

This is the chart-independent, genuinely complete object that the chart-fixed
`expMap` fails to provide: it follows the moving-foot geodesic equation at every
real time, so it remains valid after the geodesic leaves the home chart at `p`.

The fibre-norm — square-root inner-product compatibility `hEnorm` ties the
ambient bundle norm `‖·‖ₑ` to the metric `g` (the same structural hypothesis
threaded throughout the Hopf-Rinow / Bonnet-Myers pipeline); without it the
ambient norm is unrelated to `g`, so it is a genuine mathematical input rather
than a packaging of the conclusion.

CONSTRUCTION:

* SEED: `HopfRinow.exists_isGeodesicOn_Ioo_at_velocity g p v` gives a local
  geodesic `η` on `Ioo (-δ) δ` with `η 0 = p` and `mfderiv η 0 1 = v`.
* FORWARD: `HopfRinow.isGeodesicOn_Ici_of_complete_Ioo` (the `Ioo`-seeded
  forward-completeness engine) extends `η` to a geodesic on `Ioi (-δ/2)`,
  agreeing with `η` below `δ`.  Its per-extension regularity record is the
  constant-speed `hreg` data supplied by `isGeodesicOn_hreg_record`.
* BACKWARD: the same engine applied to the time-reversal `t ↦ η (-t)` extends
  left; reflecting gives a geodesic on `Iio (δ/2)`.
* GLUE at `0`: both halves agree with `η` on `Ioo (-δ/2) (δ/2)`, so the
  `if t < 0` assembly is a geodesic on all of `ℝ` (checked pointwise by
  locality), preserving the value `p` and velocity `v` at `0`. -/
theorem exists_complete_geodesic_at_velocity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ Γ : ℝ → M, IsGeodesic (I := I) g Γ ∧ Γ 0 = p ∧
      (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (v : E) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- SEED on `Ioo (-δ) δ`.
  obtain ⟨η, δ, hδ, hη0, _hηcont0, hηv, hη_mdiff, _hη_src, hη_geo⟩ :=
    HopfRinow.exists_isGeodesicOn_Ioo_at_velocity (I := I) g p v
  -- The seed is continuous on `Ioo (-δ) δ`.
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) :=
    fun t ht => (hη_mdiff t ht).continuousAt.continuousWithinAt
  -- The seed is mdifferentiable at the launch time `0`.
  have h0_mem_seed : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hη_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 := hη_mdiff 0 h0_mem_seed
  set a₀ : ℝ := -δ / 2 with ha₀_def
  have ha₀_neg : a₀ < 0 := by rw [ha₀_def]; linarith
  have ha₀_gt : -δ < a₀ := by rw [ha₀_def]; linarith
  -- The launch speed constant `c = √(g.inner (η 0) (η'(0)) (η'(0)))`.
  set c : ℝ := Real.sqrt ((g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
    (mfderiv 𝓘(ℝ, ℝ) I η 0 1)) with hc_def
  have hspeed0_nonneg : 0 ≤ (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rcases eq_or_ne (mfderiv 𝓘(ℝ, ℝ) I η 0 1) 0 with hz | hz
    · rw [hz]; simp
    · exact (g.pos (η 0) _ hz).le
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hc_sq : c ^ 2 = (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hc_def, Real.sq_sqrt hspeed0_nonneg]
  have hηspeed_le : (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I η 0 1) ≤ c ^ 2 := le_of_eq hc_sq.symm
  -- The seed restricted to `Ioo a₀ δ` (geodesic + continuous), the engine seed.
  have hη_geo' : IsGeodesicOn (I := I) g η (Set.Ioo a₀ δ) :=
    hη_geo.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  have hη_cont' : ContinuousOn η (Set.Ioo a₀ δ) :=
    hη_cont.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  -- FORWARD extension: a geodesic `Γf` on `Ioi a₀` agreeing with `η` below `δ`.
  obtain ⟨Γf, hΓf_geo, hΓf_agree⟩ :=
    HopfRinow.isGeodesicOn_Ici_of_complete_Ioo (I := I) g ha₀_neg hδ hη_geo' hη_cont'
      (fun γ b hb hγ hγ_cont hagree =>
        isGeodesicOn_hreg_record (I := I) g hEnorm ha₀_neg hδ hc_nonneg hηspeed_le
          hγ hγ_cont hb (fun t ht_a₀ ht_δ ht_b => hagree t ht_a₀ ht_δ ht_b))
  -- BACKWARD: reversal `ηr t := η (-t)` is a geodesic on `Ioo a₀ δ` (the window
  -- `Ioo (-δ) δ` is symmetric), with foot `ηr 0 = p`.  Its launch speed equals
  -- that of `η` (the reversal negates the velocity, which preserves the metric
  -- quadratic form), so the same constant `c` works.
  set ηr : ℝ → M := fun t => η (-t) with hηr_def
  have hηr_geo_full : IsGeodesicOn (I := I) g ηr (Set.Ioo (-δ) δ) := by
    have h := isGeodesicOn_comp_neg (I := I) (g := g) (γ := η) (s := Set.Ioo (-δ) δ) hη_geo
    refine h.mono ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hηr_geo' : IsGeodesicOn (I := I) g ηr (Set.Ioo a₀ δ) :=
    hηr_geo_full.mono (fun t ht => ⟨lt_trans ha₀_gt ht.1, ht.2⟩)
  have hηr_cont' : ContinuousOn ηr (Set.Ioo a₀ δ) := by
    refine ContinuousOn.comp hη_cont (continuous_neg.continuousOn) ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1, ha₀_gt]⟩
  have hηr0 : ηr 0 = p := by simp [hηr_def, neg_zero, hη0]
  -- Velocity of the reversal at `0` is the negation of `η`'s velocity at `0`.
  have hηr_mfderiv : mfderiv 𝓘(ℝ, ℝ) I ηr 0
      = (mfderiv 𝓘(ℝ, ℝ) I η 0).comp (- ContinuousLinearMap.id ℝ ℝ) := by
    have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s)
        (0 : ℝ) (- ContinuousLinearMap.id ℝ ℝ) := by
      rw [hasMFDerivAt_iff_hasFDerivAt]
      simpa using (hasFDerivAt_id (0 : ℝ)).neg
    have hη_at : HasMFDerivAt 𝓘(ℝ, ℝ) I η (-(0 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I η 0) := by
      rw [neg_zero]; exact hη_mdiff0.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I ηr 0
        ((mfderiv 𝓘(ℝ, ℝ) I η 0).comp (- ContinuousLinearMap.id ℝ ℝ)) :=
      hη_at.comp 0 hneg
    exact hcomp.mfderiv
  have hηr_val : mfderiv 𝓘(ℝ, ℝ) I ηr 0 1 = -(mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hηr_mfderiv]
    change (mfderiv 𝓘(ℝ, ℝ) I η 0) ((- ContinuousLinearMap.id ℝ ℝ) 1)
      = -(mfderiv 𝓘(ℝ, ℝ) I η 0 1)
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
    exact map_neg (mfderiv 𝓘(ℝ, ℝ) I η 0) 1
  have hηr_speed0 : (g.inner (ηr 0)) (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      = (g.inner (η 0)) (mfderiv 𝓘(ℝ, ℝ) I η 0 1) (mfderiv 𝓘(ℝ, ℝ) I η 0 1) := by
    rw [hηr_val, hηr0, hη0]
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  have hηr_speed_le : (g.inner (ηr 0)) (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I ηr 0 1) ≤ c ^ 2 := by rw [hηr_speed0]; exact hηspeed_le
  -- FORWARD extension of the reversal: a geodesic `Γrf` on `Ioi a₀` agreeing
  -- with `ηr` below `δ`.
  obtain ⟨Γrf, hΓrf_geo, hΓrf_agree⟩ :=
    HopfRinow.isGeodesicOn_Ici_of_complete_Ioo (I := I) g ha₀_neg hδ hηr_geo' hηr_cont'
      (fun γ b hb hγ hγ_cont hagree =>
        isGeodesicOn_hreg_record (I := I) g hEnorm ha₀_neg hδ hc_nonneg hηr_speed_le
          hγ hγ_cont hb (fun t ht_a₀ ht_δ ht_b => hagree t ht_a₀ ht_δ ht_b))
  -- Reflect the reversal extension back: `Γb t := Γrf (-t)` is a geodesic on
  -- `Iio (-a₀)`, agreeing with `η` above `-δ` (in particular near and left of `0`).
  set Γb : ℝ → M := fun t => Γrf (-t) with hΓb_def
  have hΓb_geo : IsGeodesicOn (I := I) g Γb (Set.Iio (-a₀)) := by
    have h := isGeodesicOn_comp_neg (I := I) (g := g) (γ := Γrf) (s := Set.Ioi a₀)
      hΓrf_geo
    refine h.mono ?_
    intro t ht
    -- `t < -a₀ ⟹ -t ∈ Ioi a₀`, i.e. `a₀ < -t`.
    simp only [Set.mem_preimage, Set.mem_Ioi]
    linarith [Set.mem_Iio.mp ht]
  -- `Γb` agrees with `η` for `t > -δ` (where `-t < δ`, so `Γrf(-t) = ηr(-t) = η t`).
  have hΓb_agree : ∀ t, -δ < t → Γb t = η t := by
    intro t ht
    have hlt : -t < δ := by linarith
    change Γrf (-t) = η t
    rw [hΓrf_agree (-t) hlt]
    change η (- -t) = η t
    rw [neg_neg]
  -- `Γf` agrees with `η` for `t < δ`.
  have hΓf_agree' : ∀ t, t < δ → Γf t = η t := hΓf_agree
  have hma₀ : -a₀ = δ / 2 := by rw [ha₀_def]; ring
  have hδ2_pos : (0 : ℝ) < δ / 2 := by linarith
  -- ASSEMBLE: `Γ t := if t < 0 then Γb t else Γf t`.
  set Γ : ℝ → M := fun t => if t < 0 then Γb t else Γf t with hΓ_def
  -- `Γ` agrees with `η` on the open window `Ioo (-δ) δ` around `0`.
  have hΓ_eq_η : ∀ t, -δ < t → t < δ → Γ t = η t := by
    intro t ht_lo ht_hi
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · rw [hΓ_def]; simp only [if_pos hlt]; exact hΓb_agree t ht_lo
    · subst heq; rw [hΓ_def]; simp only [lt_irrefl, if_false]
      exact hΓf_agree' 0 hδ
    · rw [hΓ_def]; simp only [if_neg (not_lt.mpr hgt.le)]; exact hΓf_agree' t ht_hi
  -- `Γ =ᶠ[𝓝 0] η` (on the open window `Ioo (-δ) δ`).
  have h0_win : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith [hδ], hδ⟩
  have hΓ_nhds_η : Γ =ᶠ[nhds (0 : ℝ)] η := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0_win) ?_
    intro t ht; exact hΓ_eq_η t ht.1 ht.2
  -- `Γ` is a geodesic on all of `ℝ` (pointwise, by locality).
  have hΓ_geo : IsGeodesic (I := I) g Γ := by
    intro t
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · -- `t < 0`: `Γ = Γb` near `t`; `Γb` is a geodesic at `t` (`t < δ/2 = -a₀`).
      have hΓΓb : Γ =ᶠ[nhds t] Γb := by
        refine Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) ?_
        intro s hs; rw [hΓ_def]; simp only [if_pos (Set.mem_Iio.mp hs)]
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := Γb) ?_ hΓΓb ?_
      · rw [hΓ_def]; simp only [if_pos hlt]
      · exact hΓb_geo t (Set.mem_Iio.mpr (by rw [hma₀]; linarith))
    · -- `t = 0`: `Γ = η` near `0`; `η` is a geodesic at `0`.
      subst heq
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := η)
        hΓ_nhds_η.eq_of_nhds hΓ_nhds_η ?_
      exact hη_geo 0 h0_mem_seed
    · -- `t > 0`: `Γ = Γf` near `t`; `Γf` is a geodesic at `t` (`t > 0 > a₀`).
      have hΓΓf : Γ =ᶠ[nhds t] Γf := by
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hgt) ?_
        intro s hs; rw [hΓ_def]; simp only [if_neg (not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hs)))]
      refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := Γf) ?_ hΓΓf ?_
      · rw [hΓ_def]; simp only [if_neg (not_lt.mpr hgt.le)]
      · exact hΓf_geo t (Set.mem_Ioi.mpr (lt_trans ha₀_neg hgt))
  -- Value and velocity at `0` survive the gluing (via the `𝓝 0`-agreement with `η`).
  refine ⟨Γ, hΓ_geo, ?_, ?_⟩
  · rw [hΓ_nhds_η.eq_of_nhds, hη0]
  · rw [show mfderiv 𝓘(ℝ, ℝ) I Γ 0 = mfderiv 𝓘(ℝ, ℝ) I η 0 from hΓ_nhds_η.mfderiv_eq]
    exact hηv

/-! ## The intrinsic geodesic and exponential map -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic complete geodesic through `p` with launch velocity `v`,
chosen by `exists_complete_geodesic_at_velocity`.  The hypothesis `hEnorm` is the
ambient fibre-norm — square-root inner-product compatibility tying the ambient
bundle norm to `g` (the same structural fact used across the Hopf-Rinow /
Bonnet-Myers pipeline). -/
def intrinsicGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is a geodesic on all of `ℝ`. -/
theorem intrinsicGeodesic_isGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    IsGeodesic (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic starts at `p` (value at `t = 0`). -/
@[simp] theorem intrinsicGeodesic_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    intrinsicGeodesic (I := I) g hEnorm p v 0 = p :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).2.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The launch velocity of the intrinsic geodesic at `t = 0` is `v`. -/
theorem intrinsicGeodesic_mfderiv_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) 0 (1 : ℝ) : E)
      = (v : E) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g hEnorm p v)).2.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic exponential map at `p`: the value at `t = 1` of the complete
geodesic through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`,
this follows the geodesic across charts and is the object used by the
metric-geometry (compactness / diameter) theorems. -/
def expMapIntrinsic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) : M :=
  intrinsicGeodesic (I := I) g hEnorm p v 1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem expMapIntrinsic_def
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    expMapIntrinsic (I := I) g hEnorm p v = intrinsicGeodesic (I := I) g hEnorm p v 1 := rfl

/-! ## Time-regularity of the intrinsic geodesic

A geodesic on an open set, continuous there, is `C¹` in time
(`HopfRinow.isGeodesicOn_contMDiffOn_one`).  The intrinsic geodesic is a geodesic
on all of `ℝ`; its continuity is the regularity datum exposed by the construction
in `exists_complete_geodesic_at_velocity` (the assembled curve is a chart-by-chart
glue of genuine local geodesics, each continuous).  Pending that construction, the
continuity and hence the `C¹`-in-time regularity are recorded as stubs.
-/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of the intrinsic geodesic.  Provable once
`exists_complete_geodesic_at_velocity` is built from the (continuous) chart-glue
of local geodesics; recorded here as the regularity datum feeding the `C¹`-in-time
lemma below. -/
theorem intrinsicGeodesic_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    Continuous (intrinsicGeodesic (I := I) g hEnorm p v) := by
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is `C¹` in time on all of `ℝ`.  A geodesic, continuous
on the open set `Set.univ`, is `ContMDiffOn 𝓘(ℝ,ℝ) I 1` there by
`HopfRinow.isGeodesicOn_contMDiffOn_one`. -/
theorem intrinsicGeodesic_contMDiffOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (intrinsicGeodesic (I := I) g hEnorm p v) Set.univ := by
  refine HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_univ ?_ ?_
  · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn Set.univ
  · exact (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
