import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Riemannian.Variation.PerpFrame
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Lifts
import DifferentialGeometry.Integral.Connection.ChartBridge.RiemannBasisBracket
import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Finite.Defs

/-!
# Bonnet-Myers headline theorems

This file assembles the three top-level conclusions of the Bonnet-Myers
theorem from their supporting children. Under the hypotheses
`Ric ≥ (n-1) K · g` with `K > 0` and `n ≥ 2`:

* `bonnet_myers_diameter_of_ricci_bound` — the metric diameter is at most `π / √K`.
* `bonnet_myers_compactSpace_of_ricci_bound` — the manifold is compact.
* `bonnet_myers_finite_fundamentalGroup_of_ricci_bound` — the fundamental group is finite.

Two short supporting children are also stated here:

* `bonnet_myers_pairwise_edist_le_of_ricci_bound` — the uniform pairwise edist bound.
* The `bm_c_*` compactness sub-leaves
  (`tangent_closedBall_isCompact`, `isCompact_image_closedBall_under_expMap`,
  `isCompact_univ`).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

/-! ## Compactness sub-leaves -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]

/-- **bm-c-tangent-closedBall-compact.** The closed ball of radius `R` in
the tangent space `T_p M` is compact, because `T_p M` is finite-dimensional
(it is canonically isomorphic to the model fibre `E`). Pure composition of
Mathlib `FiniteDimensional.proper_real` and `isCompact_closedBall`. -/
theorem tangent_closedBall_isCompact
    {M : Type*}
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (p : M) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact (Metric.closedBall (0 : TangentSpace I p) R) := by
  -- `TangentSpace I p` is definitionally `E`, a finite-dimensional real normed space,
  -- hence a `ProperSpace`. On a `ProperSpace`, closed balls are compact.
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  exact isCompact_closedBall (0 : TangentSpace I p) R

/-- **bm-c-continuous-image-of-compact-is-compact.** Continuous image of a
compact set is compact. Apply `IsCompact.image` to
`tangent_closedBall_isCompact` together with the continuity of `expMap`. -/
theorem isCompact_image_closedBall_under_expMap
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (p : M) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact ((expMap g p) '' Metric.closedBall (0 : TangentSpace I p) R) := by
  -- Continuous image of the compact closed ball in `T_p M`.
  have hcompact : IsCompact (Metric.closedBall (0 : TangentSpace I p) R) :=
    tangent_closedBall_isCompact (E := E) I p hR
  have hcont : Continuous (expMap (I := I) g p) :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.bm_c_expMap_continuous_of_geodesic_complete
      g p
  exact hcompact.image hcont

/-! ## Pairwise edist bound -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The uniform pairwise distance bound underlying Bonnet-Myers: for any two
points `x y` on a complete connected Riemannian manifold of dimension `n ≥ 2`
with Ricci curvature bounded below by `(n-1) K` (`K > 0`),
`edist x y ≤ π / √K`.

The hypothesis `hEnorm` is the supplied structural identity that the fibre
extended norm `‖·‖ₑ` equals `ofReal (√ g.inner)` (the Riemannian norm). The
proof composes three ingredients: a distance-realising launch velocity `v`
at `x` whose intrinsic exponential is `y` and whose `g`-norm equals the
intrinsic distance `r`, giving a unit-speed minimising geodesic `γ` of
parameter length `L = r`; the second-variation index-form length bound,
which combines with the Ricci lower bound to give `L ≤ π / √K`; and the
Riemannian-manifold identity `edist = riemannianEDist`. The
`attribute [-instance]` prefix suppresses the `Tensor0SBundle` tangent-norm
instance so every fibre `‖·‖ₑ` reduces to the Riemannian norm. -/
theorem bonnet_myers_pairwise_edist_le_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v)))
    (x y : M) :
    edist x y ≤ ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  classical
  haveI hCE : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- `IsRiemannianManifold` identity: `edist = riemannianEDist I`.
  rw [IsRiemannianManifold.out (I := I) x y]
  -- The intrinsic Riemannian distance is finite.
  have hne_top : Manifold.riemannianEDist I x y ≠ (⊤ : ℝ≥0∞) :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
      (I := I) x y
  -- `r := (riemannianEDist I x y).toReal`, so `riemannianEDist I x y = ofReal r`.
  set r : ℝ := (Manifold.riemannianEDist I x y).toReal with hr_def
  have hr_nn : 0 ≤ r := ENNReal.toReal_nonneg
  have hdist_ofReal : Manifold.riemannianEDist I x y = ENNReal.ofReal r := by
    rw [hr_def, ENNReal.ofReal_toReal hne_top]
  rw [hdist_ofReal]
  -- Reduce to the real-number bound `r ≤ π / √K`.
  refine ENNReal.ofReal_le_ofReal ?_
  -- Step 1: the distance-realising launch velocity `v` at `x`.
  obtain ⟨v, hv_exp, hv_len⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic_surjective_dist
      (I := I) g hEnorm x y
  -- `hv_len : √(g.inner x v v) = r`.
  rw [← hr_def] at hv_len
  -- Split on whether `r = 0`.
  rcases eq_or_ne r 0 with hr0 | hr_ne
  · -- `r = 0 ≤ π / √K`.
    rw [hr0]
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  -- POSITIVE CASE `r > 0`.
  have hr_pos' : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr_ne)
  -- The unit launch velocity `u := r⁻¹ • v` and the geodesic `γ`.
  set u : TangentSpace I x := r⁻¹ • v with hu_def
  set γ : ℝ → M :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm x u with hγ_def
  set L : ℝ := r with hL_def
  have hL_nn : (0 : ℝ) ≤ L := hr_nn
  have hL_pos : (0 : ℝ) < L := hr_pos'
  -- `g.inner x v v = r²` from `√(g.inner x v v) = r` and `g.inner ≥ 0`.
  have hvv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact le_of_lt (g.pos x v hv0)
  have hvv_sq : g.inner x v v = L ^ 2 := by
    have := congrArg (· ^ 2) hv_len
    simpa [Real.sq_sqrt hvv_nn] using this
  -- The launch velocity has unit `g`-norm: `g.inner x u u = 1`.
  have hu_unit : g.inner x u u = 1 := by
    have hbil : g.inner x u u = L⁻¹ * (L⁻¹ * g.inner x v v) := by
      rw [hu_def]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hbil, hvv_sq]
    field_simp
  -- `γ 0 = x`.
  have hγ0 : γ 0 = x :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
      (I := I) g hEnorm x u
  -- `γ L = y`: `γ r = intrinsicGeodesic x (r • u) 1 = expMapIntrinsic x (r • u)`,
  -- and `r • u = r • (r⁻¹ • v) = v`, whose intrinsic exponential is `y`.
  have hru : r • u = v := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hγL : γ L = y := by
    have hsmul :
        DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic
            (I := I) g hEnorm x (r • u) 1
          = γ r :=
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_smul
        (I := I) g hEnorm x u r
    rw [hL_def, ← hsmul, hru]
    -- `intrinsicGeodesic x v 1 = expMapIntrinsic x v = y`.
    have hexp :
        DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic
            (I := I) g hEnorm x v = y := hv_exp
    rw [DifferentialGeometry.Geometry.Riemannian.Exponential.expMapIntrinsic_def] at hexp
    exact hexp
  -- `γ` is a complete geodesic, continuous, hence `C^∞` in time.
  have hγ_isGeo :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_isGeodesic
      (I := I) g hEnorm x u
  have hγ_cont : Continuous γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_continuous
      (I := I) g hEnorm x u
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.isGeodesic_contMDiff
      (I := I) g hγ_isGeo hγ_cont
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L) :=
    (hγ_smooth.of_le (by exact_mod_cast le_top)).contMDiffOn
  have hγ_geoOn :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
        (I := I) g γ (Set.Icc 0 L) :=
    hγ_isGeo.isGeodesicOn (Set.Icc 0 L)
  -- The unit-speed condition holds on the whole interval: the squared speed of
  -- the intrinsic geodesic is constant `= g.inner x u u = 1`.
  have hγ_unit_mfderiv :
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
    intro t _ht
    have hspeed :
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          = g.inner x u u :=
      DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_speedSq_eq
        (I := I) g hEnorm x u t
    rw [hspeed, hu_unit]
  -- The launch unit-speed datum at `t = 0` consumed by the frame constructor.
  have hUnit0 :
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1 :=
    hγ_unit_mfderiv 0 ⟨le_refl 0, hL_nn⟩
  -- The real-valued velocity field `uPrime`.
  let uPrime : ℝ → E := fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
  have hγ_unit :
      ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1 := by
    intro t ht
    exact hγ_unit_mfderiv t ht
  -- The Hopf-Rinow style distance identity for `γ`.
  have hγ_edist : Manifold.riemannianEDist I x y = ENNReal.ofReal L := by
    rw [hL_def]; exact hdist_ofReal
  -- Adjust the Ricci hypothesis to the form expected by the length-bound
  -- assembly. The headline statement has the bound as
  -- `((Module.finrank ℝ E : ℝ) - 1) * K`, while
  -- `bonnet_myers_length_le_of_ricci_bound` reads
  -- `(Module.finrank ℝ E - 1 : ℝ) * K`. These are syntactically equal.
  have hRic' :
      RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K) := _hRic
  -- Arc-length minimisation property.
  -- Hopf-Rinow gives `riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L`.
  -- Combined with `pathELength_eq_arcLength_C1` and the fundamental
  -- inequality `riemannianEDist ≤ pathELength`, this yields
  -- `arcLength g γ 0 L ≤ arcLength g η 0 L` for every endpoint-matching
  -- competitor η.
  have hγ_min :
      ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) →
        η 0 = γ 0 → η L = γ L →
        DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g γ 0 L ≤
          DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
    -- The chain `arcLength γ = L = riemannianEDist (γ 0)(γ L) ≤
    -- pathELength η = arcLength η` is unfolded as a substantive
    -- composition of `pathELength_eq_arcLength_C1` and
    -- `riemannianEDist_le_pathELength`, using the unit-speed identity
    -- `hγ_unit` to evaluate `arcLength γ 0 L = L`.
    --
    -- Step A. Compute `arcLength γ 0 L = L` from unit-speed.
    have hγ_arcLength : DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
        (I := I) g γ 0 L = L := by
      -- The arc-length integrand for γ on `Icc 0 L` is identically 1
      -- (by `hγ_unit` and `Real.sqrt_one`), and `∫ t in 0..L, 1 = L - 0 = L`.
      unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
      have hcongr :
          ∀ t ∈ Set.uIcc (0 : ℝ) L,
            Real.sqrt
                ((g.inner (γ t))
                  (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                  (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
              = (1 : ℝ) := by
        intro t ht
        -- Since `0 ≤ L`, the uIcc is `Icc 0 L`.
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := by
          rw [Set.uIcc_of_le hL_nn] at ht
          exact ht
        have hone : (g.inner (γ t))
              (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 :=
          hγ_unit_mfderiv t htIcc
        rw [hone, Real.sqrt_one]
      rw [intervalIntegral.integral_congr hcongr]
      simp
    -- Step B. The Hopf-Rinow distance identity, transported through
    -- `hγ0` and `hγL`.
    have hdist_eq : Manifold.riemannianEDist I (γ 0) (γ L)
        = ENNReal.ofReal L := by
      have : Manifold.riemannianEDist I x y = ENNReal.ofReal L := hγ_edist
      rw [← hγ0, ← hγL] at this
      exact this
    intro η hη_C1 hη0 hηL
    -- Step C. The arcLength integrand of η is non-negative, so
    -- `arcLength η 0 L ≥ 0`.
    have hη_arcLength_nn :
        0 ≤ DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
      unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg hL_nn (fun t _ => Real.sqrt_nonneg _)
    -- Step D. Integrability and per-time enorm identification for η on
    -- `Icc 0 L`. The C¹ smoothness `hη_C1` is now given as a hypothesis
    -- of the minimisation premise. The per-time enorm identification is
    -- the explicit bundle-norm hypothesis `hEnorm` (the norm on each
    -- fibre is the square root of `g.inner`). Integrability of the speed
    -- follows from continuity of the integrand for the C¹ curve on the
    -- compact interval, which we establish below.
    -- (D.i) The per-time enorm identification, instantiated from `hEnorm`.
    have hη_enorm :
        ∀ t ∈ Set.Icc (0 : ℝ) L,
          ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ
            = ENNReal.ofReal (Real.sqrt
                (g.inner (η t)
                  (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
                  (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) :=
      fun t _ => hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
    -- (D.ii) Integrability of the speed integrand `√(g.inner η η'η')` on
    -- `Icc 0 L`. The within-velocity speed is continuous on the compact
    -- interval (the `(0,2)`-metric tensor `g.inner` is a smooth bundle section
    -- — `g.contMDiff` — applied to the continuous within-velocity vector field
    -- — `tangentMapWithin` continuity of the `C¹` curve `η`), and the `mfderiv`
    -- form agrees a.e. on the co-null interior `Ioo 0 L`.
    have hUniqueη : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
      intro u hu
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact (uniqueDiffOn_Icc hL_pos) u hu
    have hLiftη : Continuous (fun u : ℝ =>
        (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      have h_homeo :
          Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
            ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
      exact h_homeo.comp (continuous_id.prodMk continuous_const)
    have hMapsη : Set.MapsTo
        (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
      intro u hu; simpa using hu
    have hVWη : ContinuousOn
        (fun t : ℝ =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
              TangentBundle I M))
        (Set.Icc (0 : ℝ) L) := by
      have hTanη := hη_C1.continuousOn_tangentMapWithin (le_refl 1) hUniqueη
      have hCompη : ContinuousOn
          (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L)
            (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
          (Set.Icc (0 : ℝ) L) :=
        hTanη.comp hLiftη.continuousOn hMapsη
      exact hCompη.congr (fun t _ => rfl)
    -- The `(0,2)`-metric tensor section `t ↦ ⟨η t, g.inner (η t)⟩` is continuous.
    have hgSecη : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          (η t) (g.inner (η t))))
        (Set.Icc (0 : ℝ) L) := by
      have hgCont : Continuous
          (fun b : M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
            b (g.inner b))) := g.contMDiff.continuous
      exact hgCont.comp_continuousOn hη_C1.continuousOn
    -- Applying the metric to the velocity twice gives a continuous scalar
    -- (within-velocity form).
    have hScalarTotalη : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' ℝ (E := fun _ : M => ℝ)
          (η t)
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
        (Set.Icc (0 : ℝ) L) :=
      ContinuousOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := η) hgSecη hVWη hVWη
    have hScalarWη : ContinuousOn
        (fun t : ℝ => g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
        (Set.Icc (0 : ℝ) L) := by
      have hproj : Continuous
          (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
        continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
      exact hproj.comp_continuousOn hScalarTotalη
    -- Integrability of the within-velocity speed (`√` of the continuous scalar).
    have hIntWη : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc (0 : ℝ) L) t (1 : ℝ))))
        (Set.Icc 0 L) MeasureTheory.volume :=
      (Real.continuous_sqrt.comp_continuousOn hScalarWη).integrableOn_Icc
    -- Transfer to the `mfderiv` form by a.e.-equality on the interior `Ioo 0 L`.
    have hη_int :
        MeasureTheory.IntegrableOn
          (fun t : ℝ => Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
          (Set.Icc 0 L) MeasureTheory.volume := by
      refine hIntWη.congr ?_
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) L)),
          t ∈ Set.Ioo (0 : ℝ) L := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    -- Step E. `pathELength I η 0 L = ofReal (arcLength g η 0 L)`, proved inline
    -- in the active `RiemannianBundle` norm: `pathELength` is the lintegral of
    -- the velocity enorm, which `hη_enorm` rewrites to `ofReal (√(g.inner …))`,
    -- and the lintegral of `ofReal ∘ (speed)` equals `ofReal` of the Bochner
    -- integral (= `arcLength`) by `ofReal_integral_eq_lintegral_ofReal`.
    have hη_pathLen :
        Manifold.pathELength I η 0 L
          = ENNReal.ofReal
              (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
                (I := I) g η 0 L) := by
      set F : ℝ → ℝ := fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) with hF_def
      have hF_nn : ∀ t : ℝ, 0 ≤ F t := fun t => Real.sqrt_nonneg _
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
      change ∫⁻ t in Set.Icc 0 L, (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ) t
        = ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L)
      have h_lint_eq :=
        MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
          (f := fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)‖ₑ)
          (g := fun t : ℝ => ENNReal.ofReal (F t))
          (s := Set.Icc 0 L)
          measurableSet_Icc
          (fun t ht => by simpa [hF_def] using hη_enorm t ht)
      rw [h_lint_eq]
      have h_ofReal :
          ENNReal.ofReal (∫ t in Set.Icc 0 L, F t)
            = ∫⁻ t in Set.Icc 0 L, ENNReal.ofReal (F t) := by
        have hF_nn_ae : 0 ≤ᵐ[(MeasureTheory.volume).restrict (Set.Icc 0 L)] F :=
          MeasureTheory.ae_of_all _ hF_nn
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hη_int hF_nn_ae
      rw [← h_ofReal]
      have h_Icc_Ioc :
          ∫ t in Set.Icc 0 L, F t = ∫ t in Set.Ioc 0 L, F t := by
        have h_set : Set.Icc (0 : ℝ) L = {(0 : ℝ)} ∪ Set.Ioc 0 L := by
          ext z
          simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases h : z = 0
            · left; exact h
            · right; exact ⟨lt_of_le_of_ne h1 (fun h' => h h'.symm), h2⟩
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨le_refl _, hL_nn⟩
            · exact ⟨le_of_lt h1, h2⟩
        rw [h_set]
        have hdisj : Disjoint ({(0 : ℝ)} : Set ℝ) (Set.Ioc 0 L) := by
          rw [Set.disjoint_left]
          rintro z hz hz'
          simp only [Set.mem_singleton_iff] at hz
          rw [hz] at hz'; exact lt_irrefl _ hz'.1
        have h_int_singleton :
            MeasureTheory.IntegrableOn F ({(0 : ℝ)} : Set ℝ) MeasureTheory.volume := by
          rw [MeasureTheory.integrableOn_singleton_iff]; exact Or.inr (by simp)
        have h_int_Ioc :
            MeasureTheory.IntegrableOn F (Set.Ioc 0 L) MeasureTheory.volume :=
          hη_int.mono_set Set.Ioc_subset_Icc_self
        rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
          h_int_singleton h_int_Ioc]
        have h_singleton : ∫ t in ({(0 : ℝ)} : Set ℝ), F t = 0 := by simp
        rw [h_singleton, zero_add]
      have h_intInterval : ∫ t in (0 : ℝ)..L, F t = ∫ t in Set.Ioc 0 L, F t :=
        intervalIntegral.integral_of_le hL_nn
      have h_arcLength :
          DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g η 0 L
            = ∫ t in (0 : ℝ)..L, F t := rfl
      rw [h_arcLength, h_intInterval, h_Icc_Ioc]
    -- Step F. Apply `riemannianEDist_le_pathELength` to η.
    have hdist_le_pathLen :
        Manifold.riemannianEDist I (η 0) (η L)
          ≤ Manifold.pathELength I η 0 L :=
      Manifold.riemannianEDist_le_pathELength (I := I) (γ := η)
        (a := 0) (b := L) hη_C1 rfl rfl hL_nn
    -- Step G. Identify endpoints `η 0 = γ 0`, `η L = γ L` and combine
    -- with Step B to obtain `ofReal L ≤ pathELength η 0 L`.
    have hL_le_pathLen :
        ENNReal.ofReal L ≤ Manifold.pathELength I η 0 L := by
      have hrewrite : Manifold.riemannianEDist I (γ 0) (γ L)
          ≤ Manifold.pathELength I η 0 L := by
        rw [← hη0, ← hηL]
        exact hdist_le_pathLen
      calc
        ENNReal.ofReal L = Manifold.riemannianEDist I (γ 0) (γ L) := hdist_eq.symm
        _ ≤ Manifold.pathELength I η 0 L := hrewrite
    -- Step H. Chain with `hη_pathLen` and unpack `ofReal_le_ofReal_iff`.
    have hL_le_arcLength :
        L ≤ DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g η 0 L := by
      have hofReal_le :
          ENNReal.ofReal L
            ≤ ENNReal.ofReal
                (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
                  (I := I) g η 0 L) := by
        rw [← hη_pathLen]; exact hL_le_pathLen
      exact (ENNReal.ofReal_le_ofReal_iff hη_arcLength_nn).mp hofReal_le
    -- Step I. Conclude using Step A.
    rw [hγ_arcLength]
    exact hL_le_arcLength
  -- Apply the length-bound contradiction assembly to bound `L = r > 0` by
  -- `π / √K`. The goal `r ≤ π / √K` then follows directly (`L = r`).
  have hL_le : L ≤ Real.pi / Real.sqrt K := by
      -- The intrinsic geodesic has parameter length `L = r > 0`; invoke the
      -- contradiction assembly to bound `L`.
      -- The assembly consumes a parallel orthonormal frame of `(uPrime)`'s
      -- perpendicular subspace together with auxiliary regularity data
      -- (differentiability and parallelism of each frame vector, frame
      -- orthonormality, perpendicularity to `uPrime`, global bundle-smoothness
      -- of the sinusoidal test fields, and interval-integrability of the
      -- relevant integrands). The frame is the smooth parallel perpendicular
      -- frame produced by `exists_parallel_perp_frame`.
      -- (i) the `mfderiv` realisation of `uPrime` — definitionally true.
      have huPrimeEq :
          ∀ t ∈ Set.Icc (0 : ℝ) L,
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = uPrime t := by
        intro t _ht; rfl
      -- (iii) smooth parallel orthonormal perpendicular frame `e` along `γ`.
      -- Orthonormal seed of the `g`-perpendicular complement of the velocity at
      -- `γ 0`, smoothly parallel-transported along `γ`, then cut off by a smooth
      -- bump equal to `1` on `Icc 0 L`.
      obtain ⟨e, heDiff, hParallel, hON, hPerp_mfderiv, hEbundle⟩ :=
        DifferentialGeometry.Geometry.Riemannian.exists_parallel_perp_frame
          (I := I) g γ hγ_smooth hL_pos hγ_geoOn hUnit0
      -- Re-source the perpendicularity to the `uPrime` form (definitionally
      -- equal to `mfderiv γ t 1`).
      have hPerp :
          ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
            g.inner (γ t) ((e i).toFun t) (uPrime t) = 0 := by
        intro t ht i
        exact hPerp_mfderiv t ht i
      -- (iv) interval-integrability of each index-form integrand.
      -- Follows from continuity of all the building blocks (sin · e i,
      -- its derivative, the chart Christoffels, and γ itself) on the
      -- compact interval. Recorded as a structural gap.
      have hIntegrandSum :
          ∀ i : Fin (Module.finrank ℝ E - 1),
            IntervalIntegrable
              (fun t : ℝ => indexFormIntegrand (I := I) g γ
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
              MeasureTheory.volume 0 L :=
        DifferentialGeometry.Geometry.Riemannian.Variation.indexFormIntegrand_intervalIntegrable
          (I := I) g γ L hL_pos hγ_C1 hγ_geoOn hγ_unit_mfderiv e heDiff hParallel hON hPerp
      -- (v) interval-integrability of `t ↦ Ric(γ t)(uPrime t)(uPrime t)`.
      -- The Ricci tensor is a smooth `(0,2)`-tensor bundle section
      -- (`ricciTensor_contMDiff`); pulled back along the `C¹` curve `γ` it
      -- is a continuous CLM-bundle section. Applying it (via the Mathlib
      -- `ContinuousOn.clm_bundle_apply₂` bridge) to the within-velocity
      -- vector section — whose total-space continuity on the compact
      -- interval is the `tangentMapWithin` continuity of `γ` — yields a
      -- continuous scalar on `Icc 0 L`, hence interval-integrable. We
      -- prove integrability for the `mfderivWithin` form and transfer to
      -- the `mfderiv` form by a.e.-equality on the co-null interior
      -- `Ioo 0 L` (where `mfderivWithin = mfderiv`).
      have hRicIntegrable :
          IntervalIntegrable
            (fun t : ℝ => ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
            MeasureTheory.volume 0 L := by
        have hL_nn' : (0 : ℝ) ≤ L := le_of_lt hL_pos
        -- (A) Total-space continuity of the within-velocity section on `Icc 0 L`.
        -- `Icc 0 L` has the unique-mdiff property as a subset of the model `ℝ`.
        have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
          intro u hu
          rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact (uniqueDiffOn_Icc hL_pos) u hu
        have hTan := hγ_C1.continuousOn_tangentMapWithin (le_refl 1) hUnique
        have hLift : Continuous (fun u : ℝ =>
            (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
          have h_homeo :
              Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
                ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
            (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
          exact h_homeo.comp (continuous_id.prodMk continuous_const)
        have hMaps : Set.MapsTo
            (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
            (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
          intro u hu
          simpa using hu
        have hVW : ContinuousOn
            (fun t : ℝ =>
              (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
                (γ t)
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
                  TangentBundle I M))
            (Set.Icc (0 : ℝ) L) := by
          have hComp : ContinuousOn
              (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L)
                (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
              (Set.Icc (0 : ℝ) L) :=
            hTan.comp hLift.continuousOn hMaps
          exact hComp.congr (fun t _ => rfl)
        -- (B) Continuity of the Ricci `(0,2)`-tensor section pulled back along `γ`.
        have hRicSec : ContinuousOn
            (fun t : ℝ => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
              (γ t) (ricciTensor (I := I) g (γ t))))
            (Set.Icc (0 : ℝ) L) := by
          have hRicCont : Continuous
              (fun b : M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
                (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
                b (ricciTensor (I := I) g b))) :=
            (ricciTensor_contMDiff (I := I) g).continuous
          exact (hRicCont.comp_continuousOn hγ_C1.continuousOn)
        -- (C) Apply the bundle bilinear-application bridge.
        have hScalarTotal : ContinuousOn
            (fun t : ℝ => (TotalSpace.mk' ℝ (E := fun _ : M => ℝ)
              (γ t)
              (ricciTensor (I := I) g (γ t)
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
                (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
            (Set.Icc (0 : ℝ) L) :=
          ContinuousOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
            (b := γ) hRicSec hVW hVW
        -- (D) Extract the scalar continuity from the trivial-bundle total space.
        have hScalarW : ContinuousOn
            (fun t : ℝ => ricciTensor (I := I) g (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            (Set.Icc (0 : ℝ) L) := by
          have hproj : Continuous
              (fun p : TotalSpace ℝ (fun _ : M => ℝ) => p.2) :=
            continuous_snd.comp
              ((Bundle.Trivial.homeomorphProd M ℝ).continuous)
          exact hproj.comp_continuousOn hScalarTotal
        -- (E) Integrability of the within-velocity Ricci integrand on `Icc 0 L`.
        have hIntW : IntervalIntegrable
            (fun t : ℝ => ricciTensor (I := I) g (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            MeasureTheory.volume 0 L := by
          apply ContinuousOn.intervalIntegrable
          rwa [Set.uIcc_of_le hL_nn']
        -- (F) Transfer to the `mfderiv = uPrime` form by a.e.-equality on `Ioo 0 L`.
        refine hIntW.congr_ae ?_
        have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) L)),
            t ∈ Set.Ioo (0 : ℝ) L := by
          rw [Set.uIoc_of_le hL_nn', ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
          exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
        filter_upwards [hIoo_ae] with t ht
        have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
        change ricciTensor (I := I) g (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          = ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)
        rw [mfderivWithin_of_mem_nhds hmem]
      -- (vi) global bundle-smoothness of each sinusoidal test field
      -- `t ↦ ⟨γ t, sin(π t / L) • (e i) t⟩`. The scalar `sin(π · / L)` is
      -- smooth, and `t ↦ ⟨γ t, (e i) t⟩` is globally bundle-`C^∞` (`hEbundle`),
      -- so their fibrewise product is smooth (`contMDiff_smul_bundleField`).
      have hVbundle :
          ∀ i : Fin (Module.finrank ℝ E - 1),
            ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
              (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
                (γ t)
                ((SectionAlongCurve.smulFun
                  (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun t))) := by
        intro i
        have hχ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
            (fun s : ℝ => Real.sin (Real.pi * s / L)) := by
          rw [contMDiff_iff_contDiff]
          exact Real.contDiff_sin.comp
            ((contDiff_const.mul contDiff_id).div_const L)
        have hprod :=
          DifferentialGeometry.Geometry.Riemannian.Variation.contMDiff_smul_bundleField
            (I := I) hγ_smooth hχ_smooth (hEbundle i)
        -- `(smulFun χ (e i)).toFun t = χ t • (e i).toFun t` definitionally.
        exact hprod
      exact bonnet_myers_length_le_of_ricci_bound (I := I) g γ hL_pos hEnorm
        hγ_smooth hγ_C1 hγ_geoOn _hK _hdim hRic' uPrime huPrimeEq hγ_unit
        e heDiff hParallel hON hPerp hIntegrandSum hRicIntegrable hγ_min hVbundle
  -- Conclude: the goal is `r ≤ π / √K`, and `L = r`, so `hL_le` closes it.
  exact hL_le

/-! ## Headline 1: diameter bound -/

set_option linter.deprecated false in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers diameter theorem.** On a complete connected Riemannian
manifold of dimension `n ≥ 2` with Ricci curvature bounded below by
`(n-1) K` for some `K > 0`, the metric diameter `EMetric.diam univ` is at
most `π / √K`. The hypothesis `hEnorm` is the supplied structural identity
that the fibre extended norm equals `ofReal (√ g.inner)`. -/
theorem bonnet_myers_diameter_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    EMetric.diam (Set.univ : Set M) ≤
      ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  refine Metric.ediam_le ?_
  intro x _ y _
  exact bonnet_myers_pairwise_edist_le_of_ricci_bound (E := E) g _hdim _hK _hRic hEnorm x y

/-! ## Compactness sub-leaf: `univ` is compact -/

set_option linter.deprecated false in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **bm-c-univ-compact.** The whole space `Set.univ : Set M` is compact.
Combines the diameter bound (sibling headline `bonnet_myers_diameter_of_ricci_bound`) with
exponential-map surjectivity on the closed ball of radius `π / √K` and
`IsCompact.of_isClosed_subset` together with `isClosed_univ`. -/
theorem isCompact_univ
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    IsCompact (Set.univ : Set M) := by
  -- Pick a base point from `Nonempty M` (provided by `ConnectedSpace M`).
  let p : M := Classical.arbitrary M
  -- The radius `R := π / √K` is non-negative (since `K > 0`).
  set R : ℝ := Real.pi / Real.sqrt K with hR_def
  have hR_nn : 0 ≤ R := by
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  -- Diameter bound from the proved sibling headline.
  have hdiam : EMetric.diam (Set.univ : Set M) ≤ ENNReal.ofReal R :=
    bonnet_myers_diameter_of_ricci_bound (E := E) g _hdim _hK _hRic hEnorm
  -- Exponential surjectivity on the closed ball of radius `R`.  The closed-ball
  -- metric here is the one fixed at the surjectivity lemma's elaboration; we let
  -- its type flow rather than re-annotating, so it matches the image-compactness
  -- lemma's closed ball verbatim.
  have hsurj :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.bm_c_expMap_surjective_on_closedBall
      (I := I) g p hR_nn hdiam
  -- The image of the closed ball under `expMap` is compact.
  have himg :=
    isCompact_image_closedBall_under_expMap (I := I) (E := E) g p hR_nn
  -- `univ` is closed; together with the compact superset, it is compact.
  exact himg.of_isClosed_subset isClosed_univ hsurj

/-! ## Headline 2: compactness -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers compactness theorem.** On a complete connected Riemannian
manifold of dimension `n ≥ 2` with Ricci curvature bounded below by
`(n-1) K` for some `K > 0`, the manifold is compact (`CompactSpace M`). The
hypothesis `hEnorm` is the supplied structural identity that the fibre
extended norm equals `ofReal (√ g.inner)`. -/
theorem bonnet_myers_compactSpace_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v))) :
    CompactSpace M :=
  isCompact_univ_iff.mp (isCompact_univ (E := E) g _hdim _hK _hRic hEnorm)

/-! ## Headline 3: finite fundamental group -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Bonnet-Myers finiteness of the fundamental group.** On a complete
connected Riemannian manifold of dimension `n ≥ 2` with Ricci curvature
bounded below by `(n-1) K` for some `K > 0`, the fundamental group
`π₁(M, x)` at any base point is finite. The proof passes to the universal
cover, pulls back the Ricci bound, applies the compactness theorem to the
lifted manifold, and identifies the cover fibre over `x` with `π₁(M, x)`
via monodromy. The hypothesis `hEnormBase` is the supplied structural
identity that the fibre extended norm on `M` equals `ofReal (√ g.inner)`.

One residual gap remains: the cross-instance norm-diamond bridge reconciling
the lifted `RiemannianBundle` extended norm with the project `Tensor0SBundle`
extended norm in the compactness application (the two agree pointwise as the
square root of the lifted metric, but the explicit identification is left as
a `sorry`). -/
theorem bonnet_myers_finite_fundamentalGroup_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [PseudoEMetricSpace M] [Inhabited M]
    [T2Space (TangentBundle I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnormBase : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v)))
    (x : M) :
    Finite (FundamentalGroup M x) := by
  -- `[Inhabited M]` is a signature hypothesis (needed for the universal-cover
  -- infrastructure and for stating the cover's tangent-bundle separation).
  -- The universal cover and its projection.
  set UC := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
  set p :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
  -- The projection is a covering map: provided by the universal-cover infrastructure.
  have hcov :
      IsCoveringMap
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.UniversalCover.isCoveringMap
  -- `PathConnectedSpace M`: from `[ConnectedSpace M]` + `[LocPathConnectedSpace M]`.
  haveI hpcM : PathConnectedSpace M :=
    PathConnectedSpace.of_locPathConnectedSpace
  -- Lifted Riemannian metric on the universal cover.  Introduced as a transparent
  -- `let` (not `set`) so that the lifted-bundle fibre instances reduce
  -- definitionally to `(liftedMetric g).inner` for the principled completeness API.
  let gLift :
      SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := I) g
  -- Bundled Riemannian-bundle structure on the tangent bundle of the universal cover.
  -- Installed as a transparent `letI` (not `haveI`) so that the derived fibre
  -- `NormedAddCommGroup` / `InnerProductSpace` instances reduce definitionally to
  -- the lifted metric `gLift.inner`, which the principled completeness API needs.
  letI hRB :
      Bundle.RiemannianBundle
        (fun (xt :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I xt) :=
    ⟨gLift.toRiemannianMetric⟩
  -- `SecondCountableTopology H` from finite-dimensional model space `E`.
  haveI hSCH : SecondCountableTopology H :=
    ModelWithCorners.secondCountableTopology I
  -- `SecondCountableTopology M` from chart cover + σ-compactness.
  haveI hSCM : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  -- Compactness of the lifted manifold. This consumes the lifted instances and the
  -- Ricci-bound pullback (`ricciBoundedBelow_pullback_universalCover`), and the
  -- still-sorry `CompleteSpace` of the universal cover. We package the latter as a
  -- local instance to mirror the upstream skeleton, then apply the proved compactness
  -- headline (Headline 2) to the lifted data.
  -- Ricci pullback to the universal cover. The two `chartRiemannBasisIdentity`
  -- hypotheses are propagated through the chart-Riemann CLM bridge, and are
  -- isolated as named residual gaps pending the deferred-deep predicate
  -- discharge in `Integral/Connection/ChartBridge/Riemann.lean`.
  have hBasisLift : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity
        (I := I) gLift x' :=
    fun x' =>
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) gLift x'
  have hBasisBase : ∀ x : M,
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity
        (I := I) g x :=
    fun x =>
      DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) g x
  have hRicLift :
      RicciBoundedBelow (I := I) gLift (((Module.finrank ℝ E : ℝ) - 1) * K) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_pullback_universalCover
      (I := I) (g := g) _hRic hBasisLift hBasisBase
  -- The universal cover is a regular topological space (Hausdorff + locally
  -- compact ⇒ regular); this discharges the `[RegularSpace (UC M)]` hypothesis
  -- of the principled lifted pseudo-emetric API.
  haveI hRegUC :
      RegularSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace
      (M := M) I
  -- The bundle norm — square-root inner-product identity on the cover fibres,
  -- with respect to the lifted Riemannian-bundle structure `⟨gLift.toRiemannianMetric⟩`
  -- installed above (`hRB`). The fibre inner product is `gLift.inner` by the
  -- `RiemannianMetric.toCore` construction, so `‖v‖ₑ = ofReal (√ ⟪v, v⟫) =
  -- ofReal (√ gLift.inner x' v v)`.
  have hEnormCover :
      ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (v : TangentSpace I x'),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gLift.inner x' v v)) := by
    intro x' v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    -- The fibre inner product on `TangentSpace I x'` is, by the lifted
    -- Riemannian-bundle instance `hRB = ⟨gLift.toRiemannianMetric⟩`, the lifted
    -- metric `gLift.inner x'`.  The two sides agree definitionally through the
    -- `RiemannianMetric.toCore` inner product.
    have hinner : (inner ℝ v v : ℝ) = gLift.inner x' v v := rfl
    rw [hinner]
  -- Install the principled lifted pseudo-emetric structure on the universal
  -- cover, whose underlying topology is the manifold topology and whose
  -- `edist` is `riemannianEDist I`.
  letI hUCem :
      PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_pseudoEMetricSpace
      (I := I) (M := M) gLift
  -- The cover is a Riemannian manifold for this structure (`edist = riemannianEDist`).
  haveI hRiemUC :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_isRiemannianManifold
      (I := I) (M := M) gLift
  -- Completeness of the universal cover, principled (axiom-clean): every Cauchy
  -- sequence for the lifted extended metric converges, by `1`-Lipschitz
  -- projection to the complete base `M` and lifting the limit through the
  -- covering map.
  haveI hCompUC :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_universalCover_lifted
      (I := I) (M := M) g hEnormBase hEnormCover
  -- The lifted tangent bundle is a continuous Riemannian bundle: the fibre inner
  -- product is, by the installed `hRB = ⟨gLift.toRiemannianMetric⟩`, the lifted
  -- metric `gLift.inner`, which depends continuously on the base point
  -- (`gLift.contMDiff.continuous`).
  haveI hCRBcover :
      IsContinuousRiemannianBundle E
        (fun (x' :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x') :=
    ⟨gLift.inner, gLift.contMDiff.continuous, fun _ _ _ => rfl⟩
  -- The tangent bundle of the lifted manifold is Hausdorff (it is a smooth vector
  -- bundle over a Hausdorff finite-dimensional manifold).
  haveI hT2TanCover :
      T2Space (TangentBundle I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)) :=
    inferInstance
  -- Apply Headline 2 (`bonnet_myers_compactSpace_of_ricci_bound`) to the lifted Riemannian manifold.
  -- `bonnet_myers_compactSpace_of_ricci_bound`'s `hEnorm` hypothesis is in the active lifted
  -- `RiemannianBundle` enorm (`hRB`), for which the enorm identity is the
  -- already-proven `hEnormCover`.
  haveI hCompactUC :
      CompactSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    bonnet_myers_compactSpace_of_ricci_bound (E := E) gLift _hdim _hK hRicLift (by
      -- Cross-instance norm-diamond reconciliation: the `bonnet_myers_compactSpace_of_ricci_bound`
      -- enorm hypothesis is in the project `Tensor0SBundle` enorm, while
      -- `hEnormCover` provides the same identity for the lifted
      -- `RiemannianBundle` enorm `hRB`. The two enorms agree pointwise (both
      -- the square-root of `gLift.inner`); the explicit bridge is a residual
      -- tangent-bundle norm-diamond gap.
      sorry)
  -- The fibre of the covering map over `x` is finite (compact + discrete).
  haveI hFinFibre :
      Finite
        ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          ⁻¹' {x}) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibre_finite
      hcov x
  -- Pick a base lift `e' ∈ proj⁻¹{x}` via path-connectedness of `M`.
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) x
  let e' :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
    ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩,
      by
        change
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
              (X := M)
              (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
            = x
        rfl⟩
  -- Fibre ↔ fundamental group bijection (from the universal-cover infrastructure).
  have hEquiv :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x})
        ≃ FundamentalGroup M x :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hcov x e'
  -- Transport finiteness across the bijection.
  exact Finite.of_equiv _ hEquiv

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
