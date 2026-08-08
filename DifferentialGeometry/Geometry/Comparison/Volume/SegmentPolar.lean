import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentArea
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentPole
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentGauss
import DifferentialGeometry.Geometry.Comparison.Variation.MinimalGeodesicNoConjugate
import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGradMain
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

/-!
# Polar-measure layer of the segment domain: capped Bishop–Gromov inputs

This file states the two volume-comparison inequalities that brick B5 of the
A0′ `VolumeComparisonInput` lane (`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`)
composes into the capped relative Bishop–Gromov bound.  For a fixed complete
member `(M, g)` with `Ric ≥ -(n-1)q²` (`n = finrank ℝ E`):

* `segBall_vol_le` — **absolute** upper bound (deliverable B2(α)(1)):
  `V(x,R) ≤ σ · v(R)`, where `V(x,R)` is the Riemannian volume of the open
  `edist`-ball, `v(R) = hypRadVol q (n-1) R` is the *radial* model volume, and
  `σ = (modelHaar E).toSphere Set.univ` is the **model sphere mass**
  (`= finrank · vol(unit ball)`, e.g. `2π` in dimension 2).  The `σ` factor is
  the sphere-integral the polar decomposition contributes on top of the radial
  `hypRadVol`; **it must NOT be dropped** — without it the bound is false (see
  the counterexample below).
* `segBall_vol_fin` — the B6-facing finiteness corollary `V(x,R) < ∞`, derived
  from `segBall_vol_le` (`σ` is finite: `Measure.toSphere` `IsFiniteMeasure`).
* `segBall_vol_rel` — **relative** capped bound (deliverable B2(α)(2), the form
  B5 needs), in multiplicative (division-free) shape:
  `V(x,R) · v(s) ≤ v(R) · V(x,s)` for `0 < s ≤ R`.  Here `σ` cancels across the
  ratio, so this form is normalization-independent and carries no `σ`.

## Counterexample fixing the constant (do NOT re-drop `σ`)

`M = E = ℝ²` flat (complete, connected, `RicciBoundedBelow g 0` with `q = 0`):
`V(x,R) = πR²`, but `hypRadVol 0 1 R = ∫₀ᴿ t dt = R²/2`, and `πR² > R²/2`.
The corrected bound is an equality here: `σ = 2π`, so `σ · (R²/2) = πR²`.
Dimension 1 (`ℝ`): `V = 2R`, `hypRadVol 0 0 R = R`, `σ = 2`, `2R ≤ 2·R`.

## Frontier status (honest — updated 2026-07-25, B5c)

Both statements are still `sorry`, but the frontier has MOVED.  The B2-era
"missing bridge" — the manifold-valued non-injective area inequality — is now
**in-tree and proved** (`riemVol_exp_image_le`, `SegmentArea.lean`, sorry-free):
for compact `K`,
`riemannianVolumeMeasure g (expMapIntrinsic x '' K) ≤ ∫⁻ v in K, ofReal (curveDensity
g (intrinsicGeodesic x v) (intrinsic Jacobi frame) 1) ∂modelHaar`, past the cut
locus, no injectivity — via a POU-weighted `Measure.sum` decomposition, the
weighted Euclidean area inequality `image_lintegral_le`, and the density identity
`exp_density_curve`.  Off-zero regularity is `intrinsicFiber_smooth` /
`expChart_contDiffAt` (the previously-cited `expMap_contMDiffAt_of_ne_zero` was
fictional; the intrinsic exponential is globally `C^∞` in the velocity).

The proof route for these two statements:

1. `ball_sub_image_segDom` (`SegmentDomain.lean`) covers the ball by
   `expMapIntrinsic '' (SegDom ∩ gBall)` — no injectivity, past the cut locus.
2. `riemVol_exp_image_le` (SegmentArea.lean, DONE) with the compact launch set
   `K = SegDom ∩ closedGBall R` bounds `V(x,R)` by `∫⁻ v in K, ofReal (curveDensity
   full-n-frame v) ∂modelHaar`.
3. **REMAINING FRONTIER (the absolute Bishop bound `∫⁻_K curveDensity ≤
   σ·hypRadVol`, brick L6).**  This is NOT assembly — no absolute
   `V ≤ σ·hypRadVol` template exists in any regime (the diffeo regime has only
   the polar EQUALITY `normalBall_polar` and RELATIVE ratio bounds
   `normalBall_cross`/`localBall_cross`).  It needs: (a) a GLOBAL Gauss
   block-determinant factorization of the full `n`-frame density into
   radial × transverse (`intrinsic_gauss` gives the global orthogonality; the
   `endpoint_det_split`/`density_det_eq` block-det machinery in `RadialGram.lean`
   is chart-scale + `private`, so must be redone past the cut locus); (b) the
   `√det(gₓ)` E-vs-`gₓ` Haar constant reconciling `modelHaar`/`toSphere`
   (E-orthonormal sphere) with the `gₓ`-arclength model; (c) a **SHARP** (`N = 1`)
   transverse bound `curveDensity(orthonormal transverse frame) ≤ hypDensity`
   — the in-tree `intrDens_le_hyp` has a NON-sharp `N = M₀/c` (from `intrPoleCap`,
   non-orthonormal frame), so integrating it yields only `σ·N·hypRadVol`; the
   sharp `N=1` needs a `gₓ`-orthonormal parallel frame (`exists_intrFrame`) with
   pole ratio `→ 1`; (d) polar integration (`lintegral_polar`) to `σ·hypRadVol`.
   The relative bound `segBall_vol_rel` further needs the truncated polar Fubini
   (cut-time `τ(θ)`) + the cross-Chebyshev lemma (`lintegral_cross_le`, B4) +
   injectivity of `expMapIntrinsic` on the open minimizing interior.

So the remaining blocker is the absolute (and then relative) Bishop–Gromov
volume comparison built on `riemVol_exp_image_le`.  See `SegmentPolar.md` and
`SegmentArea.md`.
-/

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The closed `g`-length ball in the tangent space at `x`. -/
def closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) : Set E :=
  {v : E | Real.sqrt (g.inner x (show TangentSpace I x from v)
    (show TangentSpace I x from v)) ≤ R}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem isClosed_closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsClosed (closedGBall (I := I) g x R) :=
  by
    have hcont : Continuous (fun v : E => g.inner x (show TangentSpace I x from v)
        (show TangentSpace I x from v)) := by
      simpa using (continuous_gInner_self (I := I) g x)
    exact isClosed_le (Real.continuous_sqrt.comp hcont) continuous_const

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem isCompact_closedGBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsCompact (closedGBall (I := I) g x R) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closedGBall (I := I) g x R, ?_⟩
  rw [Metric.isBounded_iff_subset_ball (0 : E)]
  refine ⟨R / Real.sqrt (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
    (I := I) g x) + 1, ?_⟩
  intro v hv
  have hc_pos : 0 < DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
      (I := I) g x :=
    DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst_pos (I := I) g x
  have hsc_pos : 0 < Real.sqrt
      (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst (I := I) g x) :=
    Real.sqrt_pos.mpr hc_pos
  have hcoerc : DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
      (I := I) g x * ‖v‖ ^ 2 ≤ g.inner x (show TangentSpace I x from v)
        (show TangentSpace I x from v) :=
    DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst_le (I := I) g x v
  have hgnn : 0 ≤ g.inner x v v := le_trans (by positivity) hcoerc
  have hkey : Real.sqrt (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
      (I := I) g x) * ‖v‖ ≤ Real.sqrt (g.inner x v v) := by
    have hlhs_eq : Real.sqrt (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
          (I := I) g x) * ‖v‖
        = Real.sqrt (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
            (I := I) g x * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg v)]
    rw [hlhs_eq]
    exact Real.sqrt_le_sqrt hcoerc
  have hnorm : ‖v‖ ≤ Real.sqrt (g.inner x v v) / Real.sqrt
      (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst (I := I) g x) := by
    rw [le_div_iff₀ hsc_pos, mul_comm]
    exact hkey
  have hle : Real.sqrt (g.inner x v v) / Real.sqrt
        (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst (I := I) g x) ≤
      R / Real.sqrt (DifferentialGeometry.Geometry.Riemannian.gpCoerciveConst
        (I := I) g x) :=
    div_le_div_of_nonneg_right hv (Real.sqrt_nonneg _)
  simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using
    lt_of_le_of_lt (hnorm.trans hle) (lt_add_one _)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Hopf–Rinow surjectivity onto the metric ball, closed-launch version.**
Every point of the open `edist`-ball of radius `R` is the intrinsic exponential
of a segment-domain vector of `g`-length `≤ R`.  Same content as
`ball_sub_image_segDom` with the `g`-length ball closed — this is the compact
launch set used by the image-measure upper bound. -/
theorem ball_sub_image_segDom_closed [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) (R : ℝ) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) ''
        ({v : E | (show TangentSpace I x from v) ∈ SegDom (I := I) g hEnorm x}
          ∩ closedGBall (I := I) g x R) := by
  have hcov := ball_sub_image_segDom (I := I) g hEnorm x R
  have hcovE : {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      (fun b : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from b)) ''
        {v : E | (show TangentSpace I x from v) ∈
          SegDom (I := I) g hEnorm x ∩ gBall (I := I) g x R} := by
    simpa using hcov
  have hgBallE : {v : E | (show TangentSpace I x from v) ∈
        gBall (I := I) g x R} ⊆ closedGBall (I := I) g x R := by
    intro v hv
    change Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v)) ≤ R
    exact le_of_lt hv
  have hsub : {v : E | (show TangentSpace I x from v) ∈
        SegDom (I := I) g hEnorm x ∩ gBall (I := I) g x R} ⊆
      {v : E | (show TangentSpace I x from v) ∈ SegDom (I := I) g hEnorm x}
        ∩ closedGBall (I := I) g x R := by
    intro v hv
    exact ⟨hv.1, hgBallE hv.2⟩
  exact hcovE.trans (Set.image_mono hsub)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The metric ball volume is bounded by the intrinsic-Jacobi density integral
over the compact segment-domain launch ball (the image-measure reduction behind
`segBall_vol_le`). -/
private theorem segBall_vol_le_density
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) (R : ℝ) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ∫⁻ v in {v : E | (show TangentSpace I x from v) ∈
            SegDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcov := ball_sub_image_segDom_closed (I := I) g hEnorm x R
  have hK : IsCompact
      ({v : E | (show TangentSpace I x from v) ∈
          SegDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R) := by
    have hclosed : IsClosed {v : E | (show TangentSpace I x from v) ∈
        SegDom (I := I) g hEnorm x} := by
      simpa using (isClosed_segDom (I := I) g hEnorm x).preimage
        (continuous_id : Continuous (fun v : E => v))
    exact (isCompact_closedGBall (I := I) g x R).of_isClosed_subset
      (hclosed.inter (isClosed_closedGBall (I := I) g x R))
      (Set.inter_subset_right : {v : E | (show TangentSpace I x from v) ∈
          SegDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R ⊆
          closedGBall (I := I) g x R)
  have himg := riemVol_exp_image_le (I := I) g hEnorm x hK
  have hFcont : Continuous
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous
  have hball : MeasurableSet
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
    have hcont : Continuous (fun y : M => riemannianEDist I x y) := by
      simpa [Manifold.riemannianEDist_comm] using
        (continuous_riemannianEDist_to (I := I) x)
    exact (isOpen_lt hcont continuous_const).measurableSet
  have himg_meas : MeasurableSet
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) ''
        ({v : E | (show TangentSpace I x from v) ∈
          SegDom (I := I) g hEnorm x} ∩ closedGBall (I := I) g x R)) :=
    (hK.image hFcont).measurableSet
  exact (measure_mono hcov).trans himg

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A segment-domain launch vector has no conjugate vectors on the open radial
interval: the radial geodesic realizes the distance to its endpoint, so its
unit-speed reparametrization minimizes arc length, and a length-minimizing
geodesic has no interior conjugate vectors. -/
theorem segDom_not_conj
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegDom (I := I) g hEnorm x) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm x ((t • v : TangentSpace I x) : E) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set ℓ : ℝ := Real.sqrt (g.inner x v v) with hℓ_def
  by_cases hv0 : v = 0
  · have htz : ((t • v : TangentSpace I x) : E) = 0 := by simp [hv0]
    rw [htz]
    unfold IsConjVec
    simp only [not_not]
    have hz := mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm x
    change Function.Injective (fun w : E =>
      mfderiv 𝓘(ℝ, E) I (fun b : E =>
        (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from b) : M))
        (0 : E) w)
    rw [hz]
    simpa using (Function.injective_id : Function.Injective (id : E → E))
  · have hℓ_pos : 0 < ℓ := by
      rw [hℓ_def]
      exact Real.sqrt_pos.mpr (g.pos x v hv0)
    have hinner : g.inner x v v = ℓ ^ 2 := by
      rw [hℓ_def]
      exact (Real.sq_sqrt (gInner_self_nonneg (I := I) g x v)).symm
    let u : E := (ℓ⁻¹ • v : E)
    have hunit : g.inner x u u = 1 := by
      dsimp [u]
      rw [gInner_smul_self (I := I) g x ℓ⁻¹ v, hinner]
      have hpow : (ℓ⁻¹) ^ 2 * ℓ ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hℓ_pos), one_pow]
      exact hpow
    have hsmul : (ℓ : ℝ) • u = (v : E) := by
      change (ℓ : ℝ) • ((ℓ⁻¹ : ℝ) • (v : E)) = (v : E)
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ_pos), one_smul]
    have hlu : (ℓ • (show TangentSpace I x from u) : TangentSpace I x) = v := by
      simpa using hsmul
    have hmin : ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 ℓ) →
        η 0 = x →
        η ℓ = intrinsicGeodesic (I := I) g hEnorm x
            (show TangentSpace I x from u) ℓ →
        arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (show TangentSpace I x from u)) 0 ℓ ≤
          arcLength (I := I) g η 0 ℓ := by
      intro η hη hη0 hηL
      have hγ_len : arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (show TangentSpace I x from u)) 0 ℓ = ℓ := by
        rw [arcLength_radial (I := I) g hEnorm x
          (show TangentSpace I x from u) 0 ℓ, hunit]
        simp
      have hηL' : η ℓ = expMapIntrinsic (I := I) g hEnorm x v := by
        rw [hηL]
        rw [expMapIntrinsic_def]
        rw [← hlu]
        exact (intrinsicGeodesic_smul (I := I) g hEnorm x
          (show TangentSpace I x from u) ℓ).symm
      have hseg : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) =
          ENNReal.ofReal ℓ := by
        have hfin : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≠ ⊤ :=
          riemannianEDist_ne_top (I := I) x _
        rw [← (ENNReal.ofReal_toReal hfin)]
        congr 1
        exact hv.symm.trans hℓ_def.symm
      have hd := DifferentialGeometry.edistOf_le_arcLength (I := I) g
        (a := 0) (b := ℓ) hℓ_pos.le hη
      have hdist_le' : riemannianEDist I x (η ℓ) ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        have hbridge := DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist
          (I := I) g hEnorm x (η ℓ)
        rw [hη0] at hd
        rwa [hbridge] at hd
      have hof : ENNReal.ofReal ℓ ≤ ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        have hd1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≤
            ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
          simpa [hηL'] using hdist_le'
        have hd2 : riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x v 1) ≤
            ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
          simpa [expMapIntrinsic_def] using hd1
        have hseg' : riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x v 1) =
            ENNReal.ofReal ℓ := by
          simpa [expMapIntrinsic_def] using hseg
        rwa [hseg'] at hd2
      have hle : ℓ ≤ arcLength (I := I) g η 0 ℓ := by
        exact (ENNReal.ofReal_le_ofReal_iff
          (arcLength_nonneg (I := I) g hℓ_pos.le)).mp hof
      rw [hγ_len]
      exact hle
    have hc : t * ℓ ∈ Set.Ioo (0 : ℝ) ℓ := by
      constructor
      · exact mul_pos ht.1 hℓ_pos
      · simpa using (mul_lt_mul_of_pos_right ht.2 hℓ_pos)
    have hn := not_conj_of_min_len (I := I) g hEnorm x u hunit ℓ hℓ_pos hmin hc
    have htv : ((t • v : TangentSpace I x) : E) = (t * ℓ) • u := by
      rw [← hlu, smul_smul]
      rfl
    rwa [← htv] at hn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Gauss factorization of the intrinsic Jacobi endpoint density.**  For a
`gₓ`-orthonormal transverse frame perpendicular to `v`, the full-frame density
`expJacDensity x v` factors as the fixed base chart density
`normalChartDensity g x 0` (= `√det gₓ` in the model basis) times the
transverse-frame curve density at the endpoint. -/
theorem expJacDensity_eq_ncd0_mul_transverse
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {v : TangentSpace I x} (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0) :
    expJacDensity (I := I) g hEnorm x (v : E) =
      normalChartDensity (I := I) g x 0 *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hv_li : LinearIndependent ℝ w := by
    simpa using linIndep_of_ortho (I := I) g x w hON
  obtain ⟨B, hBnone, hBsome⟩ :=
    exists_perp_basis (I := I) g x v w hv_li hperp (g.pos x v hvne)
  let a : Option (Fin d) → E := fun o => (B o : E)
  let e : Option (Fin d) ≃ Fin (Module.finrank ℝ E) := basisIndexEquiv B
  let V : Option (Fin d) → ∀ t : ℝ, TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm x v t) :=
    fun o t => intrinsicJacobi (I := I) g hEnorm x v (chartModelBasis E (e o)) t
  let C : Matrix (Option (Fin d)) (Option (Fin d)) ℝ := (modelBasisFor B).toMatrix a
  have hC : ∀ o o', C o o' = (modelBasisFor B).repr (a o') o := by
    intro o o'
    rfl
  have hb : ∀ o, (modelBasisFor B) o = chartModelBasis E (e o) := by
    intro o
    simp [modelBasisFor, e, Module.Basis.reindex_apply]
  have hjac : ∀ (u : E),
      intrinsicJacobi (I := I) g hEnorm x v (show TangentSpace I x from u) 1 =
        (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) (v : E)) u := by
    intro u
    simpa [intrinsicJacobi, expMapIntrinsic_def] using
      (intrinsic_jacobi_one (I := I) g hEnorm x (v : E) u)
  have hlin : ∀ o : Option (Fin d),
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from z)) (v : E)) (a o)
        = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E)) (chartModelBasis E (e o')) := by
    intro o
    have hsum := (modelBasisFor B).sum_repr (a o)
    calc
      (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from z)) (v : E)) (a o)
          = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E))
              (∑ o', (modelBasisFor B).repr (a o) o' • (modelBasisFor B) o') := by
            exact congrArg (fun z : E =>
              (mfderiv 𝓘(ℝ, E) I (fun u : E =>
                (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from u) : M))
                (v : E)) z) hsum.symm
      _ = ∑ o', (modelBasisFor B).repr (a o) o' •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E)) ((modelBasisFor B) o') := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun o' _ => ?_)
          exact (ContinuousLinearMap.map_smul
            (mfderiv 𝓘(ℝ, E) I (fun z : E =>
              (expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from z) : M))
              (v : E)) ((modelBasisFor B).repr (a o) o') ((modelBasisFor B) o'))
      _ = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E)) (chartModelBasis E (e o')) := by
          refine Finset.sum_congr rfl (fun o' _ => ?_)
          rw [hC o' o, hb o']
  have hrecomb : ∀ o : Option (Fin d),
      velJacFrame (I := I) g hEnorm x v w o 1 = ∑ o', C o' o • V o' 1 := by
    intro o
    have hV' : velJacFrame (I := I) g hEnorm x v w o 1 =
        intrinsicJacobi (I := I) g hEnorm x v (show TangentSpace I x from a o) 1 := by
      rcases o with - | i
      · simpa [velJacFrame, a, hBnone] using
          (radialJac_eq_vel (I := I) g hEnorm x v).symm
      · simp [velJacFrame, a, hBsome]
    have h1' : velJacFrame (I := I) g hEnorm x v w o 1 =
        (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) (v : E)) (a o) :=
      hV'.trans (hjac (a o))
    have h2' : (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from z)) (v : E)) (a o)
        = ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E)) (chartModelBasis E (e o')) :=
      hlin o
    have h3' : ∑ o', C o' o •
            (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from z)) (v : E)) (chartModelBasis E (e o'))
        = ∑ o', C o' o • V o' 1 := by
      refine Finset.sum_congr rfl (fun o' _ => ?_)
      change C o' o • (mfderiv 𝓘(ℝ, E) I (fun z : E => expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from z)) (v : E)) (chartModelBasis E (e o')) =
        C o' o • V o' 1
      rw [← hjac (chartModelBasis E (e o'))]
      rfl
    exact h1'.trans (h2'.trans h3')
  have hrecomb' := curveDensity_recomb (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm x v) V
    (velJacFrame (I := I) g hEnorm x v w) 1 C hrecomb
  have hsplit := velJac_density_split (I := I) g hEnorm x v w hperp
  have hExp : expJacDensity (I := I) g hEnorm x (v : E) =
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 := by
    rw [expJacDensity]
    exact (curveDensity_reindex (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
      (fun i : Fin (Module.finrank ℝ E) =>
        intrinsicJacobi (I := I) g hEnorm x v (chartModelBasis E i)) 1 e).symm
  have hBperp : ∀ i, g.inner x (v : E) (B (some i)) = 0 := by
    intro i
    rw [hBsome i]
    exact hperp i
  have hONB : ∀ i j, g.inner x (B (some i)) (B (some j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hBsome i, hBsome j]
    exact hON i j
  have hncd := normalChartDensity_zero_of_perpOrthonormal (I := I) g x (v : E) B
    hBnone hBperp hONB
  have hdetC : |C.det| = |(modelBasisFor B).det B| := by
    change |((modelBasisFor B).toMatrix a).det| = |(modelBasisFor B).det B|
    rw [Module.Basis.det_apply]
  have hV1 : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 =
      (Real.sqrt (g.inner x v v) / |C.det|) *
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 := by
    have hdet_ne : |C.det| ≠ 0 := by
      rw [hdetC]
      exact abs_ne_zero.mpr ((modelBasisFor B).isUnit_det B).ne_zero
    have hV : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 =
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (velJacFrame (I := I) g hEnorm x v w) 1 / |C.det| := by
      have hA : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (velJacFrame (I := I) g hEnorm x v w) 1 =
          |C.det| * curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v) V 1 := by
        simpa [mul_comm] using hrecomb'
      exact (eq_div_iff hdet_ne).mpr (by rw [mul_comm]; exact hA.symm)
    rw [hV, hsplit]
    field_simp [hdet_ne]
  rw [hExp, hV1]
  rw [hncd]
  rw [← hdetC]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The transverse orthonormal-frame curve density along a segment-domain
geodesic is bounded by the speed-scaled hyperbolic model density on the open
radial interval (sharp constant 1, for a fixed `gₓ`-orthonormal perpendicular
frame). -/
theorem transverseDensity_le_hyp
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t ≤
        hypDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t := by
  have hno : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ¬ IsConjVec (I := I) g hEnorm x ((t • v : TangentSpace I x) : E) :=
    fun t ht => segDom_not_conj (I := I) g hEnorm x hv ht
  have hanti := intrRatioOfFrame (I := I) g hEnorm x v q 1 hq hd (g.pos x v hvne)
    w hON hperp hno hRic
  have hlim := poleLimit (I := I) g hEnorm x v q hq (g.pos x v hvne) w hON hperp
  intro t ht
  have hpos : 0 < hypDensity (q * Real.sqrt (g.inner x v v))
      (Module.finrank ℝ E - 1) t :=
    hypDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht.1
  have hRatioLE :
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
        hypDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) t /
          hypDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) t ≤
          curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
              (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) s /
            hypDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsb : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsb ht hs.2.le
    exact ge_of_tendsto hlim hev
  rwa [div_le_one hpos] at hRatioLE

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Absolute Bishop volume upper bound** (deliverable B2(α)(1)).

For a complete member with `Ric ≥ -(n-1)q²`, the Riemannian volume of the open
`edist`-ball of radius `R` about `x` is at most `σ · hypRadVol q (n-1) R`, where
`σ = (modelHaar E).toSphere Set.univ` is the model sphere mass
(`= finrank · vol(unit ball)`).  The sphere factor `σ` is essential — dropping
it makes the inequality false (flat `ℝ²`: `V = πR² > R²/2 = hypRadVol 0 1 R`;
with `σ = 2π` the bound is the equality `πR² ≤ 2π·(R²/2)`).

FRONTIER (`sorry`): the non-injective area inequality is now DONE
(`riemVol_exp_image_le`, `SegmentArea.lean`); the remaining gap is the absolute
Bishop bound `∫⁻ v in SegDom ∩ closedGBall R, ofReal (curveDensity v) ∂modelHaar
≤ σ·hypRadVol` — global Gauss radial/transverse split + sharp (`N=1`) transverse
density bound + Euclidean polar.  See the file header and `SegmentPolar.md`. -/
theorem segBall_vol_le [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ((modelHaar (E := E)).toSphere Set.univ)
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) := by
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finiteness of the ball volume** (B6-facing corollary of `segBall_vol_le`).

Under `Ric ≥ -(n-1)q²` the open `edist`-ball has finite Riemannian volume — the
positivity+finiteness input the packing/counting step (brick B6) consumes.
Immediate from `segBall_vol_le`: the model sphere mass `(modelHaar E).toSphere`
is a finite measure and `hypRadVol` is real. -/
theorem segBall_vol_fin [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} < ⊤ :=
  lt_of_le_of_lt (segBall_vol_le (I := I) g hEnorm x hq hR hRic)
    (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Capped relative Bishop–Gromov volume comparison** (deliverable B2(α)(2)),
multiplicative (division-free) form — the input brick B5 composes into
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

For a complete member with `Ric ≥ -(n-1)q²` and `0 < s ≤ R`, writing
`V(x,t)` for the Riemannian volume of the open `edist`-ball of radius `t` and
`v(t) = hypRadVol q (n-1) t` for the model volume,
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

FRONTIER (`sorry`): the non-injective area inequality is now DONE
(`riemVol_exp_image_le`, `SegmentArea.lean`); the remaining gap is the truncated
polar representation past the cut locus (per-direction cut time `τ(θ)`), the
cross-Chebyshev lemma `lintegral_cross_le` (brick B4), and injectivity of
`expMapIntrinsic` on the open minimizing interior.  See the file header and
`SegmentPolar.md`. -/
theorem segBall_vol_rel [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) s)
      ≤ ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  sorry

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
