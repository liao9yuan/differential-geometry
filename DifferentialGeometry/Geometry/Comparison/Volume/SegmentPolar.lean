import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentFrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentInterior
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentMeasure
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentNoConj

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
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

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
      ≤ ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g x
  let K : Set E :=
    (SegDom (I := I) g hEnorm x : Set E) ∩
      L '' Metric.closedBall (0 : E) R
  have hK : IsCompact K := by
    dsimp only [K]
    exact
      ((isCompact_closedBall (0 : E) R).image L.continuous).inter_left
        (isClosed_segDom (I := I) g hEnorm x)
  have hpre :
      L ⁻¹' gBall (I := I) g x R = Metric.ball (0 : E) R := by
    simpa only [L] using preimage_gBall (I := I) (E := E) g x R
  have hcover :
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
        (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' K := by
    intro y hy
    obtain ⟨v, hv, hexp⟩ :=
      ball_sub_image_segDom (I := I) g hEnorm x R hy
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      simpa only [Set.mem_preimage, L.apply_symm_apply] using hv.2
    refine ⟨v, ⟨hv.1, ?_⟩, hexp⟩
    exact ⟨L.symm v, Metric.ball_subset_closedBall hwopen, L.apply_symm_apply v⟩
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x (L w))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm x (L w)
          ((normalBasis (I := I) g x) i) t)
      1
  let Dh : E → ℝ≥0∞ := fun w =>
    ENNReal.ofReal
      (hypDensity (q * ‖w‖) (Module.finrank ℝ E - 1) 1)
  have hpreK :
      L ⁻¹' K ⊆ Metric.closedBall (0 : E) R := by
    intro w hw
    change L w ∈ K at hw
    rcases hw.2 with ⟨z, hz, hzw⟩
    have hzw' : z = w := L.injective hzw
    simpa only [hzw'] using hz
  have hpreK_meas : MeasurableSet (L ⁻¹' K) :=
    (hK.isClosed.preimage L.continuous).measurableSet
  have hpoint :
      ∀ᵐ w ∂(volume : Measure E), w ∈ L ⁻¹' K →
        ENNReal.ofReal (Dn w) ≤ Dh w := by
    filter_upwards [Measure.ae_ne (volume : Measure E) (0 : E)] with w hw0 hw
    change L w ∈ K at hw
    have hu0 : L w ≠ 0 := by
      intro hLw
      apply hw0
      apply L.injective
      simpa only [map_zero] using hLw
    have hno :
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          ¬ IsConjVec (I := I) g hEnorm x
            ((t • L w : TangentSpace I x) : E) :=
      segDom_no_conj (I := I) g hEnorm hw.1 hu0
    have hdens :=
      expDens_le_hyp (I := I) g hEnorm x (L w)
        (normalBasis (I := I) g x)
        (normalBasis_inner (I := I) g x)
        q hq hu0 hno hRic
    have hsqrt :
        Real.sqrt (g.inner x (L w) (L w)) = ‖w‖ := by
      simpa only [L] using normalFrame_sqrt (I := I) g x w
    apply ENNReal.ofReal_le_ofReal
    simpa only [Dn, Dh, hsqrt] using hdens
  have hmono :
      (∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
        ∫⁻ w in L ⁻¹' K, Dh w ∂(volume : Measure E) :=
    setLIntegral_mono_ae' hpreK_meas hpoint
  have hball_ae :
      Metric.closedBall (0 : E) R =ᵐ[(volume : Measure E)]
        Metric.ball (0 : E) R := by
    have hmeasure :
        (volume : Measure E) (Metric.closedBall (0 : E) R) =
          (volume : Measure E) (Metric.ball (0 : E) R) :=
      Measure.addHaar_closedBall_eq_addHaar_ball
        (volume : Measure E) (0 : E) R
    exact
      (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
        hmeasure.le measurableSet_ball.nullMeasurableSet
        measure_closedBall_lt_top.ne).symm
  have hnormal :
      (∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
        ((volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
          * ENNReal.ofReal
              (hypRadVol q (Module.finrank ℝ E - 1) R) := by
    calc
      (∫⁻ w in L ⁻¹' K,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E)) ≤
          ∫⁻ w in L ⁻¹' K, Dh w ∂(volume : Measure E) := hmono
      _ ≤ ∫⁻ w in Metric.closedBall (0 : E) R,
          Dh w ∂(volume : Measure E) :=
        lintegral_mono_set hpreK
      _ = ∫⁻ w in Metric.ball (0 : E) R,
          Dh w ∂(volume : Measure E) :=
        setLIntegral_congr hball_ae
      _ = (volume : Measure E).toSphere Set.univ *
          ENNReal.ofReal
            (hypRadVol q (Module.finrank ℝ E - 1) R) := by
        simpa only [Dh] using hypBall_lintegral (E := E) q hq hR
      _ = ((volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
          * ENNReal.ofReal
              (hypRadVol q (Module.finrank ℝ E - 1) R) := by
        rw [volSphere_finrank (E := E)]
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        ((fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' K) :=
      measure_mono hcover
    _ ≤ ∫⁻ v in K,
        ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
      riemVol_exp_image_le (I := I) g hEnorm x hK
    _ = ∫⁻ w in L ⁻¹' K,
        ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
      simpa only [Dn, L] using
        expJac_normal_int (I := I) (E := E) g hEnorm x K
    _ ≤ ((volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ)
        * ENNReal.ofReal
            (hypRadVol q (Module.finrank ℝ E - 1) R) :=
      hnormal

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
