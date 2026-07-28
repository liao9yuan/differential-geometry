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
  `σ = volume.toSphere Set.univ` on the standard `EuclideanSpace ℝ (Fin n)` is
  the **inner-product sphere mass**
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
The measure here must be the canonical inner-product `volume`, not `modelHaar`:
the latter is normalized by the arbitrary linear equivalence `toEuclidean`, so
its sphere mass changes under a rescaling of that equivalence.

## Completion status (updated 2026-07-27)

All three exported volume statements are proved.  The absolute estimate
`segBall_vol_le` uses the segment-domain cover, the non-injective exponential
area inequality, the radial/transverse density factorization, the sharp
transverse comparison, and Euclidean polar integration.  Its corollary
`segBall_vol_fin` supplies finite ball volume.

The relative estimate `segBall_vol_rel` uses the exact segment-interior polar
representation.  For each sphere direction it applies the cross inequality to
the indicator of the strict minimizing segment; downward closure comes from
`segInt_smul`, while an interior upper endpoint supplies a no-conjugacy window
beyond that endpoint.  `expDens_scale` and `hypDens_scale` cancel the positive
radial powers, and `lintegral_Iic_cross` integrates the resulting pointwise
comparison.  This route selects no global cut time and adds no consumer
assumptions.
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
`σ = volume.toSphere Set.univ` on `EuclideanSpace ℝ (Fin n)` is the canonical
inner-product sphere mass
(`= finrank · vol(unit ball)`).  The sphere factor `σ` is essential — dropping
it makes the inequality false (flat `ℝ²`: `V = πR² > R²/2 = hypRadVol 0 1 R`;
with `σ = 2π` the bound is the equality `πR² ≤ 2π·(R²/2)`).

The proof retains the essential sphere-mass factor and is sharp in the flat
model. -/
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
Immediate from `segBall_vol_le`: the canonical sphere mass
`volume.toSphere univ` on `EuclideanSpace ℝ (Fin n)` is finite and `hypRadVol`
is real. -/
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
/-- The volume of an open metric ball is the exponential-Jacobian integral
over the radially strict minimizing vectors of length below the radius. -/
theorem segBall_area_eq [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {R : ℝ} (hR : 0 < R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      = ∫⁻ v in
          SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] E :=
    normalFrame (I := I) (E := E) g x
  let Kc : Set E :=
    (SegDom (I := I) g hEnorm x : Set E) ∩
      L '' Metric.closedBall (0 : E) R
  let Ki : Set E :=
    (SegInt (I := I) g hEnorm x : Set E) ∩
      gBall (I := I) g x R
  have hKc : IsCompact Kc := by
    dsimp only [Kc]
    exact
      ((isCompact_closedBall (0 : E) R).image L.continuous).inter_left
        (isClosed_segDom (I := I) g hEnorm x)
  have hKi : MeasurableSet Ki := by
    exact (measurableSet_segInt (I := I) g hEnorm x).inter
      (measurableSet_gBall (I := I) g x R)
  have hpre :
      L ⁻¹' gBall (I := I) g x R = Metric.ball (0 : E) R := by
    simpa only [L] using preimage_gBall (I := I) (E := E) g x R
  have hKiKc : Ki ⊆ Kc := by
    intro v hv
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      simpa only [Set.mem_preimage, L.apply_symm_apply] using hv.2
    exact ⟨segInt_subset (I := I) g hEnorm x hv.1,
      ⟨L.symm v, Metric.ball_subset_closedBall hwopen,
        L.apply_symm_apply v⟩⟩
  have hdiff_sub :
      L ⁻¹' Kc \ L ⁻¹' Ki ⊆
        L ⁻¹' (SegDom (I := I) g hEnorm x \
          SegInt (I := I) g hEnorm x) ∪
            Metric.sphere (0 : E) R := by
    intro w hw
    rcases hw with ⟨hwc, hwnKi⟩
    change L w ∈ Kc at hwc
    by_cases hwI : L w ∈ SegInt (I := I) g hEnorm x
    · right
      have hwclosed : w ∈ Metric.closedBall (0 : E) R := by
        rcases hwc.2 with ⟨z, hz, hzw⟩
        have hzw' : z = w := L.injective hzw
        simpa only [hzw'] using hz
      have hwnopen : w ∉ Metric.ball (0 : E) R := by
        intro hwopen
        apply hwnKi
        change L w ∈ Ki
        refine ⟨hwI, ?_⟩
        change w ∈ L ⁻¹' gBall (I := I) g x R
        rw [hpre]
        exact hwopen
      rw [← Metric.closedBall_diff_ball]
      exact ⟨hwclosed, hwnopen⟩
    · left
      exact ⟨hwc.1, hwI⟩
  have hdiff :
      (volume : Measure E) (L ⁻¹' Kc \ L ⁻¹' Ki) = 0 := by
    apply measure_mono_null hdiff_sub
    apply measure_union_null
    · simpa only [L] using segEnd_zero (I := I) (E := E) g hEnorm x
    · exact Measure.addHaar_sphere (volume : Measure E) (0 : E) R
  have hpre_ae :
      L ⁻¹' Kc =ᵐ[(volume : Measure E)] L ⁻¹' Ki := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [diff_eq_empty.mpr (preimage_mono hKiKc), measure_empty]
  have harea :
      (∫⁻ v in Kc,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in Ki,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
    calc
      _ = ∫⁻ w in L ⁻¹' Kc,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x (L w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x (L w)
                  ((normalBasis (I := I) g x) i) t)
              1)
          ∂(volume : Measure E) := by
        simpa only [L] using
          expJac_normal_int (I := I) (E := E) g hEnorm x Kc
      _ = ∫⁻ w in L ⁻¹' Ki,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x (L w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x (L w)
                  ((normalBasis (I := I) g x) i) t)
              1)
          ∂(volume : Measure E) :=
        setLIntegral_congr hpre_ae
      _ = ∫⁻ v in Ki,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := by
        simpa only [L] using
          (expJac_normal_int (I := I) (E := E)
            g hEnorm x Ki).symm
  have hcover :
      {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
        (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' Kc := by
    intro y hy
    obtain ⟨v, hv, hexp⟩ :=
      ball_sub_image_segDom (I := I) g hEnorm x R hy
    have hwopen : L.symm v ∈ Metric.ball (0 : E) R := by
      rw [← hpre]
      simpa only [Set.mem_preimage, L.apply_symm_apply] using hv.2
    exact ⟨v, ⟨hv.1, ⟨L.symm v,
      Metric.ball_subset_closedBall hwopen,
      L.apply_symm_apply v⟩⟩, hexp⟩
  have hKi_image :
      (fun b : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from b)) '' Ki ⊆
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
    rintro y ⟨v, hv, rfl⟩
    have hvD :
        v ∈ SegDom (I := I) g hEnorm x :=
      segInt_subset (I := I) g hEnorm x hv.1
    have hfin :
        riemannianEDist I x
          (expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) ≠ ⊤ :=
      riemannianEDist_ne_top (I := I) x _
    change riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v)) < ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal hfin,
      ← (mem_segDom (I := I)).mp hvD]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 hv.2
  have hKi_inj : Set.InjOn
      (fun b : E =>
        expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from b)) Ki :=
    (exp_inj_segInt (I := I) g hEnorm x).mono inter_subset_left
  apply le_antisymm
  · calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          ((fun b : E =>
            expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from b)) '' Kc) :=
        measure_mono hcover
      _ ≤ ∫⁻ v in Kc,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
        riemVol_exp_image_le (I := I) g hEnorm x hKc
      _ = ∫⁻ v in Ki,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) :=
        harea
      _ = ∫⁻ v in
          SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E)) := rfl
  · calc
      (∫⁻ v in
          SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x R,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        riemannianVolumeMeasure (I := I) (M := M) g
          ((fun b : E =>
            expMapIntrinsic (I := I) g hEnorm x
              (show TangentSpace I x from b)) '' Ki) := by
        simpa only [Ki] using
          (riemVol_exp_image_eq (I := I) g hEnorm x hKi hKi_inj).symm
      _ ≤ riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} :=
        measure_mono hKi_image

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Capped relative Bishop–Gromov volume comparison** (deliverable B2(α)(2)),
multiplicative (division-free) form — the input brick B5 composes into
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

For a complete member with `Ric ≥ -(n-1)q²` and `0 < s ≤ R`, writing
`V(x,t)` for the Riemannian volume of the open `edist`-ball of radius `t` and
`v(t) = hypRadVol q (n-1) t` for the model volume,
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

The proof works direction by direction on the strict minimizing segment and
integrates the indicator-truncated density comparison; it does not choose a
global cut-time function. -/
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
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let L : E ≃L[ℝ] TangentSpace I x :=
    normalFrame (I := I) (E := E) g x
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    normalBasis (I := I) g x
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x (L w))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm x (L w) (B i) t)
      1
  let T : Set E :=
    L ⁻¹' SegInt (I := I) g hEnorm x
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | L (r.1 • u.1) ∈ SegInt (I := I) g hEnorm x}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (hypDensity (q * r.1) d 1)
  have hDn_eq (w : E) :
      Dn w =
        |(chartModelBasis E).det B| *
          expJacDensity (I := I) g hEnorm x (L w) := by
    simpa only [Dn, B, expJacDensity] using
      jacDens_basis (I := I) g hEnorm x (L w)
        (chartModelBasis E) B
  have hDn_cont : Continuous Dn := by
    rw [show Dn = fun w =>
        |(chartModelBasis E).det B| *
          expJacDensity (I := I) g hEnorm x (L w) by
      funext w
      exact hDn_eq w]
    exact continuous_const.mul
      ((expJac_continuous (I := I) g hEnorm x).comp L.continuous)
  have hDn_nonneg (w : E) : 0 ≤ Dn w := by
    simp only [Dn, curveDensity]
    exact Real.sqrt_nonneg _
  have hT_meas : MeasurableSet T :=
    (measurableSet_segInt (I := I) g hEnorm x).preimage
      L.continuous.measurable
  have hS_meas (u : Metric.sphere (0 : E) 1) :
      MeasurableSet (S u) := by
    exact (measurableSet_segInt (I := I) g hEnorm x).preimage
      (L.continuous.comp
        (continuous_subtype_val.smul continuous_const)).measurable
  have hF_meas (u : Metric.sphere (0 : E) 1) :
      Measurable (F u) := by
    exact (ENNReal.measurable_ofReal.comp
      (hDn_cont.measurable.comp
        (continuous_subtype_val.smul continuous_const).measurable)).indicator
          (hS_meas u)
  have hG_meas : Measurable G := by
    have hscale (r : Set.Ioi (0 : ℝ)) :
        hypDensity (q * r.1) d 1 =
          hypDensity q d r.1 / r.1 ^ d := by
      apply (eq_div_iff (pow_ne_zero d r.2.ne')).2
      simpa only [mul_one, mul_comm] using
        hypDens_scale q r.1 d 1 r.2.ne'
    rw [show G = fun r : Set.Ioi (0 : ℝ) =>
        ENNReal.ofReal (hypDensity q d r.1 / r.1 ^ d) by
      funext r
      change ENNReal.ofReal (hypDensity (q * r.1) d 1) =
        ENNReal.ofReal (hypDensity q d r.1 / r.1 ^ d)
      rw [hscale r]]
    exact ENNReal.measurable_ofReal.comp
      (((hypDen_continuous q d).measurable.comp measurable_subtype_coe).div
        (measurable_subtype_coe.pow_const d))
  have hS_down (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) :
      a ∈ S u := by
    change L (b.1 • u.1) ∈ SegInt (I := I) g hEnorm x at hb
    change L (a.1 • u.1) ∈ SegInt (I := I) g hEnorm x
    have hab' : a.1 ≤ b.1 := hab
    have hratio0 : 0 ≤ a.1 / b.1 :=
      div_nonneg a.2.le b.2.le
    have hratio1 : a.1 / b.1 ≤ 1 :=
      (div_le_one b.2).2 hab'
    have hscaled :=
      segInt_smul (I := I) g hEnorm hb hratio0 hratio1
    simpa only [map_smul, smul_smul,
      div_mul_cancel₀ a.1 b.2.ne'] using hscaled
  have hu_inner (u : Metric.sphere (0 : E) 1) :
      g.inner x (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    simp only [L, normalFrame_inner, real_inner_self_eq_norm_sq,
      hunorm, one_pow]
  have hG_pos (r : Set.Ioi (0 : ℝ)) :
      0 < hypDensity (q * r.1) d 1 :=
    hypDensity_pos (mul_nonneg hq r.2.le) one_pos
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image
        ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio_Iic (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r :=
    Iio_ae_eq_Iic' (hsingle r)
  have hR : 0 < R := hs.trans_le hsR
  have hmodel {t : ℝ} (ht : 0 < t) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
        ENNReal.ofReal (hypRadVol q d t) := by
    calc
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
            ∂Measure.volumeIoiPow d :=
        setLIntegral_congr (hIio_Iic ⟨t, ht⟩).symm
      _ = ∫⁻ r : Set.Ioi (0 : ℝ),
          (Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))).indicator G r
          ∂Measure.volumeIoiPow d :=
        (lintegral_indicator measurableSet_Iio G).symm
      _ = ENNReal.ofReal (hypRadVol q d t) := by
        simpa only [G] using hypRad_lintegral q hq d ht
  have hpolar {t : ℝ} (ht : 0 < t) :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
    let K : Set E :=
      SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x t
    have hpre :
        L ⁻¹' K = T ∩ Metric.ball (0 : E) t := by
      dsimp only [K]
      change
        (L ⁻¹' SegInt (I := I) g hEnorm x) ∩
            (L ⁻¹' gBall (I := I) g x t) =
          T ∩ Metric.ball (0 : E) t
      rw [preimage_gBall (I := I) (E := E) g x t]
    have hset : MeasurableSet (T ∩ Metric.ball (0 : E) t) :=
      hT_meas.inter measurableSet_ball
    have hfun : Measurable (fun w : E => ENNReal.ofReal (Dn w)) :=
      ENNReal.measurable_ofReal.comp hDn_cont.measurable
    have hind :
        Measurable ((T ∩ Metric.ball (0 : E) t).indicator
          (fun w : E => ENNReal.ofReal (Dn w))) :=
      hfun.indicator hset
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
          ∫⁻ v in K,
            ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
            ∂(modelHaar (E := E)) := by
        simpa only [K] using segBall_area_eq (I := I) g hEnorm x ht
      _ = ∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w)
          ∂(volume : Measure E) := by
        simpa only [Dn, L, B] using
          expJac_normal_int (I := I) (E := E) g hEnorm x K
      _ = ∫⁻ w in T ∩ Metric.ball (0 : E) t,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
        rw [hpre]
      _ = ∫⁻ w : E,
          (T ∩ Metric.ball (0 : E) t).indicator
            (fun z => ENNReal.ofReal (Dn z)) w
          ∂(volume : Measure E) :=
        (lintegral_indicator hset _).symm
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ),
            (T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        simpa only [d] using
          lintegral_polar (volume : Measure E)
            ((T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z))) hind.aemeasurable
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        apply lintegral_congr
        intro u
        have hunorm : ‖u.1‖ = 1 := by
          simpa only [mem_sphere_zero_iff_norm] using u.2
        have hball (r : Set.Ioi (0 : ℝ)) :
            r.1 • u.1 ∈ Metric.ball (0 : E) t ↔
              r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)) := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_of_nonneg r.2.le, hunorm, mul_one]
          rfl
        calc
          (∫⁻ r : Set.Ioi (0 : ℝ),
              (T ∩ Metric.ball (0 : E) t).indicator
                (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d) =
              ∫⁻ r : Set.Ioi (0 : ℝ) in
                Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
                ∂Measure.volumeIoiPow d := by
            rw [← lintegral_indicator measurableSet_Iio]
            apply lintegral_congr
            intro r
            have hseg : r ∈ S u ↔ r.1 • u.1 ∈ T := Iff.rfl
            dsimp only [F]
            by_cases hrS : r ∈ S u
            · by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · have hmem :
                    r.1 • u.1 ∈ T ∩ Metric.ball (0 : E) t :=
                  ⟨hseg.mp hrS, (hball r).mpr hrt⟩
                rw [Set.indicator_of_mem hmem,
                  Set.indicator_of_mem hrt,
                  Set.indicator_of_mem hrS]
              · rw [Set.indicator_of_notMem
                    (fun h => hrt ((hball r).mp h.2)),
                  Set.indicator_of_notMem hrt]
            · rw [Set.indicator_of_notMem
                  (fun h => hrS (hseg.mpr h.1))]
              by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · rw [Set.indicator_of_mem hrt,
                  Set.indicator_of_notMem hrS]
              · rw [Set.indicator_of_notMem hrt]
          _ = ∫⁻ r : Set.Ioi (0 : ℝ) in
              Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d :=
            setLIntegral_congr (hIio_Iic ⟨t, ht⟩)
  have hcross (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b)
      (hbR : b ≤ (⟨R, hR⟩ : Set.Ioi (0 : ℝ))) :
      F u b * G a ≤ F u a * G b := by
    by_cases hbS : b ∈ S u
    · have haS : a ∈ S u := hS_down u hab hbS
      have hbS' := hbS
      change L (b.1 • u.1) ∈ SegInt (I := I) g hEnorm x at hbS'
      obtain ⟨c, hc, hcb⟩ := hbS'
      let uT : TangentSpace I x := L u.1
      have huT_pos : 0 < g.inner x uT uT := by
        simpa only [uT, hu_inner u] using one_pos
      have huT0 : uT ≠ 0 := by
        intro hu0
        rw [hu0] at huT_pos
        simp only [map_zero, lt_self_iff_false] at huT_pos
      have hc0 : 0 < c := one_pos.trans hc
      have hcb_pos : 0 < c * b.1 := mul_pos hc0 b.2
      have hcbD :
          (c * b.1) • uT ∈ SegDom (I := I) g hEnorm x := by
        simpa only [uT, map_smul, smul_smul] using hcb
      have hcb0 : (c * b.1) • uT ≠ 0 :=
        smul_ne_zero hcb_pos.ne' huT0
      have hno :
          ∀ t ∈ Set.Ioo (0 : ℝ) (c * b.1),
            ¬ IsConjVec (I := I) g hEnorm x
              ((t • uT : TangentSpace I x) : E) := by
        intro t ht
        have hratio :
            t / (c * b.1) ∈ Set.Ioo (0 : ℝ) 1 := by
          exact ⟨div_pos ht.1 hcb_pos,
            (div_lt_one hcb_pos).2 ht.2⟩
        have hraw :=
          segDom_no_conj (I := I) g hEnorm hcbD hcb0
            (t / (c * b.1)) hratio
        simpa only [smul_smul,
          div_mul_cancel₀ t hcb_pos.ne'] using hraw
      have hb_lt : b.1 < c * b.1 :=
        lt_mul_of_one_lt_left b.2 hc
      have haWin : a.1 ∈ Set.Ioo (0 : ℝ) (c * b.1) :=
        ⟨a.2, (show a.1 ≤ b.1 from hab).trans_lt hb_lt⟩
      have hbWin : b.1 ∈ Set.Ioo (0 : ℝ) (c * b.1) :=
        ⟨b.2, hb_lt⟩
      by_cases hd : 0 < d
      · obtain ⟨v, hON, hperp'⟩ :=
          exists_perp_pos (I := I) g x uT huT_pos
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          rw [g.symm x uT (v i)]
          exact hperp' i
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have huT_one : g.inner x uT uT = 1 := by
          simpa only [uT] using hu_inner u
        have hanti :
            AntitoneOn
              (fun t => Dt t / hypDensity q d t)
              (Set.Ioo (0 : ℝ) (c * b.1)) := by
          simpa only [Dt, d, huT_one, Real.sqrt_one, mul_one] using
            intrRatioOfFrame (I := I) g hEnorm x uT q
              (c * b.1) hq hd huT_pos v hON hperp hno hRic
        have hratio :=
          hanti haWin hbWin (show a.1 ≤ b.1 from hab)
        have hHa : 0 < hypDensity q d a.1 :=
          hypDensity_pos hq a.2
        have hHb : 0 < hypDensity q d b.1 :=
          hypDensity_pos hq b.2
        have htrans :
            Dt b.1 * hypDensity q d a.1 ≤
              Dt a.1 * hypDensity q d b.1 :=
          (div_le_div_iff₀ hHb hHa).1 hratio
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa :
            a.1 ^ d * Dn (a.1 • u.1) = Dt a.1 := by
          rw [hDnA]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
        have hDb :
            b.1 ^ d * Dn (b.1 • u.1) = Dt b.1 := by
          rw [hDnB]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
        have hGa :
            a.1 ^ d * hypDensity (q * a.1) d 1 =
              hypDensity q d a.1 := by
          simpa only [mul_one] using
            hypDens_scale q a.1 d 1 a.2.ne'
        have hGb :
            b.1 ^ d * hypDensity (q * b.1) d 1 =
              hypDensity q d b.1 := by
          simpa only [mul_one] using
            hypDens_scale q b.1 d 1 b.2.ne'
        have hpowa : 0 < a.1 ^ d := pow_pos a.2 d
        have hpowb : 0 < b.1 ^ d := pow_pos b.2 d
        have hreal :
            Dn (b.1 • u.1) * hypDensity (q * a.1) d 1 ≤
              Dn (a.1 • u.1) * hypDensity (q * b.1) d 1 := by
          apply (mul_le_mul_iff_right₀ (mul_pos hpowa hpowb)).mp
          calc
            (a.1 ^ d * b.1 ^ d) *
                (Dn (b.1 • u.1) * hypDensity (q * a.1) d 1) =
                (b.1 ^ d * Dn (b.1 • u.1)) *
                  (a.1 ^ d * hypDensity (q * a.1) d 1) := by ring
            _ = Dt b.1 * hypDensity q d a.1 := by
              rw [hDb, hGa]
            _ ≤ Dt a.1 * hypDensity q d b.1 := htrans
            _ = (a.1 ^ d * Dn (a.1 • u.1)) *
                (b.1 ^ d * hypDensity (q * b.1) d 1) := by
              rw [hDa, hGb]
            _ = (a.1 ^ d * b.1 ^ d) *
                (Dn (a.1 • u.1) * hypDensity (q * b.1) d 1) := by ring
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS]
        rw [← ENNReal.ofReal_mul (hDn_nonneg (b.1 • u.1)),
          ← ENNReal.ofReal_mul (hDn_nonneg (a.1 • u.1))]
        exact ENNReal.ofReal_le_ofReal hreal
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        let v : Fin d → TangentSpace I x := fun i =>
          isEmptyElim (hd0 ▸ i)
        have hON :
            ∀ i j, g.inner x (v i) (v j) =
              if i = j then 1 else 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have hDt (t : ℝ) : Dt t = 1 := by
          have hgram :
              curveGram (I := I) g
                  (intrinsicGeodesic (I := I) g hEnorm x uT)
                  (fun i =>
                    intrinsicJacobi (I := I) g hEnorm x uT (v i)) t =
                1 := by
            ext i
            exact isEmptyElim (hd0 ▸ i)
          simp only [Dt, curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa : Dn (a.1 • u.1) = 1 := by
          rw [hDnA]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hDb : Dn (b.1 • u.1) = 1 := by
          rw [hDnB]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hGa : hypDensity (q * a.1) d 1 = 1 := by
          simp only [hd0, hypDensity, pow_zero]
        have hGb : hypDensity (q * b.1) d 1 = 1 := by
          simp only [hd0, hypDensity, pow_zero]
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS, hDa, hDb, hGa, hGb,
          ENNReal.ofReal_one, mul_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
  have hdir (u : Metric.sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (hypRadVol q d s) ≤
        (∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (hypRadVol q d R) := by
    have h :=
      lintegral_Iic_cross
        (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
        (hF_meas u).aemeasurable.restrict
        hG_meas.aemeasurable.restrict
        (fun {_a _b} hab hbR => hcross u hab hbR)
        (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
    rw [hmodel hs, hmodel hR] at h
    exact h
  rw [show Module.finrank ℝ E - 1 = d by rfl]
  rw [hpolar hR, hpolar hs]
  rw [mul_comm
    (ENNReal.ofReal (hypRadVol q d R))
    (∫⁻ u : Metric.sphere (0 : E) 1,
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d
      ∂(volume : Measure E).toSphere)]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (hypRadVol q d s))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (hypRadVol q d R))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
