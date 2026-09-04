import DifferentialGeometry.Analysis.Integration.Measure.BasisHaar
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.ManifoldImageEq
import DifferentialGeometry.Analysis.Integration.Measure.PolarEvaluation
import DifferentialGeometry.Geometry.Comparison.Volume.BishopRawDensity
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentArea
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDensity
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Raw exponential vectors whose radial length equals the ambient distance to
their endpoint. -/
def rawSeg (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v))}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
/-- A raw minimizing vector lies in the time-one raw exponential domain. -/
theorem rawSeg_mem_dom
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ rawSeg (I := I) g p) :
    (show TangentSpace I p from v) ∈ expDomain (I := I) g p := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_contra hdom
  have hexp : expMap (I := I) g p (show TangentSpace I p from v) = p :=
    expMap_of_not_mem_expDomain (I := I) hdom
  by_cases hv0 : v = 0
  · subst v
    exact hdom (zero_mem_expDomain (I := I) g p)
  · have hpos : 0 < Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v)) :=
      Real.sqrt_pos.mpr (g.pos p v hv0)
    change ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) at hv
    rw [hexp, riemannianEDist_self] at hv
    exact (ENNReal.ofReal_pos.mpr hpos).ne' hv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
/-- Raw minimizing vectors with a common raw exponential endpoint have the
same radial metric length. -/
theorem rawSeg_same_len
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (p : M) {v w : E}
    (hv : v ∈ rawSeg (I := I) g p) (hw : w ∈ rawSeg (I := I) g p)
    (hvw : expMap (I := I) g p (show TangentSpace I p from v) =
      expMap (I := I) g p (show TangentSpace I p from w)) :
    Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v)) =
      Real.sqrt (g.inner p (show TangentSpace I p from w)
        (show TangentSpace I p from w)) := by
  change ENNReal.ofReal (Real.sqrt
    (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) at hv
  change ENNReal.ofReal (Real.sqrt
    (g.inner p (show TangentSpace I p from w)
      (show TangentSpace I p from w))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from w)) at hw
  apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)).mp
  calc
    ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v)) := hv
    _ = riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from w)) := by rw [hvw]
    _ = ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from w)
          (show TangentSpace I p from w))) := hw.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Raw minimizing vectors which remain raw minimizing after a positive radial
extension. -/
def rawSegInt (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ∃ c : ℝ, 1 < c ∧ c • v ∈ rawSeg (I := I) g p}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
/-- A raw interior minimizing vector has one radial geodesic through a strictly
longer raw minimizing endpoint. -/
theorem rawSegInt_geo
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ rawSegInt (I := I) g p) :
    ∃ (c : ℝ) (γ : ℝ → M) (J : Set ℝ), 1 < c ∧
      c • v ∈ rawSeg (I := I) g p ∧ IsOpen J ∧ IsPreconnected J ∧
      Icc (0 : ℝ) c ⊆ J ∧
      Geodesic.IsGeodesicOnWithInitial (I := I) g γ J p
        (show TangentSpace I p from v) ∧
      (∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
        (fun s => expMap (I := I) g p
          (show TangentSpace I p from s • v))) ∧
      γ 1 = expMap (I := I) g p
        (show TangentSpace I p from v) ∧
      γ c = expMap (I := I) g p
        (show TangentSpace I p from c • v) := by
  rcases hv with ⟨c, hc, hcraw⟩
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hcraw
  have hcinv : c⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hcpos.le, inv_le_one_of_one_le₀ hc.le⟩
  have hvdom : (show TangentSpace I p from v) ∈ expDomain (I := I) g p := by
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from c • v) hcdom hcinv
    change (show TangentSpace I p from c⁻¹ • (c • v)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] using hscale
  obtain ⟨γ, J, hJopen, hJconn, hIcc, hγ, hγc⟩ :=
    Geodesic.radialGeo_of_end (I := I) g p
      (show TangentSpace I p from v) hcpos hcdom
  have h0J : (0 : ℝ) ∈ J := hIcc ⟨le_rfl, hcpos.le⟩
  have h1J : (1 : ℝ) ∈ J := hIcc ⟨zero_le_one, hc.le⟩
  have hγeq := Geodesic.maximalGeo_eqOn (I := I) g hJopen hJconn h0J hγ
  have hγgerm : ∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
      (fun s => expMap (I := I) g p
        (show TangentSpace I p from s • v)) := by
    intro t ht
    have ht_div : t / c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hcpos.le, (div_le_one hcpos).mpr ht.2⟩
    have htdom : (show TangentSpace I p from t • v) ∈ expDomain (I := I) g p := by
      have hscale := Geodesic.smul_mem_expDomain (I := I) g p
        (show TangentSpace I p from c • v) hcdom ht_div
      change (show TangentSpace I p from (t / c) • (c • v)) ∈
        expDomain (I := I) g p at hscale
      simpa only [smul_smul, div_mul_cancel₀ t hcpos.ne', one_smul] using hscale
    let U : Set ℝ := {s | (show TangentSpace I p from s • v) ∈
      expDomain (I := I) g p}
    have hUopen : IsOpen U :=
      (isOpen_expDomain (I := I) g p).preimage
        (continuous_id.smul continuous_const)
    have htU : t ∈ U := htdom
    filter_upwards [hUopen.mem_nhds htU, hJopen.mem_nhds (hIcc ht)] with s hsU hsJ
    by_cases hs0 : s = 0
    · subst s
      rw [hγ.start_eq, zero_smul]
      exact (expMap_zero (I := I) g p).symm
    · have hsmax := Geodesic.expMap_smul_max_ne (I := I) g p
        (show TangentSpace I p from v) hs0 hsU
      exact (hγeq hsJ).symm.trans hsmax.2.symm
  have hExp := Geodesic.expMap_smul_eq_max (I := I) g p
    (show TangentSpace I p from v) one_pos (by simpa only [one_smul] using hvdom)
  have hγone : γ 1 = expMap (I := I) g p (show TangentSpace I p from v) :=
    (hγeq h1J).symm.trans (by simpa only [one_smul] using hExp.2.symm)
  exact ⟨c, γ, J, hc, hcraw, hJopen, hJconn, hIcc, hγ, hγgerm, hγone, hγc⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
/-- A raw interior minimizing vector has a globally smooth radial extension
which remains geodesic on its compact minimizing segment. -/
theorem rawSegInt_ext
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ rawSegInt (I := I) g p) :
    ∃ (c : ℝ) (γ : ℝ → M), 1 < c ∧ c • v ∈ rawSeg (I := I) g p ∧
      ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
      Geodesic.IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) c) ∧
      ∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
        (fun s => expMap (I := I) g p
          (show TangentSpace I p from s • v)) := by
  obtain ⟨c, γ, J, hc, hcraw, hJopen, _hJconn, hIcc, hγ, hγraw, _hγone,
    _hγc⟩ := rawSegInt_geo (I := I) g p hv
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hcraw
  have hdom : ∀ t ∈ Icc (0 : ℝ) c,
      (show TangentSpace I p from t • v) ∈ expDomain (I := I) g p := by
    intro t ht
    have ht_div : t / c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hcpos.le, (div_le_one hcpos).mpr ht.2⟩
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from c • v) hcdom ht_div
    change (show TangentSpace I p from (t / c) • (c • v)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, div_mul_cancel₀ t hcpos.ne', one_smul] using hscale
  obtain ⟨γg, hγgsmooth, hγgerm⟩ :=
    exists_raw_ray_ext (I := I) g p v hcpos hdom
  have hγeq : ∀ t ∈ Icc (0 : ℝ) c, γg =ᶠ[𝓝 t] γ := by
    intro t ht
    exact (hγgerm t ht).trans (hγraw t ht).symm
  have hγgeo : Geodesic.IsGeodesicOn (I := I) g γ J := by
    intro t ht
    exact (hγ.geoAt (hJopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγggeo : Geodesic.IsGeodesicOn (I := I) g γg (Icc (0 : ℝ) c) := by
    intro t ht
    have heq := hγeq t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      heq.eq_of_nhds heq (hγgeo t (hIcc ht))
  exact ⟨c, γg, hc, hcraw, hγgsmooth, hγggeo, hγgerm⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
/-- A raw vector which extends to a longer raw minimizing vector is itself raw
minimizing. -/
theorem rawSegInt_sub
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {v : E}
    (hv : v ∈ rawSegInt (I := I) g p) :
    v ∈ rawSeg (I := I) g p := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨c, hc, hcraw⟩ := hv
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hcraw
  have hdom : ∀ t ∈ Icc (0 : ℝ) c,
      (show TangentSpace I p from t • v) ∈ expDomain (I := I) g p := by
    intro t ht
    have ht_div : t / c ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hcpos.le, (div_le_one hcpos).mpr ht.2⟩
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from c • v) hcdom ht_div
    change (show TangentSpace I p from (t / c) • (c • v)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, div_mul_cancel₀ t hcpos.ne', one_smul] using hscale
  let γ : ℝ → M := radialCurve (I := I) g p v
  let L : ℝ := Real.sqrt (g.inner p (show TangentSpace I p from v)
    (show TangentSpace I p from v))
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (0 : ℝ) c) := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => s • v) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := expMap_contMDiffAt (I := I) g p (hdom t ht)
    simpa only [γ, radialCurve] using
      ((hexp.comp t hline).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffWithinAt
  have hspeed : ∀ t ∈ Icc (0 : ℝ) c,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ ≤ ENNReal.ofReal L := by
    intro t ht
    rw [hEnorm]
    change ENNReal.ofReal (Real.sqrt
      (g.inner (radialCurve (I := I) g p v t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p v) t))) ≤
      ENNReal.ofReal L
    rw [rawSpeed_sq (I := I) g p v t ht.1
      (fun s hs => hdom s ⟨hs.1, hs.2.trans ht.2⟩)]
  have h01 := HopfRinow.curve_edist_le_speed_mul_time (I := I)
    (γ := γ) (s := (0 : ℝ)) (t := (1 : ℝ)) (c := L)
    hLnn zero_le_one
    (hγsmooth.mono (Icc_subset_Icc le_rfl hc.le))
    (fun t ht => hspeed t ⟨ht.1, ht.2.trans hc.le⟩)
  have hupper : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) ≤ ENNReal.ofReal L := by
    dsimp only [γ, radialCurve] at h01
    rw [zero_smul, one_smul] at h01
    change riemannianEDist I
      (expMap (I := I) g p (show TangentSpace I p from (0 : E)))
      (expMap (I := I) g p (show TangentSpace I p from v)) ≤
        ENNReal.ofReal (L * (1 - 0)) at h01
    rw [show expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p from
      expMap_zero (I := I) g p] at h01
    simpa only [sub_zero, mul_one] using h01
  have h1c := HopfRinow.curve_edist_le_speed_mul_time (I := I)
    (γ := γ) (s := (1 : ℝ)) (t := c) (c := L)
    hLnn hc.le
    (hγsmooth.mono (Icc_subset_Icc zero_le_one le_rfl))
    (fun t ht => hspeed t ⟨zero_le_one.trans ht.1, ht.2⟩)
  have htail : riemannianEDist I
      (expMap (I := I) g p (show TangentSpace I p from v))
      (expMap (I := I) g p (show TangentSpace I p from c • v)) ≤
      ENNReal.ofReal (L * (c - 1)) := by
    simpa only [γ, radialCurve, one_smul] using h1c
  simp only [rawSeg, Set.mem_setOf_eq] at hcraw
  have hcLen : Real.sqrt
      (g.inner p (show TangentSpace I p from c • v)
        (show TangentSpace I p from c • v)) = c * L := by
    simpa only [L] using
      sqrt_gInner_smul_self (I := I) g p hcpos.le
        (show TangentSpace I p from v)
  rw [hcLen] at hcraw
  have htailnn : 0 ≤ L * (c - 1) :=
    mul_nonneg hLnn (sub_nonneg.mpr hc.le)
  have hsplit : ENNReal.ofReal (c * L) =
      ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) := by
    rw [← ENNReal.ofReal_add hLnn htailnn]
    congr 1
    ring
  have htri : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from c • v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) +
      riemannianEDist I
        (expMap (I := I) g p (show TangentSpace I p from v))
        (expMap (I := I) g p (show TangentSpace I p from c • v)) :=
    riemannianEDist_triangle
  have hlow : ENNReal.ofReal L ≤ riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) := by
    have hchain : ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) ≤
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v)) +
        ENNReal.ofReal (L * (c - 1)) := by
      calc
        ENNReal.ofReal L + ENNReal.ofReal (L * (c - 1)) =
            ENNReal.ofReal (c * L) := hsplit.symm
        _ = riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from c • v)) := hcraw
        _ ≤ riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from v)) +
            riemannianEDist I
              (expMap (I := I) g p (show TangentSpace I p from v))
              (expMap (I := I) g p (show TangentSpace I p from c • v)) := htri
        _ ≤ riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from v)) +
            ENNReal.ofReal (L * (c - 1)) := add_le_add le_rfl htail
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  change ENNReal.ofReal L = riemannianEDist I p
    (expMap (I := I) g p (show TangentSpace I p from v))
  exact le_antisymm hlow hupper

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem mfderiv_shift
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (T a : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s + T)) a (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E) := by
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + T)
      a (ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hasFDerivAt_id a).add_const T
  have hγat : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (a + T)
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) :=
    (hγ.contMDiffAt.mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)).comp (ContinuousLinearMap.id ℝ ℝ) :=
    (hγat.comp a hshift).mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E)
  rw [hcomp]
  change (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) (1 : ℝ)
  simp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem geo_init_vel
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p} (hJ : IsOpen J) (h0J : (0 : ℝ) ∈ J)
    (hγ : Geodesic.IsGeodesicOnWithInitial (I := I) g γ J p v) :
    (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  have hfat : IsMIntegralCurveAt f (Geodesic.geodesicVectorField (I := I) g) 0 :=
    hf.isMIntegralCurveAt (hJ.mem_nhds h0J)
  have hprojcont : ContinuousAt (fun t => (f t).proj) 0 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hfat.continuousAt
  have hsrc0 : (f 0).proj ∈ (chartAt H p).source := by
    rw [hf0]
    exact mem_chart_source H p
  have hsrc : (fun t => (f t).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) :=
    hprojcont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc0)
  have hfchart : IsMIntegralCurveAt f
      (Geodesic.geodesicVectorFieldChart (I := I) g p) 0 := by
    rw [isMIntegralCurveAt_iff]
    refine ⟨J ∩ (fun t => (f t).proj) ⁻¹' (chartAt H p).source,
      Filter.inter_mem (hJ.mem_nhds h0J) hsrc, ?_⟩
    apply (Geodesic.chart_vf_on_iff (I := I) g p (fun _ ht => ht.2)).mpr
    exact hf.mono inter_subset_left
  have hvel := Geodesic.IsMIntegralCurveAt.mfderiv_proj_one (I := I) hfchart hsrc0
  have hfun : (fun t => (f t).proj) = γ := funext hproj
  rw [hfun, hf0] at hvel
  exact hvel

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
/-- The raw exponential is injective on vectors whose raw minimizing segment
extends strictly beyond time one. -/
theorem rawExp_inj_seg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    Set.InjOn (fun v : E => expMap (I := I) g p
      (show TangentSpace I p from v)) (rawSegInt (I := I) g p) := by
  intro v hv w hw heq
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hvraw : v ∈ rawSeg (I := I) g p := rawSegInt_sub (I := I) g hEnorm p hv
  have hwraw : w ∈ rawSeg (I := I) g p := rawSegInt_sub (I := I) g hEnorm p hw
  have hlen := rawSeg_same_len (I := I) g p hvraw hwraw heq
  by_cases hv0 : v = 0
  · subst v
    have hw0 : w = 0 := by
      have hzero : Real.sqrt
          (g.inner p (show TangentSpace I p from w)
            (show TangentSpace I p from w)) = 0 := by
        rw [← hlen]
        change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) = 0
        simp
      by_contra hw0
      exact (Real.sqrt_pos.mpr (g.pos p w hw0)).ne' hzero
    subst w
    rfl
  let L : ℝ := Real.sqrt (g.inner p (show TangentSpace I p from v)
    (show TangentSpace I p from v))
  have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos p v hv0)
  have hLne : L ≠ 0 := hLpos.ne'
  have hvinner : g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v) = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g p v)
    simpa only [L] using hsq.symm
  have hwinner : g.inner p (show TangentSpace I p from w)
      (show TangentSpace I p from w) = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g p w)
    rw [← hlen] at hsq
    exact hsq.symm
  let u : E := L⁻¹ • v
  let z : E := L⁻¹ • w
  have huunit : g.inner p (show TangentSpace I p from u)
      (show TangentSpace I p from u) = 1 := by
    dsimp only [u]
    change g.inner p (L⁻¹ • (show TangentSpace I p from v))
      (L⁻¹ • (show TangentSpace I p from v)) = 1
    rw [gInner_smul_self (I := I) g p L⁻¹ (show TangentSpace I p from v), hvinner]
    field_simp [hLne]
  have hzunit : g.inner p (show TangentSpace I p from z)
      (show TangentSpace I p from z) = 1 := by
    dsimp only [z]
    change g.inner p (L⁻¹ • (show TangentSpace I p from w))
      (L⁻¹ • (show TangentSpace I p from w)) = 1
    rw [gInner_smul_self (I := I) g p L⁻¹ (show TangentSpace I p from w), hwinner]
    field_simp [hLne]
  have hLu : L • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hLne, one_smul]
  have hLz : L • z = w := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hLne, one_smul]
  obtain ⟨c, hc, hcv⟩ := hv
  obtain ⟨d, hd, hdw⟩ := hw
  have hcpos : 0 < c := one_pos.trans hc
  have hdpos : 0 < d := one_pos.trans hd
  let C : ℝ := c * L
  let D : ℝ := d * L
  let ell : ℝ := (c - 1) * L
  have hCpos : 0 < C := mul_pos hcpos hLpos
  have hDpos : 0 < D := mul_pos hdpos hLpos
  have hellpos : 0 < ell := mul_pos (sub_pos.mpr hc) hLpos
  have hCeq : L + ell = C := by
    dsimp only [C, ell]
    ring
  have hcvdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hcv
  have hdwdom : (show TangentSpace I p from d • w) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hdw
  have hCu : C • u = c • v := by
    dsimp only [C, u]
    rw [smul_smul, show c * L * L⁻¹ = c by field_simp [hLne]]
  have hDz : D • z = d • w := by
    dsimp only [D, z]
    rw [smul_smul, show d * L * L⁻¹ = d by field_simp [hLne]]
  have hdomu : ∀ t ∈ Icc (0 : ℝ) C,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p := by
    intro t ht
    have hratio : t / C ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hCpos.le, (div_le_one hCpos).mpr ht.2⟩
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from c • v) hcvdom hratio
    have hscale_eq : (t / C) • (c • v) = t • u := by
      dsimp only [C, u]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hcpos.ne', hLne]
    change (show TangentSpace I p from (t / C) • (c • v)) ∈
      expDomain (I := I) g p at hscale
    change (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p
    rwa [hscale_eq] at hscale
  have hdomz : ∀ t ∈ Icc (0 : ℝ) D,
      (show TangentSpace I p from t • z) ∈ expDomain (I := I) g p := by
    intro t ht
    have hratio : t / D ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hDpos.le, (div_le_one hDpos).mpr ht.2⟩
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from d • w) hdwdom hratio
    have hscale_eq : (t / D) • (d • w) = t • z := by
      dsimp only [D, z]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hdpos.ne', hLne]
    change (show TangentSpace I p from (t / D) • (d • w)) ∈
      expDomain (I := I) g p at hscale
    change (show TangentSpace I p from t • z) ∈ expDomain (I := I) g p
    rwa [hscale_eq] at hscale
  obtain ⟨γv, Jv, hJvopen, hJvconn, hIv, hγv, hγvraw⟩ :=
    Geodesic.radialGeo_of_dom (I := I) g p (show TangentSpace I p from u)
      hCpos (fun {t} ht0 htC => hdomu t ⟨ht0.le, htC⟩)
  obtain ⟨γw, Jw, hJwopen, hJwconn, hIw, hγw, hγwraw⟩ :=
    Geodesic.radialGeo_of_dom (I := I) g p (show TangentSpace I p from z)
      hDpos (fun {t} ht0 htD => hdomz t ⟨ht0.le, htD⟩)
  obtain ⟨γvg, hγvgsmooth, hγvgraw⟩ :=
    exists_raw_ray_ext (I := I) g p u hCpos hdomu
  obtain ⟨γwg, hγwgsmooth, hγwgraw⟩ :=
    exists_raw_ray_ext (I := I) g p z hDpos hdomz
  have hγvggeo : Geodesic.IsGeodesicOn (I := I) g γvg (Icc (0 : ℝ) C) := by
    intro t ht
    have hraw := hγvgraw t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hraw.eq_of_nhds hraw
      (raw_radial_geo_at (I := I) g p (show TangentSpace I p from u) (hdomu t ht))
  have hγwggeo : Geodesic.IsGeodesicOn (I := I) g γwg (Icc (0 : ℝ) D) := by
    intro t ht
    have hraw := hγwgraw t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hraw.eq_of_nhds hraw
      (raw_radial_geo_at (I := I) g p (show TangentSpace I p from z) (hdomz t ht))
  have hγvgunit : ∀ t ∈ Icc (0 : ℝ) C,
      g.inner (γvg t) (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ)) = 1 := by
    intro t ht
    have hraw := hγvgraw t ht
    rw [hraw.eq_of_nhds, hraw.mfderiv_eq]
    change g.inner (radialCurve (I := I) g p u t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t) = 1
    rw [rawSpeed_sq (I := I) g p u t ht.1
      (fun s hs => hdomu s ⟨hs.1, hs.2.trans ht.2⟩)]
    exact huunit
  have hγwgunit : ∀ t ∈ Icc (0 : ℝ) D,
      g.inner (γwg t) (mfderiv 𝓘(ℝ, ℝ) I γwg t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γwg t (1 : ℝ)) = 1 := by
    intro t ht
    have hraw := hγwgraw t ht
    rw [hraw.eq_of_nhds, hraw.mfderiv_eq]
    change g.inner (radialCurve (I := I) g p z t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t) = 1
    rw [rawSpeed_sq (I := I) g p z t ht.1
      (fun s hs => hdomz s ⟨hs.1, hs.2.trans ht.2⟩)]
    exact hzunit
  have hLC : L < C := by
    dsimp only [C]
    nlinarith
  have hLD : L < D := by
    dsimp only [D]
    nlinarith
  have hLmemC : L ∈ Icc (0 : ℝ) C := ⟨hLpos.le, hLC.le⟩
  have hLmemD : L ∈ Icc (0 : ℝ) D := ⟨hLpos.le, hLD.le⟩
  have hγvrawL : γv =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLC⟩] with s hs
    exact hγvraw ⟨hs.1.le, hs.2.le⟩
  have hγwrawL : γw =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLD⟩] with s hs
    exact hγwraw ⟨hs.1.le, hs.2.le⟩
  have hγvgL : γvg =ᶠ[𝓝 L] γv :=
    (hγvgraw L hLmemC).trans hγvrawL.symm
  have hγwgL : γwg =ᶠ[𝓝 L] γw :=
    (hγwgraw L hLmemD).trans hγwrawL.symm
  let σ : ℝ → M := fun s => γvg (s + L)
  have hσsmooth : ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) σ := by
    dsimp only [σ]
    exact hγvgsmooth.comp (contMDiff_id.add contMDiff_const)
  have hσgeo : Geodesic.IsGeodesicOn (I := I) g σ (Icc (0 : ℝ) ell) := by
    have hsub : Icc (0 : ℝ) ell ⊆ {t : ℝ | 1 * t + L ∈ Icc (0 : ℝ) C} := by
      intro t ht
      constructor
      · simpa only [one_mul] using add_nonneg ht.1 hLpos.le
      · rw [one_mul]
        calc
          t + L = L + t := add_comm _ _
          _ = t + L := add_comm _ _
          _ ≤ ell + L := by linarith [ht.2]
          _ = L + ell := add_comm _ _
          _ = C := hCeq
    simpa only [σ, one_mul] using
      (Geodesic.isGeodesicOn_comp_affine (I := I) (c := 1) (d := L)
        hγvggeo).mono hsub
  have hσunit : ∀ t ∈ Icc (0 : ℝ) ell,
      g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ)) = 1 := by
    intro t ht
    have hderiv := mfderiv_shift (I := I) hγvgsmooth L t
    change g.inner (γvg (t + L))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γvg (s + L)) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γvg (s + L)) t (1 : ℝ)) = 1
    rw [hderiv]
    exact hγvgunit (t + L) ⟨add_nonneg ht.1 hLpos.le, by
      calc
        t + L = L + t := add_comm _ _
        _ = t + L := add_comm _ _
        _ ≤ ell + L := by linarith [ht.2]
        _ = L + ell := add_comm _ _
        _ = C := hCeq⟩
  have hγwg0 : γwg 0 = p := by
    rw [(hγwgraw 0 ⟨le_rfl, hDpos.le⟩).eq_of_nhds, zero_smul]
    exact expMap_zero (I := I) g p
  have hσell : σ ell = expMap (I := I) g p
      (show TangentSpace I p from c • v) := by
    change γvg (ell + L) = expMap (I := I) g p
      (show TangentSpace I p from c • v)
    rw [add_comm ell L, hCeq, (hγvgraw C ⟨hCpos.le, le_rfl⟩).eq_of_nhds, hCu]
  have hdistc : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from c • v)) = ENNReal.ofReal C := by
    simp only [rawSeg, Set.mem_setOf_eq] at hcv
    have hcLen : Real.sqrt
        (g.inner p (show TangentSpace I p from c • v)
          (show TangentSpace I p from c • v)) = C := by
      dsimp only [C, L]
      exact sqrt_gInner_smul_self (I := I) g p hcpos.le
        (show TangentSpace I p from v)
    rw [hcLen] at hcv
    exact hcv.symm
  have hjunc : γwg L = σ 0 := by
    change γwg L = γvg (0 + L)
    rw [zero_add, (hγwgraw L hLmemD).eq_of_nhds,
      (hγvgraw L hLmemC).eq_of_nhds, hLz, hLu]
    exact heq.symm
  have hmin : riemannianEDist I (γwg 0) (σ ell) = ENNReal.ofReal (L + ell) := by
    rw [hγwg0, hσell, hdistc]
    rw [hCeq]
  have hmatchg := broken_minimizer_velocity_match (I := I) g hEnorm hLpos hellpos
    (fun t ht => hγwggeo t ⟨ht.1, ht.2.trans hLD.le⟩) hσgeo hγwgsmooth hσsmooth
    (fun t ht => hγwgunit t ⟨ht.1, ht.2.trans hLD.le⟩) hσunit hjunc hmin
  have hmatch : (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) := by
    have hγwg : (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γwg L (1 : ℝ) : E) :=
      congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hγwgL.mfderiv_eq.symm
    have hσ0 : (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γvg L (1 : ℝ) : E) := by
      have hshift := mfderiv_shift (I := I) hγvgsmooth L 0
      rw [zero_add] at hshift
      simpa only [σ] using hshift
    have hγvg : (mfderiv 𝓘(ℝ, ℝ) I γvg L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) :=
      congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hγvgL.mfderiv_eq
    rw [hγwg, ← hγvg, ← hσ0]
    exact hmatchg
  obtain ⟨fv, hfvproj, hfv0, hfv⟩ := hγv
  obtain ⟨fw, hfwproj, hfw0, hfw⟩ := hγw
  have hγvinit : Geodesic.IsGeodesicOnWithInitial (I := I) g γv Jv p
      (show TangentSpace I p from u) := ⟨fv, hfvproj, hfv0, hfv⟩
  have hγwinit : Geodesic.IsGeodesicOnWithInitial (I := I) g γw Jw p
      (show TangentSpace I p from z) := ⟨fw, hfwproj, hfw0, hfw⟩
  have hγvgeo : Geodesic.IsGeodesicOn (I := I) g γv Jv := by
    intro t ht
    exact (hγvinit.geoAt (hJvopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγwgeo : Geodesic.IsGeodesicOn (I := I) g γw Jw := by
    intro t ht
    exact (hγwinit.geoAt (hJwopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγvcont : ContinuousOn γv Jv :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hfv.continuousOn).congr
      (fun t _ => (hfvproj t).symm)
  have hγwcont : ContinuousOn γw Jw :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hfw.continuousOn).congr
      (fun t _ => (hfwproj t).symm)
  have h0Jv : (0 : ℝ) ∈ Jv := hIv ⟨le_rfl, hCpos.le⟩
  have h0Jw : (0 : ℝ) ∈ Jw := hIw ⟨le_rfl, hDpos.le⟩
  have hfoot : γw L = γv L := by
    calc
      γw L = expMap (I := I) g p (show TangentSpace I p from L • z) := hγwraw hLmemD
      _ = expMap (I := I) g p (show TangentSpace I p from L • u) := by
        rw [hLz, hLu]
        exact heq.symm
      _ = γv L := (hγvraw hLmemC).symm
  have hγvlift := Geodesic.geoLift_isIntegralOn (I := I) g hJvopen hγvgeo hγvcont
  have hγwlift := Geodesic.geoLift_isIntegralOn (I := I) g hJwopen hγwgeo hγwcont
  let Jvshift : Set ℝ := {s : ℝ | s + L ∈ Jv}
  let Jwshift : Set ℝ := {s : ℝ | s + L ∈ Jw}
  let K : Set ℝ := Jwshift ∩ Jvshift
  have hJvshiftopen : IsOpen Jvshift :=
    hJvopen.preimage (continuous_id.add continuous_const)
  have hJwshiftopen : IsOpen Jwshift :=
    hJwopen.preimage (continuous_id.add continuous_const)
  have hJvshiftconn : IsPreconnected Jvshift :=
    (hJvconn.ordConnected.preimage_mono (f := fun s : ℝ => s + L)
      (fun _ _ hst => by linarith)).isPreconnected
  have hJwshiftconn : IsPreconnected Jwshift :=
    (hJwconn.ordConnected.preimage_mono (f := fun s : ℝ => s + L)
      (fun _ _ hst => by linarith)).isPreconnected
  have hKopen : IsOpen K := hJwshiftopen.inter hJvshiftopen
  have hKconn : IsPreconnected K :=
    (hJwshiftconn.ordConnected.inter hJvshiftconn.ordConnected).isPreconnected
  have h0K : (0 : ℝ) ∈ K := by
    constructor
    · change 0 + L ∈ Jw
      simpa using hIw hLmemD
    · change 0 + L ∈ Jv
      simpa using hIv hLmemC
  have hnegK : (-L : ℝ) ∈ K := by
    constructor
    · change -L + L ∈ Jw
      simpa using h0Jw
    · change -L + L ∈ Jv
      simpa using h0Jv
  have hlift0 :
      (Geodesic.velocityLift (I := I) γw ∘ fun s : ℝ => s + L) 0 =
        (Geodesic.velocityLift (I := I) γv ∘ fun s : ℝ => s + L) 0 := by
    simp only [Function.comp_apply, zero_add]
    apply TotalSpace.ext
    · exact hfoot
    · apply heq_of_eq
      exact hmatch
  have hlifteq := Geodesic.gvf_eqOn (I := I) g hKopen hKconn h0K
    ((hγwlift.comp_add L).mono inter_subset_left)
    ((hγvlift.comp_add L).mono inter_subset_right) hlift0
  have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) := by
    have hneg := hlifteq hnegK
    simp only [Function.comp_apply, neg_add_cancel] at hneg
    have hsnd := congrArg (fun q : TangentBundle I M => (q.snd : E)) hneg
    simpa only [Geodesic.velocityLift] using hsnd
  have hinitw := geo_init_vel (I := I) g hJwopen h0Jw hγwinit
  have hinitv := geo_init_vel (I := I) g hJvopen h0Jv hγvinit
  have hzu : (z : E) = (u : E) := by
    rw [hinitw, hinitv] at hvel0
    exact hvel0
  calc
    v = L • u := hLu.symm
    _ = L • z := congrArg (fun y : E => L • y) hzu.symm
    _ = w := hLz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The radially extendible raw minimizing locus is Borel on a compactly
buffered tangent ball. -/
theorem rawSegInt_ball_meas
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    MeasurableSet
      (rawSegInt (I := I) g p ∩ gBall (I := I) g p R) := by
  classical
  let S : ℝ := (R + R₀) / 2
  let K : Set E := rawSeg (I := I) g p ∩ closedGBall (I := I) g p S
  let Q : Set ℚ := {q | (1 : ℝ) < (q : ℝ) ∧ (q : ℝ) < S / R}
  let A : ℚ → Set E := fun q =>
    (fun v : E => (q : ℝ) • v) ⁻¹' K ∩ gBall (I := I) g p R
  have hRS : R < S := by
    dsimp only [S]
    linarith
  have hSR₀ : S < R₀ := by
    dsimp only [S]
    linarith
  have hSdiv : 1 < S / R := by
    rw [lt_div_iff₀ hR]
    simpa only [one_mul] using hRS
  have hK : IsCompact K := by
    simpa only [K] using isCompact_rawSeg (I := I) g hEnorm p hSR₀ hcpt
  have hA (q : ℚ) : MeasurableSet (A q) := by
    exact (hK.measurableSet.preimage
      (continuous_const_smul (q : ℝ)).measurable).inter
        (measurableSet_gBall (I := I) g p R)
  have hEq : rawSegInt (I := I) g p ∩ gBall (I := I) g p R =
      ⋃ q ∈ Q, A q := by
    ext v
    constructor
    · rintro ⟨hv, hvball⟩
      obtain ⟨c, hc, hcv⟩ := hv
      have hlim : 1 < min c (S / R) := lt_min hc hSdiv
      obtain ⟨q : ℚ, hq1, hqlim⟩ := exists_rat_btwn hlim
      have hqc : (q : ℝ) < c := hqlim.trans_le (min_le_left _ _)
      have hqS : (q : ℝ) < S / R := hqlim.trans_le (min_le_right _ _)
      have hqpos : 0 < (q : ℝ) := lt_trans zero_lt_one hq1
      have hqraw : (q : ℝ) • v ∈ rawSeg (I := I) g p := by
        apply rawSegInt_sub (I := I) g hEnorm p
        refine ⟨c / (q : ℝ), (one_lt_div hqpos).2 hqc, ?_⟩
        simpa only [smul_smul, div_mul_cancel₀ _ hqpos.ne'] using hcv
      have hqR : (q : ℝ) * R < S := (lt_div_iff₀ hR).mp hqS
      have hqball : (q : ℝ) • v ∈ closedGBall (I := I) g p S := by
        change Real.sqrt
          (g.inner p ((q : ℝ) • (show TangentSpace I p from v))
            ((q : ℝ) • (show TangentSpace I p from v))) ≤ S
        change Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v)) < R at hvball
        rw [sqrt_gInner_smul_self (I := I) g p hqpos.le]
        exact le_of_lt
          ((mul_le_mul_of_nonneg_left (le_of_lt hvball) hqpos.le).trans_lt hqR)
      refine mem_iUnion₂.mpr ⟨q, ⟨hq1, hqS⟩, ?_⟩
      exact ⟨⟨hqraw, hqball⟩, hvball⟩
    · rintro hv
      obtain ⟨q, hqQ, hqv⟩ := mem_iUnion₂.mp hv
      exact ⟨⟨(q : ℝ), hqQ.1, hqv.1.1⟩, hqv.2⟩
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable Q) fun q _ => hA q

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a compactly buffered tangent ball, the raw exponential transports the
raw interior density exactly onto its image. -/
theorem rawSegInt_image_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun v : E => expMap (I := I) g p
          (show TangentSpace I p from v)) ''
          (rawSegInt (I := I) g p ∩ gBall (I := I) g p R)) =
      ∫⁻ v in rawSegInt (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  let K : Set E := rawSegInt (I := I) g p ∩ gBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let U : Set E := expDomain (I := I) g p
  have hK : MeasurableSet K := by
    simpa only [K] using rawSegInt_ball_meas (I := I) g hEnorm p hR hRR₀ hcpt
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p R at hv
    exact rawSeg_mem_dom (I := I) g p
      (rawSegInt_sub (I := I) g hEnorm p hv.1)
  have hU : IsOpen U := by
    simpa only [U] using isOpen_expDomain (I := I) g p
  have hKU : K ⊆ U := by
    simpa only [U] using hKdom
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U := by
    simpa only [F, U] using
      (expMap_contMDiffOn (I := I) g p).of_le (by norm_num)
  have hinj : Set.InjOn F K := by
    simpa only [F, K] using
      (rawExp_inj_seg (I := I) g hEnorm p).mono Set.inter_subset_left
  have hcov := riemVol_image_eq (I := I) g (f := F) (U := U)
    hU hK hKU hF hinj
  have hjac : ∀ v ∈ K,
      mapJacDensity (I := I) g F v =
        curveDensity (I := I) g
          (fun t : ℝ => expMap (I := I) g p
            (show TangentSpace I p from t • v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
              expMap (I := I) g p
                (show TangentSpace I p from
                  t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
    intro v hv
    simpa only [F] using raw_exp_density (I := I) g p v (hKdom hv)
  have hint :
      (∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
          ∂(modelHaar (E := E)) := by
    refine setLIntegral_congr_fun hK (fun v hv => ?_)
    exact congrArg ENNReal.ofReal (hjac v hv)
  simpa only [F, K] using hcov.trans hint

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
/-- Along one raw ray, at most one positive raw minimizing vector fails to
extend as a raw minimizing vector. -/
theorem rawSegEnd_ray_sub
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    ({r : Ioi (0 : ℝ) |
      r.1 • u ∈ rawSeg (I := I) g p \ rawSegInt (I := I) g p} :
      Set (Ioi (0 : ℝ))).Subsingleton := by
  rintro ⟨a, ha0⟩ ⟨haD, haI⟩ ⟨b, hb0⟩ ⟨hbD, hbI⟩
  have ha_pos : 0 < a := ha0
  have hb_pos : 0 < b := hb0
  apply Subtype.ext
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    apply haI
    refine ⟨b / a, (one_lt_div ha_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
    exact hbD
  · exact hab
  · exfalso
    apply hbI
    refine ⟨a / b, (one_lt_div hb_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
    exact haD

private theorem compactRayEnd_null
    (K : Set E) (hK : IsCompact K) :
    (modelHaar (E := E))
        (K \ ⋃ n : ℕ, K ∩
          (fun z : ℝ × E => z.1 • z.2) ''
            (Icc (0 : ℝ) ((n : ℝ) / (n + 1)) ×ˢ K)) = 0 := by
  classical
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℝ E from NeZero.pos _)
  letI : Measure.IsAddHaarMeasure (modelHaar (E := E)) :=
    modelHaar_isAddHaarMeasure
  let C : ℕ → Set E := fun n => K ∩
    (fun z : ℝ × E => z.1 • z.2) ''
      (Icc (0 : ℝ) ((n : ℝ) / (n + 1)) ×ˢ K)
  let B : Set E := K \ ⋃ n : ℕ, C n
  let f : E → ℝ≥0∞ := B.indicator fun _ => 1
  have hCcompact : ∀ n : ℕ, IsCompact (C n) := by
    intro n
    apply hK.inter
    exact (isCompact_Icc.prod hK).image
      (continuous_fst.smul continuous_snd)
  have hCmeas : ∀ n : ℕ, MeasurableSet (C n) :=
    fun n => (hCcompact n).measurableSet
  have hB : MeasurableSet B :=
    hK.measurableSet.diff (MeasurableSet.iUnion hCmeas)
  have hf : Measurable f :=
    measurable_const.indicator hB
  change (modelHaar (E := E)) B = 0
  calc
    (modelHaar (E := E)) B = ∫⁻ z : E, f z ∂modelHaar (E := E) :=
      (lintegral_indicator_one hB).symm
    _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ), f (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(modelHaar (E := E)).toSphere :=
      lintegral_polar (modelHaar (E := E)) f hf.aemeasurable
    _ = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with u
      let A : Set (Ioi (0 : ℝ)) := {r | r.1 • u.1 ∈ B}
      have hA : MeasurableSet A := by
        exact hB.preimage (continuous_subtype_val.smul continuous_const).measurable
      have hAsub : A.Subsingleton := by
        rintro ⟨a, ha0⟩ ha ⟨b, hb0⟩ hb
        change a • u.1 ∈ B at ha
        change b • u.1 ∈ B at hb
        rcases ha with ⟨haK, haB⟩
        rcases hb with ⟨hbK, hbB⟩
        apply Subtype.ext
        rcases lt_trichotomy a b with hab | hab | hab
        · exfalso
          have ha_pos : 0 < a := ha0
          have hb_pos : 0 < b := hb0
          have hdiff : 0 < b - a := sub_pos.mpr hab
          obtain ⟨n, hn⟩ := exists_nat_gt (a / (b - a))
          have hn_pos : 0 < (n : ℝ) + 1 := by positivity
          have hfrac : a / b ≤ (n : ℝ) / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ hb_pos hn_pos]
            have hn' : a < (n : ℝ) * (b - a) :=
              (div_lt_iff₀ hdiff).mp hn
            nlinarith
          apply haB
          refine mem_iUnion.2 ⟨n, ?_⟩
          refine ⟨haK, ?_⟩
          refine ⟨(a / b, b • u.1), ⟨⟨?_, hbK⟩, ?_⟩⟩
          · exact ⟨div_nonneg ha_pos.le hb_pos.le, hfrac⟩
          · change (a / b) • (b • u.1) = a • u.1
            rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
        · exact hab
        · exfalso
          have ha_pos : 0 < a := ha0
          have hb_pos : 0 < b := hb0
          have hdiff : 0 < a - b := sub_pos.mpr hab
          obtain ⟨n, hn⟩ := exists_nat_gt (b / (a - b))
          have hn_pos : 0 < (n : ℝ) + 1 := by positivity
          have hfrac : b / a ≤ (n : ℝ) / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ ha_pos hn_pos]
            have hn' : b < (n : ℝ) * (a - b) :=
              (div_lt_iff₀ hdiff).mp hn
            nlinarith
          apply hbB
          refine mem_iUnion.2 ⟨n, ?_⟩
          refine ⟨hbK, ?_⟩
          refine ⟨(b / a, a • u.1), ⟨⟨?_, haK⟩, ?_⟩⟩
          · exact ⟨div_nonneg hb_pos.le ha_pos.le, hfrac⟩
          · change (b / a) • (a • u.1) = b • u.1
            rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
      have hbase :
          (Measure.comap ((↑) : Ioi (0 : ℝ) → ℝ) volume) A = 0 := by
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        exact (hAsub.image ((↑) : Ioi (0 : ℝ) → ℝ)).measure_zero volume
      have hAzero :
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A = 0 := by
        rw [Measure.volumeIoiPow]
        exact withDensity_absolutelyContinuous _ _ hbase
      calc
        ∫⁻ r : Ioi (0 : ℝ), f (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
            ∫⁻ r : Ioi (0 : ℝ), A.indicator (fun _ => 1) r
              ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
          apply lintegral_congr
          intro r
          by_cases hr : r.1 • u.1 ∈ B
          · have hrA : r ∈ A := hr
            simp only [f, Set.indicator_of_mem hr, Set.indicator_of_mem hrA]
          · have hrA : r ∉ A := hr
            simp only [f, Set.indicator_of_notMem hr, Set.indicator_of_notMem hrA]
        _ = (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) A :=
          lintegral_indicator_one hA
        _ = 0 := hAzero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a compactly buffered tangent ball, the raw minimizing endpoint locus is
`modelHaar`-null. -/
theorem rawSegEnd_null
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    (modelHaar (E := E))
        ((rawSeg (I := I) g p \ rawSegInt (I := I) g p) ∩
          closedGBall (I := I) g p R) = 0 := by
  classical
  let K : Set E := rawSeg (I := I) g p ∩ closedGBall (I := I) g p R
  let C : ℕ → Set E := fun n => K ∩
    (fun z : ℝ × E => z.1 • z.2) ''
      (Icc (0 : ℝ) ((n : ℝ) / (n + 1)) ×ˢ K)
  let B : Set E := K \ ⋃ n : ℕ, C n
  have hK : IsCompact K := by
    simpa only [K] using isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  have hBzero : (modelHaar (E := E)) B = 0 := by
    simpa only [B, C] using compactRayEnd_null (E := E) K hK
  apply measure_mono_null ?_ hBzero
  rintro v ⟨⟨hvraw, hvnot⟩, hvball⟩
  refine ⟨⟨hvraw, hvball⟩, ?_⟩
  intro hvB
  change v ∈ ⋃ n : ℕ, C n at hvB
  rcases mem_iUnion.1 hvB with ⟨n, hvC⟩
  rcases hvC.2 with ⟨z, hz, hzv⟩
  rcases hz with ⟨ht, hwK⟩
  by_cases ht0 : z.1 = 0
  · apply hvnot
    refine ⟨2, by norm_num, ?_⟩
    have hv0 : v = 0 := by
      calc
        v = (fun z : ℝ × E => z.1 • z.2) z := hzv.symm
        _ = 0 := by simp only [ht0, zero_smul]
    have hraw0 : (0 : E) ∈ rawSeg (I := I) g p := by
      change ENNReal.ofReal
          (Real.sqrt (g.inner p (0 : TangentSpace I p) 0)) =
        riemannianEDist I p
          (expMap (I := I) g p (0 : TangentSpace I p))
      rw [expMap_zero (I := I) g p, riemannianEDist_self]
      simp
    simpa only [hv0, smul_zero] using hraw0
  · apply hvnot
    have htpos : 0 < z.1 := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hnlt : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
      (div_lt_one₀ hnpos).2 (by linarith)
    have htlt : z.1 < 1 := lt_of_le_of_lt ht.2 hnlt
    refine ⟨1 / z.1, (one_lt_div htpos).2 htlt, ?_⟩
    rw [← hzv]
    change (1 / z.1) • (z.1 • z.2) ∈ rawSeg (I := I) g p
    rw [smul_smul, div_mul_cancel₀ 1 ht0, one_smul]
    exact hwK.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The compact-buffer raw endpoint locus is null-measurable for `modelHaar`. -/
theorem rawSegEnd_nullMeas
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    NullMeasurableSet
      ((rawSeg (I := I) g p \ rawSegInt (I := I) g p) ∩
        closedGBall (I := I) g p R)
      (modelHaar (E := E)) :=
  NullMeasurableSet.of_null (rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private theorem gSphere_null
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    (modelHaar (E := E))
        {v : E | Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v)) = R} = 0 := by
  classical
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let q : E → ℝ := fun v => Real.sqrt
    (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))
  let level : Set E := {v | q v = R}
  have hq_cont : Continuous q := by
    exact Real.continuous_sqrt.comp
      (by simpa only [q] using continuous_gInner_self (I := I) g p)
  have hlevel_meas : MeasurableSet level :=
    (isClosed_eq hq_cont continuous_const).measurableSet
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  have hlevel_eq : level = L '' Metric.sphere (0 : E) R := by
    ext v
    constructor
    · intro hv
      refine ⟨L.symm v, ?_, L.apply_symm_apply v⟩
      rw [mem_sphere_zero_iff_norm]
      have hqv : q v = R := hv
      have hsqrt : q v = ‖L.symm v‖ := by
        have hs := normalFrame_sqrt (I := I) g p (L.symm v)
        change q (L (L.symm v)) = ‖L.symm v‖ at hs
        simpa only [L.apply_symm_apply] using hs
      exact hsqrt.symm.trans hqv
    · rintro ⟨w, hw, rfl⟩
      have hnorm : ‖w‖ = R := by
        simpa only [mem_sphere_zero_iff_norm] using hw
      change q (L w) = R
      have hs := normalFrame_sqrt (I := I) g p w
      change q (L w) = ‖w‖ at hs
      exact hs.trans hnorm
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    b.map L.toLinearEquiv
  have hmap : Measure.map L (modelHaar (E := E)) = b'.addHaar := by
    simpa only [b, b', modelHaar] using Module.Basis.map_addHaar b L
  have hlevel_map : b'.addHaar level = 0 := by
    rw [← hmap, Measure.map_apply_of_aemeasurable
      L.continuous.measurable.aemeasurable hlevel_meas, hlevel_eq,
      L.injective.preimage_image]
    exact Measure.addHaar_sphere (modelHaar (E := E)) (0 : E) R
  have hlevel_zero : (modelHaar (E := E)) level = 0 := by
    change b.addHaar level = 0
    rw [← Module.Basis.det_smul_addHaar b b', Measure.smul_apply,
      hlevel_map, smul_zero]
  simpa only [level, q] using hlevel_zero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A compactly buffered metric ball has the raw polar integral over the
extendible raw minimizing locus. -/
theorem rawBall_integral_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ v in rawSegInt (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  classical
  let B : Set M := {q : M | riemannianEDist I p q < ENNReal.ofReal R}
  let K : Set E := rawSegInt (I := I) g p ∩ gBall (I := I) g p R
  let L : Set E := rawSeg (I := I) g p ∩ closedGBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let D : E → ENNReal := fun v => ENNReal.ofReal
    (curveDensity (I := I) g
      (fun t : ℝ => expMap (I := I) g p
        (show TangentSpace I p from t • v))
      (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
        mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          expMap (I := I) g p
            (show TangentSpace I p from
              t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
  have hL : IsCompact L := by
    simpa only [L] using isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  have hLdom : L ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ rawSeg (I := I) g p ∩ closedGBall (I := I) g p R at hv
    exact rawSeg_mem_dom (I := I) g p hv.1
  have hKsubL : K ⊆ L := by
    intro v hv
    change v ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p R at hv
    refine ⟨rawSegInt_sub (I := I) g hEnorm p hv.1, ?_⟩
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) ≤ R
    have hvball := hv.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact le_of_lt hvball
  have hdiff_sub :
      L \ K ⊆
        ((rawSeg (I := I) g p \ rawSegInt (I := I) g p) ∩
          closedGBall (I := I) g p R) ∪
          {v : E | Real.sqrt
            (g.inner p (show TangentSpace I p from v)
              (show TangentSpace I p from v)) = R} := by
    rintro v ⟨hvL, hvK⟩
    change v ∈ rawSeg (I := I) g p ∩ closedGBall (I := I) g p R at hvL
    change v ∉ rawSegInt (I := I) g p ∩ gBall (I := I) g p R at hvK
    rcases hvL with ⟨hvraw, hvclosed⟩
    by_cases hvint : v ∈ rawSegInt (I := I) g p
    · right
      change Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v)) = R
      apply le_antisymm hvclosed
      apply le_of_not_gt
      intro hvball
      apply hvK
      exact ⟨hvint, hvball⟩
    · left
      exact ⟨⟨hvraw, hvint⟩, hvclosed⟩
  have hdiff : (modelHaar (E := E)) (L \ K) = 0 := by
    apply measure_mono_null hdiff_sub
    apply measure_union_null
    · simpa only [L] using rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt
    · exact gSphere_null (I := I) (E := E) g p R
  have hLKae : L =ᵐ[modelHaar (E := E)] K := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [diff_eq_empty.mpr hKsubL, measure_empty]
  have hInt : (∫⁻ v in L, D v ∂(modelHaar (E := E))) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) :=
    setLIntegral_congr hLKae
  have hcover : B ⊆ F '' L := by
    simpa only [B, F, L] using
      ball_sub_rawSeg (I := I) g hEnorm p hRR₀.le hcpt
  have hupper : riemannianVolumeMeasure (I := I) (M := M) g B ≤
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g B ≤
          riemannianVolumeMeasure (I := I) (M := M) g (F '' L) :=
        measure_mono hcover
      _ ≤ ∫⁻ v in L, D v ∂(modelHaar (E := E)) := by
        simpa only [F, D] using riemVol_rawExp_le (I := I) g p hL hLdom
      _ = ∫⁻ v in K, D v ∂(modelHaar (E := E)) := hInt
  have hFKsub : F '' K ⊆ B := by
    rintro q ⟨v, hvK, rfl⟩
    change v ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p R at hvK
    change riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) < ENNReal.ofReal R
    have hvraw : v ∈ rawSeg (I := I) g p :=
      rawSegInt_sub (I := I) g hEnorm p hvK.1
    change ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) at hvraw
    rw [← hvraw]
    have hvball := hvK.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mpr hvball
  have himage : riemannianVolumeMeasure (I := I) (M := M) g (F '' K) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    simpa only [F, K, D] using
      rawSegInt_image_eq (I := I) g hEnorm p hR hRR₀ hcpt
  apply le_antisymm hupper
  calc
    ∫⁻ v in K, D v ∂(modelHaar (E := E)) =
        riemannianVolumeMeasure (I := I) (M := M) g (F '' K) := himage.symm
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) g B := measure_mono hFKsub

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
