import DifferentialGeometry.Analysis.Integration.Measure.ManifoldImageEq
import DifferentialGeometry.Geometry.Comparison.Volume.BishopPolarFramed
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentGauss
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDensity
import DifferentialGeometry.Geometry.Comparison.Volume.RawPullVolume
import DifferentialGeometry.Geometry.Exponential.RawFramedLocalDiffeo

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma raw_basis_density
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (B B' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    curveDensity (I := I) g (radialCurve (I := I) g p v)
        (fun i => radialJacobiField (I := I) g p v (B' i)) 1 =
      |B.det B'| *
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (B i)) 1 := by
  classical
  let F : E → M := fun w =>
    expMap (I := I) g p (show TangentSpace I p from w)
  let L : E →L[ℝ] TangentSpace I (radialCurve (I := I) g p v 1) :=
    mfderiv 𝓘(ℝ, E) I F v
  let C : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := B.toMatrix B'
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      B' i = ∑ k, C k i • B k := by
    simpa only [C, Module.Basis.toMatrix_apply] using
      (B.sum_repr (B' i)).symm
  have hcol (w : E) :
      radialJacobiField (I := I) g p v w 1 = L w := by
    simpa only [radialJacobiField, radialCurve, one_smul, F, L] using
      radial_jacobi_dom (I := I) g p v w hv
  have hjac : ∀ i,
      radialJacobiField (I := I) g p v (B' i) 1 =
        ∑ k, C k i • radialJacobiField (I := I) g p v (B k) 1 := by
    intro i
    rw [hcol, hcoord i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol]
    exact L.map_smul (C k i) (B k)
  simpa only [C, Module.Basis.det_apply] using
    curveDensity_recomb (I := I) g
    (radialCurve (I := I) g p v)
    (fun i => radialJacobiField (I := I) g p v (B i))
    (fun i => radialJacobiField (I := I) g p v (B' i))
    1 C hjac

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem rawJac_normal_int
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : MeasurableSet K)
    (hKdom : K ⊆ expDomain (I := I) g p) :
    (∫⁻ v in K,
        ENNReal.ofReal
          (mapJacDensity (I := I) g
            (fun b : E => expMap (I := I) g p
              (show TangentSpace I p from b)) v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let F : E → M := fun v =>
    expMap (I := I) g p (show TangentSpace I p from v)
  let Dn : E → ℝ := fun v =>
    curveDensity (I := I) g (radialCurve (I := I) g p v)
      (fun i => radialJacobiField (I := I) g p v (b' i)) 1
  have hD (v : E) (hv : v ∈ K) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (mapJacDensity (I := I) g F v) =
        ENNReal.ofReal (Dn v) := by
    have hraw : mapJacDensity (I := I) g F v =
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (b i)) 1 := by
      simpa only [F, b, radialCurve, radialJacobiField] using
        raw_exp_density (I := I) g p v (hKdom hv)
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    rw [hraw]
    exact (raw_basis_density (I := I) g p v (hKdom hv) b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (mapJacDensity (I := I) g F v) ∂b.addHaar := by
            rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              setLIntegral_smul_measure]
            exact
              (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            exact setLIntegral_congr_fun hK hD
  have hbmap :
      (stdOrthonormalBasis ℝ E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g p
        ((stdOrthonormalBasis ℝ E) i) = normalBasis (I := I) g p i
    exact normalFrame_basis (I := I) g p i
  have hmap : Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis ℝ E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis ℝ E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis ℝ E).toBasis.map
          L.toLinearEquiv).addHaar := Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  simpa only [Dn, L, b'] using
    (hmp.setLIntegral_comp_preimage_emb
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun v => ENNReal.ofReal (Dn v)) K).symm

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_raw_parts
    {F : E → M} {U : Set E} (hU : MeasurableSet U)
    (hloc : IsLocalHomeomorphOn F U) :
    ∃ P : ℕ → Set E,
      (∀ n, MeasurableSet (P n)) ∧
      Pairwise (Disjoint on P) ∧
      (⋃ n, P n) = U ∧
      ∀ n, Set.InjOn F (P n) := by
  classical
  choose e he hFe using hloc
  let V : E → Set E := fun x =>
    if hx : x ∈ U then (e x hx).source else ∅
  have hVopen : ∀ x, IsOpen (V x) := by
    intro x
    by_cases hx : x ∈ U
    · simpa only [V, dif_pos hx] using (e x hx).open_source
    · simp only [V, dif_neg hx, isOpen_empty]
  have hxV : ∀ x (hx : x ∈ U), x ∈ V x := by
    intro x hx
    simpa only [V, dif_pos hx] using he x hx
  have hVinj : ∀ x, Set.InjOn F (V x) := by
    intro x
    by_cases hx : x ∈ U
    · simpa only [V, dif_pos hx, hFe x hx] using (e x hx).injOn
    · simp only [V, dif_neg hx, Set.injOn_empty]
  have hVnhds : ∀ x ∈ U, V x ∈ 𝓝[U] x := by
    intro x hx
    exact mem_nhdsWithin_of_mem_nhds ((hVopen x).mem_nhds (hxV x hx))
  obtain ⟨t, _htU, htc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin hVnhds
  let enum : ℕ → E := Set.enumerateCountable htc 0
  have ht_range : t ⊆ Set.range enum := by
    intro x hx
    simpa only [enum] using Set.subset_range_enumerate htc 0 hx
  have hcoverV : U ⊆ ⋃ n, V (enum n) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨z, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hzt, hxVz⟩
    rcases ht_range hzt with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn ▸ hxVz⟩
  let W : ℕ → Set E := fun n => V (enum n)
  let P : ℕ → Set E := fun n => U ∩ disjointed W n
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hU.inter
      (MeasurableSet.disjointed
        (fun k => (hVopen (enum k)).measurableSet) n)
  · exact (disjoint_disjointed W).mono fun _ _ hij =>
      hij.mono inter_subset_right inter_subset_right
  · change (⋃ n, U ∩ disjointed W n) = U
    rw [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
    simpa only [W] using hcoverV
  · intro n
    exact (hVinj (enum n)).mono
      (inter_subset_right.trans (disjointed_subset W n))

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Raw framed-exponential multiplicity is bounded by the integral of the
time-one raw radial-Jacobi density in normal-frame coordinates. -/
theorem raw_mul_le_area
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {U : Set E} (hU : MeasurableSet U)
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hdom : ∀ w ∈ U,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap (I := I) (E := E) g p) U)
    (hcount : ∀ y ∈ S, m ≤
      {w : E | w ∈ U ∧ framedExpMap (I := I) (E := E) g p w = y}.encard) :
    m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∫⁻ w in U,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let K : Set E := L '' U
  let D : Set E := expDomain (I := I) g p
  let F : E → M := fun v =>
    expMap (I := I) g p (show TangentSpace I p from v)
  have hK : MeasurableSet K :=
    L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hU
  have hKD : K ⊆ D := by
    intro v hv
    rcases hv with ⟨w, hwU, rfl⟩
    exact hdom w hwU
  have hDopen : IsOpen D := by
    simpa only [D] using isOpen_expDomain (I := I) g p
  have hFsmooth : ContMDiffOn 𝓘(ℝ, E) I 1 F D := by
    simpa only [F, D] using
      (expMap_contMDiffOn (I := I) g p).of_le (by norm_num)
  have hLloc : IsLocalHomeomorphOn (fun w : E => L w) U :=
    L.toHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn.mono
      (Set.subset_univ U)
  have hcomp : IsLocalHomeomorphOn (F ∘ fun w : E => L w) U := by
    simpa only [F, L, Function.comp_apply, framedExpMap_apply] using
      hloc.isLocalHomeomorphOn
  have hraw : IsLocalHomeomorphOn F K := by
    simpa only [K] using hcomp.of_comp_right hLloc
  have hcountRaw : ∀ y ∈ S, m ≤
      {v : E | v ∈ K ∧ F v = y}.encard := by
    intro y hy
    let A : Set E := {w : E | w ∈ U ∧
      framedExpMap (I := I) (E := E) g p w = y}
    let B : Set E := {v : E | v ∈ K ∧ F v = y}
    let emb : A ↪ B :=
      { toFun := fun w =>
          ⟨L w.1, ⟨⟨w.1, w.2.1, rfl⟩, by
            simpa only [F, L, framedExpMap_apply] using w.2.2⟩⟩
        inj' := by
          intro w z hwz
          apply Subtype.ext
          apply L.injective
          exact congrArg Subtype.val hwz }
    exact (hcount y hy).trans (by
      simpa only [A, B] using emb.encard_le)
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPinj⟩ :=
    exists_raw_parts hK hraw
  have hPK : ∀ n, P n ⊆ K := by
    intro n v hv
    rw [← hPcover]
    exact Set.mem_iUnion.mpr ⟨n, hv⟩
  have hQmeas : ∀ n, MeasurableSet (F '' P n) := fun n =>
    (hPmeas n).image_of_continuousOn_injOn
      (hFsmooth.continuousOn.mono ((hPK n).trans hKD)) (hPinj n)
  have hpoint : ∀ y ∈ S,
      m.toENNReal ≤ ∑' n : ℕ, (F '' P n).indicator 1 y := by
    intro y hy
    let Fib : Set E := {v : E | v ∈ K ∧ F v = y}
    let J : Set ℕ := {n : ℕ | y ∈ F '' P n}
    have hvpart : ∀ v : Fib, ∃ n, v.1 ∈ P n := by
      intro v
      have hv : v.1 ∈ ⋃ n, P n := hPcover.symm ▸ v.2.1
      exact Set.mem_iUnion.mp hv
    let idx : Fib → ℕ := fun v => Classical.choose (hvpart v)
    have hidx : ∀ v : Fib, v.1 ∈ P (idx v) := fun v =>
      Classical.choose_spec (hvpart v)
    let emb : Fib ↪ J :=
      { toFun := fun v =>
          ⟨idx v, ⟨v.1, hidx v, v.2.2⟩⟩
        inj' := by
          intro v w hvw
          have hn : idx v = idx w := congrArg Subtype.val hvw
          apply Subtype.ext
          apply hPinj (idx v) (hidx v)
          · simpa only [hn] using hidx w
          · exact v.2.2.trans w.2.2.symm }
    have hcard : m.toENNReal ≤ J.encard.toENNReal :=
      (ENat.toENNReal_mono (hcountRaw y hy)).trans
        (ENat.toENNReal_mono emb.encard_le)
    calc
      m.toENNReal ≤ J.encard.toENNReal := hcard
      _ = ∑' _ : J, (1 : ENNReal) := (ENNReal.tsum_set_one J).symm
      _ = ∑' n : ℕ, J.indicator 1 n :=
        tsum_subtype J (fun _ : ℕ => (1 : ENNReal))
      _ = ∑' n : ℕ, (F '' P n).indicator 1 y := by
        apply tsum_congr
        intro n
        simp only [J, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  have harea : m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
        ∂(modelHaar (E := E)) := by
    calc
      m.toENNReal * riemannianVolumeMeasure (I := I) (M := M) g S =
          ∫⁻ _y in S, m.toENNReal
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        (setLIntegral_const S m.toENNReal).symm
      _ ≤ ∫⁻ y in S, ∑' n : ℕ, (F '' P n).indicator 1 y
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        setLIntegral_mono' hS hpoint
      _ ≤ ∫⁻ y, ∑' n : ℕ, (F '' P n).indicator 1 y
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        setLIntegral_le_lintegral S _
      _ = ∑' n : ℕ,
          ∫⁻ y, (F '' P n).indicator 1 y
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        simpa only using
          (lintegral_tsum
            (μ := riemannianVolumeMeasure (I := I) (M := M) g)
            (f := fun n y =>
              (F '' P n).indicator (fun _ => (1 : ENNReal)) y)
            (fun n =>
              (measurable_const.indicator (hQmeas n)).aemeasurable))
      _ = ∑' n : ℕ,
          riemannianVolumeMeasure (I := I) (M := M) g (F '' P n) := by
        apply tsum_congr
        intro n
        exact lintegral_indicator_one (hQmeas n)
      _ = ∑' n : ℕ,
          ∫⁻ v in P n, ENNReal.ofReal (mapJacDensity (I := I) g F v)
            ∂(modelHaar (E := E)) := by
        apply tsum_congr
        intro n
        exact riemVol_image_eq (I := I) g hDopen (hPmeas n)
          ((hPK n).trans hKD) hFsmooth (hPinj n)
      _ = ∫⁻ v in ⋃ n, P n,
          ENNReal.ofReal (mapJacDensity (I := I) g F v)
            ∂(modelHaar (E := E)) :=
        (lintegral_iUnion hPmeas hPdisj _).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
            ∂(modelHaar (E := E)) := by
        rw [hPcover]
  have hpre : L ⁻¹' K = U := Set.preimage_image_eq U L.injective
  have hpre' :
      (normalFrame (I := I) (E := E) g p) ⁻¹' K = U := by
    simpa only [L] using hpre
  rw [rawJac_normal_int (I := I) g p hK (by simpa only [D] using hKD),
    hpre'] at harea
  simpa only [F, L] using harea

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Raw framed-exponential multiplicity is bounded by the pull volume of the
centered model ball. -/
theorem raw_mul_le_pull
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R : Real)
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hdom : ∀ w ∈ Metric.ball (0 : E) R,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap (I := I) (E := E) g p) (Metric.ball (0 : E) R))
    (hcount : ∀ y ∈ S, m ≤
      {w : E | w ∈ Metric.ball (0 : E) R ∧
        framedExpMap (I := I) (E := E) g p w = y}.encard) :
    m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S ≤
      rawPullVol (I := I) g p R := by
  classical
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g p
  let K : Set E := L '' Metric.ball (0 : E) R
  have hball : MeasurableSet (Metric.ball (0 : E) R) :=
    Metric.isOpen_ball.measurableSet
  have hK : MeasurableSet K :=
    L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hball
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    rcases hv with ⟨w, hw, rfl⟩
    exact hdom w hw
  have hpre :
      (normalFrame (I := I) (E := E) g p) ⁻¹' K =
        Metric.ball (0 : E) R := by
    simpa only [L] using
      Set.preimage_image_eq (Metric.ball (0 : E) R) L.injective
  calc
    m.toENNReal * riemannianVolumeMeasure (I := I) (M := M) g S ≤
        ∫⁻ w in Metric.ball (0 : E) R,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (radialCurve (I := I) g p
                (normalFrame (I := I) (E := E) g p w))
              (fun i => radialJacobiField (I := I) g p
                (normalFrame (I := I) (E := E) g p w)
                (normalBasis (I := I) g p i)) 1)
          ∂(volume : Measure E) :=
      raw_mul_le_area (I := I) g p hball hS hdom hloc hcount
    _ = rawPullVol (I := I) g p R := by
      have hconvert := rawJac_normal_int (I := I) g p hK hKdom
      rw [hpre] at hconvert
      simpa only [rawPullVol, K, L] using hconvert.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
