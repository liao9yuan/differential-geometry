import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.BufferedExpDomain
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Comparison.RadialSurjectivity
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential

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
private local instance instMeasTangent (x : M) : MeasurableSpace (TangentSpace I x) :=
  borel _
private local instance instBorelTangent (x : M) : BorelSpace (TangentSpace I x) :=
  ⟨rfl⟩

def gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v) < R}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
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
/-- The raw minimizing equality locus in a strictly buffered tangent ball is compact. -/
theorem isCompact_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    IsCompact
      ({v : E | ENNReal.ofReal (Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v))} ∩
        closedGBall (I := I) g p R) := by
  let K : Set E := closedGBall (I := I) g p R
  have hKcpt : IsCompact K := isCompact_closedGBall (I := I) g p R
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    exact mem_expDom_of_cpt (I := I) g hEnorm p v
      (lt_of_le_of_lt hv hRR₀) hcpt
  have hexp : ContinuousOn
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) K :=
    (expMap_contMDiffOn (I := I) g p).continuousOn.mono hKdom
  have hinner : Continuous (fun v : E =>
      g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) := by
    simpa using (continuous_gInner_self (I := I) g p)
  have hleft : ContinuousOn (fun v : E => ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)))) K :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_sqrt.comp hinner).continuousOn
  have hright : ContinuousOn (fun v : E => riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v))) K := by
    have hdist : Continuous (fun q : M => riemannianEDist I q p) :=
      continuous_riemannianEDist_to (I := I) p
    exact (hdist.comp_continuousOn hexp).congr
      (fun _ _ => Manifold.riemannianEDist_comm)
  have hclosed : IsClosed
      (K ∩ {v : E | ENNReal.ofReal (Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from v))}) :=
    (isClosed_closedGBall (I := I) g p R).isClosed_eq hleft hright
  have hcompact := hKcpt.of_isClosed_subset hclosed
    (Set.inter_subset_left : K ∩ {v : E | ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v))} ⊆ K)
  simpa only [K, Set.inter_comm] using hcompact

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A compactly buffered metric ball is covered by raw minimizing exponential vectors. -/
theorem ball_sub_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R ≤ R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    {q : M | riemannianEDist I p q < ENNReal.ofReal R} ⊆
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) ''
        ({v : E | ENNReal.ofReal (Real.sqrt
            (g.inner p (show TangentSpace I p from v)
              (show TangentSpace I p from v))) =
          riemannianEDist I p
            (expMap (I := I) g p (show TangentSpace I p from v))} ∩
          closedGBall (I := I) g p R) := by
  intro q hq
  have hqR₀ : riemannianEDist I p q < ENNReal.ofReal R₀ :=
    hq.trans_le (ENNReal.ofReal_mono hRR₀)
  obtain ⟨v, _hvdom, hvexp, hvlen⟩ :=
    RadialSurjectivity.minExp_of_cptBall (I := I) g hEnorm p q hqR₀ hcpt
  refine ⟨v, ⟨?_, ?_⟩, hvexp⟩
  · subst q
    exact hvlen
  · change Real.sqrt (g.inner p v v) ≤ R
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (Real.sqrt_nonneg _)).mp (hvlen.trans_lt hq))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
def SegDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v)
        = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal}

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem mem_segDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {x : M} {v : TangentSpace I x} :
    v ∈ SegDom (I := I) g hEnorm x ↔
      Real.sqrt (g.inner x v v)
        = (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
  Iff.rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segDom_zero [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : (0 : TangentSpace I x) ∈ SegDom (I := I) g hEnorm x := by
  rw [mem_segDom, expMapIntrinsic_zero (I := I) g hEnorm x,
    show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 by simp,
    Real.sqrt_zero, Manifold.riemannianEDist_self, ENNReal.toReal_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segDom_smul [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} {v : TangentSpace I x} (hv : v ∈ SegDom (I := I) g hEnorm x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s • v ∈ SegDom (I := I) g hEnorm x := by
  set L : ℝ := Real.sqrt (g.inner x v v) with hL
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have h1s : 0 ≤ 1 - s := by linarith
  have hg0 : intrinsicGeodesic (I := I) g hEnorm x v 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hg1 : intrinsicGeodesic (I := I) g hEnorm x v 1
      = expMapIntrinsic (I := I) g hEnorm x v := rfl
  have hgs : intrinsicGeodesic (I := I) g hEnorm x v s
      = expMapIntrinsic (I := I) g hEnorm x (s • v) := by
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  have hvmem : L = (riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x v)).toReal := hv
  have hfin1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x _
  have hedist1 : riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)
      = ENNReal.ofReal L := by
    rw [hvmem, ENNReal.ofReal_toReal hfin1]
  have hup : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) ≤ ENNReal.ofReal (L * s) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := 0) (t := s) hs0
    rw [← hL, sub_zero] at h
    exact h
  have hup2 : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
      (intrinsicGeodesic (I := I) g hEnorm x v 1)
      ≤ ENNReal.ofReal (L * (1 - s)) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := s) (t := 1) hs1
    rw [← hL] at h
    exact h
  have hsplit : ENNReal.ofReal L
      = ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hLnn hs0) (mul_nonneg hLnn h1s)]
    congr 1; ring
  have hlow : ENNReal.ofReal (L * s)
      ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
          (intrinsicGeodesic (I := I) g hEnorm x v s) := by
    have htri : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
        (intrinsicGeodesic (I := I) g hEnorm x v 1)
        ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) :=
      riemannianEDist_triangle
    have hchain : ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
        ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + ENNReal.ofReal (L * (1 - s)) := by
      calc ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
          = riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) := by
            rw [← hsplit, hg1, hg0, hedist1]
        _ ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
                (intrinsicGeodesic (I := I) g hEnorm x v 1) := htri
        _ ≤ riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + ENNReal.ofReal (L * (1 - s)) := add_le_add le_rfl hup2
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have heq : riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) = ENNReal.ofReal (L * s) :=
    le_antisymm hup hlow
  rw [hg0] at heq
  rw [mem_segDom, sqrt_gInner_smul_self (I := I) g x hs0 v, ← hL, ← hgs, heq,
    ENNReal.toReal_ofReal (mul_nonneg hLnn hs0)]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem ball_sub_image_segDom [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal R} ⊆
      expMapIntrinsic (I := I) g hEnorm x ''
        (SegDom (I := I) g hEnorm x ∩ gBall (I := I) g x R) := by
  intro y hy
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm x y
  refine ⟨v, ⟨?_, ?_⟩, hexp⟩
  · rw [mem_segDom, hexp]; exact hlen
  · change Real.sqrt (g.inner x v v) < R
    rw [hlen]
    exact ENNReal.toReal_lt_of_lt_ofReal hy

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem isOpen_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsOpen (gBall (I := I) g x R) :=
  isOpen_lt (Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x))
    continuous_const

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem measurableSet_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    MeasurableSet (gBall (I := I) g x R) :=
  (isOpen_gBall (I := I) g x R).measurableSet

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem isClosed_segDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : IsClosed (SegDom (I := I) g hEnorm x) := by
  have hf₁ : Continuous fun v : TangentSpace I x => Real.sqrt (g.inner x v v) :=
    Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x)
  have hexp : Continuous fun v : TangentSpace I x =>
      expMapIntrinsic (I := I) g hEnorm x v :=
    expMapIntrinsic_continuous (I := I) g hEnorm x
  have hbase : Continuous fun v : TangentSpace I x =>
      riemannianEDist I (expMapIntrinsic (I := I) g hEnorm x v) x :=
    (continuous_riemannianEDist_to (I := I) x).comp hexp
  have hedist : Continuous fun v : TangentSpace I x =>
      riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) :=
    hbase.congr fun v => Manifold.riemannianEDist_comm
  have hf₂ : Continuous fun v : TangentSpace I x =>
      (riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hedist
      (fun v => riemannianEDist_ne_top (I := I) x _)
  exact isClosed_eq hf₁ hf₂

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem measurableSet_segDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : MeasurableSet (SegDom (I := I) g hEnorm x) :=
  (isClosed_segDom (I := I) g hEnorm x).measurableSet

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
