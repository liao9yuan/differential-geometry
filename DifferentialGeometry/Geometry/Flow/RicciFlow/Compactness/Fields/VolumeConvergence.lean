import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.KineticConvergence

set_option autoImplicit false

/-!
# Volume-density convergence in pointed charts

This file converts compact-uniform convergence of fixed-chart Gram operators
into compact-uniform convergence of the associated Riemannian volume densities.
-/

noncomputable section

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.HCGCompactness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe v vF vK

variable {F : Type vF} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F]
variable {KModel : Type vK} [TopologicalSpace KModel]
variable {J : ModelWithCorners Real F KModel} [J.Boundaryless]
variable {Y : PointedFlowSeq.{v, vF, vK} (I := J)}
variable {N : PointedRiemannianManifold.{v, vF, vK} (I := J)}
variable {subseq' : Nat → Nat}
variable (Psi : PointedCGHMaps (I := J) Y N subseq')

/-- The chart-volume density associated to a fixed-chart Gram operator. -/
private noncomputable def opVolDens (A : F →L[Real] F) : Real :=
  Real.sqrt <| Matrix.det <| Matrix.of fun i j : Fin (Module.finrank Real F) ↦
    inner Real (A (chartModelBasis F i)) (chartModelBasis F j)

omit [CompleteSpace F] in
private theorem opVolDens_cont : Continuous (opVolDens (F := F)) := by
  apply Real.continuous_sqrt.comp
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  exact ((ContinuousLinearMap.apply Real F (chartModelBasis F i)).continuous).inner
    continuous_const

omit [CompleteSpace F] [J.Boundaryless] in
private theorem opVolDens_chart {D : RealTimeInterval}
    {M : Type*} [TopologicalSpace M] [ChartedSpace KModel M]
    [IsManifold J (∞ : WithTop ℕ∞) M]
    (G : MetricConnectionFamilyOn (I := J) (M := M) D) (alpha : M)
    (p : Real × F) :
    opVolDens (chartGramOp (I := J) G alpha p) =
      chartDensity (I := J) (G.metric p.1) alpha
        ((extChartAt J alpha).symm p.2) := by
  unfold opVolDens chartDensity
  congr 1
  apply congrArg Matrix.det
  ext i j
  rw [Matrix.of_apply, chartGramOp_inner]
  exact (Tensor.Tensor0SRiemannian.chartGramMatrix_eq_innerJinv
    (I := J) (M := M) (G.metric p.1) alpha
    ((extChartAt J alpha).symm p.2) i j).symm

omit [J.Boundaryless] in
/-- Pointed compact-uniform metric convergence gives compact-uniform
convergence of the corresponding fixed-chart volume densities. -/
theorem ConvOut.volDens_compOn
    (R : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      letI : IsManifold J ∞ N.M := N.smooth
      SmoothRiemannianMetric J N.M)
    (bf : BumpFamily (I := J) Psi) (hsrc : SrcSigma Psi) (htgt : TgtSigma Psi)
    (beta psi : Real) (co : ConvOut (I := J) Psi R bf hsrc htgt beta psi)
    (hInf : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      letI : T2Space N.M := N.t2
      letI : IsManifold J ∞ N.M := N.smooth
      letI : SigmaCompactSpace N.M := N.sigmaCompact
      MetricFamilySmoothOn (I := J) (M := N.M) Y.D co.gInf)
    (hreg : Icc beta psi ⊆ Y.D.regular)
    (alpha : N.M) {K : Set F}
    (hKchart : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      K ⊆ interior (extChartAt J alpha).target)
    (hKc : IsCompact K)
    {Q : Type*} [UniformSpace Q] {tau : Q → Real}
    {u : Nat → Q → F} {uLim : Q → F}
    (htau : ∀ q, tau q ∈ Icc beta psi)
    (huK : ∀ᶠ k in atTop, ∀ q, u k q ∈ K)
    (hlimK : ∀ q, uLim q ∈ K)
    (hu : TendstoUniformly u uLim atTop) :
    letI : TopologicalSpace N.M := N.topology
    letI : ChartedSpace KModel N.M := N.charted
    letI : T2Space N.M := N.t2
    letI : IsManifold J ∞ N.M := N.smooth
    letI : SigmaCompactSpace N.M := N.sigmaCompact
    TendstoUniformly
      (fun k q ↦ chartDensity (I := J)
        (gSeqExt (I := J) Psi R bf hsrc htgt (co.φ k) (tau q)) alpha
        ((extChartAt J alpha).symm (u k q)))
      (fun q ↦ chartDensity (I := J) (co.gInf (tau q)) alpha
        ((extChartAt J alpha).symm (uLim q))) atTop := by
  classical
  letI : TopologicalSpace N.M := N.topology
  letI : ChartedSpace KModel N.M := N.charted
  letI : T2Space N.M := N.t2
  letI : IsManifold J ∞ N.M := N.smooth
  letI : SigmaCompactSpace N.M := N.sigmaCompact
  let GSeq : Nat → MetricConnectionFamilyOn (I := J) (M := N.M) Y.D := fun k ↦
    (lcMetricFamily (I := J) (M := N.M)
      (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt (co.φ k) t)).restrict Y.D
  let GInf : MetricConnectionFamilyOn (I := J) (M := N.M) Y.D :=
    (lcMetricFamily (I := J) (M := N.M) co.gInf).restrict Y.D
  have hInf' : MetricFamilySmoothOn (I := J) (M := N.M) Y.D GInf.metric := by
    simpa only [GInf, MetricConnectionFamily.restrict_metric, lcMetricFamily] using hInf
  have hGram : TendstoUniformly
      (fun k q ↦ chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
      (fun q ↦ chartGramOp (I := J) GInf alpha (tau q, uLim q)) atTop := by
    simpa only [GSeq, GInf] using
      (ConvOut.chartGram_convOn (J := J) (Y := Y) Psi R bf hsrc htgt
        beta psi co hInf hreg alpha hKchart hKc htau huK hlimK hu)
  obtain ⟨C, hC⟩ := chartGramOp_bound (I := J) (G := GInf)
    hInf' hreg isCompact_Icc alpha hKchart hKc
  let B : Set (F →L[Real] F) := Metric.closedBall 0 ((C : Real) + 1)
  have hLimB : ∀ q, chartGramOp (I := J) GInf alpha (tau q, uLim q) ∈ B := by
    intro q
    change dist (chartGramOp (I := J) GInf alpha (tau q, uLim q)) 0 ≤
      (C : Real) + 1
    rw [dist_zero_right]
    exact (hC (tau q, uLim q) ⟨htau q, hlimK q⟩).trans (by norm_num)
  have hnear := (Metric.tendstoUniformly_iff.1 hGram) 1 zero_lt_one
  have hSeqB : ∀ᶠ k in atTop,
      ∀ q, chartGramOp (I := J) (GSeq k) alpha (tau q, u k q) ∈ B := by
    filter_upwards [hnear] with k hk
    intro q
    change dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q)) 0 ≤
      (C : Real) + 1
    calc
      dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q)) 0
          ≤ dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
              (chartGramOp (I := J) GInf alpha (tau q, uLim q)) +
            dist (chartGramOp (I := J) GInf alpha (tau q, uLim q)) 0 :=
        dist_triangle _ _ _
      _ ≤ 1 + (C : Real) := by
        apply add_le_add
        · exact (by simpa only [dist_comm] using (hk q).le)
        · simpa only [dist_zero_right] using
            hC (tau q, uLim q) ⟨htau q, hlimK q⟩
      _ = (C : Real) + 1 := add_comm _ _
  letI : ProperSpace (F →L[Real] F) := FiniteDimensional.proper Real _
  have hBc : IsCompact B := isCompact_closedBall 0 ((C : Real) + 1)
  have huc : UniformContinuousOn (opVolDens (F := F)) B :=
    hBc.uniformContinuousOn_of_continuous opVolDens_cont.continuousOn
  have hdens := huc.comp_tendstoUniformly_eventually hSeqB hLimB hGram
  have hdens' : TendstoUniformly
      (fun k q ↦ chartDensity (I := J) ((GSeq k).metric (tau q)) alpha
        ((extChartAt J alpha).symm (u k q)))
      (fun q ↦ chartDensity (I := J) (GInf.metric (tau q)) alpha
        ((extChartAt J alpha).symm (uLim q))) atTop := by
    simpa only [opVolDens_chart] using hdens
  simpa only [GSeq, GInf, MetricConnectionFamily.restrict_metric,
    lcMetricFamily] using hdens'

section SourceParam

/-- The preferred chart at a limit point, followed by a pointed comparison map,
as a first-order parametrization of the approximating manifold. -/
noncomputable def mapChartParam (k : Nat) (alpha : N.M) :
    letI : TopologicalSpace N.M := N.topology
    letI : ChartedSpace KModel N.M := N.charted
    letI : TopologicalSpace (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).topology
    letI : ChartedSpace KModel (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).charted
    PartialDiffeomorph (modelWithCornersSelf Real F) J F
      (Y.term (subseq' k)).M 1 := by
  letI : TopologicalSpace N.M := N.topology
  letI : ChartedSpace KModel N.M := N.charted
  letI : IsManifold J ∞ N.M := N.smooth
  letI : TopologicalSpace (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).topology
  letI : ChartedSpace KModel (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).charted
  letI : IsManifold J ∞ (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).smooth
  let chart : PartialDiffeomorph (modelWithCornersSelf Real F) J F N.M 1 :=
    { toPartialEquiv := (extChartAt J alpha).symm
      open_source := isOpen_extChartAt_target alpha
      open_target := isOpen_extChartAt_source alpha
      contMDiffOn_toFun :=
        contMDiffOn_extChartAt_symm (I := J) (n := 1) alpha
      contMDiffOn_invFun := by
        change ContMDiffOn J (modelWithCornersSelf Real F) 1 (extChartAt J alpha)
          (extChartAt J alpha).source
        rw [extChartAt_source_eq_chartAt_source (I := J)]
        exact contMDiffOn_extChartAt (I := J) (n := 1) (x := alpha) }
  let pointMap : PartialDiffeomorph J J N.M (Y.term (subseq' k)).M 1 :=
    { toPartialEquiv := (Psi.partialDiffeomorph k).toPartialEquiv
      open_source := (Psi.partialDiffeomorph k).open_source
      open_target := (Psi.partialDiffeomorph k).open_target
      contMDiffOn_toFun :=
        (Psi.partialDiffeomorph k).contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun :=
        (Psi.partialDiffeomorph k).contMDiffOn_invFun.of_le (by norm_num) }
  refine
    { toPartialEquiv := chart.toPartialEquiv.trans pointMap.toPartialEquiv
      open_source := ?_
      open_target := ?_
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · change IsOpen (chart.source ∩ (chart : F → N.M) ⁻¹' pointMap.source)
    exact chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      chart.open_source pointMap.open_source
  · rw [PartialEquiv.trans_target]
    change IsOpen (pointMap.target ∩
      (pointMap.symm : (Y.term (subseq' k)).M → N.M) ⁻¹' chart.target)
    exact pointMap.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      pointMap.open_target chart.open_target
  · exact pointMap.contMDiffOn_toFun.comp
      (chart.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ h ↦ h.2)
  · rw [PartialEquiv.trans_target]
    exact chart.symm.contMDiffOn_toFun.comp
      (pointMap.symm.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ h ↦ h.2)

/-- On the bump-one region, the density of the pointed source
parametrization is the fixed-chart density of the extended metric. -/
theorem paramDens_src_eq
    (R : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      letI : IsManifold J ∞ N.M := N.smooth
      SmoothRiemannianMetric J N.M)
    (bf : BumpFamily (I := J) Psi) (hsrc : SrcSigma Psi) (htgt : TgtSigma Psi)
    (k : Nat) (t : Real) (alpha : N.M) {w : F}
    (hw : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      letI : TopologicalSpace (Y.term (subseq' k)).M :=
        (Y.term (subseq' k)).topology
      letI : ChartedSpace KModel (Y.term (subseq' k)).M :=
        (Y.term (subseq' k)).charted
      w ∈ (mapChartParam (J := J) Psi k alpha).source)
    (hOne : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      bf.chi k ((extChartAt J alpha).symm w) = 1) :
    letI : TopologicalSpace N.M := N.topology
    letI : ChartedSpace KModel N.M := N.charted
    letI : T2Space N.M := N.t2
    letI : IsManifold J ∞ N.M := N.smooth
    letI : SigmaCompactSpace N.M := N.sigmaCompact
    letI : TopologicalSpace (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).topology
    letI : ChartedSpace KModel (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).charted
    letI : T2Space (Y.term (subseq' k)).M := (Y.term (subseq' k)).t2
    letI : IsManifold J ∞ (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).smooth
    letI : SigmaCompactSpace (Y.term (subseq' k)).M :=
      (Y.term (subseq' k)).sigmaCompact
    paramDensity (I := J) ((Y.term (subseq' k)).S.base.metric t)
        (mapChartParam (J := J) Psi k alpha) w =
      chartDensity (I := J) (gSeqExt (I := J) Psi R bf hsrc htgt k t) alpha
        ((extChartAt J alpha).symm w) := by
  classical
  letI : TopologicalSpace N.M := N.topology
  letI : ChartedSpace KModel N.M := N.charted
  letI : T2Space N.M := N.t2
  letI : IsManifold J ∞ N.M := N.smooth
  letI : SigmaCompactSpace N.M := N.sigmaCompact
  letI : TopologicalSpace (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).topology
  letI : ChartedSpace KModel (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).charted
  letI : T2Space (Y.term (subseq' k)).M := (Y.term (subseq' k)).t2
  letI : IsManifold J ∞ (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).smooth
  letI : SigmaCompactSpace (Y.term (subseq' k)).M :=
    (Y.term (subseq' k)).sigmaCompact
  let chart : PartialDiffeomorph (modelWithCornersSelf Real F) J F N.M 1 :=
    { toPartialEquiv := (extChartAt J alpha).symm
      open_source := isOpen_extChartAt_target alpha
      open_target := isOpen_extChartAt_source alpha
      contMDiffOn_toFun :=
        contMDiffOn_extChartAt_symm (I := J) (n := 1) alpha
      contMDiffOn_invFun := by
        change ContMDiffOn J (modelWithCornersSelf Real F) 1 (extChartAt J alpha)
          (extChartAt J alpha).source
        rw [extChartAt_source_eq_chartAt_source (I := J)]
        exact contMDiffOn_extChartAt (I := J) (n := 1) (x := alpha) }
  let pointMap : PartialDiffeomorph J J N.M (Y.term (subseq' k)).M 1 :=
    { toPartialEquiv := (Psi.partialDiffeomorph k).toPartialEquiv
      open_source := (Psi.partialDiffeomorph k).open_source
      open_target := (Psi.partialDiffeomorph k).open_target
      contMDiffOn_toFun :=
        (Psi.partialDiffeomorph k).contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun :=
        (Psi.partialDiffeomorph k).contMDiffOn_invFun.of_le (by norm_num) }
  let x : N.M := chart w
  have hwParts : w ∈ chart.source ∩ (chart : F → N.M) ⁻¹' pointMap.source := by
    simpa only [mapChartParam] using hw
  have hwChart : w ∈ chart.source := hwParts.1
  have hxSrc : x ∈ Psi.source k := hwParts.2
  let xsrc : SourceDomain (I := J) Psi k := ⟨x, hxSrc⟩
  letI : TopologicalSpace (SourceDomain (I := J) Psi k) :=
    sourceDomTop (I := J) Psi k
  letI : ChartedSpace KModel (SourceDomain (I := J) Psi k) :=
    sourceDomCharted (I := J) Psi k
  letI : T2Space (SourceDomain (I := J) Psi k) := sourceDomT2 (I := J) Psi k
  letI : IsManifold J ∞ (SourceDomain (I := J) Psi k) :=
    sourceDomSmooth (I := J) Psi k
  letI : SigmaCompactSpace (SourceDomain (I := J) Psi k) :=
    sourceDomSigmaOf (I := J) Psi k (hsrc k)
  have hMap : mapChartParam (J := J) Psi k alpha w = Psi.map k x := by
    rfl
  have hChartDiff : MDifferentiableAt (modelWithCornersSelf Real F) J chart w :=
    (chart.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hwChart).mdifferentiableAt
      (chart.open_source.mem_nhds hwChart)
  have hPointDiff : MDifferentiableAt J J pointMap x :=
    (pointMap.contMDiffOn_toFun.mdifferentiableOn one_ne_zero x hxSrc).mdifferentiableAt
      (pointMap.open_source.mem_nhds hxSrc)
  have hDeriv :
      mfderiv (modelWithCornersSelf Real F) J
          (mapChartParam (J := J) Psi k alpha) w =
        (mfderiv J J pointMap x).comp
          (mfderiv (modelWithCornersSelf Real F) J chart w) := by
    simpa only [mapChartParam, x, Function.comp_def] using
      (mfderiv_comp w hPointDiff hChartDiff)
  have hRestrict (v : TangentSpace J xsrc) :
      mfderiv J J (fun y : SourceDomain (I := J) Psi k ↦
        Psi.map k (y : N.M)) xsrc v =
        mfderiv J J pointMap x v := by
    have hVal : MDifferentiableAt J J
        (fun y : SourceDomain (I := J) Psi k ↦ (y : N.M)) xsrc :=
      ContMDiffAt.mdifferentiableAt
        ((contMDiff_subtype_val (I := J) (n := 1)
          (U := sourceOpen (I := J) Psi k)).contMDiffAt) (by norm_num)
    have hComp := mfderiv_comp xsrc hPointDiff hVal
    have hvinc :
        mfderiv J J (fun y : SourceDomain (I := J) Psi k ↦ (y : N.M)) xsrc v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := J) (sourceOpen (I := J) Psi k) xsrc v
    change mfderiv J J
      (pointMap ∘ (fun y : SourceDomain (I := J) Psi k ↦ (y : N.M))) xsrc v =
        mfderiv J J pointMap x v
    rw [congrArg (fun L ↦ L v) hComp]
    change mfderiv J J pointMap (xsrc : N.M)
      (mfderiv J J (fun y : SourceDomain (I := J) Psi k ↦ (y : N.M)) xsrc v) =
        mfderiv J J pointMap x v
    rw [hvinc]
  let D := SourceDomainMetricData.ofRestrictPullback (I := J)
    (Φ := Psi) (k := k) (hsrc k) (htgt k)
    (fun _ ↦ refRes (I := J) Psi R hsrc k) (fun _ ↦ R)
  have hMetric : srcMetric (I := J) Psi hsrc htgt k t = D.pullbackMetric t := by
    simpa only [srcMetric, D] using
      sourceFlow_metric_eq (I := J) Psi k (hsrc k) (htgt k)
        (fun _ ↦ refRes (I := J) Psi R hsrc k) (fun _ ↦ R) t
  have hSrcInner (v q : TangentSpace J xsrc) :
      (srcMetric (I := J) Psi hsrc htgt k t).inner xsrc v q =
        ((Y.term (subseq' k)).S.family.metric t).inner (Psi.map k x)
          (mfderiv J J pointMap x v) (mfderiv J J pointMap x q) := by
    rw [hMetric]
    have hpull := D.pullback_inner t xsrc v q
    simp only [xsrc] at hpull
    have hvMap :
        mfderiv J J (fun y : SourceDomain (I := J) Psi k ↦ Psi.map k (y : N.M))
            (⟨x, hxSrc⟩ : SourceDomain (I := J) Psi k) v =
          mfderiv J J pointMap x v := by
      simpa only [xsrc] using hRestrict v
    have hqMap :
        mfderiv J J (fun y : SourceDomain (I := J) Psi k ↦ Psi.map k (y : N.M))
            (⟨x, hxSrc⟩ : SourceDomain (I := J) Psi k) q =
          mfderiv J J pointMap x q := by
      simpa only [xsrc] using hRestrict q
    exact hpull.trans (congrArg₂
      (fun a b ↦ ((Y.term (subseq' k)).S.family.metric t).inner (Psi.map k x) a b)
      hvMap hqMap)
  have hGram :
      paramGramMatrix (I := J) ((Y.term (subseq' k)).S.base.metric t)
          (mapChartParam (J := J) Psi k alpha) w =
        paramGramMatrix (I := J) (gSeqExt (I := J) Psi R bf hsrc htgt k t)
          chart w := by
    ext i j
    simp only [paramGramMatrix_apply]
    let v := mfderiv (modelWithCornersSelf Real F) J chart w (chartModelBasis F i)
    let q := mfderiv (modelWithCornersSelf Real F) J chart w (chartModelBasis F j)
    rw [hMap, hDeriv]
    change ((Y.term (subseq' k)).S.base.metric t).inner (Psi.map k x)
        (mfderiv J J pointMap x v) (mfderiv J J pointMap x q) =
      (gSeqExt (I := J) Psi R bf hsrc htgt k t).inner (chart w) v q
    have hExt := gSeqExt_inner_of_mem (I := J) Psi R bf hsrc htgt k t x hxSrc v q
    rw [hOne] at hExt
    simp only [one_smul, sub_self, zero_smul, add_zero] at hExt
    exact (hSrcInner v q).symm.trans hExt.symm
  have hParam :
      paramDensity (I := J) ((Y.term (subseq' k)).S.base.metric t)
          (mapChartParam (J := J) Psi k alpha) w =
        paramDensity (I := J) (gSeqExt (I := J) Psi R bf hsrc htgt k t)
          chart w := by
    unfold paramDensity
    rw [hGram]
  have hxChart : x ∈ (chartAt KModel alpha).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := J)]
    exact (extChartAt J alpha).map_target hwChart
  have hxTriv : x ∈ (trivializationAt F (TangentSpace J) alpha).baseSet := by
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using hxChart
  have hLocal : paramChartMap (I := J) alpha chart =ᶠ[𝓝 w] id := by
    filter_upwards [(isOpen_extChartAt_target alpha).mem_nhds hwChart] with z hz
    simpa only [paramChartMap, chart, id_eq] using (extChartAt J alpha).right_inv hz
  have hfderiv : fderiv Real (paramChartMap (I := J) alpha chart) w =
      ContinuousLinearMap.id Real F := by
    rw [hLocal.fderiv_eq]
    exact fderiv_id
  have hDet : ((ContinuousLinearMap.id Real F) : F →L[Real] F).det = 1 := by
    change LinearMap.det (LinearMap.id : F →ₗ[Real] F) = 1
    exact LinearMap.det_id
  have hChartDensity := paramDensity_eq_abs_det_mul_chartDensity
    (I := J) (gSeqExt (I := J) Psi R bf hsrc htgt k t) alpha chart hwChart hxTriv
  rw [hfderiv, hDet] at hChartDensity
  simp only [abs_one, one_mul] at hChartDensity
  exact hParam.trans hChartDensity

end SourceParam

end DifferentialGeometry.HCGCompactness
