import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.UniformEquivalence
import DifferentialGeometry.Geometry.Operator.MetricFamilyGram
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramWeak

set_option autoImplicit false

/-!
# Kinetic convergence along a fixed curve

This file turns compact-uniform zeroth-order convergence of the extended
pointed metrics into uniform convergence of their kinetic quadratic forms
along a fixed `C¹` curve.
-/

noncomputable section

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff

open DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : Nat → Nat}
variable (Phi : PointedCGHMaps (I := I) X P subseq)

section KineticConv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-- Compact-uniform zeroth-order convergence of pointed metrics gives uniform
convergence of the kinetic quadratic form along a fixed `C¹` curve. -/
theorem ConvOut.kinetic_convOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) (co : ConvOut (I := I) Phi R bf hsrc htgt beta psi)
    (T a b : Real) (alpha : Real → P.M)
    (halpha : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k s ↦
        (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (fun s ↦
        (co.gInf (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      atTop (Icc a b) := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  let K : Set P.M := alpha '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn halpha.continuous.continuousOn
  have hv : ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 0
      (fun s ↦ TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s)) := by
    have ht := halpha.contMDiff_tangentMap (m := 0) (by norm_num)
    have hone : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent 0
        (fun s : Real ↦
          (⟨s, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
      rw [contMDiff_vectorSpace_iff_contDiff]
      exact contDiff_const
    simpa only [lVelocity, tangentMap] using ht.comp hone
  letI cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : P.M → Type _) := R.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : P.M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  let q : Real → Real := fun s ↦
    R.inner (alpha s) (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  have hq : Continuous q := by
    have hinner := Continuous.inner_bundle (F := E) (B := P.M)
      (E := (TangentSpace I : P.M → Type _))
      (b := alpha) (v := fun s ↦ lVelocity (I := I) alpha s)
      (w := fun s ↦ lVelocity (I := I) alpha s) hv.continuous hv.continuous
    simpa only [q] using hinner
  obtain ⟨V₀, hV₀⟩ := isCompact_Icc.bddAbove_image hq.continuousOn
  let V : Real := max V₀ 0
  have hV0 : 0 ≤ V := le_max_right V₀ 0
  have hV : ∀ s ∈ Icc a b, q s ≤ V := by
    intro s hs
    exact (hV₀ ⟨s, hs, rfl⟩).trans (le_max_left V₀ 0)
  let n : Real := Module.finrank Real E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let delta : Real := epsilon / (n * V + 1)
  have hden : 0 < n * V + 1 := by
    nlinarith [mul_nonneg hn hV0]
  have hdelta : 0 < delta := div_pos hepsilon hden
  obtain ⟨k0, hk0⟩ := co.conv K hK 0 delta hdelta
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  intro s hs
  rw [Real.dist_eq, abs_sub_comm]
  have hpoint := metricQuadFormDiff_le_metricDerivNorm (I := I)
    (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s))
    (co.gInf (T - s)) R (alpha s) (lVelocity (I := I) alpha s)
  have hsup := derivNorm_le_sup (I := I) hK (Nat.zero_le 0)
    (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s))
    (co.gInf (T - s)) R (show alpha s ∈ K from ⟨s, hs, rfl⟩)
  have hsmall := hk0 k hk (T - s) (hback hs)
  have hq0 : 0 ≤ q s := by
    by_cases hv0 : lVelocity (I := I) alpha s = 0
    · simp [q, hv0]
    · exact (R.pos (alpha s) (lVelocity (I := I) alpha s) hv0).le
  have hdim : (Module.finrank Real (TangentSpace I (alpha s)) : Real) = n := by
    rfl
  rw [hdim] at hpoint
  calc
    |(gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) -
        (co.gInf (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)|
        ≤ n * metricDerivNorm (I := I) 0
            (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s))
            (co.gInf (T - s)) R (alpha s) * q s := hpoint
    _ ≤ n * metricDerivNormSupOn (I := I) K 0
            (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s))
            (co.gInf (T - s)) R * q s := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsup hn) hq0
    _ ≤ n * delta * V := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hsmall.le hn) (hV s hs)
            hq0 (mul_nonneg hn hdelta.le)
    _ < epsilon := by
          have hdeltaEq : delta * (n * V + 1) = epsilon := by
            dsimp only [delta]
            exact div_mul_cancel₀ epsilon hden.ne'
          nlinarith

end KineticConv

section ChartGramConv

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Operator
open MeasureTheory

universe v vF vK

variable {F : Type vF} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [CompleteSpace F]
variable {KModel : Type vK} [TopologicalSpace KModel]
variable {J : ModelWithCorners Real F KModel} [J.Boundaryless]
variable {Y : PointedFlowSeq.{v, vF, vK} (I := J)}
variable {N : PointedRiemannianManifold.{v, vF, vK} (I := J)}
variable {subseq' : Nat → Nat}
variable (Psi : PointedCGHMaps (I := J) Y N subseq')

omit [J.Boundaryless] in
/-- Along compact-confined coordinate paths, the raw fixed-chart Gram
operators of the pointed metrics converge uniformly to those of the limit
metric. -/
theorem ConvOut.chartGram_convOn
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
      (fun k q ↦ chartGramOp (I := J)
        ((lcMetricFamily (I := J) (M := N.M)
          (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt (co.φ k) t)).restrict Y.D)
        alpha (tau q, u k q))
      (fun q ↦ chartGramOp (I := J)
        ((lcMetricFamily (I := J) (M := N.M) co.gInf).restrict Y.D)
        alpha (tau q, uLim q)) atTop := by
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
  have hKtgt : K ⊆ (extChartAt J alpha).target := hKchart.trans interior_subset
  let Kbase : Set N.M := (extChartAt J alpha).symm '' K
  have hKbase : IsCompact Kbase :=
    hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := J) alpha).mono hKtgt)
  obtain ⟨C, hC, hdiff⟩ :=
    chartGramOp_diff_le (I := J) (D := Y.D) R alpha hKc hKchart
  have hInf' : MetricFamilySmoothOn (I := J) (M := N.M) Y.D GInf.metric := by
    simpa only [GInf, MetricConnectionFamily.restrict_metric, lcMetricFamily] using hInf
  have hfixed : TendstoUniformly
      (fun k q ↦ chartGramOp (I := J) GInf alpha (tau q, u k q))
      (fun q ↦ chartGramOp (I := J) GInf alpha (tau q, uLim q)) atTop := by
    apply chartGramOp_unif (I := J) (G := GInf) hInf' hreg isCompact_Icc
      alpha hKchart hKc htau huK hlimK hu
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let eta : Real := epsilon / (2 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hC1)
  have hetaEq : (C + 1) * eta = epsilon / 2 := by
    dsimp only [eta]
    field_simp
  have hCeta : C * eta < epsilon / 2 := by
    calc
      C * eta < (C + 1) * eta :=
        mul_lt_mul_of_pos_right (lt_add_of_pos_right C zero_lt_one) heta
      _ = epsilon / 2 := hetaEq
  obtain ⟨k0, hk0⟩ := co.conv Kbase hKbase 0 eta heta
  have hmove := (Metric.tendstoUniformly_iff.1 hfixed) (epsilon / 2)
    (half_pos hepsilon)
  filter_upwards [Filter.eventually_ge_atTop k0, huK, hmove] with k hk huKk hmovek
  intro q
  have hx : (extChartAt J alpha).symm (u k q) ∈ Kbase :=
    ⟨u k q, huKk q, rfl⟩
  have hpoint := derivNorm_le_sup (I := J) hKbase (Nat.zero_le 0)
    ((GSeq k).metric (tau q)) (GInf.metric (tau q)) R hx
  have hsmall : metricDerivNormSupOn (I := J) Kbase 0
      ((GSeq k).metric (tau q)) (GInf.metric (tau q)) R < eta := by
    simpa only [GSeq, GInf, MetricConnectionFamily.restrict_metric,
      lcMetricFamily] using hk0 k hk (tau q) (htau q)
  have herr : dist
      (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
      (chartGramOp (I := J) GInf alpha (tau q, u k q)) < epsilon / 2 := by
    rw [dist_eq_norm]
    calc
      ‖chartGramOp (I := J) (GSeq k) alpha (tau q, u k q) -
          chartGramOp (I := J) GInf alpha (tau q, u k q)‖
          ≤ C * metricDerivNorm (I := J) 0
              ((GSeq k).metric (tau q)) (GInf.metric (tau q)) R
              ((extChartAt J alpha).symm (u k q)) :=
            hdiff (GSeq k) GInf (tau q, u k q) (huKk q)
      _ ≤ C * metricDerivNormSupOn (I := J) Kbase 0
              ((GSeq k).metric (tau q)) (GInf.metric (tau q)) R :=
            mul_le_mul_of_nonneg_left hpoint hC
      _ ≤ C * eta := mul_le_mul_of_nonneg_left hsmall.le hC
      _ < epsilon / 2 := hCeta
  rw [dist_comm]
  change dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
      (chartGramOp (I := J) GInf alpha (tau q, uLim q)) < epsilon
  calc
    dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
        (chartGramOp (I := J) GInf alpha (tau q, uLim q))
        ≤ dist (chartGramOp (I := J) (GSeq k) alpha (tau q, u k q))
            (chartGramOp (I := J) GInf alpha (tau q, u k q)) +
          dist (chartGramOp (I := J) GInf alpha (tau q, u k q))
            (chartGramOp (I := J) GInf alpha (tau q, uLim q)) := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 :=
      add_lt_add herr (by simpa only [dist_comm] using hmovek q)
    _ = epsilon := by ring

private theorem gSeqGram_contOn
    (R : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      letI : IsManifold J ∞ N.M := N.smooth
      SmoothRiemannianMetric J N.M)
    (bf : BumpFamily (I := J) Psi) (hsrc : SrcSigma Psi) (htgt : TgtSigma Psi)
    (k : Nat) (alpha : N.M) {K : Set F}
    (hKchart : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      K ⊆ interior (extChartAt J alpha).target) :
    letI : TopologicalSpace N.M := N.topology
    letI : ChartedSpace KModel N.M := N.charted
    letI : T2Space N.M := N.t2
    letI : IsManifold J ∞ N.M := N.smooth
    letI : SigmaCompactSpace N.M := N.sigmaCompact
    ContinuousOn
      (chartGramOp (I := J)
        ((lcMetricFamily (I := J) (M := N.M)
          (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt k t)).restrict Y.D)
        alpha)
      (Y.D.carrier ×ˢ K) := by
  classical
  letI : TopologicalSpace N.M := N.topology
  letI : ChartedSpace KModel N.M := N.charted
  letI : T2Space N.M := N.t2
  letI : IsManifold J ∞ N.M := N.smooth
  letI : SigmaCompactSpace N.M := N.sigmaCompact
  let G : MetricConnectionFamilyOn (I := J) (M := N.M) Y.D :=
    (lcMetricFamily (I := J) (M := N.M)
      (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt k t)).restrict Y.D
  have hKtgt : K ⊆ (extChartAt J alpha).target := hKchart.trans interior_subset
  have hpair : ContinuousOn
      (fun p : Real × F ↦ (p.1, (extChartAt J alpha).symm p.2))
      (Y.D.carrier ×ˢ K) := by
    exact continuousOn_fst.prodMk
      (((continuousOn_extChartAt_symm (I := J) alpha).mono hKtgt).comp
        continuousOn_snd (fun p hp ↦ hp.2))
  have hpairMem : MapsTo
      (fun p : Real × F ↦ (p.1, (extChartAt J alpha).symm p.2))
      (Y.D.carrier ×ˢ K)
      (Y.D.carrier ×ˢ
        (trivializationAt F (TangentSpace J) alpha).baseSet) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hsrc' := (extChartAt J alpha).map_target (hKtgt hp.2)
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hsrc'
  have hentry : ∀ i j : Fin (Module.finrank Real F),
      ContinuousOn
        (fun p : Real × F ↦
          chartGramOnE (I := J) (G.metric p.1) alpha i j p.2)
        (Y.D.carrier ×ˢ K) := by
    intro i j
    simpa only [G, MetricConnectionFamily.restrict_metric, lcMetricFamily,
      chartGramOnE_def] using
      (gSeqExt_gram_cont (I := J) Psi R bf hsrc htgt k alpha i j).comp
        hpair hpairMem
  have hbilin : ContinuousOn
      (fun p : Real × F ↦
        chartGramBilin (E := F) (I := J) (M := N.M) (G.metric p.1) alpha
          ((extChartAt J alpha).symm p.2))
      (Y.D.carrier ×ˢ K) := by
    change ContinuousOn
      (fun p : Real × F ↦
        ∑ i : Fin (Module.finrank Real F), ∑ j : Fin (Module.finrank Real F),
          chartGramOnE (I := J) (G.metric p.1) alpha i j p.2 •
            (chartCoordCLM F i).smulRight (chartCoordCLM F j))
      (Y.D.carrier ×ˢ K)
    exact continuousOn_finset_sum _ fun i _ ↦
      continuousOn_finset_sum _ fun j _ ↦ (hentry i j).smul continuousOn_const
  exact (IsCoercive.gramCLM (F := F)).continuous.comp_continuousOn hbilin

/-- Fixed-chart kinetic energy is lower semicontinuous for weakly convergent
coordinate velocities when both the pointed metrics and the coordinate paths
vary along the pointed-convergence subsequence. -/
theorem ConvOut.chartKin_liminf
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
    (alpha : N.M) {L : Real} (hL : 0 ≤ L) (tau : Real → Real)
    (htauCont : ContinuousOn tau (Icc (0 : Real) L))
    (htau : MapsTo tau (Icc (0 : Real) L) (Icc beta psi))
    {K : Set F} (hKc : IsCompact K)
    (hKchart : letI : TopologicalSpace N.M := N.topology
      letI : ChartedSpace KModel N.M := N.charted
      K ⊆ interior (extChartAt J alpha).target)
    (u : Nat → timeH1 F L) (uLim : timeH1 F L)
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) L, uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 F L,
      Tendsto (fun n ↦ inner Real (u n).deriv z) atTop
        (nhds (inner Real uLim.deriv z))) :
    letI : TopologicalSpace N.M := N.topology
    letI : ChartedSpace KModel N.M := N.charted
    letI : T2Space N.M := N.t2
    letI : IsManifold J ∞ N.M := N.smooth
    letI : SigmaCompactSpace N.M := N.sigmaCompact
    (∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := J)
          ((lcMetricFamily (I := J) (M := N.M) co.gInf).restrict Y.D)
          alpha (tau r, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) ≤
      liminf (fun n ↦ ∫ r in (0 : Real)..L,
        (1 / 2 : Real) * inner Real
          (chartGramOp (I := J)
            ((lcMetricFamily (I := J) (M := N.M)
              (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt (co.φ n) t)).restrict Y.D)
            alpha (tau r, (u n).toFun r) ((u n).deriv r))
          ((u n).deriv r)) atTop := by
  classical
  letI : TopologicalSpace N.M := N.topology
  letI : ChartedSpace KModel N.M := N.charted
  letI : T2Space N.M := N.t2
  letI : IsManifold J ∞ N.M := N.smooth
  letI : SigmaCompactSpace N.M := N.sigmaCompact
  let GSeq : Nat → MetricConnectionFamilyOn (I := J) (M := N.M) Y.D := fun n ↦
    (lcMetricFamily (I := J) (M := N.M)
      (fun t ↦ gSeqExt (I := J) Psi R bf hsrc htgt (co.φ n) t)).restrict Y.D
  let GInf : MetricConnectionFamilyOn (I := J) (M := N.M) Y.D :=
    (lcMetricFamily (I := J) (M := N.M) co.gInf).restrict Y.D
  let A : Nat → Real → F →L[Real] F := fun n r ↦
    (1 / 2 : Real) • chartGramOp (I := J) (GSeq n) alpha
      (tau r, (u n).toFun r)
  let ALim : Real → F →L[Real] F := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := J) GInf alpha
      (tau r, uLim.toFun r)
  have hpair (n : Nat) : ContinuousOn
      (fun r ↦ (tau r, (u n).toFun r)) (Icc (0 : Real) L) :=
    htauCont.prodMk (u n).continuousOn_toFun
  have hpairLim : ContinuousOn
      (fun r ↦ (tau r, uLim.toFun r)) (Icc (0 : Real) L) :=
    htauCont.prodMk uLim.continuousOn_toFun
  have hAcont (n : Nat) : ContinuousOn (A n) (Icc (0 : Real) L) := by
    apply ContinuousOn.const_smul
    exact (gSeqGram_contOn (J := J) (Y := Y) Psi R bf hsrc htgt
      (co.φ n) alpha hKchart).comp (hpair n) fun r hr ↦
        ⟨Y.D.regular_subset (hreg (htau hr)), huK n ⟨r, hr⟩⟩
  have hInf' : MetricFamilySmoothOn (I := J) (M := N.M) Y.D GInf.metric := by
    simpa only [GInf, MetricConnectionFamily.restrict_metric, lcMetricFamily] using hInf
  have hALimCont : ContinuousOn ALim (Icc (0 : Real) L) := by
    apply ContinuousOn.const_smul
    exact (chartGramOp_cont (I := J) hInf' hreg alpha hKchart).comp
      hpairLim fun r hr ↦ ⟨htau hr, huLimK ⟨r, hr⟩⟩
  have hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure L) := fun n ↦ by
    simpa only [timeMeasure] using
      (hAcont n).aestronglyMeasurable measurableSet_Icc
  have hALim : AEStronglyMeasurable ALim (timeMeasure L) := by
    simpa only [timeMeasure] using
      hALimCont.aestronglyMeasurable measurableSet_Icc
  have hAbound (n : Nat) : ∃ C : NNReal,
      ∀ r ∈ Icc (0 : Real) L, ‖A n r‖ ≤ (C : Real) := by
    obtain ⟨c, hc⟩ := isCompact_Icc.bddAbove_image (hAcont n).norm
    let C : NNReal := ⟨max c 0, le_max_right c 0⟩
    refine ⟨C, ?_⟩
    intro r hr
    change ‖A n r‖ ≤ max c 0
    exact (hc ⟨r, hr, rfl⟩).trans (le_max_left c 0)
  choose C hCpt using hAbound
  have hC : ∀ n, ∀ᵐ r ∂timeMeasure L, ‖A n r‖ ≤ (C n : Real) := fun n ↦ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hCpt n r hr
  obtain ⟨cLim, hcLim⟩ := isCompact_Icc.bddAbove_image hALimCont.norm
  let CLim : NNReal := ⟨max cLim 0, le_max_right cLim 0⟩
  have hCLim : ∀ᵐ r ∂timeMeasure L, ‖ALim r‖ ≤ (CLim : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    change ‖ALim r‖ ≤ max cLim 0
    exact (hcLim ⟨r, hr, rfl⟩).trans (le_max_left cLim 0)
  have hGramUnif : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦
        chartGramOp (I := J) (GSeq n) alpha
          (tau r.1, (u n).toFun r.1))
      (fun r ↦ chartGramOp (I := J) GInf alpha
        (tau r.1, uLim.toFun r.1)) atTop := by
    simpa only [GSeq, GInf] using
      (ConvOut.chartGram_convOn (J := J) (Y := Y) Psi R bf hsrc htgt
        beta psi co hInf hreg alpha hKchart hKc
        (tau := fun r : Icc (0 : Real) L ↦ tau r.1)
        (u := fun n r ↦ (u n).toFun r.1)
        (uLim := fun r ↦ uLim.toFun r.1)
        (fun r ↦ htau r.2) (Eventually.of_forall huK) huLimK hu)
  have hconv : ∀ delta : Real, 0 < delta → ∀ᶠ n in atTop,
      ∀ᵐ r ∂timeMeasure L, ‖A n r - ALim r‖ ≤ delta := by
    intro delta hdelta
    have hev := (Metric.tendstoUniformly_iff.1 hGramUnif) (2 * delta) (by positivity)
    filter_upwards [hev] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hraw := hn ⟨r, hr⟩
    have hraw' :
        ‖chartGramOp (I := J) (GSeq n) alpha (tau r, (u n).toFun r) -
          chartGramOp (I := J) GInf alpha (tau r, uLim.toFun r)‖ <
            2 * delta := by
      simpa only [dist_eq_norm, norm_sub_rev] using hraw
    dsimp only [A, ALim]
    rw [← smul_sub, norm_smul]
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    linarith
  have hself : ∀ n, ∀ᵐ r ∂timeMeasure L, IsSelfAdjoint (A n r) := fun n ↦
    Eventually.of_forall fun r ↦ by
      exact (IsSelfAdjoint.all (1 / 2 : Real)).smul
        (chartGramOp_self (I := J) (GSeq n) alpha (tau r, (u n).toFun r))
  have hpos : ∀ n, ∀ᵐ r ∂timeMeasure L, ∀ x,
      0 ≤ inner Real (A n r x) x := fun n ↦ Eventually.of_forall fun r x ↦ by
    dsimp only [A]
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := J) (GSeq n) alpha (tau r, (u n).toFun r) x)
  have hq := timeQuad_weak_unif A ALim hA hALim C CLim hC hCLim hconv
    hself hpos (fun n ↦ (u n).deriv) uLim.deriv hdu
  have hlimEq := timeQuad_eq_integral ALim hALim CLim hCLim hL uLim.deriv
  have hseqEq :
      (fun n ↦ timeQuad (A n) (hA n) (C n) (hC n) (u n).deriv) =
        (fun n ↦ ∫ r in (0 : Real)..L,
          inner Real (A n r ((u n).deriv r)) ((u n).deriv r)) := by
    funext n
    exact timeQuad_eq_integral (A n) (hA n) (C n) (hC n) hL (u n).deriv
  rw [hlimEq, hseqEq] at hq
  dsimp only [A, ALim, GSeq, GInf] at hq
  simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left] using hq

end ChartGramConv

end DifferentialGeometry.HCGCompactness
