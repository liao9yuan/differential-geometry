import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CompleteMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SegmentDensity

set_option autoImplicit false

/-!
# Complete-flow same-clock action attainability

This file turns the regularized minimizer on a complete bounded-curvature
Ricci flow into an attainer for the finite-action same-clock segment value.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} {H : Type uH} {D : RealTimeInterval}

section SegmentBridge

variable [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M] [ConnectedSpace M]

omit [FiniteDimensional Real E] in
private theorem c1On_lip_Icc
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (alpha : Real → M)
    (halpha : ContMDiffOn 𝓘(Real, Real) I 1 alpha (Icc a b)) :
    letI : PseudoMetricSpace M := lSegmentMetric S T
    ∃ K, LipschitzOnWith K alpha (Icc a b) := by
  let g := S.base.metric T
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI : PseudoMetricSpace M := lSegmentMetric S T
  have hloc : LocallyLipschitzOn (Icc a b) alpha := by
    intro t ht
    rcases DifferentialGeometry.Geometry.Riemannian.chart_symm_edist_le
        (I := I) (alpha t) with ⟨C, _hC, R, hR, hchart⟩
    let F := extChartAt I (alpha t) ∘ alpha
    have hF : ContDiffWithinAt Real 1 F (Icc a b) t := by
      apply ContMDiffWithinAt.contDiffWithinAt
      simpa only [F] using
        (contMDiffAt_extChartAt (I := I) (x := alpha t) (n := 1)).comp_contMDiffWithinAt
          t (halpha t ht)
    obtain ⟨K, v, hv, hKv⟩ :=
      hF.exists_lipschitzOnWith (convex_Icc a b)
    have hsrc :
        alpha ⁻¹' (extChartAt I (alpha t)).source ∈ 𝓝[Icc a b] t := by
      apply (halpha t ht).continuousWithinAt.preimage_mem_nhdsWithin
      exact extChartAt_source_mem_nhds (I := I) (alpha t)
    have hF0 : F t = extChartAt I (alpha t) (alpha t) := by
      simp only [F, Function.comp_apply]
    have hball :
        F ⁻¹' Metric.ball (extChartAt I (alpha t) (alpha t)) R ∈
          𝓝[Icc a b] t := by
      apply hF.continuousWithinAt.preimage_mem_nhdsWithin
      simpa only [hF0] using
        Metric.ball_mem_nhds (extChartAt I (alpha t) (alpha t)) hR
    let s := v ∩ alpha ⁻¹' (extChartAt I (alpha t)).source ∩
      F ⁻¹' Metric.ball (extChartAt I (alpha t) (alpha t)) R
    have hs : s ∈ 𝓝[Icc a b] t := inter_mem (inter_mem hv hsrc) hball
    refine ⟨C * K, s, hs, ?_⟩
    intro y hy z hz
    rcases hy with ⟨⟨hyv, hySrc⟩, hyBall⟩
    rcases hz with ⟨⟨hzv, hzSrc⟩, hzBall⟩
    have hyRange : F y ∈ range I :=
      extChartAt_target_subset_range (alpha t)
        ((extChartAt I (alpha t)).map_source hySrc)
    have hzRange : F z ∈ range I :=
      extChartAt_target_subset_range (alpha t)
        ((extChartAt I (alpha t)).map_source hzSrc)
    have hyInv : (extChartAt I (alpha t)).symm (F y) = alpha y := by
      simpa only [F, Function.comp_apply] using
        (extChartAt I (alpha t)).left_inv hySrc
    have hzInv : (extChartAt I (alpha t)).symm (F z) = alpha z := by
      simpa only [F, Function.comp_apply] using
        (extChartAt I (alpha t)).left_inv hzSrc
    rw [IsRiemannianManifold.out (I := I) (alpha y) (alpha z),
      ← hyInv, ← hzInv]
    refine (hchart (F y) ⟨hyBall, hyRange⟩
      (F z) ⟨hzBall, hzRange⟩).trans ?_
    calc
      (C : ENNReal) * edist (F y) (F z) ≤
          C * (K * edist y z) := mul_right_mono (hKv hyv hzv)
      _ = (C * K) * edist y z := by simp only [mul_assoc]
  exact hloc.exists_lipschitzOnWith_of_compact isCompact_Icc

/-- A curve that is `C1` only on a nonnegative compact square-root-time
interval still defines a finite-action same-clock segment after squaring time. -/
theorem lSegCurve_sqrtOn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : Real → M)
    (halpha : ContMDiffOn 𝓘(Real, Real) I 1 alpha (Icc a b))
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω) :
    IsLSegCurve S T Ω (a ^ 2) (b ^ 2) (sqrtReparam alpha) := by
  have habSq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha (ha.trans hab)).2 hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI : PseudoMetricSpace M := lSegmentMetric S T
    change AbsolutelyContinuousOnInterval
      (sqrtReparam alpha) (a ^ 2) (b ^ 2)
    obtain ⟨K, hLip⟩ := c1On_lip_Icc (I := I) S T a b alpha halpha
    have hMaps : MapsTo Real.sqrt (uIcc (a ^ 2) (b ^ 2)) (Icc a b) := by
      intro tau htau
      rw [uIcc_of_le habSq] at htau
      refine ⟨Real.le_sqrt_of_sq_le htau.1, ?_⟩
      have hroot := Real.sqrt_le_sqrt htau.2
      simpa only [Real.sqrt_sq (ha.trans hab)] using hroot
    simpa only [sqrtReparam, Function.comp_def] using
      AbsolutelyContinuousOnInterval.comp_lipschitzOn hLip
        (AbsolutelyContinuousOnInterval.Real.sqrt_ac_sq ha hab) hMaps
  · rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with tau htau
    intro htauIcc
    have htauIoo : tau ∈ Ioo (a ^ 2) (b ^ 2) := htau.mpr htauIcc
    have htauPos : 0 < tau := (sq_nonneg a).trans_lt htauIoo.1
    have hsqrt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
        Real.sqrt tau :=
      mdifferentiableAt_iff_differentiableAt.mpr
        (Real.hasDerivAt_sqrt htauPos.ne').differentiableAt
    have hsIoo : Real.sqrt tau ∈ Ioo a b := by
      refine ⟨(Real.lt_sqrt ha).2 htauIoo.1, ?_⟩
      exact (Real.sqrt_lt htauPos.le (ha.trans hab)).2 htauIoo.2
    have halphaAt : MDifferentiableAt 𝓘(Real, Real) I alpha
        (Real.sqrt tau) :=
      ((halpha (Real.sqrt tau) ⟨hsIoo.1.le, hsIoo.2.le⟩).contMDiffAt
        (Icc_mem_nhds hsIoo.1 hsIoo.2)).mdifferentiableAt (by norm_num)
    simpa only [sqrtReparam] using halphaAt.comp tau hsqrt
  · let gamma : Real → M := sqrtReparam alpha
    have hChange :=
      intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
        (g := lDensity S T gamma) (f := fun s : Real ↦ s ^ 2)
        (f' := fun s : Real ↦ 2 * s) (a := a) (b := b)
        (continuous_id.pow 2).continuousOn
        (by
          intro s _
          simpa using hasDerivAt_pow 2 s)
        (by
          intro s hs
          have hsa : a < s := by
            simpa only [min_eq_left hab] using hs.1
          exact mul_nonneg (by norm_num) (ha.trans hsa.le))
    apply hChange.mp
    refine hLag.congr ?_
    intro s hs
    have hsIoc : s ∈ Ioc a b := by
      simpa only [uIoc_of_le hab] using hs
    have hsPos : 0 < s := ha.trans_lt hsIoc.1
    have hdens := lDensity_sq_pos (I := I) S T gamma s hsPos
    have hev : sqReparam gamma =ᶠ[𝓝 s] alpha := by
      filter_upwards [Ioi_mem_nhds hsPos] with r hr
      simp only [sqReparam, gamma, sqrtReparam, Real.sqrt_sq hr.le]
    have hval : sqReparam gamma s = alpha s := hev.self_of_nhds
    have hmf :
        mfderiv 𝓘(Real, Real) I (sqReparam gamma) s =
          mfderiv 𝓘(Real, Real) I alpha s :=
      Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) hev
    have hvel :
        lVelocity (I := I) (sqReparam gamma) s =
          lVelocity (I := I) alpha s := by
      simpa only [lVelocity] using
        congrArg (fun L ↦ L (1 : Real)) hmf
    calc
      lRegLag S T alpha s = lRegLag S T (sqReparam gamma) s := by
        simp only [lRegLag]
        rw [hval, hvel]
      _ = lRegDensity S T gamma s :=
        (lRegDensity_eq (I := I) S T gamma s).symm
      _ = (lDensity S T gamma ∘ fun r : Real ↦ r ^ 2) s * (2 * s) := by
        simpa only [Function.comp_apply] using hdens.symm
  · intro tau htau
    have htauNonneg : 0 ≤ tau := (sq_nonneg a).trans htau.1
    have hroot : Real.sqrt tau ∈ Icc a b := by
      refine ⟨Real.le_sqrt_of_sq_le htau.1, ?_⟩
      have hle := Real.sqrt_le_sqrt htau.2
      simpa only [Real.sqrt_sq (ha.trans hab)] using hle
    simpa only [sqrtReparam, Real.sq_sqrt htauNonneg] using
      hΩ (Real.sqrt tau) hroot

end SegmentBridge

section Complete

variable [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [ConnectedSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem scalar_lower_rm
    (S : SolutionOn (I := I) (M := M) D) (K T a b : Real)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K) :
    ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) ≤
        S.scalar (T - tau) z := by
  intro tau htau z
  have ht : T - tau ∈ Icc (T - b ^ 2) T := by
    exact ⟨sub_le_sub_left htau.2 T,
      sub_le_self T ((sq_nonneg a).trans htau.1)⟩
  have hs := scalar_abs_le_rm (I := I) (S.base.metric (T - tau)) z
  have hs' : |S.scalar (T - tau) z| ≤
      (Module.finrank Real E : Real) ^ 2 * Real.sqrt K := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar,
      SolutionFamily.rm04, metricRm04_apply] using
      hs.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hRm _ ht z)) (sq_nonneg _))
  exact neg_le_of_abs_le hs'

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private theorem lSegAtt_of_reg
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K0 T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K0 ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha0 gamma : Real → M)
    (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc a b))
    (hga : gamma a = x) (hgb : gamma b = y)
    (hcost : lRegAction S T gamma a b = lRegCostC1 S T a b x y) :
    IsLSegAttainer S T Set.univ (a ^ 2) (b ^ 2) x y
      (sqrtReparam gamma) := by
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hb : 0 ≤ b := ha.trans hab
  have hLag : IntervalIntegrable (lRegLag S T gamma) volume a b :=
    lRegLag_int_c1 (I := I) S hMet hSc T a b hab gamma hgamma hreg
  have hseg : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2)
      (sqrtReparam gamma) :=
    lSegCurve_sqrtOn (I := I) S T Set.univ a b ha hab gamma hgamma
      hLag (by simp)
  have hvalue :=
    lSegValue_eq_reg (I := I) S hMet hSc T K0 a b ha hab
      hR hreg x y alpha0 halpha0 h0a h0b
  refine ⟨hseg, ?_, ?_, ?_⟩
  · simpa only [sqrtReparam, Real.sqrt_sq ha] using hga
  · simpa only [sqrtReparam, Real.sqrt_sq hb] using hgb
  · calc
      lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y =
          (lRegCostC1 S T a b x y : WithTop Real) := hvalue
      _ = (lRegAction S T gamma a b : WithTop Real) :=
        congrArg (fun r : Real ↦ (r : WithTop Real)) hcost.symm
      _ = (lLength S T (sqrtReparam gamma)
          (a ^ 2) (b ^ 2) : WithTop Real) :=
        congrArg (fun r : Real ↦ (r : WithTop Real))
          (lLength_sqrt_Icc (I := I) S T gamma a b ha hab).symm

/-- On a complete bounded-curvature flow, the regularized minimizer attains
the finite-action same-clock segment value on every nondegenerate nonnegative
square-root-time interval with a supplied endpoint competitor. -/
theorem exists_lSegAtt_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b : Real) (ha : 0 ≤ a) (hab : a < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    ∃ gamma : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc a b) ∧
        IsLSegAttainer S T Set.univ (a ^ 2) (b ^ 2) x y
          (sqrtReparam gamma) := by
  let K0 : Real :=
    (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  have hb : 0 ≤ b := ha.trans hab.le
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  obtain ⟨gamma, _hcont, hgamma, hga, hgb, hcost, _hmin, _hsol⟩ :=
    exists_lRegMin_rm (I := I) S hS K T hg a b ha hab hreg hRm
      x y alpha0 halpha0 h0a h0b
  have hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K0 ≤ S.scalar (T - tau) z := by
    simpa only [K0] using scalar_lower_rm (I := I) S K T a b hRm
  refine ⟨gamma, hgamma, ?_⟩
  exact lSegAtt_of_reg (I := I) S hS K0 T a b ha hab.le hR hregBack
    x y alpha0 gamma halpha0 h0a h0b hgamma hga hgb hcost

end Complete

end DifferentialGeometry.PDE.RicciFlow.Perelman
