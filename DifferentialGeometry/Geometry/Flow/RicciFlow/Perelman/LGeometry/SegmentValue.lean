import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

/-!
# Same-clock finite-action segments

This file supplies the finite-action curve category, its exact restriction and
concatenation closure, the extended-real fixed-endpoint segment value, and its
same-clock dynamic-programming law for Perelman's L-action.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M] [ConnectedSpace M]
variable {D : RealTimeInterval}

/-- The fixed pole-time metric used to measure absolute continuity of
same-clock finite-action segments. -/
@[reducible] noncomputable def lSegmentMetric
    (S : SolutionOn (I := I) (M := M) D) (T : Real) : PseudoMetricSpace M :=
  let g := S.base.metric T
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace fun x y ↦
    DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
      (I := I) x y

private def lSegmentAC
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (gamma : Real → M) : Prop :=
  letI : PseudoMetricSpace M := lSegmentMetric S T
  AbsolutelyContinuousOnInterval gamma a b

/-- A finite-action same-clock L-curve confined to a spacetime set.  Absolute
continuity is measured using the flow metric at the fixed pole time. -/
def IsLSegCurve
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (gamma : Real → M) : Prop :=
  lSegmentAC S T a b gamma ∧
    (∀ᵐ s ∂volume.restrict (Icc a b),
      MDifferentiableAt 𝓘(Real, Real) I gamma s) ∧
    IntervalIntegrable (lDensity S T gamma) volume a b ∧
    ∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ω

/-- The absolute-continuity field of a finite-action same-clock segment. -/
theorem IsLSegCurve.ac
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Ω a b gamma) :
    letI : PseudoMetricSpace M := lSegmentMetric S T
    AbsolutelyContinuousOnInterval gamma a b :=
  hgamma.1

omit [FiniteDimensional Real E] in
private theorem c1_lip_Icc
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (alpha : Real → M)
    (halpha : ContMDiff 𝓘(Real, Real) I 1 alpha) :
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
    intro t _ht
    rcases DifferentialGeometry.Geometry.Riemannian.chart_symm_edist_le
        (I := I) (alpha t) with ⟨C, _hC, R, hR, hchart⟩
    let F := extChartAt I (alpha t) ∘ alpha
    have hF : ContDiffAt Real 1 F t := by
      apply contMDiffAt_iff_contDiffAt.mp
      simpa only [F] using
        (contMDiffAt_extChartAt (I := I) (x := alpha t) (n := 1)).comp t
          halpha.contMDiffAt
    obtain ⟨K, u, hu, hKu⟩ := hF.exists_lipschitzOnWith
    have hsrc :
        alpha ⁻¹' (extChartAt I (alpha t)).source ∈ 𝓝 t := by
      apply halpha.continuous.continuousAt.preimage_mem_nhds
      exact extChartAt_source_mem_nhds (I := I) (alpha t)
    have hF0 : F t = extChartAt I (alpha t) (alpha t) := by
      simp only [F, Function.comp_apply]
    have hball :
        F ⁻¹' Metric.ball (extChartAt I (alpha t) (alpha t)) R ∈ 𝓝 t := by
      apply hF.continuousAt.preimage_mem_nhds
      simpa only [hF0] using
        Metric.ball_mem_nhds (extChartAt I (alpha t) (alpha t)) hR
    let s := u ∩ alpha ⁻¹' (extChartAt I (alpha t)).source ∩
      F ⁻¹' Metric.ball (extChartAt I (alpha t) (alpha t)) R
    have hs : s ∈ 𝓝 t := inter_mem (inter_mem hu hsrc) hball
    refine ⟨C * K, s, mem_nhdsWithin_of_mem_nhds hs, ?_⟩
    intro y hy z hz
    rcases hy with ⟨⟨hyu, hySrc⟩, hyBall⟩
    rcases hz with ⟨⟨hzu, hzSrc⟩, hzBall⟩
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
          C * (K * edist y z) := mul_right_mono (hKu hyu hzu)
      _ = (C * K) * edist y z := by simp only [mul_assoc]
  exact hloc.exists_lipschitzOnWith_of_compact isCompact_Icc

/-- A global C1 square-root-time curve with integrable regularized Lagrangian
defines a finite-action same-clock segment on the squared interval. -/
theorem lSegCurve_sqrt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : Real → M)
    (halpha : ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω) :
    IsLSegCurve S T Ω (a ^ 2) (b ^ 2) (sqrtReparam alpha) := by
  have habSq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha (ha.trans hab)).2 hab
  change lSegmentAC S T (a ^ 2) (b ^ 2) (sqrtReparam alpha) ∧
    (∀ᵐ tau ∂volume.restrict (Icc (a ^ 2) (b ^ 2)),
      MDifferentiableAt 𝓘(Real, Real) I (sqrtReparam alpha) tau) ∧
    IntervalIntegrable (lDensity S T (sqrtReparam alpha)) volume
      (a ^ 2) (b ^ 2) ∧
    ∀ tau ∈ Icc (a ^ 2) (b ^ 2),
      (sqrtReparam alpha tau, T - tau) ∈ Ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI : PseudoMetricSpace M := lSegmentMetric S T
    change AbsolutelyContinuousOnInterval
      (sqrtReparam alpha) (a ^ 2) (b ^ 2)
    obtain ⟨K, hLip⟩ := c1_lip_Icc (I := I) S T a b alpha halpha
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
    simpa only [sqrtReparam] using
      (halpha.mdifferentiableAt (by norm_num)).comp tau hsqrt
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

/-- A finite-action same-clock curve remains admissible after restricting its
parameter interval. -/
theorem lSegCurve_restrict
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) {a b c d : Real} {gamma : Real → M}
    (hab : a ≤ b) (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (hgamma : IsLSegCurve S T Ω a b gamma) :
    IsLSegCurve S T Ω c d gamma := by
  change lSegmentAC S T a b gamma ∧
      (∀ᵐ s ∂volume.restrict (Icc a b),
        MDifferentiableAt 𝓘(Real, Real) I gamma s) ∧
      IntervalIntegrable (lDensity S T gamma) volume a b ∧
      (∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ω) at hgamma
  change lSegmentAC S T c d gamma ∧
      (∀ᵐ s ∂volume.restrict (Icc c d),
        MDifferentiableAt 𝓘(Real, Real) I gamma s) ∧
      IntervalIntegrable (lDensity S T gamma) volume c d ∧
      ∀ s ∈ Icc c d, (gamma s, T - s) ∈ Ω
  rcases hgamma with ⟨hAC, hDiff, hInt, hΩ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI : PseudoMetricSpace M := lSegmentMetric S T
    change AbsolutelyContinuousOnInterval gamma a b at hAC
    change AbsolutelyContinuousOnInterval gamma c d
    exact hAC.mono (by
      simpa only [uIcc_of_le hcd, uIcc_of_le hab] using hsub)
  · exact ae_mono (Measure.restrict_mono hsub le_rfl) hDiff
  · exact hInt.mono_set (by
      simpa only [uIcc_of_le hcd, uIcc_of_le hab] using hsub)
  · intro s hs
    exact hΩ s (hsub hs)

/-- Same-clock finite-action curves with a common endpoint can be pasted on
adjacent intervals without leaving their spacetime confinement set. -/
theorem lSegCurve_join
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) {a b c : Real} {gamma eta : Real → M}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hgamma : IsLSegCurve S T Ω a b gamma)
    (heta : IsLSegCurve S T Ω b c eta)
    (hnode : gamma b = eta b) :
    IsLSegCurve S T Ω a c (Set.piecewise (Set.Iic b) gamma eta) := by
  classical
  change lSegmentAC S T a b gamma ∧
      (∀ᵐ s ∂volume.restrict (Icc a b),
        MDifferentiableAt 𝓘(Real, Real) I gamma s) ∧
      IntervalIntegrable (lDensity S T gamma) volume a b ∧
      (∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ω) at hgamma
  change lSegmentAC S T b c eta ∧
      (∀ᵐ s ∂volume.restrict (Icc b c),
        MDifferentiableAt 𝓘(Real, Real) I eta s) ∧
      IntervalIntegrable (lDensity S T eta) volume b c ∧
      (∀ s ∈ Icc b c, (eta s, T - s) ∈ Ω) at heta
  change lSegmentAC S T a c (Set.piecewise (Set.Iic b) gamma eta) ∧
    (∀ᵐ s ∂volume.restrict (Icc a c),
      MDifferentiableAt 𝓘(Real, Real) I
        (Set.piecewise (Set.Iic b) gamma eta) s) ∧
    IntervalIntegrable
      (lDensity S T (Set.piecewise (Set.Iic b) gamma eta)) volume a c ∧
    ∀ s ∈ Icc a c,
      (Set.piecewise (Set.Iic b) gamma eta s, T - s) ∈ Ω
  rcases hgamma with ⟨hgammaAC, hgammaDiff, hgammaInt, hgammaΩ⟩
  rcases heta with ⟨hetaAC, hetaDiff, hetaInt, hetaΩ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI : PseudoMetricSpace M := lSegmentMetric S T
    change AbsolutelyContinuousOnInterval gamma a b at hgammaAC
    change AbsolutelyContinuousOnInterval eta b c at hetaAC
    change AbsolutelyContinuousOnInterval
      (Set.piecewise (Set.Iic b) gamma eta) a c
    exact AbsolutelyContinuousOnInterval.piecewise_Iic
      hab hbc hgammaAC hetaAC hnode
  · have hgammaDiff' :
        ∀ᵐ s ∂volume, s ∈ Icc a b →
          MDifferentiableAt 𝓘(Real, Real) I gamma s :=
      (ae_restrict_iff' measurableSet_Icc).mp hgammaDiff
    have hetaDiff' :
        ∀ᵐ s ∂volume, s ∈ Icc b c →
          MDifferentiableAt 𝓘(Real, Real) I eta s :=
      (ae_restrict_iff' measurableSet_Icc).mp hetaDiff
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        ae_mono Measure.restrict_le_self hgammaDiff',
        ae_mono Measure.restrict_le_self hetaDiff',
        Measure.ae_ne (volume.restrict (Icc a c)) b]
        with s hs hsGamma hsEta hsb
    by_cases hleft : s ≤ b
    · have hslt : s < b := lt_of_le_of_ne hleft hsb
      apply (hsGamma ⟨hs.1, hleft⟩).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hslt] with r hr
      exact (Set.piecewise_eq_of_mem (Set.Iic b) gamma eta
        (Set.mem_Iic.mpr hr.le))
    · have hright : b < s := lt_of_not_ge hleft
      apply (hsEta ⟨hright.le, hs.2⟩).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hright] with r hr
      exact (Set.piecewise_eq_of_notMem (Set.Iic b) gamma eta
        (by simpa only [Set.mem_Iic] using not_le_of_gt hr))
  · let joined : Real → M := Set.piecewise (Set.Iic b) gamma eta
    have hleft_ae :
        lDensity S T gamma =ᵐ[volume.restrict (Set.uIoc a b)]
          lDensity S T joined := by
      filter_upwards
        [ae_restrict_mem measurableSet_uIoc,
          Measure.ae_ne (volume.restrict (Set.uIoc a b)) b]
          with s hs hsb
      have hs' : s ∈ Set.Ioc a b := by
        simpa only [Set.uIoc_of_le hab] using hs
      have hslt : s < b := lt_of_le_of_ne hs'.2 hsb
      apply lDensity_congr S T s
      filter_upwards [Iio_mem_nhds hslt] with r hr
      exact ((Set.Iic b).piecewise_eq_of_mem gamma eta
        (Set.mem_Iic.mpr hr.le)).symm
    have hright_ae :
        lDensity S T eta =ᵐ[volume.restrict (Set.uIoc b c)]
          lDensity S T joined := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs' : s ∈ Set.Ioc b c := by
        simpa only [Set.uIoc_of_le hbc] using hs
      apply lDensity_congr S T s
      filter_upwards [Ioi_mem_nhds hs'.1] with r hr
      exact ((Set.Iic b).piecewise_eq_of_notMem gamma eta
        (by simpa only [Set.mem_Iic] using not_le_of_gt hr)).symm
    exact (hgammaInt.congr_ae hleft_ae).trans
      (hetaInt.congr_ae hright_ae)
  · intro s hs
    by_cases hleft : s ≤ b
    · rw [Set.piecewise_eq_of_mem (Set.Iic b) gamma eta hleft]
      exact hgammaΩ s ⟨hs.1, hleft⟩
    · rw [Set.piecewise_eq_of_notMem (Set.Iic b) gamma eta hleft]
      exact hetaΩ s ⟨le_of_not_ge hleft, hs.2⟩

omit [RegularSpace M] [ConnectedSpace M] in
/-- A scalar lower bound along a nonnegative backward-time segment gives the
uniform lower bound for its same-clock L-action. -/
theorem lLength_lower
    (S : SolutionOn (I := I) (M := M) D)
    (T a b K : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (gamma : Real → M)
    (hR : ∀ s ∈ Icc a b, -K ≤ S.scalar (T - s) (gamma s))
    (hInt : IntervalIntegrable (lDensity S T gamma) volume a b) :
    -(2 * K / 3) *
        (b * Real.sqrt b - a * Real.sqrt a) ≤
      lLength S T gamma a b := by
  have hb : 0 ≤ b := ha.trans hab
  have hsqrtInt :
      (∫ s in a..b, Real.sqrt s) =
        (2 / 3 : Real) *
          (b * Real.sqrt b - a * Real.sqrt a) := by
    have hbpow : b ^ ((1 / 2 : Real) + 1) = b * Real.sqrt b := by
      rw [Real.rpow_add' hb (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      ring
    have hapow : a ^ ((1 / 2 : Real) + 1) = a * Real.sqrt a := by
      rw [Real.rpow_add' ha (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      ring
    calc
      (∫ s in a..b, Real.sqrt s) =
          ∫ s in a..b, s ^ (1 / 2 : Real) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact Real.sqrt_eq_rpow s
      _ = (b ^ ((1 / 2 : Real) + 1) -
            a ^ ((1 / 2 : Real) + 1)) / ((1 / 2 : Real) + 1) :=
        integral_rpow (Or.inl (by norm_num))
      _ = (2 / 3 : Real) *
          (b * Real.sqrt b - a * Real.sqrt a) := by
        rw [hbpow, hapow]
        ring
  have hleftInt : IntervalIntegrable
      (fun s : Real ↦ -K * Real.sqrt s) volume a b :=
    (show Continuous (fun s : Real ↦ -K * Real.sqrt s) from
      continuous_const.mul Real.continuous_sqrt).intervalIntegrable
        (μ := volume) a b
  have hpoint : ∀ s ∈ Icc a b,
      -K * Real.sqrt s ≤ lDensity S T gamma s := by
    intro s hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    have hspeed : 0 ≤ lSpeedSq S T gamma s :=
      lSpeedSq_nonneg S T gamma s
    calc
      -K * Real.sqrt s = Real.sqrt s * (-K) := by ring
      _ ≤ Real.sqrt s *
          (S.scalar (T - s) (gamma s) + lSpeedSq S T gamma s) :=
        mul_le_mul_of_nonneg_left
          ((hR s hs).trans (le_add_of_nonneg_right hspeed))
          (Real.sqrt_nonneg s)
      _ = lDensity S T gamma s := rfl
  have hmono := intervalIntegral.integral_mono_on hab hleftInt hInt hpoint
  calc
    -(2 * K / 3) * (b * Real.sqrt b - a * Real.sqrt a) =
        -K * ((2 / 3 : Real) *
          (b * Real.sqrt b - a * Real.sqrt a)) := by ring
    _ = -K * (∫ s in a..b, Real.sqrt s) := by rw [hsqrtInt]
    _ = ∫ s in a..b, -K * Real.sqrt s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in a..b, lDensity S T gamma s := hmono
    _ = lLength S T gamma a b := rfl

private def lSegCosts
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (x y : M) : Set Real :=
  {r | ∃ gamma : Real → M,
    IsLSegCurve S T Ω a b gamma ∧
      gamma a = x ∧ gamma b = y ∧ lLength S T gamma a b = r}

private theorem lSegCosts_split
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) {a b c : Real}
    (hab : a ≤ b) (hbc : b ≤ c) (x z : M) :
    lSegCosts S T Ω a c x z =
      ⋃ y : M,
        Set.image2 (fun u v : Real ↦ u + v)
          (lSegCosts S T Ω a b x y)
          (lSegCosts S T Ω b c y z) := by
  classical
  have hac : a ≤ c := hab.trans hbc
  ext r
  constructor
  · rintro ⟨gamma, hgamma, hga, hgc, hr⟩
    have hleft : IsLSegCurve S T Ω a b gamma :=
      lSegCurve_restrict S T Ω hac hab
        (fun s hs ↦ ⟨hs.1, hs.2.trans hbc⟩) hgamma
    have hright : IsLSegCurve S T Ω b c gamma :=
      lSegCurve_restrict S T Ω hac hbc
        (fun s hs ↦ ⟨hab.trans hs.1, hs.2⟩) hgamma
    apply Set.mem_iUnion_of_mem (gamma b)
    refine ⟨lLength S T gamma a b, ?_,
      lLength S T gamma b c, ?_, ?_⟩
    · exact ⟨gamma, hleft, hga, rfl, rfl⟩
    · exact ⟨gamma, hright, rfl, hgc, rfl⟩
    · exact
        (lLength_add_adj S T gamma a b c
          hleft.2.2.1 hright.2.2.1).trans hr
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨y, hy⟩
    rcases hy with ⟨u, hu, v, hv, huv⟩
    rcases hu with ⟨gamma, hgamma, hga, hgb, hu⟩
    rcases hv with ⟨eta, heta, heb, hec, hv⟩
    refine ⟨Set.piecewise (Set.Iic b) gamma eta,
      lSegCurve_join S T Ω hab hbc hgamma heta
        (hgb.trans heb.symm), ?_, ?_, ?_⟩
    · rw [Set.piecewise_eq_of_mem (Set.Iic b) gamma eta hab]
      exact hga
    · by_cases hcb : c ≤ b
      · have hcb' : c = b := le_antisymm hcb hbc
        subst c
        rw [Set.piecewise_eq_of_mem
          (Set.Iic b) gamma eta (Set.mem_Iic.mpr le_rfl)]
        exact (hgb.trans heb.symm).trans hec
      · rw [Set.piecewise_eq_of_notMem
          (Set.Iic b) gamma eta hcb]
        exact hec
    · calc
        lLength S T
            (Set.piecewise (Set.Iic b) gamma eta) a c =
            lLength S T gamma a b +
              lLength S T eta b c :=
          lLength_join S T a b c gamma eta hab hbc
            hgamma.2.2.1 heta.2.2.1
        _ = u + v := congrArg₂ (· + ·) hu hv
        _ = r := huv

/-- The extended-real infimum of L-actions of admissible curves with fixed
endpoints and spacetime confinement. -/
def lSegValue
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (x y : M) : WithTop Real :=
  sInf ((fun r : Real ↦ (r : WithTop Real)) '' lSegCosts S T Ω a b x y)

/-- A lower bound for every admissible fixed-endpoint action is a lower bound
for the extended-real segment value. -/
theorem le_lSegValue
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (x y : M)
    (A : WithTop Real)
    (hA : ∀ gamma : Real → M,
      IsLSegCurve S T Ω a b gamma →
      gamma a = x → gamma b = y →
      A ≤ (lLength S T gamma a b : WithTop Real)) :
    A ≤ lSegValue S T Ω a b x y := by
  unfold lSegValue
  by_cases hne : (lSegCosts S T Ω a b x y).Nonempty
  · apply le_csInf (hne.image fun r : Real ↦ (r : WithTop Real))
    intro q hq
    rcases hq with ⟨r, hr, rfl⟩
    rcases hr with ⟨gamma, hgamma, hxa, hyb, rfl⟩
    exact hA gamma hgamma hxa hyb
  · have hempty : lSegCosts S T Ω a b x y = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Set.image_empty, WithTop.sInf_empty]
    exact le_top

/-- A restricted segment attainer is an admissible fixed-endpoint curve whose
actual L-action realizes the extended-real segment value. -/
def IsLSegAttainer
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (x y : M)
    (gamma : Real → M) : Prop :=
  IsLSegCurve S T Ω a b gamma ∧
    gamma a = x ∧ gamma b = y ∧
      lSegValue S T Ω a b x y = (lLength S T gamma a b : WithTop Real)

private theorem lSegCosts_bdd
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1) (x y : M) :
    BddBelow (lSegCosts S T Ω a b x y) := by
  refine ⟨-(2 * K / 3) *
    (b * Real.sqrt b - a * Real.sqrt a), ?_⟩
  intro r hr
  rcases hr with ⟨gamma, hgamma, _, _, rfl⟩
  rcases hgamma with ⟨_, _, hInt, hΩ⟩
  exact lLength_lower S T a b K ha hab gamma
    (fun s hs ↦ hR (gamma s, T - s) (hΩ s hs)) hInt

private theorem lSegValue_add
    (S : SolutionOn (I := I) (M := M) D)
    (T K : Real) (Ω : Set (M × Real))
    {a b c : Real} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y z : M) :
    lSegValue S T Ω a b x y +
        lSegValue S T Ω b c y z =
      sInf ((fun r : Real ↦ (r : WithTop Real)) ''
        Set.image2 (fun u v : Real ↦ u + v)
          (lSegCosts S T Ω a b x y)
          (lSegCosts S T Ω b c y z)) := by
  classical
  let A := lSegCosts S T Ω a b x y
  let B := lSegCosts S T Ω b c y z
  change
    sInf ((fun r : Real ↦ (r : WithTop Real)) '' A) +
        sInf ((fun r : Real ↦ (r : WithTop Real)) '' B) =
      sInf ((fun r : Real ↦ (r : WithTop Real)) ''
        Set.image2 (fun u v : Real ↦ u + v) A B)
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hb : 0 ≤ b := ha.trans hab
      have hAbdd : BddBelow A :=
        lSegCosts_bdd S T K Ω ha hab hR x y
      have hBbdd : BddBelow B :=
        lSegCosts_bdd S T K Ω hb hbc hR y z
      have hAB :
          (Set.image2 (fun u v : Real ↦ u + v) A B).Nonempty :=
        hA.image2 hB
      have hABbdd :
          BddBelow (Set.image2 (fun u v : Real ↦ u + v) A B) := by
        rcases hAbdd with ⟨p, hp⟩
        rcases hBbdd with ⟨q, hq⟩
        refine ⟨p + q, ?_⟩
        rintro w ⟨u, hu, v, hv, rfl⟩
        exact add_le_add (hp hu) (hq hv)
      have hInf :
          sInf (Set.image2 (fun u v : Real ↦ u + v) A B) =
            sInf A + sInf B :=
        csInf_image2_eq_csInf_csInf
          (u := fun p q : Real ↦ p + q)
          (l₁ := fun q p : Real ↦ p - q)
          (l₂ := fun p q : Real ↦ q - p)
          (fun _ _ _ ↦ sub_le_iff_le_add)
          (fun _ _ _ ↦ sub_le_iff_le_add')
          hA hAbdd hB hBbdd
      calc
        sInf ((fun r : Real ↦ (r : WithTop Real)) '' A) +
            sInf ((fun r : Real ↦ (r : WithTop Real)) '' B) =
            ((sInf A + sInf B : Real) : WithTop Real) := by
          simpa only [WithTop.coe_add] using
            congrArg₂ (· + ·)
              (WithTop.coe_sInf' hA hAbdd).symm
              (WithTop.coe_sInf' hB hBbdd).symm
        _ = ((sInf
            (Set.image2 (fun u v : Real ↦ u + v) A B) : Real) :
              WithTop Real) :=
          congrArg (fun q : Real ↦ (q : WithTop Real)) hInf.symm
        _ = sInf ((fun r : Real ↦ (r : WithTop Real)) ''
            Set.image2 (fun u v : Real ↦ u + v) A B) :=
          WithTop.coe_sInf' hAB hABbdd
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      rw [hBe, Set.image_empty, WithTop.sInf_empty,
        Set.image2_empty_right, Set.image_empty,
        WithTop.sInf_empty, WithTop.add_top]
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    by_cases hB : B.Nonempty
    · rw [hAe, Set.image_empty, WithTop.sInf_empty,
        Set.image2_empty_left, Set.image_empty,
        WithTop.sInf_empty, WithTop.top_add]
    · rw [hAe, Set.image_empty, WithTop.sInf_empty,
        Set.image2_empty_left, Set.image_empty,
        WithTop.sInf_empty, WithTop.top_add]

private theorem lSegValue_coe
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (Ω : Set (M × Real)) (a b : Real) (x y : M)
    (hne : (lSegCosts S T Ω a b x y).Nonempty)
    (hbdd : BddBelow (lSegCosts S T Ω a b x y)) :
    lSegValue S T Ω a b x y =
      ((sInf (lSegCosts S T Ω a b x y) : Real) : WithTop Real) := by
  unfold lSegValue
  exact (WithTop.coe_sInf' hne hbdd).symm

/-- The restricted segment value is no larger than the action of any
admissible fixed-endpoint competitor. -/
theorem lSegValue_le
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (gamma : Real → M) (hgamma : IsLSegCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegValue S T Ω a b x y ≤
      (lLength S T gamma a b : WithTop Real) := by
  have hmem : lLength S T gamma a b ∈ lSegCosts S T Ω a b x y :=
    ⟨gamma, hgamma, hxa, hyb, rfl⟩
  have hbdd := lSegCosts_bdd S T K Ω ha hab hR x y
  rw [lSegValue_coe S T Ω a b x y ⟨_, hmem⟩ hbdd]
  exact WithTop.coe_le_coe.2 (csInf_le hbdd hmem)

/-- A time-slab scalar lower bound is enough to compare the restricted segment
value with any admissible fixed-endpoint competitor. -/
theorem lSegValue_le_time
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ s ∈ Icc a b, ∀ z : M, -K ≤ S.scalar (T - s) z)
    (x y : M)
    (gamma : Real → M) (hgamma : IsLSegCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegValue S T Ω a b x y ≤
      (lLength S T gamma a b : WithTop Real) := by
  have hmem : lLength S T gamma a b ∈ lSegCosts S T Ω a b x y :=
    ⟨gamma, hgamma, hxa, hyb, rfl⟩
  have hbdd : BddBelow (lSegCosts S T Ω a b x y) := by
    refine ⟨-(2 * K / 3) *
      (b * Real.sqrt b - a * Real.sqrt a), ?_⟩
    intro r hr
    rcases hr with ⟨eta, heta, _, _, rfl⟩
    exact lLength_lower S T a b K ha hab eta
      (fun s hs ↦ hR s hs (eta s)) heta.2.2.1
  rw [lSegValue_coe S T Ω a b x y ⟨_, hmem⟩ hbdd]
  exact WithTop.coe_le_coe.2 (csInf_le hbdd hmem)

/-- Every admissible global `C1` square-root-time competitor bounds the
same-clock segment value on the corresponding squared interval. -/
theorem lSegValue_le_c1
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) (a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K ≤ S.scalar (T - tau) z)
    (x y : M) (alpha : Real → M)
    (halpha : ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lSegValue S T Ω (a ^ 2) (b ^ 2) x y ≤
      (lRegAction S T alpha a b : WithTop Real) := by
  have habSq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha (ha.trans hab)).2 hab
  have hseg := lSegCurve_sqrt (I := I) S T Ω a b ha hab alpha halpha hLag hΩ
  calc
    lSegValue S T Ω (a ^ 2) (b ^ 2) x y ≤
        (lLength S T (sqrtReparam alpha) (a ^ 2) (b ^ 2) : WithTop Real) :=
      lSegValue_le_time S T K Ω (sq_nonneg a) habSq hR x y
        (sqrtReparam alpha) hseg
        (by simpa only [sqrtReparam, Real.sqrt_sq ha] using hxa)
        (by simpa only [sqrtReparam, Real.sqrt_sq (ha.trans hab)] using hyb)
    _ = (lRegAction S T alpha a b : WithTop Real) :=
      congrArg (fun r : Real ↦ (r : WithTop Real))
        (lLength_sqrt_Icc (I := I) S T alpha a b ha hab)

/-- A scalar lower bound on the confinement set gives a uniform lower bound
for the restricted segment value. -/
theorem lSegValue_lower
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1) (x y : M) :
    ((-(2 * K / 3) *
        (b * Real.sqrt b - a * Real.sqrt a) : Real) : WithTop Real) ≤
      lSegValue S T Ω a b x y := by
  by_cases hne : (lSegCosts S T Ω a b x y).Nonempty
  · have hbdd := lSegCosts_bdd S T K Ω ha hab hR x y
    rw [lSegValue_coe S T Ω a b x y hne hbdd]
    exact WithTop.coe_le_coe.2 (le_csInf hne fun r hr ↦ by
      rcases hr with ⟨gamma, hgamma, _, _, rfl⟩
      rcases hgamma with ⟨_, _, hInt, hΩ⟩
      exact lLength_lower S T a b K ha hab gamma
        (fun s hs ↦ hR (gamma s, T - s) (hΩ s hs)) hInt)
  · have hempty : lSegCosts S T Ω a b x y = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [lSegValue, hempty]

/-- A single admissible fixed-endpoint competitor makes the restricted segment
value finite. -/
theorem lSegValue_ne_top
    (S : SolutionOn (I := I) (M := M) D) (T K : Real)
    (Ω : Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (gamma : Real → M) (hgamma : IsLSegCurve S T Ω a b gamma)
    (hxa : gamma a = x) (hyb : gamma b = y) :
    lSegValue S T Ω a b x y ≠ ⊤ := by
  have hmem : lLength S T gamma a b ∈ lSegCosts S T Ω a b x y :=
    ⟨gamma, hgamma, hxa, hyb, rfl⟩
  have hbdd := lSegCosts_bdd S T K Ω ha hab hR x y
  rw [lSegValue_coe S T Ω a b x y ⟨_, hmem⟩ hbdd]
  exact WithTop.coe_ne_top

/-- Enlarging the spacetime confinement set cannot increase the restricted
segment value. -/
theorem lSegValue_mono
    (S : SolutionOn (I := I) (M := M) D)
    (T K : Real) {Ω Ω' : Set (M × Real)} {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b) (hΩ : Ω ⊆ Ω')
    (hR : ∀ q ∈ Ω', -K ≤ S.scalar q.2 q.1) (x y : M) :
    lSegValue S T Ω' a b x y ≤ lSegValue S T Ω a b x y := by
  let A := lSegCosts S T Ω a b x y
  let B := lSegCosts S T Ω' a b x y
  have hAB : A ⊆ B := by
    intro r hr
    rcases hr with ⟨gamma, hgamma, hxa, hyb, haction⟩
    rcases hgamma with ⟨hAC, hDiff, hInt, hgraph⟩
    exact ⟨gamma, ⟨hAC, hDiff, hInt,
      fun s hs ↦ hΩ (hgraph s hs)⟩, hxa, hyb, haction⟩
  have hImage :
      (fun r : Real ↦ (r : WithTop Real)) '' A ⊆
        (fun r : Real ↦ (r : WithTop Real)) '' B :=
    Set.image_mono hAB
  have hBbdd : BddBelow B :=
    lSegCosts_bdd S T K Ω' ha hab hR x y
  have hBImageBdd :
      BddBelow ((fun r : Real ↦ (r : WithTop Real)) '' B) :=
    Monotone.map_bddBelow
      (fun _ _ h ↦ WithTop.coe_mono h) hBbdd
  change sInf ((fun r : Real ↦ (r : WithTop Real)) '' B) ≤
    sInf ((fun r : Real ↦ (r : WithTop Real)) '' A)
  by_cases hA : A.Nonempty
  · exact csInf_le_csInf hBImageBdd (hA.image _) hImage
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    rw [hAe, Set.image_empty, WithTop.sInf_empty]
    exact le_top

/-- Exhausting every admissible fixed-endpoint curve by confinement subsets
recovers the value as the infimum of the restricted values. -/
theorem lSegValue_exhaust
    (S : SolutionOn (I := I) (M := M) D)
    (T K : Real) (Ω : Set (M × Real))
    (Ωj : Nat → Set (M × Real)) {a b : Real}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hsub : ∀ j, Ωj j ⊆ Ω)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x y : M)
    (hgraph : ∀ gamma : Real → M,
      IsLSegCurve S T Ω a b gamma →
      gamma a = x → gamma b = y →
      ∃ j, ∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ωj j) :
    lSegValue S T Ω a b x y =
      sInf (Set.range fun j : Nat ↦
        lSegValue S T (Ωj j) a b x y) := by
  classical
  let V : Nat → WithTop Real := fun j ↦
    lSegValue S T (Ωj j) a b x y
  have hle (j : Nat) : lSegValue S T Ω a b x y ≤ V j := by
    dsimp only [V]
    exact lSegValue_mono S T K ha hab (hsub j) hR x y
  have hRangeNonempty : (Set.range V).Nonempty :=
    ⟨V 0, ⟨0, rfl⟩⟩
  have hRangeBdd : BddBelow (Set.range V) := by
    refine ⟨lSegValue S T Ω a b x y, ?_⟩
    rintro q ⟨j, rfl⟩
    exact hle j
  change lSegValue S T Ω a b x y = sInf (Set.range V)
  apply le_antisymm
  · exact le_csInf hRangeNonempty fun q hq ↦ by
      rcases hq with ⟨j, rfl⟩
      exact hle j
  · by_cases hA : (lSegCosts S T Ω a b x y).Nonempty
    · change sInf (Set.range V) ≤
        sInf ((fun r : Real ↦ (r : WithTop Real)) ''
          lSegCosts S T Ω a b x y)
      apply le_csInf (hA.image _)
      intro q hq
      rcases hq with ⟨r, hr, rfl⟩
      rcases hr with ⟨gamma, hgamma, hxa, hyb, haction⟩
      obtain ⟨j, hgraphj⟩ := hgraph gamma hgamma hxa hyb
      rcases hgamma with ⟨hAC, hDiff, hInt, _⟩
      have hgammaj : IsLSegCurve S T (Ωj j) a b gamma :=
        ⟨hAC, hDiff, hInt, hgraphj⟩
      have hRj : ∀ q ∈ Ωj j, -K ≤ S.scalar q.2 q.1 :=
        fun q hqj ↦ hR q (hsub j hqj)
      calc
        sInf (Set.range V) ≤ V j :=
          csInf_le hRangeBdd ⟨j, rfl⟩
        _ ≤ (lLength S T gamma a b : WithTop Real) := by
          dsimp only [V]
          exact lSegValue_le S T K (Ωj j) ha hab hRj x y
            gamma hgammaj hxa hyb
        _ = (r : WithTop Real) :=
          congrArg (fun u : Real ↦ (u : WithTop Real)) haction
    · have hAe : lSegCosts S T Ω a b x y = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hA
      have htop : lSegValue S T Ω a b x y = ⊤ := by
        simp [lSegValue, hAe]
      rw [htop]
      exact le_top

/-- Same-clock restricted L-values satisfy the dynamic-programming law. -/
theorem lSegValue_dpp
    (S : SolutionOn (I := I) (M := M) D)
    (T K : Real) (Ω : Set (M × Real))
    {a b c : Real} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hR : ∀ q ∈ Ω, -K ≤ S.scalar q.2 q.1)
    (x z : M) :
    lSegValue S T Ω a c x z =
      sInf (Set.range fun y : M ↦
        lSegValue S T Ω a b x y +
          lSegValue S T Ω b c y z) := by
  classical
  have hac : a ≤ c := hab.trans hbc
  let F : M → Set (WithTop Real) := fun y ↦
    (fun r : Real ↦ (r : WithTop Real)) ''
      Set.image2 (fun u v : Real ↦ u + v)
        (lSegCosts S T Ω a b x y)
        (lSegCosts S T Ω b c y z)
  let U : Set (WithTop Real) := ⋃ y : M, F y
  let V : M → WithTop Real := fun y ↦
    lSegValue S T Ω a b x y + lSegValue S T Ω b c y z
  have hUeq : U = (fun r : Real ↦ (r : WithTop Real)) ''
      lSegCosts S T Ω a c x z := by
    dsimp only [U, F]
    rw [← Set.image_iUnion, ← lSegCosts_split S T Ω hab hbc x z]
  have hUbdd : BddBelow U := by
    rw [hUeq]
    exact Monotone.map_bddBelow
      (fun _ _ h ↦ WithTop.coe_mono h)
      (lSegCosts_bdd S T K Ω ha hac hR x z)
  have hFbdd (y : M) : BddBelow (F y) :=
    hUbdd.mono (by
      intro q hq
      change q ∈ ⋃ y : M, F y
      exact Set.mem_iUnion_of_mem y hq)
  have hFglb : ∀ y : M, IsGLB (F y) (sInf (F y)) := by
    intro y
    by_cases hy : (F y).Nonempty
    · exact isGLB_csInf hy (hFbdd y)
    · have hy0 : F y = ∅ := Set.not_nonempty_iff_eq_empty.mp hy
      simpa only [hy0, WithTop.sInf_empty] using
        (isGLB_empty : IsGLB (∅ : Set (WithTop Real)) ⊤)
  have hRangeBdd : BddBelow (Set.range fun y : M ↦ sInf (F y)) := by
    rcases hUbdd with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rintro q ⟨y, rfl⟩
    apply (hFglb y).2
    intro w hw
    apply hp
    change w ∈ ⋃ y : M, F y
    exact Set.mem_iUnion_of_mem y hw
  have hRangeNonempty :
      (Set.range fun y : M ↦ sInf (F y)).Nonempty :=
    ⟨sInf (F x), ⟨x, rfl⟩⟩
  have hRangeGLB : IsGLB
      (Set.range fun y : M ↦ sInf (F y))
      (sInf (Set.range fun y : M ↦ sInf (F y))) :=
    isGLB_csInf hRangeNonempty hRangeBdd
  have hUnionGLB : IsGLB U
      (sInf (Set.range fun y : M ↦ sInf (F y))) := by
    change IsGLB (⋃ y : M, F y) _
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases Set.mem_iUnion.mp hq with ⟨y, hy⟩
      exact (hRangeGLB.1 ⟨y, rfl⟩).trans ((hFglb y).1 hy)
    · intro q hq
      apply hRangeGLB.2
      rintro _ ⟨y, rfl⟩
      apply (hFglb y).2
      intro w hw
      apply hq
      exact Set.mem_iUnion_of_mem y hw
  have hOuter : sInf U =
      sInf (Set.range fun y : M ↦ sInf (F y)) := by
    by_cases hU : U.Nonempty
    · exact hUnionGLB.csInf_eq hU
    · have hU0 : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
      have hTop : IsGLB U (⊤ : WithTop Real) := by
        rw [hU0]
        exact isGLB_empty
      rw [hU0, WithTop.sInf_empty]
      exact hTop.unique hUnionGLB
  have hadd (y : M) : V y = sInf (F y) := by
    dsimp only [V, F]
    exact lSegValue_add S T K Ω ha hab hbc hR x y z
  have hfun : V = fun y : M ↦ sInf (F y) := funext hadd
  have hRange : Set.range V = Set.range (fun y : M ↦ sInf (F y)) :=
    congrArg Set.range hfun
  change sInf ((fun r : Real ↦ (r : WithTop Real)) ''
      lSegCosts S T Ω a c x z) = sInf (Set.range V)
  calc
    sInf ((fun r : Real ↦ (r : WithTop Real)) ''
        lSegCosts S T Ω a c x z) = sInf U := congrArg sInf hUeq.symm
    _ = sInf (Set.range fun y : M ↦ sInf (F y)) := hOuter
    _ = sInf (Set.range V) := congrArg sInf hRange.symm

/-- An action gap for ambient curves leaving a restricted confinement set
identifies the two segment values and traps sufficiently good ambient
competitors in the restricted set. -/
theorem lSegValue_gap
    (S : SolutionOn (I := I) (M := M) D)
    (T K : Real) (Ω₁ Ω₂ : Set (M × Real))
    {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b)
    (hΩ : Ω₁ ⊆ Ω₂)
    (hR : ∀ q ∈ Ω₂, -K ≤ S.scalar q.2 q.1)
    (x y : M) (η : Real) (hη : 0 < η)
    (hfin : lSegValue S T Ω₁ a b x y ≠ ⊤)
    (hgap : ∀ gamma : Real → M,
      IsLSegCurve S T Ω₂ a b gamma →
      gamma a = x → gamma b = y →
      ¬ IsLSegCurve S T Ω₁ a b gamma →
      lSegValue S T Ω₁ a b x y + (η : WithTop Real) ≤
        (lLength S T gamma a b : WithTop Real)) :
    lSegValue S T Ω₂ a b x y = lSegValue S T Ω₁ a b x y ∧
      ∀ (ε : Real), ε < η →
        ∀ gamma : Real → M,
          IsLSegCurve S T Ω₂ a b gamma →
          gamma a = x → gamma b = y →
          (lLength S T gamma a b : WithTop Real) <
            lSegValue S T Ω₂ a b x y + (ε : WithTop Real) →
          IsLSegCurve S T Ω₁ a b gamma := by
  classical
  have hR₁ : ∀ q ∈ Ω₁, -K ≤ S.scalar q.2 q.1 :=
    fun q hq ↦ hR q (hΩ hq)
  have curve_mono {gamma : Real → M}
      (hgamma : IsLSegCurve S T Ω₁ a b gamma) :
      IsLSegCurve S T Ω₂ a b gamma :=
    ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      fun s hs ↦ hΩ (hgamma.2.2.2 s hs)⟩
  have hCostsNe : (lSegCosts S T Ω₁ a b x y).Nonempty := by
    by_contra hne
    apply hfin
    have hCostsEmpty : lSegCosts S T Ω₁ a b x y = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [lSegValue, hCostsEmpty, Set.image_empty, WithTop.sInf_empty]
  let B : Set (WithTop Real) :=
    (fun r : Real ↦ (r : WithTop Real)) ''
      lSegCosts S T Ω₂ a b x y
  have hBne : B.Nonempty := by
    rcases hCostsNe with ⟨r, gamma, hgamma, hga, hgb, hr⟩
    refine ⟨(r : WithTop Real), r, ?_, rfl⟩
    exact ⟨gamma, curve_mono hgamma, hga, hgb, hr⟩
  have hRestricted_le :
      lSegValue S T Ω₁ a b x y ≤ lSegValue S T Ω₂ a b x y := by
    change lSegValue S T Ω₁ a b x y ≤ sInf B
    apply le_csInf hBne
    intro q hq
    rcases hq with ⟨r, hr, rfl⟩
    rcases hr with ⟨gamma, hgamma, hga, hgb, hr⟩
    rw [← hr]
    by_cases hin : IsLSegCurve S T Ω₁ a b gamma
    · exact lSegValue_le S T K Ω₁ ha hab hR₁ x y gamma hin hga hgb
    · have hη0 : (0 : WithTop Real) ≤ (η : WithTop Real) := by
        norm_cast
        exact hη.le
      calc
        lSegValue S T Ω₁ a b x y =
            lSegValue S T Ω₁ a b x y + 0 := (add_zero _).symm
        _ ≤ lSegValue S T Ω₁ a b x y + (η : WithTop Real) :=
          add_le_add_right hη0 _
        _ ≤ (lLength S T gamma a b : WithTop Real) :=
          hgap gamma hgamma hga hgb hin
  have hAmbient_le :
      lSegValue S T Ω₂ a b x y ≤ lSegValue S T Ω₁ a b x y :=
    lSegValue_mono S T K ha hab hΩ hR x y
  have hEq :
      lSegValue S T Ω₂ a b x y = lSegValue S T Ω₁ a b x y :=
    le_antisymm hAmbient_le hRestricted_le
  refine ⟨hEq, ?_⟩
  intro ε hε gamma hgamma hga hgb hmin
  by_contra hout
  obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hfin
  have houtGap := hgap gamma hgamma hga hgb hout
  rw [← hL] at houtGap
  have houtGap' :
      ((L + η : Real) : WithTop Real) ≤
        (lLength S T gamma a b : WithTop Real) := by
    simpa only [WithTop.coe_add] using houtGap
  have houtGapReal : L + η ≤ lLength S T gamma a b :=
    WithTop.coe_le_coe.mp houtGap'
  rw [hEq, ← hL] at hmin
  have hmin' :
      (lLength S T gamma a b : WithTop Real) <
        ((L + ε : Real) : WithTop Real) := by
    simpa only [WithTop.coe_add] using hmin
  have hminReal : lLength S T gamma a b < L + ε :=
    WithTop.coe_lt_coe.mp hmin'
  exact (not_lt_of_ge houtGapReal)
    (hminReal.trans (add_lt_add_right hε L))

end DifferentialGeometry.PDE.RicciFlow.Perelman
