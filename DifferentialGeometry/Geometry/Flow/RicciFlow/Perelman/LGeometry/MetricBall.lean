import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShiBallAnchor

set_option autoImplicit false

/-!
# Uniform metric comparison on a controlled flow ball

The metric ODE is integrated at one fixed spatial point.  A terminal
radius-`1/32` hypothesis and the ball-local distance anchor keep that point in
the controlled moving ball throughout the short backward interval.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff ENNReal Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem metricPair_at
    (g : Real → SmoothRiemannianMetric I M)
    {a b K : Real} (hab : a ≤ b) (x : M) (v : TangentSpace I x)
    (hpde : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun s : Real ↦ (g s).inner x v v)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v v)
        (Set.Icc a b) t)
    (hric : ∀ t ∈ Set.Icc a b,
      |ricciTensor (I := I) (g t) x v v| ≤
        K * (g t).inner x v v) :
    Real.exp (-(2 * K * (b - a))) * (g b).inner x v v ≤
        (g a).inner x v v ∧
      (g a).inner x v v ≤
        Real.exp (2 * K * (b - a)) * (g b).inner x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hpos : ∀ t : Real, 0 < (g t).inner x v v :=
    fun t ↦ (g t).pos x v hv
  have hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt
        (fun s : Real ↦ Real.log ((g s).inner x v v))
        ((-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v)
        (Set.Icc a b) t := by
    intro t ht
    exact (hpde t ht).log (hpos t).ne'
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖(-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v‖ ≤ 2 * K := by
    intro t ht
    have hden := hpos t
    have hricT := hric t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [abs_mul]
    norm_num
    nlinarith
  have hmvt := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hlog :
      |Real.log ((g b).inner x v v) - Real.log ((g a).inner x v v)| ≤
        2 * K * (b - a) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hab)] at hmvt
    exact hmvt
  have hequiv := exp_bounds_log (hpos a) (hpos b) hlog
  constructor
  · calc
      Real.exp (-(2 * K * (b - a))) * (g b).inner x v v ≤
          Real.exp (-(2 * K * (b - a))) *
            (Real.exp (2 * K * (b - a)) * (g a).inner x v v) :=
        mul_le_mul_of_nonneg_left hequiv.2 (Real.exp_pos _).le
      _ = (g a).inner x v v := by
        rw [← mul_assoc, ← Real.exp_add]
        simp only [neg_add_cancel, Real.exp_zero, one_mul]
  · calc
      (g a).inner x v v =
          Real.exp (2 * K * (b - a)) *
            (Real.exp (-(2 * K * (b - a))) * (g a).inner x v v) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp only [add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (2 * K * (b - a)) * (g b).inner x v v :=
        mul_le_mul_of_nonneg_left hequiv.1 (Real.exp_pos _).le

variable [SigmaCompactSpace M]

omit [FiniteDimensional Real E] [SigmaCompactSpace M] in
private theorem radiusRic_eq (n : Nat) {r : Real} (hr : 0 < r) :
    r ^ 2 * ((n : Real) ^ 2 * Real.sqrt (1 / r ^ 4)) = (n : Real) ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
  rw [show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
  field_simp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A terminal minimizing curve transports a sufficiently small terminal
distance backward while staying inside the controlled flow metric ball. -/
theorem edistTo_terminal
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {s t : Real} (hst : s ≤ t)
    (hreg : Set.Ioc s t ⊆ D.regular)
    (hstB : Set.Icc s t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_t : RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
      ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x := by
  let D' := D.timeShift s
  let S' : SolutionOn (I := I) (M := M) D' := S.timeShift s
  let time' : RealTimeInterval.FlowTime D' :=
    ⟨(time : Real) - s, by
      change (time : Real) - s + s ∈ D.carrier
      simpa only [sub_add_cancel] using time.2⟩
  let B' : FlowMetricBall S' time' := {
    center := B.center
    radius := B.radius
    radius_pos := B.radius_pos }
  let delta : Real := t - s
  have hdelta : 0 ≤ delta := sub_nonneg.mpr hst
  have hS' : IsSolutionOn (I := I) S' := by
    simpa only [S'] using isSolutionOn_timeShift (I := I) hS s
  have hB' : B'.IsRmControlled := by
    constructor
    · intro r hr
      change r + s ∈ D.carrier
      apply hB.1
      dsimp only [B', time'] at hr ⊢
      constructor <;> linarith [hr.1, hr.2]
    · intro r hr y hy
      have hr' : r + s ∈
          Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
        dsimp only [B', time'] at hr
        constructor <;> linarith [hr.1, hr.2]
      have hy' : y ∈ B.setAt (r + s) := by
        simpa only [B', FlowMetricBall.setAt, S',
          SolutionOn.timeShift_base_metric] using hy
      have hraw := hB.2 (r + s) hr' y hy'
      simpa only [B', FlowMetricBall.rmNormSq, S',
        SolutionOn.timeShift_base_metric] using hraw
  have hreg' : Set.Ioc 0 delta ⊆ D'.regular := by
    intro r hr
    change r + s ∈ D.regular
    apply hreg
    dsimp only [delta] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hstB' : Set.Icc 0 delta ⊆
      Set.Icc ((time' : Real) - B'.radius ^ 2) (time' : Real) := by
    intro r hr
    have hrst : r + s ∈ Set.Icc s t := by
      dsimp only [delta] at hr
      constructor <;> linarith [hr.1, hr.2]
    have hraw := hstB hrst
    dsimp only [B', time']
    constructor <;> linarith [hraw.1, hraw.2]
  have hcomplete_delta :
      RiemannianMetricComplete (I := I) (S'.base.metric delta) := by
    simpa only [S', SolutionOn.timeShift_base_metric, delta, sub_add_cancel] using
      hcomplete_t
  have hraw := dist0_le_scaled (I := I) hS' B' hB' hdelta hreg' hstB'
    hcomplete_delta (x := x) (by
      simpa only [B', S', SolutionOn.timeShift_base_metric, delta,
        sub_add_cancel] using hx)
  simpa only [B', S', SolutionOn.timeShift_base_metric, zero_add, delta,
    sub_add_cancel] using hraw

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a dimension-uniform short backward interval, the metric on the terminal
radius-`1/32` ball is quadratically comparable with the terminal metric. -/
theorem lMetric_ball
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D}
          (B : FlowMetricBall S time), B.IsRmControlled →
          Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) →
          ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
            ∀ t ∈ Set.Icc
              ((time : Real) - eps * B.radius ^ 2) (time : Real),
              ∀ x : M,
                riemannianEDistOf (I := I) (S.base.metric (time : Real))
                    B.center x ≤ ENNReal.ofReal (B.radius / 32) →
                ∀ v : TangentSpace I x,
                  Real.exp (-(2 * (Module.finrank Real E : Real) ^ 2 * eps)) *
                      (S.base.metric (time : Real)).inner x v v ≤
                        (S.base.metric t).inner x v v ∧
                    (S.base.metric t).inner x v v ≤
                      Real.exp (2 * (Module.finrank Real E : Real) ^ 2 * eps) *
                        (S.base.metric (time : Real)).inner x v v := by
  let n : Real := Module.finrank Real E
  let eps₀ : Real := Real.log 2 / (4 * (n ^ 2 + 1))
  have hn0 : 0 ≤ n ^ 2 := sq_nonneg n
  have hden : 0 < 4 * (n ^ 2 + 1) := by positivity
  have heps₀ : 0 < eps₀ :=
    div_pos (Real.log_pos (by norm_num)) hden
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hB hreg hcomplete eps heps heps₀ t ht x hx v
  have hepsLog : n ^ 2 * eps ≤ Real.log 2 := by
    have hmul : eps * (4 * (n ^ 2 + 1)) ≤ Real.log 2 := by
      apply (le_div_iff₀ hden).mp
      simpa only [eps₀] using heps₀
    nlinarith [hn0]
  have htBig : Set.Icc t (time : Real) ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro q hq
    have hepsOne : eps ≤ 1 := by
      have hlogTwo : Real.log 2 < 1 := by
        nlinarith [Real.log_lt_sub_one_of_pos
          (by norm_num : (0 : Real) < 2) (by norm_num : (2 : Real) ≠ 1)]
      have hepsSmall : eps < 1 := by
        have hmulPos : 0 < 4 * (n ^ 2 + 1) := hden
        have hbound : eps * (4 * (n ^ 2 + 1)) ≤ Real.log 2 := by
          apply (le_div_iff₀ hden).mp
          simpa only [eps₀] using heps₀
        nlinarith [hn0]
      exact hepsSmall.le
    constructor
    · have hr2 := sq_nonneg B.radius
      nlinarith [ht.1, hq.1]
    · exact hq.2
  by_cases htt : t = (time : Real)
  · subst t
    have hqnn : 0 ≤ (S.base.metric (time : Real)).inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact ((S.base.metric (time : Real)).pos x v hv).le
    constructor
    · apply mul_le_of_le_one_left hqnn
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [hn0, heps.le]
    · calc
        (S.base.metric (time : Real)).inner x v v =
            1 * (S.base.metric (time : Real)).inner x v v := by rw [one_mul]
        _ ≤ Real.exp (2 * n ^ 2 * eps) *
            (S.base.metric (time : Real)).inner x v v := by
          apply mul_le_mul_of_nonneg_right _ hqnn
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith [hn0, heps.le]
  have htlt : t < (time : Real) := lt_of_le_of_ne ht.2 htt
  have hregSmall : Set.Ioc t (time : Real) ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨(htBig ⟨le_rfl, ht.2⟩).1.trans_lt hq.1, hq.2⟩
  have hpde := metricPDE_Icc (I := I) S hS htlt
    (fun _ hq ↦ hB.1 (htBig hq)) hregSmall
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have hK0 : 0 ≤ K :=
    mul_nonneg hn0 (Real.sqrt_nonneg _)
  have hdelta : (time : Real) - t ≤ eps * B.radius ^ 2 := by
    linarith [ht.1]
  have hscale : B.radius ^ 2 * K = n ^ 2 := by
    simpa only [K, n] using radiusRic_eq (Module.finrank Real E) B.radius_pos
  have hKdelta : K * ((time : Real) - t) ≤ n ^ 2 * eps := by
    calc
      K * ((time : Real) - t) ≤ K * (eps * B.radius ^ 2) :=
        mul_le_mul_of_nonneg_left hdelta hK0
      _ = n ^ 2 * eps := by rw [← hscale]; ring
  have hmem : ∀ q ∈ Set.Icc t (time : Real), x ∈ B.setAt q := by
    intro q hq
    change riemannianEDistOf (I := I) (S.base.metric q) B.center x <
      ENNReal.ofReal B.radius
    by_cases hqtime : q = (time : Real)
    · simpa only [hqtime] using hx.trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2
          (by nlinarith [B.radius_pos]))
    have hqlt : q < (time : Real) := lt_of_le_of_ne hq.2 hqtime
    have hqdelta : (time : Real) - q ≤ eps * B.radius ^ 2 := by
      linarith [ht.1, hq.1]
    have harg : n ^ 2 / B.radius ^ 2 * ((time : Real) - q) ≤
        n ^ 2 * eps := by
      have hcoef : 0 ≤ n ^ 2 / B.radius ^ 2 :=
        div_nonneg hn0 (sq_nonneg B.radius)
      calc
        _ ≤ (n ^ 2 / B.radius ^ 2) * (eps * B.radius ^ 2) :=
          mul_le_mul_of_nonneg_left hqdelta hcoef
        _ = n ^ 2 * eps := by field_simp [B.radius_pos.ne']
    have hexp : Real.exp
          (n ^ 2 / B.radius ^ 2 * ((time : Real) - q)) ≤ 2 := by
      calc
        _ ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (harg.trans hepsLog)
        _ = 2 := Real.exp_log (by norm_num)
    have hscaled : ENNReal.ofReal (Real.exp
          (n ^ 2 / B.radius ^ 2 * ((time : Real) - q))) *
        riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center x <
          ENNReal.ofReal B.radius := by
      calc
        _ ≤ ENNReal.ofReal 2 *
            riemannianEDistOf (I := I)
              (S.base.metric (time : Real)) B.center x :=
          by
            simpa only [mul_comm] using
              (mul_le_mul_right (ENNReal.ofReal_le_ofReal hexp)
                (riemannianEDistOf (I := I)
                  (S.base.metric (time : Real)) B.center x))
        _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (B.radius / 32) :=
          mul_le_mul_right hx _
        _ = ENNReal.ofReal (B.radius / 16) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
          apply congrArg ENNReal.ofReal
          ring
        _ < ENNReal.ofReal B.radius :=
          (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2
            (by nlinarith [B.radius_pos])
    have hdist := edistTo_terminal hS B hB hq.2
      (fun _ hz ↦ hregSmall ⟨hq.1.trans_lt hz.1, hz.2⟩)
      (fun _ hr ↦ htBig ⟨hq.1.trans hr.1, hr.2⟩) hcomplete (x := x)
      (by simpa only [n] using hscaled)
    exact hdist.trans_lt hscaled
  have hric : ∀ q ∈ Set.Icc t (time : Real),
      |ricciTensor (I := I) (S.base.metric q) x v v| ≤
        K * (S.base.metric q).inner x v v := by
    intro q hq
    simpa only [K, n] using
      ricci_abs_of_rm (I := I) B hB (htBig hq) (hmem q hq) v
  have hpair := metricPair_at (fun q ↦ S.base.metric q)
    ht.2 x v (fun q hq ↦ hpde q hq x v v) hric
  have hTnn : 0 ≤ (S.base.metric (time : Real)).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric (time : Real)).pos x v hv).le
  constructor
  · calc
      Real.exp (-(2 * n ^ 2 * eps)) *
          (S.base.metric (time : Real)).inner x v v ≤
        Real.exp (-(2 * K * ((time : Real) - t))) *
          (S.base.metric (time : Real)).inner x v v := by
            apply mul_le_mul_of_nonneg_right _ hTnn
            apply Real.exp_le_exp.mpr
            nlinarith [hKdelta]
      _ ≤ (S.base.metric t).inner x v v := hpair.1
  · calc
      (S.base.metric t).inner x v v ≤
          Real.exp (2 * K * ((time : Real) - t)) *
            (S.base.metric (time : Real)).inner x v v := hpair.2
      _ ≤ Real.exp (2 * n ^ 2 * eps) *
          (S.base.metric (time : Real)).inner x v v := by
            apply mul_le_mul_of_nonneg_right _ hTnn
            apply Real.exp_le_exp.mpr
            nlinarith [hKdelta]

end DifferentialGeometry.PDE.RicciFlow.Perelman
