import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MetricBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegSpeedBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayContinue
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper

set_option autoImplicit false

/-!
# Uniform range control on a flow metric ball

The ball-local speed and metric estimates close the maximal regularized-ray
domain by a terminal-metric first-exit argument.  Completeness is used only to
make one explicit terminal closed ball compact.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal Topology

/-- The scalar normalization used for the initial regularized L-speed bound. -/
private theorem source_sq_eq {eps : Real} (heps : 0 < eps) :
    4 * (1 / (128 * Real.sqrt eps)) ^ 2 = 1 / (4096 * eps) := by
  rw [div_pow, mul_pow, Real.sq_sqrt heps.le]
  field_simp [heps.ne']
  ring

/-- The source norm bound gives the normalized initial speed budget. -/
private theorem source_speed_le {eps U : Real} (heps : 0 < eps)
    (hU : U ≤ (1 / (128 * Real.sqrt eps)) ^ 2) :
    4 * U ≤ 1 / (4096 * eps) := by
  calc
    4 * U ≤ 4 * (1 / (128 * Real.sqrt eps)) ^ 2 :=
      mul_le_mul_of_nonneg_left hU (by norm_num)
    _ = 1 / (4096 * eps) := source_sq_eq heps

/-- The scalar smallness threshold absorbs the additive speed constant. -/
private theorem one_le_scaled {eps : Real} (heps : 0 < eps)
    (hsmall : eps ≤ 1 / 8192) : (1 : Real) ≤ 1 / (8192 * eps) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) heps)).2
  calc
    1 * ((8192 : Real) * eps) = (8192 : Real) * eps := one_mul _
    _ ≤ (8192 : Real) * (1 / 8192 : Real) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : Real) ≤ 8192)
    _ = 1 := by norm_num

/-- The initial speed and additive error fit the uniform speed budget. -/
private theorem speed_absorb {eps U : Real} (heps : 0 < eps)
    (hU : U ≤ 1 / (4096 * eps)) (hone : 1 ≤ 1 / (8192 * eps)) :
    (4 / 3 : Real) * (U + 1) ≤ 1 / (2048 * eps) := by
  calc
    (4 / 3 : Real) * (U + 1) ≤
        (4 / 3 : Real) *
          (1 / (4096 * eps) + 1 / (8192 * eps)) :=
      mul_le_mul_of_nonneg_left (add_le_add hU hone) (by norm_num)
    _ = 1 / (2048 * eps) := by
      field_simp [heps.ne']
      ring

/-- The terminal energy budget stays strictly inside the radius-`1/32` ball. -/
private theorem reach_small {t eps r : Real} (ht : 0 < t) (heps : 0 < eps)
    (htSq : t ^ 2 ≤ eps * r ^ 2) (hr : 0 < r) :
    Real.sqrt (Real.sqrt (t ^ 2)) * Real.sqrt (t / (1536 * eps)) <
      r / 32 := by
  have hC0 : 0 ≤ t / (1536 * eps) :=
    div_nonneg ht.le (mul_nonneg (by norm_num) heps.le)
  have hscalePos : 0 < eps * r ^ 2 :=
    mul_pos heps (sq_pos_of_pos hr)
  have hleft0 : 0 ≤ Real.sqrt (Real.sqrt (t ^ 2)) *
      Real.sqrt (t / (1536 * eps)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ r / 32 :=
    div_nonneg hr.le (by norm_num)
  apply (sq_lt_sq₀ hleft0 hright0).1
  rw [mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos ht,
    Real.sq_sqrt ht.le, Real.sq_sqrt hC0]
  field_simp [heps.ne']
  nlinarith only [htSq, hscalePos]

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A terminal radius-`1/32` bound transports to a moving radius-`1/16`
bound on a sufficiently short backward parabolic interval. -/
private theorem edist_move_lt
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    (hreg : Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular)
    (hcompleteT :
      RiemannianMetricComplete (I := I) (S.base.metric (time : Real)))
    {eps q : Real} (heps : 0 < eps) (hepsOne : eps < 1)
    (hqSq : q ^ 2 ≤ eps * B.radius ^ 2)
    (hsmall : 2 * (Module.finrank Real E : Real) ^ 2 * eps ≤
      Real.log (4 / 3))
    {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center x ≤ ENNReal.ofReal (B.radius / 32)) :
    riemannianEDistOf (I := I)
        (S.base.metric ((time : Real) - q ^ 2)) B.center x <
      ENNReal.ofReal (B.radius / 16) := by
  let n : Real := Module.finrank Real E
  let P : Real := Real.exp
    ((n ^ 2 / B.radius ^ 2) *
      ((time : Real) - ((time : Real) - q ^ 2)))
  have hnne : 0 ≤ n ^ 2 * eps :=
    mul_nonneg (sq_nonneg n) heps.le
  have hdim : n ^ 2 * eps ≤ Real.log (4 / 3) := by
    calc
      n ^ 2 * eps = 1 * (n ^ 2 * eps) := by ring
      _ ≤ 2 * (n ^ 2 * eps) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnne
      _ = 2 * n ^ 2 * eps := by ring
      _ ≤ Real.log (4 / 3) := by simpa only [n] using hsmall
  have hParg :
      (n ^ 2 / B.radius ^ 2) *
          ((time : Real) - ((time : Real) - q ^ 2)) ≤
        Real.log (4 / 3) := by
    calc
      (n ^ 2 / B.radius ^ 2) *
            ((time : Real) - ((time : Real) - q ^ 2)) =
          (n ^ 2 / B.radius ^ 2) * q ^ 2 := by ring
      _ ≤ (n ^ 2 / B.radius ^ 2) * (eps * B.radius ^ 2) :=
        mul_le_mul_of_nonneg_left hqSq (by positivity)
      _ = n ^ 2 * eps := by
        field_simp [B.radius_pos.ne']
      _ ≤ Real.log (4 / 3) := hdim
  have hPpos : 0 < P := Real.exp_pos _
  have hPle : P ≤ 4 / 3 := by
    calc
      P ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr hParg
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have hqLt : q ^ 2 < B.radius ^ 2 := by
    calc
      q ^ 2 ≤ eps * B.radius ^ 2 := hqSq
      _ < B.radius ^ 2 := by
        nlinarith [hepsOne, sq_pos_of_pos B.radius_pos]
  have hregSmall : Set.Ioc ((time : Real) - q ^ 2) (time : Real) ⊆
      D.regular := by
    intro t ht
    apply hreg
    exact ⟨by linarith [ht.1, hqLt], ht.2⟩
  have hstB : Set.Icc ((time : Real) - q ^ 2) (time : Real) ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro t ht
    exact ⟨(sub_lt_sub_left hqLt (time : Real)).le.trans ht.1, ht.2⟩
  have hPr : P * (B.radius / 32) < B.radius := by
    calc
      P * (B.radius / 32) ≤ (4 / 3 : Real) * (B.radius / 32) :=
        mul_le_mul_of_nonneg_right hPle
          (div_nonneg B.radius_pos.le (by norm_num))
      _ < B.radius := by nlinarith only [B.radius_pos]
  have hPr16 : P * (B.radius / 32) < B.radius / 16 := by
    calc
      P * (B.radius / 32) ≤ (4 / 3 : Real) * (B.radius / 32) :=
        mul_le_mul_of_nonneg_right hPle
          (div_nonneg B.radius_pos.le (by norm_num))
      _ < B.radius / 16 := by nlinarith only [B.radius_pos]
  have hxP :
      ENNReal.ofReal P *
            riemannianEDistOf (I := I) (S.base.metric (time : Real))
              B.center x <
          ENNReal.ofReal B.radius := by
    calc
      ENNReal.ofReal P *
            riemannianEDistOf (I := I) (S.base.metric (time : Real))
              B.center x ≤
          ENNReal.ofReal P * ENNReal.ofReal (B.radius / 32) :=
        mul_le_mul_of_nonneg_left hx (by exact bot_le)
      _ = ENNReal.ofReal (P * (B.radius / 32)) := by
        rw [ENNReal.ofReal_mul hPpos.le]
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 hPr
  have hdist := edistTo_terminal (I := I)
    (s := (time : Real) - q ^ 2) (t := (time : Real)) hS B hB
    (sub_le_self _ (sq_nonneg q)) hregSmall hstB hcompleteT
    (x := x) (by simpa only [P, n] using hxP)
  calc
    riemannianEDistOf (I := I)
        (S.base.metric ((time : Real) - q ^ 2)) B.center x ≤
        ENNReal.ofReal P *
          riemannianEDistOf (I := I) (S.base.metric (time : Real))
            B.center x := hdist
    _ ≤ ENNReal.ofReal P * ENNReal.ofReal (B.radius / 32) :=
      mul_le_mul_of_nonneg_left hx (by exact bot_le)
    _ = ENNReal.ofReal (P * (B.radius / 32)) := by
      rw [ENNReal.ofReal_mul hPpos.le]
    _ < ENNReal.ofReal (B.radius / 16) :=
      (ENNReal.ofReal_lt_ofReal_iff (by
        nlinarith only [B.radius_pos])).2 hPr16

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On one dimension-uniform short parabolic interval, every regularized
L-ray with small terminal source stays in a terminal radius-`1/32` closed
ball and in the corresponding moving radius-`1/16` open ball. -/
theorem lRegRange_unif
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M] :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                  1 / (128 * Real.sqrt eps) →
                let b := Real.sqrt eps * B.radius
                ∀ s ∈ Set.Icc (0 : Real) b,
                  s ∈ lRegDomain S (time : Real) B.center Z ∧
                    riemannianEDistOf (I := I)
                        (S.base.metric (time : Real)) B.center
                        (lRegCurve S (time : Real) B.center Z s) ≤
                      ENNReal.ofReal (B.radius / 32) ∧
                    riemannianEDistOf (I := I)
                        (S.base.metric ((time : Real) - s ^ 2)) B.center
                        (lRegCurve S (time : Real) B.center Z s) <
                      ENNReal.ofReal (B.radius / 16) := by
  obtain ⟨theta, htheta, hthetaOne, hspeed⟩ :=
    lRegSpeed_unif (E := E) (I := I) (M := M)
  obtain ⟨epsM, hepsM, hmetric⟩ :=
    lMetric_ball (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  obtain ⟨epsS, hepsS, hspeed'⟩ := hspeed rho hrho
  let n : Real := Module.finrank Real E
  let epsF : Real := Real.log (4 / 3) / (2 * (n ^ 2 + 1))
  have hdenF : 0 < 2 * (n ^ 2 + 1) := by positivity
  have hepsF : 0 < epsF :=
    div_pos (Real.log_pos (by norm_num)) hdenF
  let eps₀ : Real := min epsS (min epsM (min epsF (1 / 8192)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsS (lt_min hepsM (lt_min hepsF (by norm_num)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z hZ
  dsimp only
  have hepsS' : eps ≤ epsS :=
    heps₀.trans (min_le_left epsS (min epsM (min epsF (1 / 8192))))
  have hepsM' : eps ≤ epsM := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ epsM := min_le_left _ _
  have hepsF' : eps ≤ epsF := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ min epsF (1 / 8192) := min_le_right _ _
      _ ≤ epsF := min_le_left _ _
  have hepsTiny : eps ≤ (1 / 8192 : Real) := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min epsM (min epsF (1 / 8192)) := min_le_right _ _
      _ ≤ min epsF (1 / 8192) := min_le_right _ _
      _ ≤ 1 / 8192 := min_le_right _ _
  have hepsOne : eps < 1 := by linarith
  let b : Real := Real.sqrt eps * B.radius
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hbSqLt : b ^ 2 < B.radius ^ 2 := by
    rw [hbSq]
    nlinarith [sq_pos_of_pos B.radius_pos]
  have hTreg : (time : Real) ∈ D.regular :=
    hreg ⟨by nlinarith [sq_pos_of_pos B.radius_pos], le_rfl⟩
  have hslab : Set.Icc ((time : Real) - b ^ 2) (time : Real) ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨by linarith [hq.1, hbSqLt], hq.2⟩
  have hcompleteT :
      RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) :=
    hcomplete (time : Real)
      ⟨sub_le_self _ (mul_nonneg htheta.le (sq_nonneg B.radius)), le_rfl⟩
  let alpha : Real → M := lRegCurve S (time : Real) B.center Z
  have halpha_zero : alpha 0 = B.center := by
    simpa only [alpha] using
      lRegCurve_zero S (time : Real) B.center Z
  have halpha_of : ∀ {s : Real},
      s ∈ lRegDomain S (time : Real) B.center Z →
        ContinuousOn alpha (Set.Icc (0 : Real) s) := by
    intro s hs
    simpa only [alpha] using
      (lRegCurve_c1On S hS (time : Real) B.center Z hs).continuousOn
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  let O : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y < ENNReal.ofReal (B.radius / 32)}
  have hKcompact : IsCompact K := by
    simpa only [K] using
      RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcompleteT B.center (B.radius / 32)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hOopen : IsOpen O := by
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(S.base.metric (time : Real)).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : M ↦ TangentSpace I x) :=
      ⟨(S.base.metric (time : Real)).inner,
        (S.base.metric (time : Real)).contMDiff.continuous,
        fun _ _ _ ↦ rfl⟩
    dsimp only [O]
    exact isOpen_lt
      (continuous_riemannianEDist (S.base.metric (time : Real)) B.center)
      continuous_const
  have hOK : O ⊆ K := by
    intro y hy
    change riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center y < ENNReal.ofReal (B.radius / 32) at hy
    change riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center y ≤ ENNReal.ofReal (B.radius / 32)
    exact hy.le
  have hcenterO : B.center ∈ O := by
    change riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center B.center < ENNReal.ofReal (B.radius / 32)
    simpa only [riemannianEDistOf_self] using
      ENNReal.ofReal_pos.2 (by nlinarith [B.radius_pos])
  have hcenterK : B.center ∈ interior K :=
    (interior_maximal hOK hOopen) hcenterO
  let Q : Real := Real.exp (2 * n ^ 2 * eps)
  have harg : 2 * n ^ 2 * eps ≤ Real.log (4 / 3) := by
    have hcore : eps * (2 * (n ^ 2 + 1)) ≤ Real.log (4 / 3) := by
      apply (le_div_iff₀ hdenF).mp
      simpa only [epsF] using hepsF'
    nlinarith [sq_nonneg n, heps.le]
  have hQpos : 0 < Q := Real.exp_pos _
  have hQle : Q ≤ 4 / 3 := by
    calc
      Q ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr harg
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have htime : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈
        Set.Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    rw [hbSq] at hqSq
    exact ⟨by linarith, by nlinarith [sq_nonneg q]⟩
  have hKmove : ∀ q ∈ Set.Icc (0 : Real) b, alpha q ∈ K →
      riemannianEDistOf (I := I)
          (S.base.metric ((time : Real) - q ^ 2)) B.center (alpha q) <
        ENNReal.ofReal (B.radius / 16) := by
    intro q hq hqK
    have hqSq : q ^ 2 ≤ eps * B.radius ^ 2 := by
      have hqb : q ^ 2 ≤ b ^ 2 :=
        (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
      simpa only [hbSq] using hqb
    apply edist_move_lt (I := I) hS B hB hreg hcompleteT
      heps hepsOne hqSq harg
    simpa only [K] using hqK
  have hU0 : lRegSpeedSq S (time : Real) alpha 0 =
      4 * (S.base.metric (time : Real)).inner B.center Z Z := by
    dsimp only [lRegSpeedSq, alpha]
    norm_num only [zero_pow, sub_zero]
    rw [lRegCurve_zero, lRegCurve_vel_zero S hS (time : Real) B.center Z hTreg]
    calc
      (S.base.metric (time : Real)).inner B.center ((2 : Real) • Z)
          ((2 : Real) • Z) =
        (2 : Real) * 2 *
          (S.base.metric (time : Real)).inner B.center Z Z :=
            metric_smul2 (I := I) (S.base.metric (time : Real)) (2 : Real) Z
      _ = 4 * (S.base.metric (time : Real)).inner B.center Z Z := by ring
  have hZsq : (S.base.metric (time : Real)).inner B.center Z Z ≤
      (1 / (128 * Real.sqrt eps)) ^ 2 := by
    have hZ0 : 0 ≤ (S.base.metric (time : Real)).inner B.center Z Z := by
      by_cases hzero : Z = 0
      · subst Z
        rw [((S.base.metric (time : Real)).inner B.center).map_zero,
          ContinuousLinearMap.zero_apply]
      · exact ((S.base.metric (time : Real)).pos B.center Z hzero).le
    have hZrhs : 0 ≤ 1 / (128 * Real.sqrt eps) :=
      (one_div_pos.mpr (mul_pos (by norm_num) hsqrteps)).le
    rw [← Real.sq_sqrt hZ0]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hZrhs).2 hZ
  have hU0le : lRegSpeedSq S (time : Real) alpha 0 ≤ 1 / (4096 * eps) := by
    rw [hU0]
    exact source_speed_le heps hZsq
  have hone : (1 : Real) ≤ 1 / (8192 * eps) :=
    one_le_scaled heps hepsTiny
  have hspeedBound : ∀ q ∈ Set.Icc (0 : Real) b,
      q ∈ lRegDomain S (time : Real) B.center Z →
      (∀ u ∈ Set.Icc (0 : Real) q, alpha u ∈ K) →
      lRegSpeedSq S (time : Real) alpha q ≤ 1 / (2048 * eps) := by
    intro q hq hqDom hqK
    have hmove : ∀ u ∈ Set.Icc (0 : Real) q,
        riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - u ^ 2)) B.center (alpha u) <
          ENNReal.ofReal (B.radius / 16) := by
      intro u hu
      exact hKmove u ⟨hu.1, hu.2.trans hq.2⟩ (hqK u hu)
    have hqSpeed := hspeed' hS B hBrho hB hreg hcomplete eps heps hepsS'
      Z q hq hqDom hmove
    exact hqSpeed.trans (speed_absorb heps hU0le hone)
  have htermRange : ∀ s ∈ Set.Icc (0 : Real) b,
      s ∈ lRegDomain S (time : Real) B.center Z → alpha s ∈ K := by
    intro s hs hsDom
    apply Classical.byContradiction
    intro hsK
    have hsne : s ≠ 0 := by
      intro hs0
      apply hsK
      rw [hs0, halpha_zero]
      exact interior_subset hcenterK
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
    have halpha := halpha_of hsDom
    have halpha0 : alpha 0 ∈ interior K := by
      rw [halpha_zero]
      exact hcenterK
    obtain ⟨t, ht, hstay, hfront⟩ :=
      first_exit_to hKclosed hspos halpha halpha0 hsK
    have htDom : t ∈ lRegDomain S (time : Real) B.center Z :=
      lRegDomain_seg S (time : Real) B.center Z hsDom ht.1.le ht.2
    have htIcc : t ∈ Set.Icc (0 : Real) b :=
      ⟨ht.1.le, ht.2.trans hs.2⟩
    have hterm : ∀ q ∈ Set.Icc (0 : Real) t,
        (S.base.metric (time : Real)).inner (alpha q)
          (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) ≤
            1 / (1536 * eps) := by
      intro q hq
      have hqIcc : q ∈ Set.Icc (0 : Real) b :=
        ⟨hq.1, hq.2.trans htIcc.2⟩
      have hqDom : q ∈ lRegDomain S (time : Real) B.center Z :=
        lRegDomain_seg S (time : Real) B.center Z htDom hq.1 hq.2
      have hqSpeed := hspeedBound q hqIcc hqDom
        (fun u hu ↦ hstay u ⟨hu.1, hu.2.trans hq.2⟩)
      have hpair := hmetric hS B hB hreg hcompleteT eps heps hepsM'
        ((time : Real) - q ^ 2) (htime q hqIcc) (alpha q) (by
          simpa only [K] using hstay q hq)
        (lVelocity (I := I) alpha q)
      have htermMove :
          (S.base.metric (time : Real)).inner (alpha q)
              (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) ≤
            Q * (S.base.metric ((time : Real) - q ^ 2)).inner (alpha q)
              (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) := by
        calc
          (S.base.metric (time : Real)).inner (alpha q)
              (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) =
            Q * (Real.exp (-(2 * n ^ 2 * eps)) *
              (S.base.metric (time : Real)).inner (alpha q)
                (lVelocity (I := I) alpha q)
                (lVelocity (I := I) alpha q)) := by
                  dsimp only [Q]
                  rw [← mul_assoc, ← Real.exp_add]
                  ring_nf
                  simp
          _ ≤ Q * (S.base.metric ((time : Real) - q ^ 2)).inner (alpha q)
              (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) :=
            mul_le_mul_of_nonneg_left hpair.1 hQpos.le
      calc
        (S.base.metric (time : Real)).inner (alpha q)
            (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) ≤
          Q * (S.base.metric ((time : Real) - q ^ 2)).inner (alpha q)
            (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q) := htermMove
        _ ≤ Q * (1 / (2048 * eps)) :=
          mul_le_mul_of_nonneg_left (by
            simpa only [lRegSpeedSq, alpha] using hqSpeed) hQpos.le
        _ ≤ (4 / 3 : Real) * (1 / (2048 * eps)) :=
          mul_le_mul_of_nonneg_right hQle (by positivity)
        _ = 1 / (1536 * eps) := by
          field_simp [heps.ne']
          ring
    have hE := lRegTerm_int (I := I) S hS (time : Real) B.center Z ht.1 htDom
    have hEint : IntervalIntegrable (fun q ↦
        (S.base.metric (time : Real)).inner (alpha q)
          (lVelocity (I := I) alpha q) (lVelocity (I := I) alpha q))
        volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le]
      simpa only [alpha] using hE
    have hEC : curveEnergy (I := I) (S.base.metric (time : Real)) alpha 0 t ≤
        t / (1536 * eps) := by
      calc
        curveEnergy (I := I) (S.base.metric (time : Real)) alpha 0 t ≤
            ∫ _q in (0 : Real)..t, 1 / (1536 * eps) := by
          unfold curveEnergy
          exact intervalIntegral.integral_mono_on ht.1.le hEint
            intervalIntegrable_const hterm
        _ = t / (1536 * eps) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
    let Bsmall : FlowMetricBall S time :=
      ⟨B.center, B.radius / 32, by nlinarith [B.radius_pos]⟩
    have hreach : Real.sqrt (Real.sqrt (t ^ 2)) *
        Real.sqrt (t / (1536 * eps)) < Bsmall.radius := by
      have htSq : t ^ 2 ≤ eps * B.radius ^ 2 := by
        rw [← hbSq]
        exact (sq_le_sq₀ ht.1.le hbpos.le).2 htIcc.2
      change Real.sqrt (Real.sqrt (t ^ 2)) *
        Real.sqrt (t / (1536 * eps)) < B.radius / 32
      exact reach_small ht.1 heps htSq B.radius_pos
    have hsmall := lExp_mem_ball (I := I) S hS time Bsmall Z (t ^ 2)
      (t / (1536 * eps)) (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1] using htDom)
      (by simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1, alpha, Bsmall] using hE)
      (by simpa only [Real.sqrt_sq_eq_abs, abs_of_pos ht.1, alpha, Bsmall] using hEC)
      hreach
    have halphaO : alpha t ∈ O := by
      simpa only [alpha, O, Bsmall, lExp, Real.sqrt_sq_eq_abs,
        abs_of_pos ht.1, FlowMetricBall.set, FlowMetricBall.setAt] using hsmall
    have hfrontNot : alpha t ∉ interior K := by
      rw [frontier, hKclosed.closure_eq] at hfront
      exact hfront.2
    exact hfrontNot ((interior_maximal hOK hOopen) halphaO)
  have hbDom : b ∈ lRegDomain S (time : Real) B.center Z := by
    apply lRegDomain_of_cpt (I := I) S hS (time : Real) B.center Z b
      hbpos.le hslab K hKcompact (1 / (2048 * eps))
    · intro s hs hsDom
      exact htermRange s hs hsDom
    · intro s hs hsDom
      exact hspeedBound s hs hsDom (fun u hu ↦
        htermRange u ⟨hu.1, hu.2.trans hs.2⟩
          (lRegDomain_seg S (time : Real) B.center Z hsDom hu.1 hu.2))
  intro s hs
  have hsDom : s ∈ lRegDomain S (time : Real) B.center Z :=
    lRegDomain_seg S (time : Real) B.center Z hbDom hs.1 hs.2
  have hsK : alpha s ∈ K := htermRange s hs hsDom
  refine ⟨hsDom, ?_, ?_⟩
  · simpa only [K, alpha] using hsK
  · simpa only [alpha] using hKmove s hs hsK

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A uniformly small parabolic-time L-exponential endpoint lies in the
terminal flow metric ball under the ball-local regularity hypotheses. -/
theorem lExp_ball_unif
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M] :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                  1 / (128 * Real.sqrt eps) →
                lExp S (time : Real) B.center Z (eps * B.radius ^ 2) ∈
                  B.set := by
  obtain ⟨theta, htheta, hthetaOne, hrange⟩ :=
    lRegRange_unif (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  obtain ⟨eps₀, heps₀, hrange'⟩ := hrange rho hrho
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z hZ
  let b : Real := Real.sqrt eps * B.radius
  have hbpos : 0 < b := mul_pos (Real.sqrt_pos.2 heps) B.radius_pos
  have hb : Real.sqrt (eps * B.radius ^ 2) = b := by
    dsimp only [b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs,
      abs_of_pos B.radius_pos]
  have hrangeB := hrange' hS B hBrho hB hreg hcomplete eps heps heps₀ Z hZ b
    ⟨hbpos.le, le_rfl⟩
  change riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
      (lExp S (time : Real) B.center Z (eps * B.radius ^ 2)) <
        ENNReal.ofReal B.radius
  rw [lExp, hb]
  exact hrangeB.2.1.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))

end DifferentialGeometry.PDE.RicciFlow.Perelman
