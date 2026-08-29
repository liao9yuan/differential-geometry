import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.FiniteCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.NormRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.SolutionHeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShiBallCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ScaleTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The scale-one error budget of the fixed ball cutoff in real dimension
`d`. -/
private def shiUnitError (d : Nat) (T : Real) : Real :=
  let dR : Real := d
  let Lambda : Real := dR ^ 2
  let a : Real := 4
  let U : Real := Real.exp (Lambda * T)
  let Csq := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  let Ceta := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  Csq * a ^ 2 * U ^ 2 +
    Ceta * (2 * (dR - 1) * a ^ 2 * U ^ 2 +
      a * U * Real.sqrt ((dR - 1) * Lambda) + a ^ 2 * U ^ 2)

private theorem shiUnitError_cont (d : Nat) :
    Continuous (shiUnitError d) := by
  unfold shiUnitError
  fun_prop

private theorem exists_theta
    (d : Nat) (e : Real → Real) (he : ContinuousAt e 0) :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      Real.exp (2 * (d : Real) ^ 2 * theta) < 2 ∧
      2 * e theta * theta * cutErrCoeff 1 ≤ 1 := by
  let short : Real → Real := fun T ↦
    Real.exp (2 * (d : Real) ^ 2 * T)
  let small : Real → Real := fun T ↦
    2 * e T * T * cutErrCoeff 1
  have hshort_cont : ContinuousAt short 0 := by
    dsimp only [short]
    fun_prop
  have hsmall_cont : ContinuousAt small 0 := by
    dsimp only [small]
    fun_prop
  have hshort_nhds : {T : Real | short T < 2} ∈ nhds 0 :=
    hshort_cont.eventually_lt_const (by norm_num [short])
  have hsmall_nhds : {T : Real | small T < 1} ∈ nhds 0 :=
    hsmall_cont.eventually_lt_const (by norm_num [small])
  obtain ⟨delta, hdelta, hgood⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem hshort_nhds hsmall_nhds)
  let theta : Real := min (1 / 2) (delta / 2)
  have htheta_pos : 0 < theta := by
    dsimp only [theta]
    exact lt_min (by norm_num) (half_pos hdelta)
  have htheta_one : theta < 1 := by
    exact (min_le_left (1 / 2 : Real) (delta / 2)).trans_lt (by norm_num)
  have htheta_delta : theta < delta := by
    exact (min_le_right (1 / 2 : Real) (delta / 2)).trans_lt
      (half_lt_self hdelta)
  have htheta_ball : theta ∈ Metric.ball (0 : Real) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg htheta_pos.le]
    exact htheta_delta
  rcases hgood htheta_ball with ⟨hshort, hsmall⟩
  exact ⟨theta, htheta_pos, htheta_one, hshort, hsmall.le⟩

/-- There is a dimension-only scale-one time on which the cutoff remains
short and its finite Bernstein error can be absorbed. -/
private theorem exists_shi_time (d : Nat) :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      Real.exp (2 * (d : Real) ^ 2 * theta) < 2 ∧
      2 * shiUnitError d theta * theta * cutErrCoeff 1 ≤ 1 :=
  exists_theta d (shiUnitError d) (shiUnitError_cont d).continuousAt

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem shiError_eq_unit
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hradius : B.radius = 1) (T : Real) :
    shiCutoffError (I := I) B T =
      shiUnitError (Module.finrank Real E) T := by
  simp [shiCutoffError, shiUnitError, hradius]

private theorem exists_reg_window
    {D : RealTimeInterval} {T : Real} (hT : 0 < T)
    (hreg : Set.Icc 0 T ⊆ D.regular) :
    ∃ a b : Real, a < 0 ∧ T < b ∧ a < b ∧
      Set.Ico a b ⊆ D.carrier ∧ Set.Ioo a b ⊆ D.regular := by
  have hzero : (0 : Real) ∈ D.regular := hreg ⟨le_rfl, hT.le⟩
  have htop : T ∈ D.regular := hreg ⟨hT.le, le_rfl⟩
  obtain ⟨delta0, hdelta0, hball0⟩ :=
    Metric.mem_nhds_iff.mp (D.regular_isOpen.mem_nhds hzero)
  obtain ⟨deltaT, hdeltaT, hballT⟩ :=
    Metric.mem_nhds_iff.mp (D.regular_isOpen.mem_nhds htop)
  let a : Real := -(delta0 / 2)
  let b : Real := T + deltaT / 2
  have ha : a < 0 := by
    dsimp only [a]
    linarith [half_pos hdelta0]
  have hb : T < b := by
    dsimp only [b]
    linarith [half_pos hdeltaT]
  have hab : a < b := ha.trans (hT.trans hb)
  have hsub : Set.Ico a b ⊆ D.regular := by
    intro q hq
    by_cases hq0 : q ≤ 0
    · apply hball0
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonpos hq0]
      dsimp only [a] at hq
      linarith [hq.1, half_lt_self hdelta0]
    · by_cases hqT : q ≤ T
      · exact hreg ⟨le_of_not_ge hq0, hqT⟩
      · apply hballT
        rw [Metric.mem_ball, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hqT))]
        dsimp only [b] at hq
        linarith [hq.2, half_lt_self hdeltaT]
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · exact fun q hq ↦ D.regular_subset (hsub hq)
  · exact fun q hq ↦ hsub ⟨hq.1.le, hq.2⟩

private def shiCost (d : Nat) : Real :=
  max (rmTowerCost d 0) (rmTowerCost d 1)

private theorem shiCost_nonneg (d : Nat) : 0 ≤ shiCost d :=
  (rmTowerCost_nonneg d 0).trans (le_max_left _ _)

private def shiUnitBound (d : Nat) (T : Real) : Real :=
  let c := shiCost d
  let beta := towerBeta c T (towerConst c T) 1
  2 * ((towerConst c T 1) ^ 2 +
    9 * shiUnitError d T * beta * T) / T

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem shiRm1_unit
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real} (hT : 0 < T) (hTone : T ≤ 1)
    (htime : (time : Real) = T) (hradius : B.radius = 1)
    (hreg : Set.Icc 0 T ⊆ D.regular)
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * (Module.finrank Real E : Real) ^ 2 * T) < 2)
    (hsmall : 2 * shiUnitError (Module.finrank Real E) T * T *
      cutErrCoeff 1 ≤ 1)
    {t : Real} (ht : t ∈ Set.Icc (T / 2) T) {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (1 / 8 : Real)) :
    nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
      shiUnitBound (Module.finrank Real E) T := by
  classical
  letI : IsManifold I 1 M := IsManifold.of_le
    (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  letI : IsManifold I 2 M := IsManifold.of_le
    (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  let d : Nat := Module.finrank Real E
  let c : Real := shiCost d
  let beta : Real := towerBeta c T (towerConst c T) 1
  have hc : 0 ≤ c := by
    simpa only [c] using shiCost_nonneg d
  have hbeta : 0 ≤ beta := by
    simpa only [beta] using towerBeta_nonneg hc hT.le 1
  have hTB : Set.Icc 0 T ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro s hs
    rw [htime, hradius]
    norm_num
    constructor
    · linarith [hs.1, hTone]
    · exact hs.2
  have hslab : Set.Icc 0 T ⊆ D.carrier := fun s hs ↦
    D.regular_subset (hreg hs)
  have hregular : ∀ s ∈ Set.Icc 0 T, 0 < s → s ∈ D.regular :=
    fun s hs _ ↦ hreg hs
  have hregCut : Set.Ioc 0 T ⊆ D.regular := fun s hs ↦
    hreg ⟨hs.1.le, hs.2⟩
  have hshortCut : Real.exp
      (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * T) < 2 := by
    simpa only [hradius, one_pow, div_one, mul_assoc] using hshort
  let cut : ShiFixedCutoff (I := I) (flowG (I := I) S) T
      (shiCutoffError (I := I) B T) :=
    shiFixedCutoff (I := I) hS B hB hT hregCut hTB hcomplete hshortCut
  have hsmallCut :
      2 * shiCutoffError (I := I) B T * T * cutErrCoeff 1 ≤ 1 := by
    rw [shiError_eq_unit (I := I) B hradius T]
    exact hsmall
  obtain ⟨a, b, ha, hb, hab, hcarCo, hregCo⟩ :=
    exists_reg_window hT hreg
  let Dco : RealTimeInterval := RealTimeInterval.closedOpen a b hab
  let Sco : SolutionOn (I := I) (M := M) Dco := S.timeRestrict Dco
  have hSco : IsSolutionOn (I := I) Sco := by
    apply isSoln_timeRestrict (I := I) hS
    · simpa only [Dco, RealTimeInterval.closedOpen] using hcarCo
    · simpa only [Dco, RealTimeInterval.closedOpen] using hregCo
  have hfield_restrict (q : Real) (k : Nat) :
      nablaKRm04Field (I := I) S q k =
        nablaKRm04Field (I := I) Sco q k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [nablaKRm04Field_succ, nablaKRm04Field_succ]
        simp only [Sco, SolutionOn.timeRestrict, SolutionOn.family, ih]
  have hw_cont : ∀ k ≤ 1,
      ContinuousOn
        (fun p : Real × M ↦
          nablaKRm04NormSqIntrinsic (I := I) S k p.1 p.2)
        (spacetimeSlab (M := M) T) := by
    intro k _hk
    have hJoint := (towerNorm_joint (I := I) hSco k).continuousOn
    have hSub : spacetimeSlab (M := M) T ⊆ Dco.regular ×ˢ Set.univ := by
      intro p hp
      change p.1 ∈ Set.Icc 0 T ∧ p.2 ∈ Set.univ at hp
      change p.1 ∈ Set.Ioo a b ∧ p.2 ∈ Set.univ
      exact ⟨⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩, hp.2⟩
    have hfun :
        (fun p : Real × M ↦
          nablaKRm04NormSqIntrinsic (I := I) S k p.1 p.2) =
        (fun p : Real × M ↦
          nablaKRm04NormSqIntrinsic (I := I) Sco k p.1 p.2) := by
      funext p
      unfold nablaKRm04NormSqIntrinsic
      rw [hfield_restrict p.1 k]
      rfl
    rw [hfun]
    exact hJoint.mono hSub
  have hw0_cut : ∀ s ∈ Set.Icc 0 T, ∀ y,
      0 < cut.chi s y →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1 ^ 2 := by
    intro s hs y hy
    have hy' : 0 < shiBallCutoff (I := I) B s y := by
      simpa only [cut, shiFixedCutoff] using hy
    have hdist := shiCutoff_dist_lt (I := I) B hs.1 hy'
    have hyset : y ∈ B.setAt s := by
      exact hdist.trans
        ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2
          (by linarith [B.radius_pos]))
    have hraw := hB.2 s (hTB hs) y hyset
    simpa only [hradius, one_pow, one_mul, FlowMetricBall.rmNormSq,
      nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hraw
  have hheat : ∀ k ≤ 1,
      TowerHeatBoundOn (D := D)
        (nablaKRm04NormSqIntrinsic (I := I) S)
        (nablaKNormLap (I := I) S) c k := by
    intro k hk
    apply TowerHeatBoundOn.mono_cost (h := towerHeatSol_raw (I := I) S hS k)
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hLap : ∀ k ≤ 1, ∀ s ∈ Set.Icc 0 T, 0 < s → ∀ y,
      heatOperatorWithDrift (I := I) (flowG (I := I) S) s
        (fun z : M ↦ (0 : TangentSpace I z))
        (nablaKRm04NormSqIntrinsic (I := I) S k s) y =
          nablaKNormLap (I := I) S k s y := by
    intro k _hk s _hs _hspos y
    rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt,
      laplacianAt_eq]
    rfl
  have hEstimate := estimate_cutoff_one (I := I) (D := D)
    (flowG (I := I) S)
    (nablaKRm04NormSqIntrinsic (I := I) S)
    (nablaKNormLap (I := I) S)
    T c 1 T (shiCutoffError (I := I) B T) cut
    hT hc one_pos hT.le hslab hregular (by norm_num) hsmallCut
    (fun k _hk s _hs y ↦
      nablaKRm04NormSqIntrinsic_nonneg (I := I) S k s y)
    hw0_cut hheat hLap hw_cont
    (fun k _hk s _hs _hspos y ↦
      (nablaKNorm_smooth (I := I) S s k).contMDiffAt.mdifferentiableAt (by simp))
    (fun k _hk s _hs _hspos y ↦
      gradientFun_mdiffAt (I := I) (S.base.metric s)
        (nablaKNorm_smooth (I := I) S s k) y)
    (fun k _hk s _hs _hspos y ↦ towerNorm_grad_le (I := I) S k s y)
  have htpos : 0 < t := by linarith [ht.1, hT]
  have hexp : Real.exp ((d : Real) ^ 2 * t) < 2 := by
    have harg : (d : Real) ^ 2 * t ≤ 2 * (d : Real) ^ 2 * T := by
      nlinarith [sq_nonneg (d : Real), ht.2, hT]
    have hshort' : Real.exp (2 * (d : Real) ^ 2 * T) < 2 := by
      simpa only [d] using hshort
    exact (Real.exp_le_exp.mpr harg).trans_lt hshort'
  have hplateReal : (1 / 8 : Real) ≤
      1 / (4 * Real.exp ((d : Real) ^ 2 * t)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 8)
      (mul_pos (by norm_num) (Real.exp_pos _))]
    nlinarith [hexp]
  have hchi : shiBallCutoff (I := I) B t x = 1 := by
    apply shiCutoff_one (I := I) B
    apply hx.le.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [hradius, one_pow, div_one, d] using hplateReal
  have hchiCut : cut.chi t x = 1 := by
    simpa only [cut, shiFixedCutoff] using hchi
  have hpoint := hEstimate t ⟨(by linarith [ht.1, hT]), ht.2⟩ htpos x
  rw [hchiCut, shiError_eq_unit (I := I) B hradius T] at hpoint
  norm_num at hpoint
  have heps : 0 ≤ shiUnitError d T := by
    rw [← shiError_eq_unit (I := I) B hradius T]
    exact cutoffError_nonneg (I := I) B T
  have hcoef : 0 ≤ 9 * shiUnitError d T * beta := by positivity
  have htimeTerm :
      9 * shiUnitError d T * beta * t ≤
        9 * shiUnitError d T * beta * T :=
    mul_le_mul_of_nonneg_left ht.2 hcoef
  have htimeTerm' :
      9 * shiUnitError (Module.finrank Real E) T *
          towerBeta c T (towerConst c T) 1 * t ≤
        9 * shiUnitError d T * beta * T := by
    simpa only [d, beta] using htimeTerm
  have htop :
      t * nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
        (towerConst c T 1) ^ 2 +
          9 * shiUnitError d T * beta * T :=
    by nlinarith [hpoint, htimeTerm']
  have hw : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 t x
  have hleft :
      (T / 2) * nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
        t * nablaKRm04NormSqIntrinsic (I := I) S 1 t x :=
    mul_le_mul_of_nonneg_right ht.1 hw
  apply (le_div_iff₀ hT).2
  dsimp only [shiUnitBound, c, beta, d]
  nlinarith [hleft, htop]

private theorem shiRm1_scaled
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {theta : Real} (htheta : 0 < theta) (htheta_one : theta < 1)
    (hshort : Real.exp
      (2 * (Module.finrank Real E : Real) ^ 2 * theta) < 2)
    (hsmall : 2 * shiUnitError (Module.finrank Real E) theta * theta *
      cutErrCoeff 1 ≤ 1)
    (hreg : Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆
      D.regular)
    (hcomplete : ∀ q ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2) (time : Real),
        RiemannianMetricComplete (I := I) (S.base.metric q))
    {t : Real}
    (ht : t ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real))
    {x : M}
    (hx : riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal (B.radius / 8)) :
    B.radius ^ 6 *
        nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤
      shiUnitBound (Module.finrank Real E) theta := by
  classical
  let R : Real := B.radius⁻¹ ^ 2
  let tau : Real := (time : Real) - theta * B.radius ^ 2
  have hR : 0 < R := by
    exact pow_pos (inv_pos.mpr B.radius_pos) 2
  have htau_window : tau ∈
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
    dsimp only [tau]
    constructor
    · nlinarith [sq_pos_of_pos B.radius_pos]
    · nlinarith [mul_nonneg htheta.le (sq_nonneg B.radius)]
  have htau : tau ∈ D.carrier := hB.1 htau_window
  have hpara (q : Real) :
      paraTime tau R q =
        (time : Real) - theta * B.radius ^ 2 + q * B.radius ^ 2 := by
    unfold paraTime
    dsimp only [tau, R]
    field_simp [ne_of_gt B.radius_pos]
  have hpara_end : paraTime tau R theta = (time : Real) := by
    rw [hpara]
    ring
  have htheta_carrier : theta ∈ (paraInterval D tau R hR htau).carrier := by
    change paraTime tau R theta ∈ D.carrier
    rw [hpara_end]
    exact time.2
  let st : (paraInterval D tau R hR htau).FlowTime :=
    ⟨theta, htheta_carrier⟩
  let B0 : FlowMetricBall S (paraFlowTime tau R hR htau st) :=
    { center := B.center
      radius := B.radius
      radius_pos := B.radius_pos }
  have htime0 :
      (paraFlowTime tau R hR htau st : Real) = (time : Real) := by
    simpa only [paraFlowTime_coe, st] using hpara_end
  have hB0 : B0.IsRmControlled := by
    constructor
    · intro s hs
      apply hB.1
      simpa only [B0, htime0] using hs
    · intro s hs y hy
      have hs' : s ∈ Set.Icc
          ((time : Real) - B.radius ^ 2) (time : Real) := by
        simpa only [B0, htime0] using hs
      have hy' : y ∈ B.setAt s := by
        simpa only [B0, FlowMetricBall.setAt] using hy
      simpa only [B0] using hB.2 s hs' y hy'
  let Sn : SolutionOn (I := I) (M := M) (paraInterval D tau R hR htau) :=
    paraSolution (I := I) S tau R hR htau
  let Bn : FlowMetricBall Sn st :=
    paraBall S tau R hR htau st B0
  have hSn : IsSolutionOn (I := I) Sn := by
    exact paraSol (I := I) S hS tau R hR htau
  have hBn : Bn.IsRmControlled := by
    exact paraBall_rm (I := I) S tau R hR htau st B0 hB0
  have hsqrtR : Real.sqrt R = B.radius⁻¹ := by
    dsimp only [R]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr B.radius_pos)]
  have hBn_radius : Bn.radius = 1 := by
    dsimp only [Bn, paraBall, B0]
    rw [hsqrtR]
    exact inv_mul_cancel₀ (ne_of_gt B.radius_pos)
  have hregn : Set.Icc 0 theta ⊆
      (paraInterval D tau R hR htau).regular := by
    intro q hq
    change paraTime tau R q ∈ D.regular
    apply hreg
    rw [hpara]
    constructor
    · have hcoef : 0 < 1 - theta + q := by linarith [hq.1]
      have hprod : 0 < (1 - theta + q) * B.radius ^ 2 :=
        mul_pos hcoef (sq_pos_of_pos B.radius_pos)
      nlinarith
    · have hmul :=
        mul_le_mul_of_nonneg_right hq.2 (sq_nonneg B.radius)
      nlinarith
  have hcompleten : ∀ q ∈ Set.Icc 0 theta,
      RiemannianMetricComplete (I := I) (Sn.base.metric q) := by
    intro q hq
    have hq_old : paraTime tau R q ∈ Set.Icc
        ((time : Real) - theta * B.radius ^ 2) (time : Real) := by
      rw [hpara]
      have hlow := mul_nonneg hq.1 (sq_nonneg B.radius)
      have hupp :=
        mul_le_mul_of_nonneg_right hq.2 (sq_nonneg B.radius)
      constructor <;> nlinarith
    change RiemannianMetricComplete (I := I)
      (scaleMetric (I := I) R hR (S.base.metric (paraTime tau R q)))
    apply RiemannianMetricComplete.of_lower (hcomplete _ hq_old) hR
    intro y v
    rw [scaleMetric_inner]
  let q : Real := paraBack tau R t
  have hq_time : paraTime tau R q = t := by
    exact paraTime_back (ne_of_gt hR)
  have hq_eq :
      (time : Real) - theta * B.radius ^ 2 + q * B.radius ^ 2 = t := by
    rw [← hpara q, hq_time]
  have hq : q ∈ Set.Icc (theta / 2) theta := by
    constructor
    · by_contra hnot
      have hlt : q < theta / 2 := lt_of_not_ge hnot
      have hmul :=
        mul_lt_mul_of_pos_right hlt (sq_pos_of_pos B.radius_pos)
      nlinarith [ht.1]
    · by_contra hnot
      have hlt : theta < q := lt_of_not_ge hnot
      have hmul :=
        mul_lt_mul_of_pos_right hlt (sq_pos_of_pos B.radius_pos)
      nlinarith [ht.2]
  have hx_scaled :
      riemannianEDistOf (I := I) (Sn.base.metric q) Bn.center x <
        ENNReal.ofReal (1 / 8 : Real) := by
    have hx' :
        riemannianEDistOf (I := I)
            (scaleMetric (I := I) R hR (S.base.metric t)) B.center x <
          ENNReal.ofReal (Real.sqrt R * (B.radius / 8)) := by
      change x ∈ {y : M | riemannianEDistOf (I := I)
        (scaleMetric (I := I) R hR (S.base.metric t)) B.center y <
          ENNReal.ofReal (Real.sqrt R * (B.radius / 8))}
      rw [edistBall_scale (I := I)]
      exact hx
    have hscale_radius : Real.sqrt R * (B.radius / 8) = 1 / 8 := by
      rw [hsqrtR]
      field_simp [ne_of_gt B.radius_pos]
    change riemannianEDistOf (I := I)
        (scaleMetric (I := I) R hR (S.base.metric (paraTime tau R q)))
          B.center x < ENNReal.ofReal (1 / 8 : Real)
    rw [hq_time, ← hscale_radius]
    exact hx'
  have hunit := shiRm1_unit (I := I) hSn Bn hBn htheta
    htheta_one.le rfl hBn_radius hregn hcompleten hshort hsmall hq hx_scaled
  have hscale := paraNablaRmNormSq (I := I) S tau R hR htau q x
  rw [hq_time] at hscale
  have hR_inv : R⁻¹ = B.radius ^ 2 := by
    dsimp only [R]
    field_simp [ne_of_gt B.radius_pos]
  calc
    B.radius ^ 6 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x =
        (R⁻¹) ^ 3 * nablaKRm04NormSqIntrinsic (I := I) S 1 t x := by
          rw [hR_inv]
          ring
    _ = nablaKRm04NormSqIntrinsic (I := I) Sn 1 q x := hscale.symm
    _ ≤ shiUnitBound (Module.finrank Real E) theta := hunit

/-- A first spatial derivative of curvature is controlled on the later half
of a strictly smaller cylinder inside any curvature-controlled flow ball. -/
theorem shiRm1_ball
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M] :
    ∃ theta C : Real, 0 < theta ∧ theta < 1 ∧ 0 < C ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D}
          (B : FlowMetricBall S time), B.IsRmControlled →
          Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          (∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2) (time : Real),
              RiemannianMetricComplete (I := I) (S.base.metric q)) →
          ∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real),
            ∀ x : M,
              riemannianEDistOf (I := I) (S.base.metric q) B.center x <
                ENNReal.ofReal (B.radius / 8) →
              Real.sqrt
                  (nablaKRm04NormSqIntrinsic (I := I) S 1 q x) ≤
                C / B.radius ^ 3 := by
  let d : Nat := Module.finrank Real E
  obtain ⟨theta, htheta, htheta_one, hshort, hsmall⟩ := exists_shi_time d
  let A : Real := shiUnitBound d theta
  let C : Real := Real.sqrt A + 1
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [Real.sqrt_nonneg A]
  refine ⟨theta, C, htheta, htheta_one, hC, ?_⟩
  intro D S hS time B hB hreg hcomplete q hq x hx
  have hscaled := shiRm1_scaled (I := I) hS B hB htheta htheta_one
    (by simpa only [d] using hshort) (by simpa only [d] using hsmall)
    hreg hcomplete hq hx
  let W : Real := nablaKRm04NormSqIntrinsic (I := I) S 1 q x
  change B.radius ^ 6 * W ≤ A at hscaled
  have hW : 0 ≤ W := by
    exact nablaKRm04NormSqIntrinsic_nonneg (I := I) S 1 q x
  have hA : 0 ≤ A := by
    exact (mul_nonneg (pow_nonneg B.radius_pos.le 6) hW).trans hscaled
  have hsqrtW : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hW
  have hsqrtA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hroot : B.radius ^ 3 * Real.sqrt W ≤ Real.sqrt A := by
    apply (sq_le_sq₀
      (mul_nonneg (pow_nonneg B.radius_pos.le 3) (Real.sqrt_nonneg W))
      (Real.sqrt_nonneg A)).mp
    calc
      (B.radius ^ 3 * Real.sqrt W) ^ 2 = B.radius ^ 6 * W := by
        rw [mul_pow, hsqrtW]
        ring
      _ ≤ A := hscaled
      _ = (Real.sqrt A) ^ 2 := hsqrtA.symm
  apply (le_div_iff₀ (pow_pos B.radius_pos 3)).2
  dsimp only [C, W]
  nlinarith

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
