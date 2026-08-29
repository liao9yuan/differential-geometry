import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShiBallAnchor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShiBallCalabi

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

/-- The fixed-radius radial cutoff associated to a controlled flow metric
ball, with parabolic scale built into the distance variable. -/
def shiBallCutoff
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (s : Real) (y : M) : Real :=
  let d : Real := Module.finrank Real E
  let Λ : Real := d ^ 2 / B.radius ^ 2
  DifferentialGeometry.Analysis.CutoffProfile.evalue
    (ENNReal.ofReal (4 * Real.exp (Λ * s) / B.radius) *
      riemannianEDistOf (I := I) (S.base.metric s) B.center y)

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The fixed radial cutoff is one on its exact inner plateau. -/
theorem shiCutoff_one
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) {s : Real} {y : M}
    (hy : riemannianEDistOf (I := I) (S.base.metric s) B.center y ≤
      ENNReal.ofReal (B.radius /
        (4 * Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * s)))) :
    shiBallCutoff (I := I) B s y = 1 := by
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let A : Real := 4 * Real.exp (Lambda * s) / B.radius
  have hA : 0 < A :=
    div_pos (mul_pos (by norm_num) (Real.exp_pos _)) B.radius_pos
  dsimp only [shiBallCutoff]
  apply DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
  calc
    ENNReal.ofReal A *
          riemannianEDistOf (I := I) (S.base.metric s) B.center y ≤
        ENNReal.ofReal A * ENNReal.ofReal
          (B.radius / (4 * Real.exp (Lambda * s))) :=
      mul_le_mul_of_nonneg_left (by simpa only [d, Lambda] using hy) (by simp)
    _ = ENNReal.ofReal
          (A * (B.radius / (4 * Real.exp (Lambda * s)))) := by
      rw [ENNReal.ofReal_mul hA.le]
    _ = 1 := by
      have hmul : A * (B.radius / (4 * Real.exp (Lambda * s))) = 1 := by
        dsimp only [A]
        field_simp [ne_of_gt B.radius_pos, ne_of_gt (Real.exp_pos _)]
      rw [hmul]
      norm_num

/-- The time-zero half-ball that carries the fixed radial cutoff after the
local distance anchor is applied. -/
def shiBallSupport
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) : Set M :=
  {x : M |
    riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
      ENNReal.ofReal (B.radius / 2)}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Completeness of the time-zero metric makes the fixed cutoff support
compact. -/
theorem shiBallSupport_cpt
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time)
    (h0 : RiemannianMetricComplete (I := I) (S.base.metric 0)) :
    IsCompact (shiBallSupport (I := I) B) := by
  simpa only [shiBallSupport] using
    (RiemannianMetricComplete.closedEBall_isCompact
      (I := I) h0 B.center (B.radius / 2))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem dist_support_pair
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hTB : Set.Icc 0 T ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * T) < 2)
    {s t : Real} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) {x : M} (hx : x ∈ shiBallSupport (I := I) B) :
    riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x ∧
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x := by
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  have hLambda : 0 ≤ Lambda :=
    div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  have h0T : 0 ≤ T := hs.1.trans hs.2
  have hx0 :
      riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
        ENNReal.ofReal (B.radius / 2) := by
    simpa only [shiBallSupport, Set.mem_setOf_eq] using hx
  have hexp_s : Real.exp (2 * Lambda * s) < 2 := by
    have harg : 2 * Lambda * s ≤ 2 * Lambda * T := by
      nlinarith [hLambda, hs.2]
    exact (Real.exp_le_exp.mpr harg).trans_lt
      (by simpa only [Lambda, d] using hshort)
  have hreal_s : Real.exp (2 * Lambda * s) * (B.radius / 2) < B.radius := by
    have hmul := mul_lt_mul_of_pos_right hexp_s
      (div_pos B.radius_pos (by norm_num : (0 : Real) < 2))
    nlinarith
  have hroom0 :
      ENNReal.ofReal (Real.exp (2 * Lambda * s)) *
          riemannianEDistOf (I := I) (S.base.metric 0) B.center x <
        ENNReal.ofReal B.radius := by
    calc
      ENNReal.ofReal (Real.exp (2 * Lambda * s)) *
          riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
          ENNReal.ofReal (Real.exp (2 * Lambda * s)) *
            ENNReal.ofReal (B.radius / 2) :=
        mul_le_mul_right hx0 _
      _ = ENNReal.ofReal
          (Real.exp (2 * Lambda * s) * (B.radius / 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 hreal_s
  have hpair0 := distPair_scaled (I := I) hS B hB hs.1
    (fun r hr ↦ hreg ⟨hr.1, hr.2.trans hs.2⟩)
    (fun r hr ↦ hTB ⟨hr.1, hr.2.trans hs.2⟩)
    (hcomplete 0 ⟨le_rfl, h0T⟩) (hcomplete s hs) (x := x)
    (by simpa only [Lambda, d, sub_zero] using hroom0)
  have hdist_s :
      riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
        ENNReal.ofReal (Real.exp (Lambda * s)) *
          riemannianEDistOf (I := I) (S.base.metric 0) B.center x := by
    simpa only [Lambda, d, sub_zero] using hpair0.2
  have hexp_st :
      Real.exp (2 * Lambda * (t - s) + Lambda * s) < 2 := by
    have harg : 2 * Lambda * (t - s) + Lambda * s ≤
        2 * Lambda * T := by
      nlinarith [hLambda, hs.1, ht.2]
    exact (Real.exp_le_exp.mpr harg).trans_lt
      (by simpa only [Lambda, d] using hshort)
  have hreal_st :
      Real.exp (2 * Lambda * (t - s) + Lambda * s) *
          (B.radius / 2) < B.radius := by
    have hmul := mul_lt_mul_of_pos_right hexp_st
      (div_pos B.radius_pos (by norm_num : (0 : Real) < 2))
    nlinarith
  have hroom_st :
      ENNReal.ofReal (Real.exp (2 * Lambda * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x <
        ENNReal.ofReal B.radius := by
    calc
      ENNReal.ofReal (Real.exp (2 * Lambda * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
          ENNReal.ofReal (Real.exp (2 * Lambda * (t - s))) *
            (ENNReal.ofReal (Real.exp (Lambda * s)) *
              riemannianEDistOf
                (I := I) (S.base.metric 0) B.center x) :=
        mul_le_mul_right hdist_s _
      _ = ENNReal.ofReal
            (Real.exp (2 * Lambda * (t - s) + Lambda * s)) *
          riemannianEDistOf (I := I) (S.base.metric 0) B.center x := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add]
      _ ≤ ENNReal.ofReal
            (Real.exp (2 * Lambda * (t - s) + Lambda * s)) *
          ENNReal.ofReal (B.radius / 2) :=
        mul_le_mul_right hx0 _
      _ = ENNReal.ofReal
          (Real.exp (2 * Lambda * (t - s) + Lambda * s) *
            (B.radius / 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ < ENNReal.ofReal B.radius :=
        (ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 hreal_st
  simpa only [Lambda, d] using
    distPair_scaled (I := I) hS B hB hst
      (fun r hr ↦ hreg ⟨hs.1.trans_lt hr.1, hr.2.trans ht.2⟩)
      (fun r hr ↦ hTB ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩)
      (hcomplete s hs) (hcomplete t ht) (x := x) hroom_st

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem dist_support_cont
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hTB : Set.Icc 0 T ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * T) < 2) :
    ContinuousOn
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2)
      (Set.Icc 0 T ×ˢ shiBallSupport (I := I) B) := by
  classical
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  intro p hp
  let A : Real × M → Real := fun q ↦ Lambda * |q.1 - p.1|
  let dp : Real × M → ENNReal := fun q ↦
    riemannianEDistOf (I := I) (S.base.metric p.1) B.center q.2
  have hA : Continuous A :=
    continuous_const.mul (continuous_fst.sub continuous_const).abs
  have hdp : Continuous dp := by
    have hfixed : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) B.center y) := by
      unfold riemannianEDistOf
      exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
        (I := I) (S.base.metric p.1) B.center
    exact hfixed.comp continuous_snd
  have hlo : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.exp (-A q))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hA.neg)
  have hhi : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.exp (A q))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hA)
  have hlo_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.exp (-A q)) * dp q) :=
    hlo.ennreal_mul hdp
      (fun q ↦ Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  have hhi_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.exp (A q)) * dp q) :=
    hhi.ennreal_mul hdp
      (fun q ↦ Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  have hbounds : ∀ q ∈ Set.Icc 0 T ×ˢ shiBallSupport (I := I) B,
      dp q ≤ ENNReal.ofReal (Real.exp (A q)) *
          riemannianEDistOf (I := I) (S.base.metric q.1) B.center q.2 ∧
        riemannianEDistOf (I := I) (S.base.metric q.1) B.center q.2 ≤
          ENNReal.ofReal (Real.exp (A q)) * dp q := by
    intro q hq
    by_cases hpq : p.1 ≤ q.1
    · simpa only [A, dp, Lambda, d,
        abs_of_nonneg (sub_nonneg.mpr hpq)] using
        dist_support_pair (I := I) hS B hB hreg hTB hcomplete hshort
          hp.1 hq.1 hpq hq.2
    · have hqp : q.1 ≤ p.1 := le_of_not_ge hpq
      have hpair := dist_support_pair (I := I) hS B hB hreg hTB
        hcomplete hshort hq.1 hp.1 hqp hq.2
      simpa only [A, dp, Lambda, d,
        abs_of_nonpos (sub_nonpos.mpr hqp), neg_sub] using
        And.intro hpair.2 hpair.1
  have hcancel : ∀ q : Real × M,
      ENNReal.ofReal (Real.exp (-A q)) *
          ENNReal.ofReal (Real.exp (A q)) = 1 := by
    intro q
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun q : Real × M ↦ ENNReal.ofReal (Real.exp (-A q)) * dp q)
    (h := fun q : Real × M ↦ ENNReal.ofReal (Real.exp (A q)) * dp q)
    ?_ ?_ ?_ ?_
  · simpa only [A, dp, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (hlo_mul.tendsto p).mono_left inf_le_left
  · simpa only [A, dp, sub_self, abs_zero, mul_zero,
      Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (hhi_mul.tendsto p).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hb := (hbounds q hq).1
    calc
      ENNReal.ofReal (Real.exp (-A q)) * dp q ≤
          ENNReal.ofReal (Real.exp (-A q)) *
            (ENNReal.ofReal (Real.exp (A q)) *
              riemannianEDistOf
                (I := I) (S.base.metric q.1) B.center q.2) :=
        mul_le_mul_right hb _
      _ = riemannianEDistOf
          (I := I) (S.base.metric q.1) B.center q.2 := by
        rw [← mul_assoc, hcancel q, one_mul]
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hbounds q hq).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a sufficiently short controlled slab, the fixed ball cutoff is jointly
continuous on its compact time-zero support. -/
theorem shiBallCutoff_cont
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hTB : Set.Icc 0 T ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * T) < 2) :
    ContinuousOn (fun p : Real × M ↦ shiBallCutoff (I := I) B p.1 p.2)
      (Set.Icc 0 T ×ˢ shiBallSupport (I := I) B) := by
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  have hdist := dist_support_cont (I := I) hS B hB hreg hTB hcomplete hshort
  have hreal : Continuous (fun p : Real × M ↦
      4 * Real.exp (Lambda * p.1) / B.radius) := by
    simpa only [div_eq_mul_inv] using
      ((continuous_const.mul
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst))).mul continuous_const)
  have hcoef : Continuous (fun p : Real × M ↦
      ENNReal.ofReal (4 * Real.exp (Lambda * p.1) / B.radius)) :=
    ENNReal.continuous_ofReal.comp hreal
  have harg : ContinuousOn (fun p : Real × M ↦
      ENNReal.ofReal (4 * Real.exp (Lambda * p.1) / B.radius) *
        riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2)
      (Set.Icc 0 T ×ˢ shiBallSupport (I := I) B) :=
    hcoef.continuousOn.ennreal_mul hdist
      (fun p _ ↦ Or.inl (ENNReal.ofReal_ne_zero_iff.mpr
        (div_pos (mul_pos (by norm_num) (Real.exp_pos _)) B.radius_pos)))
      (fun _ _ ↦ Or.inr ENNReal.ofReal_ne_top)
  have hcomp :=
    DifferentialGeometry.Analysis.CutoffProfile.continuous_evalue
      |>.comp_continuousOn harg
  simpa only [shiBallCutoff, Lambda, d] using hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The fixed radial cutoff vanishes outside its time-zero half-ball support. -/
theorem shiCutoff_zero
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real} (ht : 0 ≤ t)
    (hreg : Set.Ioc 0 t ⊆ D.regular)
    (htB : Set.Icc 0 t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M} (hx : x ∉ shiBallSupport (I := I) B) :
    shiBallCutoff (I := I) B t x = 0 := by
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let q : ENNReal :=
    ENNReal.ofReal (Real.exp (Lambda * t)) *
      riemannianEDistOf (I := I) (S.base.metric t) B.center x
  let a : Real := 4 / B.radius
  have ha : 0 ≤ a := (div_pos (by norm_num) B.radius_pos).le
  have harg :
      ENNReal.ofReal (4 * Real.exp (Lambda * t) / B.radius) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x =
        ENNReal.ofReal a * q := by
    dsimp only [a, q]
    rw [show 4 * Real.exp (Lambda * t) / B.radius =
        (4 / B.radius) * Real.exp (Lambda * t) by ring,
      ENNReal.ofReal_mul ha]
    ring
  have hhalf :
      (2 : ENNReal) = ENNReal.ofReal a * ENNReal.ofReal (B.radius / 2) := by
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : Real) := by norm_num
      _ = ENNReal.ofReal (a * (B.radius / 2)) := by
        congr 1
        dsimp only [a]
        field_simp [B.radius_pos.ne']
        norm_num
      _ = ENNReal.ofReal a * ENNReal.ofReal (B.radius / 2) :=
        ENNReal.ofReal_mul ha
  have hfour :
      (4 : ENNReal) = ENNReal.ofReal a * ENNReal.ofReal B.radius := by
    calc
      (4 : ENNReal) = ENNReal.ofReal (4 : Real) := by norm_num
      _ = ENNReal.ofReal (a * B.radius) := by
        congr 1
        dsimp only [a]
        field_simp [B.radius_pos.ne']
      _ = ENNReal.ofReal a * ENNReal.ofReal B.radius :=
        ENNReal.ofReal_mul ha
  have htwo : (2 : ENNReal) ≤
      ENNReal.ofReal (4 * Real.exp (Lambda * t) / B.radius) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x := by
    rw [harg]
    by_cases hq : q < ENNReal.ofReal B.radius
    · have hanchor := dist0_le_scaled (I := I) hS B hB ht hreg htB
        hcomplete_t (x := x) (by simpa only [q, Lambda, d] using hq)
      have hx' : ¬ riemannianEDistOf
          (I := I) (S.base.metric 0) B.center x ≤
            ENNReal.ofReal (B.radius / 2) := by
        simpa only [shiBallSupport, Set.mem_setOf_eq] using hx
      have hhalf_le : ENNReal.ofReal (B.radius / 2) ≤ q :=
        (lt_of_not_ge hx').le.trans (by simpa only [q, Lambda, d] using hanchor)
      rw [hhalf]
      simpa only [mul_comm] using
        mul_le_mul_right hhalf_le (ENNReal.ofReal a)
    · have hq' : ENNReal.ofReal B.radius ≤ q := le_of_not_gt hq
      calc
        (2 : ENNReal) ≤ 4 := by norm_num
        _ = ENNReal.ofReal a * ENNReal.ofReal B.radius := hfour
        _ ≤ ENNReal.ofReal a * q :=
          by simpa only [mul_comm] using
            mul_le_mul_right hq' (ENNReal.ofReal a)
  dsimp only [shiBallCutoff, Lambda, d]
  exact DifferentialGeometry.Analysis.CutoffProfile.evalue_zero_of_ge htwo

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The ball cutoff always takes values between zero and one. -/
theorem shiBallCutoff_mem
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (s : Real) (y : M) :
    shiBallCutoff (I := I) B s y ∈ Set.Icc (0 : Real) 1 := by
  exact DifferentialGeometry.Analysis.CutoffProfile.evalue_mem_Icc _

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The ball cutoff equals one at its center. -/
theorem shiBallCutoff_ctr
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (s : Real) :
    shiBallCutoff (I := I) B s B.center = 1 := by
  dsimp only [shiBallCutoff]
  apply DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
  rw [riemannianEDistOf_self]
  simp only [mul_zero, zero_le_one]

/-- The scale-exact error budget for the fixed radial ball cutoff. -/
def shiCutoffError
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (T : Real) : Real :=
  let d : Real := Module.finrank Real E
  let Λ : Real := d ^ 2 / B.radius ^ 2
  let a : Real := 4 / B.radius
  let U : Real := Real.exp (Λ * T)
  let Csq := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  let Cη := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  Csq * a ^ 2 * U ^ 2 +
    Cη * (2 * (d - 1) * a ^ 2 * U ^ 2 +
      a * U * Real.sqrt ((d - 1) * Λ) + a ^ 2 * U ^ 2)

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The fixed ball cutoff error budget is nonnegative in positive dimension. -/
theorem cutoffError_nonneg
    [NeZero (Module.finrank Real E)]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (T : Real) :
    0 ≤ shiCutoffError (I := I) B T := by
  let d : Real := Module.finrank Real E
  let Λ : Real := d ^ 2 / B.radius ^ 2
  let a : Real := 4 / B.radius
  let U : Real := Real.exp (Λ * T)
  let Csq := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  let Cη := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  have hdNat : 0 < Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hd : (1 : Real) ≤ d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hc : 0 ≤ d - 1 := sub_nonneg.mpr hd
  have hΛ : 0 ≤ Λ := div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  have ha : 0 ≤ a := (div_pos (by norm_num) B.radius_pos).le
  have hU : 0 ≤ U := (Real.exp_pos _).le
  have hCsq : 0 ≤ Csq :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq).1
  have hCη : 0 ≤ Cη :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds).1
  have hfirst : 0 ≤ Csq * a ^ 2 * U ^ 2 :=
    mul_nonneg (mul_nonneg hCsq (sq_nonneg a)) (sq_nonneg U)
  have hinside :
      0 ≤ 2 * (d - 1) * a ^ 2 * U ^ 2 +
        a * U * Real.sqrt ((d - 1) * Λ) + a ^ 2 * U ^ 2 := by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg a))
          (sq_nonneg U))
        (mul_nonneg (mul_nonneg ha hU) (Real.sqrt_nonneg _)))
      (mul_nonneg (sq_nonneg a) (sq_nonneg U))
  simpa only [shiCutoffError, d, Λ, a, U, Csq, Cη] using
    add_nonneg hfirst (mul_nonneg hCη hinside)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem edistOf_finite
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (O x : M) :
    riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal) := by
  letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  unfold riemannianEDistOf
  exact riemannianEDist_ne_top (I := I) O x

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- Positivity of the fixed radial cutoff forces the intrinsic distance into
the exact inner half-radius. -/
theorem shiCutoff_dist_lt
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) {s : Real} (hs : 0 ≤ s) {y : M}
    (hy : 0 < shiBallCutoff (I := I) B s y) :
    riemannianEDistOf (I := I) (S.base.metric s) B.center y <
      ENNReal.ofReal (B.radius / 2) := by
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let A : Real := 4 * Real.exp (Lambda * s) / B.radius
  let e : ENNReal :=
    riemannianEDistOf (I := I) (S.base.metric s) B.center y
  have hLambda : 0 ≤ Lambda := by
    exact div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  have hexp : 1 ≤ Real.exp (Lambda * s) := by
    rw [show (1 : Real) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (mul_nonneg hLambda hs)
  have hA : 0 < A := by
    exact div_pos (mul_pos (by norm_num) (Real.exp_pos _)) B.radius_pos
  have hzlt : ENNReal.ofReal A * e < (2 : ENNReal) := by
    by_contra hz
    have hzero : shiBallCutoff (I := I) B s y = 0 := by
      apply DifferentialGeometry.Analysis.CutoffProfile.evalue_zero_of_ge
      simpa only [shiBallCutoff, d, Lambda, A, e] using le_of_not_gt hz
    linarith
  have hefin : e ≠ (⊤ : ENNReal) := by
    intro he
    have hA0 : ENNReal.ofReal A ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hA
    rw [he, ENNReal.mul_top hA0] at hzlt
    exact (not_lt_of_ge le_top) hzlt
  have hzreal : A * e.toReal < 2 := by
    have h :=
      (ENNReal.toReal_lt_toReal
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hefin)
        (by norm_num : (2 : ENNReal) ≠ ⊤)).2 hzlt
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA.le] at h
    norm_num at h ⊢
    exact h
  have hfour : 4 / B.radius ≤ A := by
    dsimp only [A]
    apply div_le_div_of_nonneg_right _ B.radius_pos.le
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : Real) ≤ 4))
  have hbase : (4 / B.radius) * e.toReal < 2 :=
    (mul_le_mul_of_nonneg_right hfour (ENNReal.toReal_nonneg)).trans_lt hzreal
  have hbase' : 4 * e.toReal / B.radius < 2 := by
    calc
      4 * e.toReal / B.radius = (4 / B.radius) * e.toReal := by ring
      _ < 2 := hbase
  have hmul : 4 * e.toReal < 2 * B.radius :=
    (div_lt_iff₀ B.radius_pos).1 hbase'
  have hehalf : e.toReal < B.radius / 2 := by
    linarith
  have helt : e < ENNReal.ofReal (B.radius / 2) := by
    apply (ENNReal.toReal_lt_toReal hefin ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal
      (div_nonneg B.radius_pos.le (by norm_num : (0 : Real) ≤ 2))]
    exact hehalf
  simpa only [e] using helt

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- At nonnegative time, positivity of the radial cutoff forces the point into
the inner half of the controlled flow metric ball. -/
theorem shiCutoff_inner
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) {s : Real} (hs : 0 ≤ s)
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric s))
    {y : M} (hy : 0 < shiBallCutoff (I := I) B s y) :
    y ∈ Metric.eball B.center (ENNReal.ofReal (B.radius / 2)) := by
  have helt := shiCutoff_dist_lt (I := I) B hs hy
  rw [Metric.mem_eball',
    IsRiemannianManifold.out (I := I) B.center y]
  simpa only [
    riemannianEDistOf_eq_riemannianEDist
      (I := I) (S.base.metric s) hEnorm] using helt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [SigmaCompactSpace M] in
/-- At the center, the constant function one is a lower parabolic support for
the fixed ball cutoff. -/
theorem exists_cutoff_ctr
    [NeZero (Module.finrank Real E)]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) {T t : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) :
    Nonempty (ShiCutoffLowerSupportAt (I := I) (flowG (I := I) S) T
      (shiCutoffError (I := I) B T) (shiBallCutoff (I := I) B) t B.center) := by
  classical
  let d : Real := Module.finrank Real E
  let Λ : Real := d ^ 2 / B.radius ^ 2
  let A : Real → Real := fun s ↦ 4 * Real.exp (Λ * s) / B.radius
  let z : Real × M → ENNReal := fun p ↦
    ENNReal.ofReal (A p.1) *
      riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2
  let phi : Real → M → Real := fun _ _ ↦ 1
  have hregt : t ∈ D.regular := hreg ⟨htpos, ht.2⟩
  have hedist : ContinuousAt
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2)
      (t, B.center) :=
    edistContAt_ctr (I := I) S hS hregt B.center
  have hAcont : Continuous (fun p : Real × M ↦ A p.1) := by
    dsimp only [A]
    simpa only [div_eq_mul_inv] using
      ((continuous_const.mul
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst))).mul continuous_const)
  have hcoef : ContinuousAt
      (fun p : Real × M ↦ ENNReal.ofReal (A p.1)) (t, B.center) :=
    (ENNReal.continuous_ofReal.comp hAcont).continuousAt
  have hApos : 0 < A t := by
    dsimp only [A]
    exact div_pos (mul_pos (by norm_num) (Real.exp_pos _)) B.radius_pos
  have hcoef0 : ENNReal.ofReal (A t) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hApos
  have hcoefTop : ENNReal.ofReal (A t) ≠ (⊤ : ENNReal) :=
    ENNReal.ofReal_ne_top
  have hz_at : ContinuousAt z (t, B.center) := by
    dsimp only [z]
    exact ENNReal.Tendsto.mul hcoef (Or.inl hcoef0) hedist (Or.inr hcoefTop)
  have hzlt : z (t, B.center) < (1 : ENNReal) := by
    dsimp only [z]
    rw [riemannianEDistOf_self]
    simpa only [mul_zero] using (zero_lt_one : (0 : ENNReal) < 1)
  have hz_nhds :
      ∀ᶠ p in nhdsWithin (t, B.center) (spacetimeSlab (M := M) T),
        z p < (1 : ENNReal) :=
    hz_at.continuousWithinAt (Iio_mem_nhds hzlt)
  refine ⟨{
    phi := phi
    eq_at := ?_
    lower_nhds := ?_
    time_diff := ?_
    space_diff_nhds := ?_
    grad_diff := ?_
    grad_sq_le := ?_
    parabolic_le := ?_ }⟩
  · simpa only [phi] using (shiBallCutoff_ctr (I := I) B t).symm
  · filter_upwards [hz_nhds] with p hp
    constructor
    · exact zero_le_one
    · dsimp only [phi, shiBallCutoff, d, Λ, z, A]
      rw [DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le hp.le]
  · exact differentiableWithinAt_const (c := (1 : Real))
  · exact Filter.Eventually.of_forall fun _ ↦ mdifferentiableAt_const
  · simpa only [phi] using
      (gradientFun_mdiffAt
        (I := I) ((flowG (I := I) S).metric t)
        (f := fun _ : M ↦ (1 : Real)) contMDiff_const B.center)
  · have hgradzero :
        gradientFun (I := I) ((flowG (I := I) S).metric t)
            (phi t) B.center = 0 := by
      exact gradientFun_const
        (I := I) ((flowG (I := I) S).metric t) 1 B.center
    rw [hgradzero]
    dsimp only [phi]
    simpa only [map_zero, mul_one] using
      (cutoffError_nonneg (I := I) B T)
  · have hheat_one :
        heatOperatorWithDrift
            (I := I) (flowG (I := I) S) t
            (fun y ↦ (0 : TangentSpace I y))
            (phi t) B.center = 0 := by
      unfold heatOperatorWithDrift laplacianAt laplacian driftTerm gradientAt
      have hzero :
          gradientFun (I := I) ((flowG (I := I) S).metric t) (phi t) = 0 := by
        funext y
        exact gradientFun_const
          (I := I) ((flowG (I := I) S).metric t) 1 y
      rw [hzero]
      simp
    have hpar :
        parabolicOperatorWithDrift
            (I := I) (flowG (I := I) S) T
            (fun _ y ↦ (0 : TangentSpace I y))
            phi t B.center = 0 := by
      unfold parabolicOperatorWithDrift
      rw [hheat_one]
      change derivWithin (Function.const Real (1 : Real)) (Set.Icc 0 T) t - 0 = 0
      rw [derivWithin_const]
      simp only [Pi.zero_apply, sub_self]
    rw [hpar]
    exact cutoffError_nonneg (I := I) B T

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Away from the center, the controlled ball supplies the fixed radial
cutoff's scale-exact lower parabolic support. -/
theorem exists_cutoff_ne
    [NeZero (Module.finrank Real E)] [ConnectedSpace M]
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T t : Real} (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (htB : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    {x : M} (hOx : B.center ≠ x)
    (hxχ : 0 < shiBallCutoff (I := I) B t x) :
    Nonempty (ShiCutoffLowerSupportAt (I := I) (flowG (I := I) S) T
      (shiCutoffError (I := I) B T) (shiBallCutoff (I := I) B) t x) := by
  classical
  let d : Real := Module.finrank Real E
  let Λ : Real := d ^ 2 / B.radius ^ 2
  let a : Real := 4 / B.radius
  let U : Real := Real.exp (Λ * T)
  let Csq := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  let Cη := Classical.choose
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  have hΛ : 0 ≤ Λ := div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  have ha : 0 < a := div_pos (by norm_num) B.radius_pos
  have hU : 0 ≤ U := (Real.exp_pos _).le
  have heU : Real.exp (Λ * t) ≤ U := by
    dsimp only [U]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hΛ)
  have hdNat : 0 < Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hd : (1 : Real) ≤ d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hc : 0 ≤ d - 1 := sub_nonneg.mpr hd
  have hfin :
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≠
        (⊤ : ENNReal) :=
    edistOf_finite (I := I) (S.base.metric t) B.center x
  have hfin_nhds :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        riemannianEDistOf (I := I) (S.base.metric p.1) B.center p.2 ≠
          (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun p =>
      edistOf_finite (I := I) (S.base.metric p.1) B.center p.2
  have hx := shiCutoff_inner (I := I) B ht.1 hEnorm hxχ
  obtain ⟨hρ⟩ := exists_ballFlow (I := I) hS B hB hT hreg ht htpos
    htB hEnorm hOx hx
  have hr :
      (riemannianEDist I B.center x).toReal =
        (riemannianEDistOf (I := I) (S.base.metric t) B.center x).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist
      (I := I) (S.base.metric t) hEnorm]
  have hχ : shiBallCutoff (I := I) B = fun s y =>
      DifferentialGeometry.Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (a * Real.exp (Λ * s)) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center y) := by
    funext s y
    dsimp only [shiBallCutoff, a, Λ, d]
    congr 2
    ring_nf
  have hCsq : 0 ≤ Csq :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq).1
  have hsq : ∀ s : Real,
      deriv DifferentialGeometry.Analysis.CutoffProfile.value s ^ 2 ≤
        Csq * DifferentialGeometry.Analysis.CutoffProfile.value s :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq).2
  have hCη : 0 ≤ Cη :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds).1
  have hη₁ : ∀ s : Real,
      |deriv DifferentialGeometry.Analysis.CutoffProfile.value s| ≤ Cη :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds).2.1
  have hη₂ : ∀ s : Real,
      |deriv (deriv DifferentialGeometry.Analysis.CutoffProfile.value) s| ≤ Cη :=
    (Classical.choose_spec
      DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds).2.2
  simpa only [shiCutoffError, d, Λ, a, U, Csq, Cη] using
    (support_of_scaled (I := I) ha hU heU hc hr hfin hfin_nhds
      (shiBallCutoff (I := I) B) hχ hCsq hsq hCη hη₁ hη₂ hρ)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every positive point of the fixed ball cutoff admits a scale-exact lower
parabolic support. -/
theorem exists_cutoff
    [NeZero (Module.finrank Real E)] [ConnectedSpace M]
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T t : Real} (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (htB : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    {x : M} (hxχ : 0 < shiBallCutoff (I := I) B t x) :
    Nonempty (ShiCutoffLowerSupportAt (I := I) (flowG (I := I) S) T
      (shiCutoffError (I := I) B T) (shiBallCutoff (I := I) B) t x) := by
  by_cases hOx : B.center = x
  · subst x
    exact exists_cutoff_ctr (I := I) hS B hreg ht htpos
  · exact exists_cutoff_ne (I := I) hS B hB hT hreg ht htpos
      htB hEnorm hOx hxχ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The fixed radial cutoff packages the compact finite-error cutoff data on a
sufficiently short controlled slab. -/
def shiFixedCutoff
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T : Real} (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hTB : Set.Icc 0 T ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete : ∀ s ∈ Set.Icc 0 T,
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hshort : Real.exp
      (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * T) < 2) :
    ShiFixedCutoff (I := I) (flowG (I := I) S) T
      (shiCutoffError (I := I) B T) where
  chi := shiBallCutoff (I := I) B
  support := shiBallSupport (I := I) B
  err_nonneg := cutoffError_nonneg (I := I) B T
  support_compact := shiBallSupport_cpt (I := I) B
    (hcomplete 0 ⟨le_rfl, hT.le⟩)
  support_zero := by
    intro t ht x hx
    exact shiCutoff_zero (I := I) hS B hB ht.1
      (fun s hs ↦ hreg ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs ↦ hTB ⟨hs.1, hs.2.trans ht.2⟩)
      (hcomplete t ht) hx
  range := fun t _ht x ↦ shiBallCutoff_mem (I := I) B t x
  joint_cont := shiBallCutoff_cont (I := I) hS B hB hreg hTB
    hcomplete hshort
  lower_support := by
    intro t ht htpos x hx
    letI : IsManifold I 1 M := IsManifold.of_le
      (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(S.base.metric t).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun y : M ↦ TangentSpace I y) :=
      ⟨⟨(S.base.metric t).inner,
        (S.base.metric t).contMDiff.continuous,
        by intro y v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : CompleteSpace M := (hcomplete t ht).complete
    have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t) := by
      intro y w
      rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
      congr 2
    exact exists_cutoff (I := I) hS B hB hT hreg ht htpos
      (hTB ht) hEnorm hx

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
