import DifferentialGeometry.Geometry.Comparison.Volume.FamilySmallBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.LateVolumeLow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCBallUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmallVolume

set_option autoImplicit false

/-!
# Smooth-flow noncollapsing from reduced volume

This file combines the initial small-ball volume estimate with the uniform
late reduced-volume floor and controlled-ball reduced-volume upper bound to
prove the compact ordinary-flow no-local-collapsing endpoint.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory

universe u uE uH

section SmoothCapstone

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Every compact smooth finite-dimensional Ricci flow on a finite half-open
time interval is kappa-noncollapsed below each positive fixed scale. -/
theorem smooth_nlc
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S)
    {rho : Real} (hrho : 0 < rho) :
    NoLocalCollapsing S rho := by
  classical
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨tauE, kappaE, htauE, htauEomega, hkappaE, hearly⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.family_vol_low
      (I := I) (M := M) h0omega S.family.metric hS.smoothMetric hrho
  let a₀ : Real := tauE / 4
  let a : Real := tauE / 2
  have ha₀a : a₀ < a := by
    dsimp only [a₀, a]
    linarith
  have haomega : a < omega := by
    dsimp only [a]
    linarith
  have hregLate : Set.Ico a₀ omega ⊆
      (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
    intro q hq
    exact ⟨(div_pos htauE (by norm_num)).trans_le hq.1, hq.2⟩
  let x₀ : M := Classical.choice inferInstance
  obtain ⟨v₀, hv₀, hlate⟩ :=
    redVolume_late_low (I := I) S hS ha₀a haomega hregLate x₀
  have hv₀one : v₀ ≤ 1 := by
    have hfloor : v₀ ≤ redVolume S a x₀ (a - a₀) :=
      hlate le_rfl haomega x₀ (sub_pos.mpr ha₀a) le_rfl
    have hslab : Set.Icc (a - (a - a₀)) a ⊆
        (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
      intro q hq
      have hq' : q ∈ Set.Icc a₀ a := by
        simpa only [sub_sub_cancel] using hq
      exact hregLate ⟨hq'.1, hq'.2.trans_lt haomega⟩
    exact hfloor.trans
      (redVolume_le_one (I := I) S hS a x₀ (a - a₀)
        (sub_pos.mpr ha₀a) hslab)
  have hv₀top : v₀ ≠ (⊤ : ENNReal) := by
    exact (hv₀one.trans_lt ENNReal.one_lt_top).ne
  let eta : ENNReal := v₀ / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    exact ENNReal.half_pos hv₀.ne'
  obtain ⟨eps₀, heps₀, hball⟩ :=
    redVolume_ball_unif (E := E) (I := I) (M := M) rho hrho eta heta
  let eps : Real := min eps₀ (1 / 2)
  have heps : 0 < eps := lt_min heps₀ (by norm_num)
  have heps_le : eps ≤ eps₀ := min_le_left _ _
  have heps_half : eps ≤ (1 / 2 : Real) := min_le_right _ _
  let n : Nat := Module.finrank Real E
  let core : Real := Real.exp
    ((n : Real) ^ 2 * eps -
      ((n : Real) / 2) * Real.log eps -
      ((n : Real) / 2) * Real.log (4 * Real.pi))
  let sqrtC : Real := Real.sqrt ((4 / 3 : Real) ^ n)
  let Ceps : Real := core * sqrtC
  have hcore : 0 < core := Real.exp_pos _
  have hsqrtC : 0 < sqrtC := by
    dsimp only [sqrtC]
    exact Real.sqrt_pos.2 (pow_pos (by norm_num) _)
  have hCeps : 0 < Ceps := mul_pos hcore hsqrtC
  let delta : ENNReal := v₀ / 2
  let coeff : ENNReal := ENNReal.ofReal Ceps
  have hdelta : 0 < delta := by
    simpa only [delta] using ENNReal.half_pos hv₀.ne'
  have hdeltatop : delta ≠ (⊤ : ENNReal) := by
    exact ENNReal.div_ne_top hv₀top (by norm_num)
  have hcoeff : 0 < coeff := by
    simpa only [coeff] using ENNReal.ofReal_pos.2 hCeps
  have hcoefftop : coeff ≠ (⊤ : ENNReal) := by
    exact ENNReal.ofReal_ne_top
  let kappaL : Real := (delta / coeff).toReal
  have hkappaL : 0 < kappaL := by
    apply ENNReal.toReal_pos
    · exact (ENNReal.div_pos hdelta.ne' hcoefftop).ne'
    · exact ENNReal.div_ne_top hdeltatop hcoeff.ne'
  let kappa : Real := min kappaE kappaL
  have hkappa : 0 < kappa := lt_min hkappaE hkappaL
  refine ⟨kappa, hkappa, hrho, ?_⟩
  intro t B hBrho hB
  have hleft_mem :
      (t : Real) - B.radius ^ 2 ∈
        (RealTimeInterval.closedOpen 0 omega h0omega).carrier :=
    hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg B.radius)⟩
  have hleft_nonneg : 0 ≤ (t : Real) - B.radius ^ 2 := by
    simpa only [RealTimeInterval.closedOpen] using hleft_mem.1
  have hsq : B.radius ^ 2 ≤ (t : Real) := by
    linarith
  by_cases ht : (t : Real) ≤ a
  · have htE : (t : Real) ≤ tauE := by
      dsimp only [a] at ht
      linarith
    refine ⟨hkappa, ?_⟩
    have hvol := hearly t htE B.center B.radius_pos hBrho hsq
    have hvol' : ENNReal.ofReal kappaE *
        ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume := by
      simpa only [FlowMetricBall.volume, FlowMetricBall.set,
        FlowMetricBall.setAt, volumeMeasureOn_eq_metric,
        SolutionOn.family_metric] using hvol
    exact (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (min_le_left kappaE kappaL)) le_rfl).trans hvol'
  · have hat : a ≤ (t : Real) := le_of_not_ge ht
    have hregB : Set.Ioc ((t : Real) - B.radius ^ 2) (t : Real) ⊆
        (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
      intro q hq
      have hqCarrier := hB.1 ⟨hq.1.le, hq.2⟩
      exact ⟨hleft_nonneg.trans_lt hq.1, hqCarrier.2⟩
    let tau : Real := eps * B.radius ^ 2
    have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
    have htau_le : tau ≤ (t : Real) - a₀ := by
      have hhalf_t : eps * B.radius ^ 2 ≤ (t : Real) / 2 := by
        calc
          eps * B.radius ^ 2 ≤ (1 / 2 : Real) * B.radius ^ 2 :=
            mul_le_mul_of_nonneg_right heps_half (sq_nonneg B.radius)
          _ ≤ (t : Real) / 2 := by linarith
      dsimp only [tau]
      dsimp only [a₀, a] at hat ⊢
      linarith
    have hlower : v₀ ≤ redVolume S (t : Real) B.center tau :=
      hlate hat t.2.2 B.center htau htau_le
    let c : Real := Real.exp
      ((n : Real) ^ 2 * eps -
        ((n : Real) / 2) * Real.log tau -
        ((n : Real) / 2) * Real.log (4 * Real.pi))
    have hupper : redVolume S (t : Real) B.center tau ≤
        ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) + eta := by
      simpa only [tau, c, n, sqrtC] using
        hball hS B hBrho hB hregB eps heps heps_le
    have hhalf : delta ≤
        ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) := by
      have hsub : v₀ - eta ≤
          ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume) := by
        apply (tsub_le_iff_right).2
        simpa only [add_comm] using hlower.trans hupper
      rw [show eta = v₀ / 2 by rfl, ENNReal.sub_half hv₀top] at hsub
      simpa only [delta] using hsub
    have hlogtau : Real.log tau =
        Real.log eps + 2 * Real.log B.radius := by
      dsimp only [tau]
      rw [Real.log_mul heps.ne' (sq_pos_of_pos B.radius_pos).ne']
      rw [Real.log_pow]
      norm_num
    have hcscale : c * B.radius ^ n = core := by
      have hexpPow : Real.exp ((n : Real) * Real.log B.radius) =
          B.radius ^ n := by
        rw [Real.exp_nat_mul, Real.exp_log B.radius_pos]
      dsimp only [c, core]
      rw [hlogtau]
      rw [show
        (n : Real) ^ 2 * eps -
            (n : Real) / 2 * (Real.log eps + 2 * Real.log B.radius) -
              (n : Real) / 2 * Real.log (4 * Real.pi) =
          ((n : Real) ^ 2 * eps -
              (n : Real) / 2 * Real.log eps -
                (n : Real) / 2 * Real.log (4 * Real.pi)) -
            (n : Real) * Real.log B.radius by ring]
      rw [Real.exp_sub, hexpPow]
      field_simp [ne_of_gt (pow_pos B.radius_pos n)]
    have hscaled : delta * ENNReal.ofReal B.radius ^ n ≤
        coeff * B.volume := by
      have hc : 0 < c := Real.exp_pos _
      calc
        delta * ENNReal.ofReal B.radius ^ n ≤
            (ENNReal.ofReal c * (ENNReal.ofReal sqrtC * B.volume)) *
              ENNReal.ofReal B.radius ^ n :=
          by
            exact mul_le_mul_left hhalf (ENNReal.ofReal B.radius ^ n)
        _ = (ENNReal.ofReal c * ENNReal.ofReal sqrtC *
              ENNReal.ofReal B.radius ^ n) * B.volume := by
          ac_rfl
        _ = ENNReal.ofReal
              ((c * sqrtC) * B.radius ^ n) * B.volume := by
          congr 1
          rw [← ENNReal.ofReal_pow B.radius_pos.le,
            ← ENNReal.ofReal_mul hc.le,
            ← ENNReal.ofReal_mul (mul_nonneg hc.le hsqrtC.le)]
        _ = coeff * B.volume := by
          congr 1
          rw [show (c * sqrtC) * B.radius ^ n = Ceps by
            dsimp only [Ceps]
            rw [show (c * sqrtC) * B.radius ^ n =
              (c * B.radius ^ n) * sqrtC by ring, hcscale]]
    have hratio : (delta / coeff) * ENNReal.ofReal B.radius ^ n ≤
        B.volume := by
      have hdiv :
          (delta * ENNReal.ofReal B.radius ^ n) / coeff ≤ B.volume :=
        (ENNReal.div_le_iff hcoeff.ne' hcoefftop).2 (by
          simpa only [mul_comm] using hscaled)
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    refine ⟨hkappa, ?_⟩
    have hkappaLvol : ENNReal.ofReal kappaL *
        ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume := by
      have hratioTop : delta / coeff ≠ (⊤ : ENNReal) :=
        ENNReal.div_ne_top hdeltatop hcoeff.ne'
      have hkappaLEq : ENNReal.ofReal kappaL = delta / coeff := by
        dsimp only [kappaL]
        exact ENNReal.ofReal_toReal hratioTop
      rw [hkappaLEq]
      simpa only [n] using hratio
    exact (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (min_le_right kappaE kappaL)) le_rfl).trans
        hkappaLvol

end SmoothCapstone

end DifferentialGeometry.PDE.RicciFlow.Perelman
