import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

/-!
# Perelman L-length on a fixed Ricci-flow manifold

This file defines the velocity, squared speed, density, and interval
`L`-length of a raw curve parameterized by backward time.  The metric and
scalar curvature are evaluated at forward time `T - tau`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

/-- Velocity of a raw manifold curve with respect to backward time. -/
noncomputable def lVelocity (gamma : Real -> M) (tau : Real) :
    TangentSpace I (gamma tau) :=
  (mfderiv 𝓘(Real, Real) I gamma tau :
    Real →L[Real] TangentSpace I (gamma tau)) (1 : Real)

/-- Squared speed of a backward-time curve in the metric at forward time `T - tau`. -/
noncomputable def lSpeedSq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) : Real :=
  (S.base.metric (T - tau)).inner (gamma tau)
    (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau)

/-- Squared L-speed is nonnegative at every backward time. -/
theorem lSpeedSq_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) :
    0 <= lSpeedSq S T gamma tau := by
  unfold lSpeedSq
  by_cases hv : lVelocity (I := I) gamma tau = 0
  · simp [hv]
  · exact ((S.base.metric (T - tau)).pos (gamma tau)
      (lVelocity (I := I) gamma tau) hv).le

variable [FiniteDimensional Real E]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

/-- Perelman L-density of a backward-time curve. -/
noncomputable def lDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau : Real) : Real :=
  Real.sqrt tau * (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)

/-- Perelman L-length of a backward-time curve on an oriented real interval. -/
noncomputable def lLength
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a b : Real) : Real :=
  ∫ tau in a..b, lDensity S T gamma tau

omit [T2Space M] [SigmaCompactSpace M] in
/-- L-length over a zero interval vanishes. -/
@[simp] theorem lLength_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a : Real) :
    lLength S T gamma a a = 0 := by
  simp [lLength]

omit [T2Space M] [SigmaCompactSpace M] in
/-- L-length is additive across adjacent intervals when the density is
integrable on both pieces. -/
theorem lLength_add_adj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (a b c : Real)
    (hab : IntervalIntegrable (lDensity S T gamma) volume a b)
    (hbc : IntervalIntegrable (lDensity S T gamma) volume b c) :
    lLength S T gamma a b + lLength S T gamma b c =
      lLength S T gamma a c := by
  simpa [lLength] using intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [T2Space M] [SigmaCompactSpace M] in
/-- Germ-equivalent curves have the same L-density at the base time. -/
theorem lDensity_congr
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    {gamma delta : Real -> M} (h : gamma =ᶠ[nhds tau] delta) :
    lDensity S T gamma tau = lDensity S T delta tau := by
  have hval : gamma tau = delta tau := h.self_of_nhds
  have hder := Filter.EventuallyEq.mfderiv_eq
    (I := 𝓘(Real, Real)) (I' := I) h
  simp only [lDensity, lSpeedSq, lVelocity]
  rw [hval, hder]

omit [T2Space M] [SigmaCompactSpace M] in
/-- L-length is unchanged when the curves have the same germ at every point
of the integration interval. -/
theorem lLength_congr
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    {gamma delta : Real -> M}
    (h : ∀ tau ∈ uIcc a b, gamma =ᶠ[nhds tau] delta) :
    lLength S T gamma a b = lLength S T delta a b := by
  unfold lLength
  apply intervalIntegral.integral_congr
  intro tau htau
  exact lDensity_congr S T tau (h tau htau)

omit [T2Space M] [SigmaCompactSpace M] in
/-- L-length of two pasted curve pieces is the sum of their L-lengths. -/
theorem lLength_join
    (S : SolutionOn (I := I) (M := M) D) (T a c b : Real)
    (gamma0 gamma1 : Real -> M) (hac : a ≤ c) (hcb : c ≤ b)
    (h0 : IntervalIntegrable (lDensity S T gamma0) volume a c)
    (h1 : IntervalIntegrable (lDensity S T gamma1) volume c b) :
    lLength S T (Set.piecewise (Set.Iic c) gamma0 gamma1) a b =
      lLength S T gamma0 a c + lLength S T gamma1 c b := by
  classical
  let gamma : Real -> M := Set.piecewise (Set.Iic c) gamma0 gamma1
  have hleft_ae :
      lDensity S T gamma0 =ᵐ[volume.restrict (Set.uIoc a c)]
        lDensity S T gamma := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
        MeasureTheory.Measure.ae_ne (volume.restrict (Set.uIoc a c)) c]
        with s hs hsc
    have hs' : s ∈ Set.Ioc a c := by
      simpa only [Set.uIoc_of_le hac] using hs
    have hlt : s < c := lt_of_le_of_ne hs'.2 hsc
    apply lDensity_congr S T s
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact ((Set.Iic c).piecewise_eq_of_mem gamma0 gamma1
      (Set.mem_Iic.mpr hr.le)).symm
  have hright_ae :
      lDensity S T gamma1 =ᵐ[volume.restrict (Set.uIoc c b)]
        lDensity S T gamma := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with s hs
    have hs' : s ∈ Set.Ioc c b := by
      simpa only [Set.uIoc_of_le hcb] using hs
    apply lDensity_congr S T s
    filter_upwards [Ioi_mem_nhds hs'.1] with r hr
    exact ((Set.Iic c).piecewise_eq_of_notMem gamma0 gamma1
      (by simpa only [Set.mem_Iic] using not_le_of_gt hr)).symm
  have hleft : IntervalIntegrable (lDensity S T gamma) volume a c :=
    h0.congr_ae hleft_ae
  have hright : IntervalIntegrable (lDensity S T gamma) volume c b :=
    h1.congr_ae hright_ae
  have hleft_eq : lLength S T gamma a c = lLength S T gamma0 a c := by
    unfold lLength
    exact intervalIntegral.integral_congr_ae_restrict hleft_ae.symm
  have hright_eq : lLength S T gamma c b = lLength S T gamma1 c b := by
    unfold lLength
    exact intervalIntegral.integral_congr_ae_restrict hright_ae.symm
  change lLength S T gamma a b =
    lLength S T gamma0 a c + lLength S T gamma1 c b
  calc
    lLength S T gamma a b =
        lLength S T gamma a c + lLength S T gamma c b :=
      (lLength_add_adj S T gamma a c b hleft hright).symm
    _ = lLength S T gamma0 a c + lLength S T gamma1 c b := by
      rw [hleft_eq, hright_eq]

omit [T2Space M] [SigmaCompactSpace M] in
/-- Squared speed is continuous on a backward-time interval whose corresponding
forward times remain in the metric-family carrier. -/
theorem lSpeedSq_contOn
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    ContinuousOn (lSpeedSq S T gamma) (uIcc a b) := by
  rw [continuousOn_iff_continuous_restrict]
  let P := {tau : Real // tau ∈ uIcc a b}
  let timeLift : P -> {t : Real // t ∈ D.carrier} :=
    fun tau => ⟨T - tau.1, hback tau.2⟩
  let velLift : P -> TangentBundle I M :=
    fun tau => tangentMap 𝓘(Real, Real) I gamma
      (⟨tau.1, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)
  let input : P -> {t : Real // t ∈ D.carrier} × TangentBundle I M :=
    fun tau => (timeLift tau, velLift tau)
  have htime : Continuous timeLift := by
    exact ((continuous_const.sub continuous_subtype_val).subtype_mk _)
  have hvel : Continuous velLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) hgamma).comp
        continuous_subtype_val
  have hinput : Continuous input := htime.prodMk hvel
  have hquad :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hG (K := D.carrier) (fun _ ht => ht)
  have hcomp := hquad.comp hinput
  simpa [P, input, timeLift, velLift, DifferentialGeometry.metricTimeBundleQuad,
    lSpeedSq, lVelocity, tangentMap] using hcomp

omit [T2Space M] [SigmaCompactSpace M] in
/-- The L-density is continuous when the moving metric and scalar curvature
are continuous along the corresponding solution times. -/
theorem lDensity_contOn
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
      (D.carrier ×ˢ (univ : Set M)))
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    ContinuousOn (lDensity S T gamma) (uIcc a b) := by
  have hpair : ContinuousOn (fun tau : Real => (T - tau, gamma tau)) (uIcc a b) :=
    ((continuous_const.sub continuous_id).prodMk hgamma.continuous).continuousOn
  have hmaps : MapsTo (fun tau : Real => (T - tau, gamma tau)) (uIcc a b)
      (D.carrier ×ˢ (univ : Set M)) := by
    intro tau htau
    exact ⟨hback htau, mem_univ _⟩
  have hscalar : ContinuousOn (fun tau : Real => S.scalar (T - tau) (gamma tau))
      (uIcc a b) := by
    simpa [Function.comp_def] using hR.comp hpair hmaps
  have hspeed := lSpeedSq_contOn S T a b gamma hG hgamma hback
  simpa only [lDensity] using
    Real.continuous_sqrt.continuousOn.mul (hscalar.add hspeed)

omit [T2Space M] [SigmaCompactSpace M] in
/-- The L-density is interval-integrable under the same moving-metric and
scalar-continuity hypotheses. -/
theorem lDensity_integrable
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (gamma : Real -> M)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hR : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
      (D.carrier ×ˢ (univ : Set M)))
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real => T - tau) (uIcc a b) D.carrier) :
    IntervalIntegrable (lDensity S T gamma) volume a b :=
  (lDensity_contOn S T a b gamma hG hR hgamma hback).intervalIntegrable

end DifferentialGeometry.PDE.RicciFlow.Perelman
