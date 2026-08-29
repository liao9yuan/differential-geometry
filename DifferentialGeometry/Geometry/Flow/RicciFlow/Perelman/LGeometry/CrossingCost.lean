import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Metric.CurveEnergy

set_option autoImplicit false

/-!
# Crossing cost for Perelman L-length

This file gives the fixed-manifold crossing estimate: a scalar-curvature
barrier and a lower comparison with a fixed metric force positive L-cost for
every curve with prescribed reference-metric length.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [T2Space M] [SigmaCompactSpace M] in
/-- A scalar barrier and reference-metric coercivity bound the L-length below
by the cost of crossing a prescribed amount of reference arc length. -/
theorem lLength_cross
    (S : SolutionOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn
      (I := I) (M := M) D S.family.metric)
    (hRcont : ContinuousOn (fun q : Real × M ↦ S.scalar q.1 q.2)
      (D.carrier ×ˢ (univ : Set M)))
    (T : Real) (gamma : Real → M)
    (gRef : SmoothRiemannianMetric I M)
    (a b c Q d : Real)
    (hab : a ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hQ : 0 ≤ Q)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hback : MapsTo (fun tau : Real ↦ T - tau) (uIcc a b) D.carrier)
    (hscalar : ∀ tau ∈ Icc a b,
      Q ≤ S.scalar (T - tau) (gamma tau))
    (hmetric : ∀ tau ∈ Icc a b,
      c * gRef.inner (gamma tau)
          (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau) ≤
        lSpeedSq S T gamma tau)
    (hcross : d ≤ Variation.arcLength (I := I) gRef gamma a b) :
    2 * Real.sqrt (a * c * Q) * d ≤ lLength S T gamma a b := by
  let speedRef : Real → Real := fun tau ↦
    Real.sqrt (gRef.inner (gamma tau)
      (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau))
  let K : Real := 2 * Real.sqrt (a * c * Q)
  have hrefOn : IntegrableOn speedRef (Icc a b) := by
    simpa only [speedRef, lVelocity] using
      Geodesic.speedSqrt_integrableOn_Icc_of_C1
        (I := I) gRef hab hgamma.contMDiffOn
  have href : IntervalIntegrable speedRef volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hrefOn
  have hden : IntervalIntegrable (lDensity S T gamma) volume a b :=
    lDensity_integrable S T a b gamma hG hRcont hgamma hback
  have hK : 0 ≤ K := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmono :
      (∫ tau in a..b, K * speedRef tau) ≤ lLength S T gamma a b := by
    unfold lLength
    refine intervalIntegral.integral_mono_on hab (href.const_mul K) hden ?_
    intro tau htau
    let v := lVelocity (I := I) gamma tau
    let q := gRef.inner (gamma tau) v v
    have hq : 0 ≤ q := by
      rcases eq_or_ne v 0 with hv | hv
      · simp only [q, hv, map_zero]
        exact le_rfl
      · exact (gRef.pos (gamma tau) v hv).le
    have hbase : 0 ≤ Q + c * q :=
      add_nonneg hQ (mul_nonneg hc hq)
    have hsum :
        Q + c * q ≤
          S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau := by
      exact add_le_add (hscalar tau htau) (by
        simpa only [q, v] using hmetric tau htau)
    have htime : Real.sqrt a ≤ Real.sqrt tau :=
      Real.sqrt_le_sqrt htau.1
    have hcq : (Real.sqrt c * Real.sqrt q) ^ 2 = c * q := by
      rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hq]
    have hamgm :
        2 * Real.sqrt Q * (Real.sqrt c * Real.sqrt q) ≤ Q + c * q := by
      nlinarith [sq_nonneg (Real.sqrt Q - Real.sqrt c * Real.sqrt q),
        Real.sq_sqrt hQ, hcq]
    have hroot :
        Real.sqrt (a * c * Q) =
          Real.sqrt a * (Real.sqrt c * Real.sqrt Q) := by
      rw [show a * c * Q = a * (c * Q) by ring,
        Real.sqrt_mul ha, Real.sqrt_mul hc]
    change K * Real.sqrt q ≤
      Real.sqrt tau *
        (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)
    calc
      K * Real.sqrt q =
          Real.sqrt a *
            (2 * Real.sqrt Q * (Real.sqrt c * Real.sqrt q)) := by
        simp only [K, hroot]
        ring
      _ ≤ Real.sqrt a * (Q + c * q) :=
        mul_le_mul_of_nonneg_left hamgm (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt tau * (Q + c * q) :=
        mul_le_mul_of_nonneg_right htime hbase
      _ ≤ Real.sqrt tau *
          (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
  calc
    2 * Real.sqrt (a * c * Q) * d = K * d := by rfl
    _ ≤ K * Variation.arcLength (I := I) gRef gamma a b :=
      mul_le_mul_of_nonneg_left hcross hK
    _ = ∫ tau in a..b, K * speedRef tau := by
      simp only [Variation.arcLength, speedRef, lVelocity,
        intervalIntegral.integral_const_mul]
    _ ≤ lLength S T gamma a b := hmono

end DifferentialGeometry.PDE.RicciFlow.Perelman
