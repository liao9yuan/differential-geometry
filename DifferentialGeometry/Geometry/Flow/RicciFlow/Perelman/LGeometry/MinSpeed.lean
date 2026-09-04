import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.HamiltonH
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength

/-!
# Speed identity on minimizing L-rays

This module combines the minimizing cost realization with Hamilton's ray
energy identity to express the ordinary L-exponential speed exactly.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

/-- The ordinary L-speed on a minimizing L-ray is exactly determined by its
reduced length, scalar curvature, and Hamilton `K` quantity. -/
theorem lMinSpeed_eq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x) (htau : 0 < tau) :
    lSpeedSq S T (fun r : Real => lExp S T x Z r) tau =
      redLength S T x (lExp S T x Z tau) tau / tau -
        S.scalar (T - tau) (lExp S T x Z tau) -
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (tau * Real.sqrt tau) := by
  obtain ⟨hdom, hcost⟩ := (mem_lMinDomain S T x Z tau).1 hmin
  have hExpDom : tau ∈ lExpDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).2
  have hregDom : Real.sqrt tau ∈ lRegDomain S T x Z := hExpDom.2
  have hs : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hlen :
      lLength S T (fun r : Real => lExp S T x Z r) 0 tau =
        lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) := by
    simpa only [lExp, sqrtReparam] using
      lLength_sqrt (I := I) S T (lRegCurve S T x Z) tau htau.le
  have hact :
      lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) =
        (2 * Real.sqrt tau) * redLength S T x (lExp S T x Z tau) tau := by
    calc
      lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : Real => lExp S T x Z r) 0 tau := hlen.symm
      _ = lCost S T x (lExp S T x Z tau) tau := hcost
      _ = (2 * Real.sqrt tau) * redLength S T x (lExp S T x Z tau) tau :=
        (redLength_mul S T x (lExp S T x Z tau) htau).symm
  have hK := lK_ray_energy S hS T x Z hs hregDom
  rw [hact] at hK
  have hvel := lExp_vel_sqrt (I := I) S T x Z htau
  have hmetric :
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          ((2 * Real.sqrt tau) •
            lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
          ((2 * Real.sqrt tau) •
            lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) =
        4 * tau *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) := by
    calc
      _ = (2 * Real.sqrt tau) * (2 * Real.sqrt tau) *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) :=
        metric_smul2 (I := I) (S.base.metric (T - tau))
          (2 * Real.sqrt tau)
          (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
      _ = 4 * (Real.sqrt tau) ^ 2 *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) := by
        ring
      _ = _ := by rw [Real.sq_sqrt htau.le]
  have hlag :
      lRegLag S T (lRegCurve S T x Z) (Real.sqrt tau) =
        2 * tau *
          (S.scalar (T - tau) (lExp S T x Z tau) +
            lSpeedSq S T (fun r : Real => lExp S T x Z r) tau) := by
    simp only [lRegLag]
    rw [show lRegCurve S T x Z (Real.sqrt tau) = lExp S T x Z tau from rfl]
    rw [hvel, Real.sq_sqrt htau.le, hmetric]
    simp only [lSpeedSq]
    ring
  rw [hlag] at hK
  have hs0 : Real.sqrt tau ≠ 0 := hs.ne'
  field_simp [htau.ne', hs0]
  nlinarith [hK, Real.sq_sqrt htau.le]

end DifferentialGeometry.PDE.RicciFlow.Perelman
