import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.HamiltonH
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength

/-!
# Reduced length on minimizing L-ray prefixes

This module compares reduced lengths at two positive minimizing times on one
L-exponential ray when scalar curvature is nonnegative only on the intervening
square-root-time segment.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

/-- Along a minimizing L-ray, nonnegative scalar curvature on the intervening
square-root-time segment bounds a prefix reduced length by the endpoint
reduced length. -/
theorem lMinPrefix_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {s tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x) (hs : 0 < s) (hst : s ≤ tau)
    (hscalar : ∀ r ∈ Icc (Real.sqrt s) (Real.sqrt tau),
      0 ≤ S.scalar (T - r ^ 2) (lRegCurve S T x Z r)) :
    redLength S T x (lExp S T x Z s) s ≤
      (Real.sqrt tau / Real.sqrt s) *
        redLength S T x (lExp S T x Z tau) tau := by
  let alpha : Real → M := lRegCurve S T x Z
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have htauSqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hsqrtLe : Real.sqrt s ≤ Real.sqrt tau := Real.sqrt_le_sqrt hst
  have hminS : (Z, s) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin hs hst
  have hdomTau : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hmin).1
  rcases (mem_lExpPosDom S T x Z tau).1 hdomTau with
    ⟨_htau, _htauNonneg, hdomTau⟩
  have hint : IntervalIntegrable (lRegLag S T alpha) volume 0
      (Real.sqrt tau) := by
    simpa only [alpha] using
      lRayLag_int S hS T x Z htauSqrt hdomTau
  have hheadInt : IntervalIntegrable (lRegLag S T alpha) volume 0
      (Real.sqrt s) :=
    hint.mono_set (by
      simpa only [uIcc_of_le hsqrt.le, uIcc_of_le htauSqrt.le] using
        (show Icc (0 : Real) (Real.sqrt s) ⊆ Icc (0 : Real) (Real.sqrt tau)
          from fun r hr ↦ ⟨hr.1, hr.2.trans hsqrtLe⟩))
  have htailInt : IntervalIntegrable (lRegLag S T alpha) volume
      (Real.sqrt s) (Real.sqrt tau) :=
    hint.mono_set (by
      simpa only [uIcc_of_le hsqrtLe, uIcc_of_le htauSqrt.le] using
        (show Icc (Real.sqrt s) (Real.sqrt tau) ⊆
            Icc (0 : Real) (Real.sqrt tau)
          from fun r hr ↦ ⟨hsqrt.le.trans hr.1, hr.2⟩))
  have hlag : ∀ r ∈ Icc (Real.sqrt s) (Real.sqrt tau),
      0 ≤ lRegLag S T alpha r := by
    intro r hr
    have hspeed : 0 ≤ lRegSpeedSq S T alpha r :=
      lRegSpeedSq_nonneg S T alpha r
    have hpot : 0 ≤ S.scalar (T - r ^ 2) (alpha r) := by
      simpa only [alpha] using hscalar r hr
    dsimp only [lRegLag]
    simpa only [lRegSpeedSq] using
      add_nonneg (mul_nonneg (by norm_num) hspeed)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hpot)
  have htail : 0 ≤ lRegAction S T alpha (Real.sqrt s) (Real.sqrt tau) := by
    unfold lRegAction
    exact intervalIntegral.integral_nonneg hsqrtLe hlag
  have hact : lRegAction S T alpha 0 (Real.sqrt s) ≤
      lRegAction S T alpha 0 (Real.sqrt tau) := by
    have hadd := lRegAction_add S T alpha 0 (Real.sqrt s) (Real.sqrt tau)
      hheadInt htailInt
    linarith
  have hactS : lRegAction S T alpha 0 (Real.sqrt s) =
      lCost S T x (lExp S T x Z s) s := by
    calc
      lRegAction S T alpha 0 (Real.sqrt s) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 s := by
        simpa only [alpha, lExp, sqrtReparam] using
          (lLength_sqrt S T alpha s hs.le).symm
      _ = lCost S T x (lExp S T x Z s) s :=
        ((mem_lMinDomain S T x Z s).1 hminS).2
  have hactTau : lRegAction S T alpha 0 (Real.sqrt tau) =
      lCost S T x (lExp S T x Z tau) tau := by
    calc
      lRegAction S T alpha 0 (Real.sqrt tau) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := by
        simpa only [alpha, lExp, sqrtReparam] using
          (lLength_sqrt S T alpha tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau :=
        ((mem_lMinDomain S T x Z tau).1 hmin).2
  have hcost : lCost S T x (lExp S T x Z s) s ≤
      lCost S T x (lExp S T x Z tau) tau := by
    calc
      lCost S T x (lExp S T x Z s) s =
          lRegAction S T alpha 0 (Real.sqrt s) := hactS.symm
      _ ≤ lRegAction S T alpha 0 (Real.sqrt tau) := hact
      _ = lCost S T x (lExp S T x Z tau) tau := hactTau
  calc
    redLength S T x (lExp S T x Z s) s =
        lCost S T x (lExp S T x Z s) s / (2 * Real.sqrt s) := rfl
    _ ≤ lCost S T x (lExp S T x Z tau) tau / (2 * Real.sqrt s) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hsqrt)).2 hcost
    _ = (Real.sqrt tau / Real.sqrt s) *
        redLength S T x (lExp S T x Z tau) tau := by
      rw [← redLength_mul S T x (lExp S T x Z tau) htau]
      field_simp [hsqrt.ne']

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
