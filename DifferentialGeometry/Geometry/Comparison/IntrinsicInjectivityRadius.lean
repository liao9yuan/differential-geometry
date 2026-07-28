import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedCoordinates
import Mathlib.Data.ENNReal.Real

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intrinsic framed injectivity radius

This file defines the injectivity radius of the complete intrinsic framed
exponential.  It is separate from the legacy chart-fixed `injRadius` while the
normal-coordinate consumers migrate to intrinsic whole-ball branches.
-/

noncomputable section

open Bundle Set
open scoped Topology Manifold ContDiff ENNReal NNReal Bundle

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Radii on which the complete intrinsic framed exponential is injective. -/
def intrInjRadiusSet
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : Set ℝ≥0∞ :=
  {r | InjOn (intrinsicFramedExp (I := I) g hEnorm p)
    (Metric.eball (0 : E) r)}

/-- The injectivity radius of the complete intrinsic framed exponential. -/
def intrInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : ℝ≥0∞ :=
  sSup (intrInjRadiusSet (I := I) g hEnorm p)

/-- The intrinsic injectivity-radius set is downward closed. -/
lemma intrInj_down
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r r' : ℝ≥0∞} (h : r' ≤ r)
    (hr : r ∈ intrInjRadiusSet (I := I) g hEnorm p) :
    r' ∈ intrInjRadiusSet (I := I) g hEnorm p :=
  hr.mono (Metric.eball_subset_eball h)

/-- The zero radius belongs to the intrinsic injectivity-radius set. -/
lemma zero_mem_intrInj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    (0 : ℝ≥0∞) ∈ intrInjRadiusSet (I := I) g hEnorm p := by
  classical
  change InjOn _ (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

/-- Every admissible radius is bounded by the intrinsic injectivity radius. -/
lemma le_intrInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : ℝ≥0∞}
    (hr : r ∈ intrInjRadiusSet (I := I) g hEnorm p) :
    r ≤ intrInjRadius (I := I) g hEnorm p :=
  le_sSup hr

omit [ConnectedSpace M] in
/-- The intrinsic framed exponential is injective on every extended ball
strictly below its intrinsic injectivity radius. -/
theorem intrInjOn_eball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : ℝ≥0∞}
    (hr : r < intrInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  exact hr'_mem.mono
    (Metric.eball_subset_eball (le_of_lt hr_lt_r'))

omit [ConnectedSpace M] in
/-- Real-radius form of `intrInjOn_eball`. -/
theorem intrInjOn_ball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : Real}
    (hr : ENNReal.ofReal r < intrInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r) := by
  have h := intrInjOn_eball (I := I) g hEnorm p hr
  rwa [Metric.eball_ofReal] at h

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
