import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SegmentValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionAttain

set_option autoImplicit false

/-!
# Same-clock segment value versus regular cost

This file compares the finite-action same-clock segment infimum with the
existing global `C1` regularized cost.  The easy inclusion of regular curves
into finite-action segments is kept separate from the reverse density problem.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [ConnectedSpace M]
variable {D : RealTimeInterval}

/-- Under a scalar lower bound and regularity on the relevant backward-time
slab, the same-clock finite-action value is no larger than the global `C1`
regularized cost. -/
theorem lSegValue_le_reg
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y ≤
      (lRegCostC1 S T a b x y : WithTop Real) := by
  let costs : Set Real := {r | ∃ alpha : Real → M,
    ContMDiff 𝓘(Real, Real) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r}
  have hne : costs.Nonempty :=
    ⟨lRegAction S T alpha0 a b, alpha0, halpha0, h0a, h0b, rfl⟩
  have habSq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha (ha.trans hab)).2 hab
  have hbdd : BddBelow costs := by
    refine ⟨-(2 * K / 3) *
      (b ^ 2 * Real.sqrt (b ^ 2) - a ^ 2 * Real.sqrt (a ^ 2)), ?_⟩
    intro r hr
    rcases hr with ⟨alpha, halpha, _hxa, _hyb, rfl⟩
    have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab alpha
      halpha.contMDiffOn hreg
    have hseg := lSegCurve_sqrt (I := I) S T Set.univ a b ha hab alpha
      halpha hLag (by simp)
    have hlow := lLength_lower S T (a ^ 2) (b ^ 2) K
      (sq_nonneg a) habSq (sqrtReparam alpha)
      (fun tau htau ↦ hR tau htau (sqrtReparam alpha tau)) hseg.2.2.1
    rw [lLength_sqrt_Icc (I := I) S T alpha a b ha hab] at hlow
    exact hlow
  change lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y ≤
    ((sInf costs : Real) : WithTop Real)
  rw [WithTop.coe_sInf' hne hbdd]
  apply le_csInf (hne.image fun r : Real ↦ (r : WithTop Real))
  intro q hq
  rcases hq with ⟨r, hr, rfl⟩
  rcases hr with ⟨alpha, halpha, hxa, hyb, rfl⟩
  have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hreg
  exact lSegValue_le_c1 (I := I) S T K Set.univ a b ha hab hR x y
    alpha halpha hLag (by simp) hxa hyb

end DifferentialGeometry.PDE.RicciFlow.Perelman
