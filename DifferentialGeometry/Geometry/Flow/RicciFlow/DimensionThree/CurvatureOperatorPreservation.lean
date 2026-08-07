import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReactionPreservation
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem metricCurvatureOperatorNonnegative_of_ricci_upper_bound
    [I.Boundaryless] [T2Space M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (hUpper : ∀ (t : ℝ) (x : M) (v : TangentSpace I x),
      S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v v) ≤
        (S.scalar t x / 2) * (S.base.metric t).inner x v v) :
    ∀ (t : ℝ) (x : M),
      DifferentialGeometry.Integral.Connection.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          DifferentialGeometry.Integral.Connection.algebraicCurvatureOperatorNonnegativeCone := by
  intro t x
  have hsymm : DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) :=
    ricciAt_symm (I := I) S t x
  have htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
          (I := I) (S.base.metric t) (-(S.ricciAt t x)) (-(S.scalar t x))
          ((DifferentialGeometry.Integral.Connection.metricAlgebraicCurvatureTensorAt
            (I := I) (M := M) (S.base.metric t) x :
              DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)) basis := by
    intro basis horth
    have htd := traceData_metricTrace (I := I) (M := M) S (t := t) (x := x) horth
    have hsc : S.scalar t x =
        DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I)
          (S.base.metric t) (S.ricciAt t x) := by
      simp
    have hrm : S.base.rm04 t x =
        DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (M := M)
          (S.base.metric t) x := by
      rfl
    rw [hrm] at htd
    simpa [hsc] using htd
  exact (DifferentialGeometry.Integral.Connection.algebraicCurvatureOperatorNonnegative_iff_ricci_upper_bound3
    (I := I) (M := M) (g := S.base.metric t) (Ric := S.ricciAt t x) (scalar := S.scalar t x)
    (A := DifferentialGeometry.Integral.Connection.metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric t) x)
    (hdim := hdim x) (hsymm := hsymm) (htrace := htrace)).mpr (fun v => hUpper t x v)

end DifferentialGeometry.PDE.RicciFlow
