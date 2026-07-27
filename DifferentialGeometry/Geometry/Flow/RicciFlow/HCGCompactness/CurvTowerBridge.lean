import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ProductMFoldNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciTowerTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical curvature-tower bridge

This file identifies the static curvature-derivative tower used by the HCG
bounded-geometry API with the intrinsic solution tower used by the
Bernstein--Shi estimates.  The only representation difference is the
definitionally different slot count `k + 4` versus `4 + k`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- The curvature step is the generic covariant-derivative step at base rank
four. -/
theorem curvStep_eq_covStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    curvCovDerivStep (I := I) g a A =
      covStep (I := I) g (a + 4) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply]
  rfl

/-- Recursive slot reindexing between the two curvature-tower arities. -/
private def curvEquiv : (m : Nat) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (curvEquiv m)

/-- The static curvature tower and the generic iterated derivative agree after
slot reindexing, in the scalar normal form needed by the norm bridge. -/
private theorem curv_apply_iterCov
    (g : SmoothRiemannianMetric I M) :
    ∀ (m : Nat) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Integral.Connection.metricRm04
              (I := I) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (curvEquiv m)
              (iterCov (I := I) g 4
                (DifferentialGeometry.Integral.Connection.metricRm04
                  (I := I) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I) g m
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I) (M := M) g m)
        _ = covStep (I := I) g (m + 4)
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvStep_eq_covStep (I := I) (M := M) g m _)
        _ = covStep (I := I) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
                (∞ : WithTop ℕ∞) (curvEquiv m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Integral.Connection.metricRm04
                    (I := I) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (frontExtendEquiv (curvEquiv m))
              (covStep (I := I) g (4 + m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Integral.Connection.metricRm04
                    (I := I) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I) g (curvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (curvEquiv (m + 1))
              ((iterCov (I := I) g 4
                (DifferentialGeometry.Integral.Connection.metricRm04
                  (I := I) (M := M) g) (m + 1)) x)) v := by
          rfl

/-- On a Ricci-flow solution, the HCG squared curvature-derivative norm is the
intrinsic squared norm controlled by the Bernstein--Shi tower. -/
theorem curvNormSq_eq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    curvDerivNormSq (I := I) (M := M) k (S.base.metric t) x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  classical
  unfold curvDerivNormSq nablaKRm04NormSqIntrinsic
  have hfiber :
      curvCovDeriv (I := I) (M := M) (S.base.metric t) k x =
        ContinuousMultilinearMap.domDomCongr (curvEquiv k)
          ((iterCov (I := I) (S.base.metric t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04
              (I := I) (M := M) (S.base.metric t)) k) x) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact curv_apply_iterCov (I := I) (M := M) (S.base.metric t) k x v
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis (I := I) (S.base.metric t) x
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' :=
      metricInverseInBasis_of_orthonormal
        (I := I) (S.base.metric t) basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  calc
    normSq0S (I := I) (S.base.metric t) x (k + 4)
        (curvCovDeriv (I := I) (M := M) (S.base.metric t) k x) =
      normSq0S (I := I) (S.base.metric t) x (k + 4)
        (ContinuousMultilinearMap.domDomCongr (curvEquiv k)
          ((iterCov (I := I) (S.base.metric t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04
              (I := I) (M := M) (S.base.metric t)) k) x)) :=
      congrArg (fun A => normSq0S (I := I) (S.base.metric t) x (k + 4) A) hfiber
    _ = normSq0S (I := I) (S.base.metric t) x (4 + k)
        ((iterCov (I := I) (S.base.metric t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04
            (I := I) (M := M) (S.base.metric t)) k) x) :=
      normSq0S_domDomCongr (I := I) (S.base.metric t) x basis hinv
        (curvEquiv k)
        ((iterCov (I := I) (S.base.metric t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04
            (I := I) (M := M) (S.base.metric t)) k) x)
    _ = normSq0S (I := I) (S.base.metric t) x (4 + k)
        (nablaKRm04Field (I := I) S t k x) := by
      exact congrArg
        (fun A => normSq0S (I := I) (S.base.metric t) x (4 + k) (A x))
        (nablaKRm_eq_iterCov (I := I) S t k).symm

end HCGCompactness
end DifferentialGeometry
