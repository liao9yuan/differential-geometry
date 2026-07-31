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

/-- **The curvature-tower packaging identity** (`∇^m Rm` in generic covariant-derivative
currency).

The squared `g`-fibre norm of the static curvature-derivative tower `curvCovDeriv g m`
equals the squared `g`-fibre norm of the *generic* iterated covariant derivative
`iterCov g 4 (metricRm04 g) m` of the lowered Riemann tensor.

This is the public face of the slot-reindexing bridge: it lets any estimate proved in the
generic `iterCov` / `covStep` / `diffStep` currency (where `metricRm04 g` is just a
`Tensor0SField` of rank `4`) be read off on the canonical static tower and conversely,
without exposing the `Fin (4 + m) ≃ Fin (m + 4)` reindexing. -/
theorem curvCovDeriv_normSq_eq
    (g : SmoothRiemannianMetric I M) (m : Nat) (x : M) :
    normSq0S (I := I) g x (m + 4) (curvCovDeriv (I := I) (M := M) g m x) =
      normSq0S (I := I) g x (4 + m)
        ((iterCov (I := I) g 4
          (DifferentialGeometry.Integral.Connection.metricRm04
            (I := I) (M := M) g) m) x) := by
  classical
  have hfiber :
      curvCovDeriv (I := I) (M := M) g m x =
        ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Integral.Connection.metricRm04
              (I := I) (M := M) g) m) x) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact curv_apply_iterCov (I := I) (M := M) g m x v
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv :
      MetricInverseInBasis_gen (I := I) g x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  rw [hfiber]
  exact normSq0S_domDomCongr (I := I) g x basis hinv (curvEquiv m)
    ((iterCov (I := I) g 4
      (DifferentialGeometry.Integral.Connection.metricRm04
        (I := I) (M := M) g) m) x)

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
  rw [curvCovDeriv_normSq_eq (I := I) (M := M) (S.base.metric t) k x]
  exact congrArg
    (fun A => normSq0S (I := I) (S.base.metric t) x (4 + k) (A x))
    (nablaKRm_eq_iterCov (I := I) S t k).symm

end HCGCompactness
end DifferentialGeometry
