import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ProductMFoldNorm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The metric covariant-derivative arity bridge (`metricCovDerivNorm ↔ iterCov`)

`metricCovDeriv h gRef N` (= `covDerivOfField gRef (metricTensorField h) N`, arity
`N + 2`, the `metricCovDerivStep` recursion) and `iterCov gRef 2 A0 N` (arity
`2 + N`, the `covStep` recursion) are the same iterated `gRef`-Levi-Civita
derivative written with the rank in opposite order.  This file bridges them:

* **`covDerivOfField_eq_iterCov`** — the field-level identity
  `covDerivOfField gRef A0 N = (iterCov gRef 2 A0 N) · acEquiv N`, by induction
  (the same shift pattern as `iterCov_shift`: `covStep_domDomCongr` pushes the
  rank cast through each step, and `metricCovDerivStep = covStep` at the right
  arity).
* **`metricCovDerivNorm_eq_iterCov`** — the norm bridge
  `metricCovDerivNorm N h gRef x = √normSq0S gRef x (2 + N) (iterCov gRef 2 (metricTensorField h) N x)`
  at a `gRef`-orthonormal basis, via `normSq0S_domDomCongr`.

This connects the `iterCov`-form output of `RicBoundAssembly.aN_intrinsic_point`
to the `metricCovDerivNorm` form required by the `ric_bound` endpoint. -/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The recursive arity-cast equiv `Fin (2 + m) ≃ Fin (m + 2)` threading the
`covDerivOfField` (`m + 2`) / `iterCov gRef 2` (`2 + m`) rank mismatch:
`refl` at `m = 0`, `frontExtendEquiv` of the previous at `m + 1` (matching
`covStep`'s new leading slot). -/
def acEquiv : (m : ℕ) → Fin (2 + m) ≃ Fin (m + 2)
  | 0 => Equiv.refl _
  | (m + 1) => Tensor0SBundle.frontExtendEquiv (acEquiv m)

/-- The metric covariant-derivative step is the `covStep` at the matching arity
(both are `totalNabla0SFun (a + 2)` of the `gRef` Levi-Civita connection). -/
theorem metricCovDerivStep_eq_covStep (gRef : SmoothRiemannianMetric I M) (a : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a A = covStep (I := I) gRef (a + 2) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, covStep_apply]

/-- **The field-level arity bridge.**  `∇_gRef^m A0` in the `covDerivOfField`
(`m + 2`) indexing equals the `iterCov gRef 2` (`2 + m`) tower reindexed by
`acEquiv m`. -/
theorem covDerivOfField_eq_iterCov (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) (m : ℕ) :
    covDerivOfField (I := I) gRef A0 m =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (acEquiv m)
        (iterCov (I := I) gRef 2 A0 m) := by
  induction m with
  | zero =>
      simp only [acEquiv]
      rfl
  | succ m ih =>
      rw [covDerivOfField_succ, ih, metricCovDerivStep_eq_covStep, covStep_domDomCongr,
        ← iterCov_succ]
      rfl

/-- **The norm bridge.**  At a `gRef`-orthonormal basis, the textbook
`metricCovDerivNorm N h gRef x` equals the `iterCov`-tower norm
`√normSq0S gRef x (2 + N) (∇_gRef^N (metricTensorField h))`.  The rank cast is
absorbed by `normSq0S_domDomCongr`. -/
theorem metricCovDerivNorm_eq_iterCov {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) (N : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    metricCovDerivNorm (I := I) N h gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x)) := by
  unfold metricCovDerivNorm
  rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov]
  show Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
      (ContinuousMultilinearMap.domDomCongr (acEquiv N)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x))) =
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x))
  rw [normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv N)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x)]

end HCGCompactness
end DifferentialGeometry
