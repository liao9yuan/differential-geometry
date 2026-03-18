/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Product.Defs
/-!
# Currying of Covariant Tensors

This file defines currying and uncurrying operations for covariant tensors on smooth manifolds.

## Main Definitions

* `tensor0S_curryLeft r r' x` : CLM currying a (0,r+r')-tensor along `Fin r ⊕ Fin r'`.
* `tensor0S_uncurryLeft r r' x` : inverse of `tensor0S_curryLeft`.

## Tags

currying, covariant tensor, smooth manifold
-/

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Curry a (0,r+r')-tensor into a multilinear map from `r` tangent vectors to (0,r')-tensors,
using the decomposition `Fin (r+r') ≃ Fin r ⊕ Fin r'`. -/
noncomputable def tensor0S_curryLeft (r r' : ℕ) (x : M) :
    Tensor0SSpace (r + r') I x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace r' I x) := by
  unfold Tensor0SSpace TangentSpace
  let e1 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 :=
    ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 finSumFinEquiv.symm
  let e2 : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
             (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜) :=
    ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  exact (e1.trans e2).toContinuousLinearMap

/-- Uncurry a multilinear map from `r` tangent vectors to (0,r')-tensors back into
a (0,r+r')-tensor, the inverse of `tensor0S_curryLeft`. -/
noncomputable def tensor0S_uncurryLeft (r r' : ℕ) (x : M) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace r' I x) →L[𝕜]
    Tensor0SSpace (r + r') I x := by
  unfold Tensor0SSpace TangentSpace
  let e1 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 :=
    ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 finSumFinEquiv.symm
  let e2 : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
             (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜) :=
    ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  exact (e1.trans e2).symm.toContinuousLinearMap

end
end Tensor0SBundle
