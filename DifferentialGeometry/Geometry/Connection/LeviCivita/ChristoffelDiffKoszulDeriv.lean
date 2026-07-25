import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.KoszulDifference
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

/-!
# Toward the differentiated Christoffel-difference Koszul identity (B2 P2.a)

This leaf builds the covariant derivative of the Christoffel-difference Koszul identity, the crux of the
UNGATED order-1 connection-difference-derivative norm bound (mission B2; see
`HCGCompactness/UNIF_ITEM6_RECON.md` §4b for the full route).

The target identity (differentiating `connDiff_koszul` covariantly along `W` under `∇₂ = LeviCivita g₂`):
```
2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y), Z),
```
with `A = connDiff g₁ g₂ = difference (LC g₁) (LC g₂)`.  The differentiation base is the Tensor-layer
`koszul_difference` (`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean`) in the
`nabla0SFun (metricTensorField g₁)` currency, whose derivative is differentiable via
`nabla0SFun_eval_smooth_slots`.

**Landed so far:** the a=0 differentiation base `connDiff_koszul_nabla` — `koszul_difference` specialised
to the Levi-Civita pair `(LC g₁, LC g₂)`, in the `nabla0SFun` currency that the covariant differentiation
consumes.  The full differentiated identity is the multi-brick continuation (recon §4b, 6-step plan).
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **The Christoffel-difference Koszul identity in `nabla0SFun` currency** (the a=0 differentiation
base).  Specialisation of the Tensor-layer `koszul_difference` to the Levi-Civita pair `(LC g₁, LC g₂)`:
pairing the connection difference `A = difference (LC g₁) (LC g₂)` against `g₁` equals the symmetric
Koszul combination of the `∇₂`-covariant derivative of `g₁`, expressed as
`nabla0SFun 2 (LC g₂) · (metricTensorField g₁)` (= `∇₂g₁`).

This is `connDiff_koszul` in the currency whose covariant derivative is Tensor-layer differentiable
(`nabla0SFun_eval_smooth_slots`); the differentiated identity (B2 P2.a) is obtained by applying that
engine to the right-hand side and metric-compatibility to the left. -/
theorem connDiff_koszul_nabla
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M} :
    g₁.inner x
        ((CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
          (Y x) (X x)) (Z x) =
      (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) X (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) +
        (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) Y (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then X x else Z x) -
        (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) Z (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then X x else Y x) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  have hmc : IsMetricCompatible_gen (I := I) (LeviCivita (I := I) g₁) g₁ := by
    simpa [LeviCivita] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g₁
  have htf : IsTorsionFreeAt (I := I) (LeviCivita (I := I) g₁) x :=
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g₁) x
  have htf' : IsTorsionFreeAt (I := I) (LeviCivita (I := I) g₂) x :=
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g₂) x
  exact Tensor0SBundle.koszul_difference (I := I)
    (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) g₁ hmc htf htf' X Y Z

end Connection
end Integral
end DifferentialGeometry

end
