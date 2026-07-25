import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.KoszulDifference
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- Smoothness of `∇₂g₁ = totalNabla0SFun 2 (LC g₂) (metricTensorField g₁)` as a `(0,3)`-field, so it
can be bundled via `totalNabla0S` and differentiated a second time.  From `totalNabla0S_reg` and the
local smoothness of the `g₂`-Levi-Civita connection. -/
theorem metricField_totalReg
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.TotalNabla0SRegular (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
      (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁) :=
  Tensor0SBundle.totalNabla0S_reg (I := I) 2 (LeviCivita (I := I) g₂)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g₂)
    (Tensor0SBundle.metricTensorField (I := I) g₁)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **One combo term of the differentiated Koszul RHS.**  The directional derivative along `W` of a
`∇₂g₁` combo term (direction `V 0`, slots `V 1, V 2`) equals the second covariant derivative `∇₂²g₁`
(`nabla0SFun 3 (LC g₂) W (∇₂g₁-field)`) plus the Leibniz slot corrections, by
`nabla0SFun_eval_smooth_slots` on the bundled `∇₂g₁` field, bridged to the first-order combo term via
`totalNabla0SFun_apply_section`.  This is the RHS engine step of the B2 P2.a differentiated identity; the
three combo terms of `connDiff_koszul_nabla` are its instances at `V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`. -/
theorem nablaMetric_combo_extDeriv
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (V 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
          (fun q : Fin 2 => V q.succ p)) x (W x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
          (fun a : Fin 3 => V a x) +
        ∑ a : Fin 3,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
            (Function.update (fun b : Fin 3 => V b x) a
              (((LeviCivita (I := I) g₂) (fun p : M => V a p) x) (W x))) := by
  classical
  set α := Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
    (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
    (metricField_totalReg (I := I) g₁ g₂) with hαdef
  have hbridge : (fun p : M => α p (fun a : Fin 3 => V a p)) =
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (LeviCivita (I := I) g₂) (V 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
        (fun q : Fin 2 => V q.succ p)) := by
    funext p
    rw [hαdef, Tensor0SBundle.totalNabla0S_apply,
      show (fun a : Fin 3 => V a p) =
          Fin.cons ((V 0) p) (fun q : Fin 2 => (V q.succ) p) from
        (Fin.cons_self_tail (fun a : Fin 3 => V a p)).symm,
      Tensor0SBundle.totalNabla0SFun_apply_section]
  rw [Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (LeviCivita (I := I) g₂) W V α x, hbridge]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **The LHS metric-compatibility Leibniz** for the differentiated Koszul identity.  The directional
derivative along `W` of the `g₁`-contraction `p ↦ g₁(a p, b p)` (slots `a = V 0`, `b = V 1`) equals the
first covariant derivative `(∇₂g₁)(a,b)` (`nabla0SFun 2 (LC g₂) W (metricTensorField g₁)`) plus the two
`g₁(∇₂_W ·, ·)` Leibniz corrections.  Direct application of `nabla0SFun_eval_smooth_slots` to
`metricTensorField g₁`; this expands the LHS of `connDiff_koszul_nabla` under differentiation. -/
theorem metric_leibniz_extDeriv
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => Tensor0SBundle.metricTensorField (I := I) g₁ p
          (fun c : Fin 2 => V c p)) x (W x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun c : Fin 2 => V c x) +
        ∑ c : Fin 2,
          Tensor0SBundle.metricTensorField (I := I) g₁ x
            (Function.update (fun d : Fin 2 => V d x) c
              (((LeviCivita (I := I) g₂) (fun p : M => V c p) x) (W x))) := by
  rw [Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (LeviCivita (I := I) g₂) W V (Tensor0SBundle.metricTensorField (I := I) g₁) x]
  abel

end Connection
end Integral
end DifferentialGeometry

end
