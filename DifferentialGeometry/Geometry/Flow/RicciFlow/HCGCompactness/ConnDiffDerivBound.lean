import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound

/-!
# Order-1 connection-difference-derivative: the ungated fibre→vector reduction (B2 P1)

The B2 mission target is the UNGATED general-`Λ` pointwise bound on the output vector of
`covDerivConnDiff g₂ g₁ X Y Z x` (`= (∇₂_X A)(Y, Z)` for `A = connDiff g₁ g₂`), the shared wall of the
T-B `mixedComm_norm_le`/`hA1` and 2a-tel composition-(b) consumers.  See
`HCGCompactness/UNIF_ITEM6_RECON.md` for the full route.

This file lands the reference session's **P1** brick: the ungated half of the δ<1-gated
`exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope` (`Curvature/CovDerivConnDiffQuadraticBound.lean`).
It reduces the output-vector `g₂`-norm to the **fibre** norm of the bundled order-1 covariant derivative
`covGrad g₂ 1 2 (connDiffSection g₁ g₂)`:
```
√(g₂(covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x, ·))
    ≤ ‖(covGrad g₂ 1 2 (connDiffSection g₁ g₂)).toSection x‖ · √(g₂ v v)·√(g₂ w w)·√(g₂ u u).
```
There is **no `δ < 1` gate**: the reduction uses only the flat/eval bridge
`connDiffSection_covGrad_eq_covDerivConnDiff` and the fibre Cauchy–Schwarz
`abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt` (both public).  The δ<1 gate in the parent theorem is
consumed exclusively by the fibre bound `‖covGrad connDiffSection‖ ≤ CA` (P2), which is the single
remaining B2 frontier (the a=1 analogue of `lcDiff_norm_le`).

NOTE (home debt): this brick is pure fibre-currency Curvature-layer content and canonically belongs
next to `abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt` in
`Geometry/Curvature/CovDerivConnDiffFibreExtraction.lean`; it is placed in this HCG leaf only because the
leaf is the ratified B2 home and its editable set.  Promote upstream once B2 assembles.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The flat/eval bridge specialised to the connection-difference section: the model-basis evaluation of
`covGrad g₂ 1 2 (connDiffSection g₁ g₂)` on the `g₂`-flat of `A = covDerivConnDiff g₂ g₁ …` reads off the
squared `g₂`-length of `A`.  Public re-derivation of the parent file's `private`
`covGrad_connDiffSection_flat_eval_eq_inner`, built from the PUBLIC
`connDiffSection_covGrad_eq_covDerivConnDiff`. -/
private theorem covGrad_connDiffSection_flat_eval_eq_inner
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₂ 1 2 (connDiffSection (I := I) g₁ g₂)).toSection x)
          (g0FlatCLM (I := I) g₂ x
            (covDerivConnDiff (I := I) g₂ g₁
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₂.inner x
        (covDerivConnDiff (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnDiff (I := I) g₂ g₁ Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₂ x A)
  have hbridge := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g₁ g₂ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₂ x A) (fun _ : Fin 1 => A) = g₂.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₂ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₂ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₂ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **B2 P1 — the ungated fibre→vector reduction.**

The output-vector `g₂`-length of `covDerivConnDiff g₂ g₁ (ext v)(ext w)(ext u) x` is bounded by the
`g₂`-fibre norm of the bundled order-1 covariant derivative `covGrad g₂ 1 2 (connDiffSection g₁ g₂)` at
`x`, times the three vector `g₂`-lengths.  No `δ < 1` / metric-perturbation gate: this is the
Cauchy–Schwarz half of `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`, valid at general `Λ`.

Compose with any bound `‖(covGrad g₂ 1 2 (connDiffSection g₁ g₂)).toSection x‖ ≤ CA(Λ, Λ', Λ'')` (the
B2 P2 frontier, the a=1 analogue of `lcDiff_norm_le`) to obtain the full B2 output-vector bound
`≤ CA · √(g₂ v v)·√(g₂ w w)·√(g₂ u u)` that both consumers (`mixedComm_norm_le`/`hA1`, 2a-tel (b))
require. -/
theorem covDerivConnDiff_fibreNorm_le
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₂ 1 3
    Real.sqrt (g₂.inner x
        (covDerivConnDiff (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)) ≤
      ‖((covGrad (I := I) (M := M) g₂ 1 2 (connDiffSection (I := I) g₁ g₂)).toSection x :
          Tensor0SBundle.TensorRSSpace 1 3 I x)‖ *
        Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
          Real.sqrt (g₂.inner x u u) := by
  classical
  letI instW : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 1 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₂ 1 3
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₂ 1 2 (connDiffSection (I := I) g₁ g₂)).toSection x with hW_def
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₂.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₂ x A
  set NA : ℝ := Real.sqrt (g₂.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connDiffSection_flat_eval_eq_inner (I := I) (M := M) g₂ g₁ x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor13_flat_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₂ x W A v u w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₂.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  have hvv_nn : 0 ≤ g₂.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₂ x v
  have hww_nn : 0 ≤ g₂.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₂ x w
  have huu_nn : 0 ≤ g₂.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₂ x u
  set Sv : ℝ := Real.sqrt (g₂.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₂.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₂.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    have hp := hprim
    rw [hAA_sq] at hp
    rw [Real.sqrt_sq hNA_nn] at hp
    exact hp
  rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
  · rw [← hNA0]
    positivity
  · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
      rw [show NA * NA = NA ^ 2 from by ring]
      refine le_trans hprim' ?_
      apply le_of_eq; ring
    have hcancel := le_of_mul_le_mul_left hkey hNApos
    calc NA ≤ NW * Sv * Su * Sw := hcancel
      _ = NW * Sv * Sw * Su := by ring

end Curvature
end Geometry
end DifferentialGeometry

end
