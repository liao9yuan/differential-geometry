import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJetBound
import DifferentialGeometry.Geometry.Curvature.PerturbedCurvatureOperatorBound
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound

/-!
# Low-order class-uniform curvature and connection-difference bounds (brick E3)

This file now has two scopes.

* `unifConnDiffSup` and `unifCovConnDiffSup` are finite-order estimates for
  arbitrary `Λ ≥ 1`.  They use the explicit Koszul estimates
  `connDiff_gJet_le` and `covDerivConnDiff_gJet_le`, so no perturbative
  `Λ < 2` gate remains.
* `unifRicSup` and its bilinear face `unifRicBilin` still use the older
  perturbative Ricci asset and therefore retain `Λ < 2`.

In every case the constant is chosen before the class member `g₀`.  The two
connection-difference constants are explicit functions of `Λ`; the Ricci
constant is closed in `(Λ, gBase)`.

The arbitrary-`Λ` order-zero curvature producer now lives in
`UnifCurvatureJetBound.lean`, while the differentiated Palatini and first
curvature-jet assembly live in their dedicated sibling modules.  See
`UnifCurvatureJetsLow.md` for the current consumer-migration status.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **The `Λ`-comparability input conversion.**  `Λ⁻¹ · gBase ≤ g₀` rearranges to
`gBase ≤ Λ · g₀` on the diagonal. -/
private lemma gBase_le_scaled (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) (v : TangentSpace I x) :
    gBase.inner x v v ≤ Λ * g₀.inner x v v := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hz := mul_le_mul_of_nonneg_left (hcomp x v).1 hΛ0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz

/-- **Class-uniform raised-Ricci sup (`1 ≤ Λ < 2`).**

Under `Λ`-comparability of `g₀` with `gBase` and the class metric-jet bounds
`MetricCovDerivOrderBoundOn` at orders `1` and `2`, the raised Ricci endomorphism
of `g₀` obeys `g₀(Ric♯v, Ric♯v) ≤ C² · g₀(v,v)` with a constant `C = Λ · C₀`
depending only on `(Λ, gBase)`, where `C₀` is the constant of
`exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope` at radius
`δ₀ = Λ − 1` and envelope `B = n(Λ−1) + 2Λ`.

Together with `ricEndoRaisedFib`'s defining property
`g₀(Ric♯ v, w) = Ric(v, w)` this is the Ricci half of the E6 static-field
fibre bound. -/
theorem unifRicSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v : TangentSpace I x),
        g₀.inner x (ricEndoRaisedFib (I := I) g₀ x v)
            (ricEndoRaisedFib (I := I) g₀ x v) ≤
          C ^ 2 * g₀.inner x v v := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  have hB0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hΛ1) (by linarith)
  obtain ⟨C, hC0, hC⟩ :=
    exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope (I := I) (M := M)
      gBase (δ₀ := Λ - 1) (by linarith : Λ - 1 < 1)
      ((Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ) hB0
  refine ⟨Λ * C, mul_nonneg hΛ0.le hC0, ?_⟩
  intro x v
  have hbase := hC g₀ (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) (δ := Λ - 1)
    (le_of_eq (max_eq_left hΛ1).symm)
    (metricDiff_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp)
    (fun y a b => metricDiff_tie (I := I) (M := M) gBase g₀ y a b) x
    (metricDiff_jetEnvelope (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x) v
  set R : TangentSpace I x := ricEndoRaisedFib (I := I) g₀ x v with hR
  have hout : g₀.inner x R R ≤ Λ * gBase.inner x R R := (hcomp x R).2
  have hin : gBase.inner x v v ≤ Λ * g₀.inner x v v :=
    gBase_le_scaled (I := I) (M := M) gBase g₀ hΛ hcomp x v
  calc g₀.inner x R R
      ≤ Λ * gBase.inner x R R := hout
    _ ≤ Λ * (C ^ 2 * gBase.inner x v v) := mul_le_mul_of_nonneg_left hbase hΛ0.le
    _ ≤ Λ * (C ^ 2 * (Λ * g₀.inner x v v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (sq_nonneg C)) hΛ0.le
    _ = (Λ * C) ^ 2 * g₀.inner x v v := by ring

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- Explicit order-zero connection-difference coefficient. -/
noncomputable def connDiffZeroC (Λ : ℝ) : ℝ :=
  3 / 2 * Λ ^ 3 * Λ

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The order-zero connection-difference estimate with its fixed coefficient. -/
theorem connDiffSup_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)) ≤
        connDiffZeroC Λ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  intro x v w
  have h := connDiff_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
  simpa [connDiffZeroC, DifferentialGeometry.PDE.DeTurck.connDiff,
    mul_assoc, mul_left_comm, mul_comm] using h

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Class-uniform connection-difference sup for arbitrary `Λ ≥ 1`, order `0`.**

The Levi-Civita connection difference `A = Γ(g₀) − Γ(gBase)` has `gBase`-fibre
length at most `C · √(gBase(v,v)) · √(gBase(w,w))` with `C` closed in
`Λ`: the order-`1` metric jet of the class feeds the ungated finite-order
Koszul estimate `connDiff_gJet_le`.

This is the order-`0` half of the DeTurck vector-field envelope: the DeTurck
field `W = deTurckVF g₀ gBase` is the `g₀`-trace of `A`
(`deTurckVF_eq_orthoFrame_trace`). -/
theorem unifConnDiffSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x),
        Real.sqrt (gBase.inner x
            (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)
            (DifferentialGeometry.PDE.DeTurck.connDiff (I := I) g₀ gBase x v w)) ≤
          C * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by
  refine ⟨connDiffZeroC Λ, ?_, ?_⟩
  · dsimp [connDiffZeroC]
    positivity
  · exact connDiffSup_le (I := I) (M := M) gBase g₀ hΛ hcomp hjet1

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- Explicit order-one connection-difference coefficient. -/
noncomputable def connDiffOneC (Λ : ℝ) : ℝ :=
  3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2)

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The order-one connection-difference estimate with its fixed coefficient. -/
theorem covConnDiff_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (covDerivConnDiff (I := I) gBase g₀
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) gBase g₀
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)) ≤
        connDiffOneC Λ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) * Real.sqrt (gBase.inner x u u) := by
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  intro x v w u
  simpa [connDiffOneC] using
    covDerivConnDiff_gJet_le (I := I) hEq hjet1 hjet2
      (Set.mem_univ x) v w u

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Class-uniform connection-difference sup for arbitrary `Λ ≥ 1`, order `1`.**

The first `gBase`-covariant derivative `∇^{gBase}A` of the connection difference
obeys the `gBase`-quadratic bound with a constant closed in `(Λ, gBase)`,
obtained directly from the ungated finite-order estimate
`covDerivConnDiff_gJet_le`.

This is the order-`1` half of the DeTurck vector-field envelope.  (An
`MetricUniformEquivalentOn`-currency sibling with the *explicit* constant
`(3/2)Λ⁴(Λ'' + ΛΛ'²)` and no `Λ < 2` gate is
`HCGCompactness.covDerivConnDiff_gJet_le`; this statement is the jet-envelope
face, matching the hypothesis package the other `Geometry/Curvature/` assets in
this lane consume.) -/
theorem unifCovConnDiffSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        Real.sqrt (gBase.inner x
            (covDerivConnDiff (I := I) gBase g₀
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w)
                (smoothExtensionTangent (I := I) x u) x)
            (covDerivConnDiff (I := I) gBase g₀
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w)
                (smoothExtensionTangent (I := I) x u) x)) ≤
          C * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) *
            Real.sqrt (gBase.inner x u u) := by
  refine ⟨connDiffOneC Λ, ?_, ?_⟩
  · dsimp [connDiffOneC]
    positivity
  · exact covConnDiff_le (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2

set_option linter.unusedSectionVars false in
/-- Explicit zero-order Ricci coefficient with the fixed background curvature
cap supplied. -/
noncomputable def ricciZeroC (Λ Kb : ℝ) : ℝ :=
  (Module.finrank ℝ E : ℝ) *
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb))

set_option linter.unusedSectionVars false in
/-- **Class-uniform Ricci bilinear bound for arbitrary `Λ ≥ 1`.**

The arbitrary-`Λ` curvature operator estimate `unifCurvSup` is traced in a
`g₀`-orthonormal frame.  Cauchy--Schwarz on each trace summand gives the
bilinear Ricci bound with the sole dimensional loss `finrank ℝ E`. -/
theorem ricciBilin_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (v w : TangentSpace I x),
      |ricciTensor (I := I) g₀ x v w| ≤
        ricciZeroC (E := E) Λ Kb * Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) := by
  classical
  let F : ℝ := Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb)
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  have hF0 : 0 ≤ F :=
    mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  have hF := unifCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  intro x v w
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x
  have hB : ∀ i j : Fin (Module.finrank ℝ E),
      g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) g₀ x v w B hB]
  calc
    |∑ i, g₀.inner x
        (riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w) (B i)|
        ≤ ∑ i, |g₀.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w) (B i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
        F * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      set R : TangentSpace I x :=
        riemannOp (cov := LeviCivita (I := I) g₀) x (B i) v w with hR
      have hBii : g₀.inner x (B i) (B i) = 1 := by
        rw [hB i i]
        simp
      have hRR : g₀.inner x R R ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w := by
        have h := hF x (B i) v w
        rw [← hR, hBii] at h
        simpa only [mul_one] using h
      have hv0 : 0 ≤ g₀.inner x v v :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x v
      have hw0 : 0 ≤ g₀.inner x w w :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x w
      have hsqrt : Real.sqrt (g₀.inner x R R) ≤
          F * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by
        have heq : F ^ 2 * g₀.inner x v v * g₀.inner x w w =
            (F * Real.sqrt (g₀.inner x v v) *
              Real.sqrt (g₀.inner x w w)) ^ 2 := by
          calc
            F ^ 2 * g₀.inner x v v * g₀.inner x w w =
                F ^ 2 * Real.sqrt (g₀.inner x v v) ^ 2 *
                  Real.sqrt (g₀.inner x w w) ^ 2 := by
              rw [Real.sq_sqrt hv0, Real.sq_sqrt hw0]
            _ = (F * Real.sqrt (g₀.inner x v v) *
                Real.sqrt (g₀.inner x w w)) ^ 2 := by ring
        rw [heq] at hRR
        have h := Real.sqrt_le_sqrt hRR
        rwa [Real.sqrt_sq
          (mul_nonneg (mul_nonneg hF0 (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))] at h
      change |g₀.inner x R (B i)| ≤ _
      calc
        |g₀.inner x R (B i)| ≤
            Real.sqrt (g₀.inner x R R) *
              Real.sqrt (g₀.inner x (B i) (B i)) :=
          abs_metric_inner_le_sqrt_metric_quadratic
            (I := I) (M := M) g₀ x R (B i)
        _ = Real.sqrt (g₀.inner x R R) := by
          rw [hBii]
          simp
        _ ≤ _ := hsqrt
    _ = ricciZeroC (E := E) Λ Kb *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [ricciZeroC, F]
      ring

set_option linter.unusedSectionVars false in
/-- **Class-uniform Ricci bilinear bound for arbitrary `Λ ≥ 1`.** -/
theorem unifRicBilin
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x),
        |ricciTensor (I := I) g₀ x v w| ≤
          C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  have hCd0 : 0 ≤ riemannDiffC Λ Λ Λ := by
    unfold riemannDiffC
    positivity
  refine ⟨ricciZeroC (E := E) Λ Kb, ?_, ?_⟩
  · dsimp [ricciZeroC]
    exact mul_nonneg (Nat.cast_nonneg _) <|
      mul_nonneg (sq_nonneg _) (add_nonneg hCd0 (Real.sqrt_nonneg _))
  · exact ricciBilin_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2

end RicciFlow
end PDE
end DifferentialGeometry

end
