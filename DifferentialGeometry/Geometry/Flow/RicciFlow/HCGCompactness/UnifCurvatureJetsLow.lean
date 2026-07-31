import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJetBound
import DifferentialGeometry.Geometry.Curvature.PerturbedCurvatureOperatorBound
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound

/-!
# Low-order class-uniform curvature and connection-difference bounds (brick E3, `Λ < 2`)

The `Λ < 2` staging layer of brick E3.  `UnifCurvatureJetBound.lean` proves the
order-`0` Riemann sup `unifCurvatureSup_singleLink` for the `Λ`-class together
with the three dischargers of the perturbation package consumed by the
`Geometry/Curvature/` jet-envelope assets:

* `metricDiff_gFibreOpBound` — the fibre operator bound `δ = Λ − 1`;
* `metricDiff_tie` — `g₀ = gBase + h_sym(g₀ − gBase)`;
* `metricDiff_jetEnvelope` — `∑_{j ≤ 2} ‖∇^{gBase,j}(g₀ − gBase)‖ ≤ n(Λ−1) + 2Λ`.

This file reads three further `Geometry/Curvature/` assets through the *same*
discharger triple, producing the remaining order-`≤ 1` class-uniform geometric
bounds that the E6 static-field fibre bound `Ksup` consumes:

* `unifRicSup` — the raised Ricci endomorphism of `g₀`;
* `unifConnDiffSup` — the Levi-Civita connection difference `Γ(g₀) − Γ(gBase)`;
* `unifCovConnDiffSup` — its first `gBase`-covariant derivative.

All three constants are closed in `(Λ, gBase)` alone: they are chosen from
assets applied at the fixed background `gBase` with radius `δ₀ = Λ − 1` and
envelope `B = n(Λ−1) + 2Λ`, before any class member `g₀` is named.  That is the
class-uniformity the E5/E6 endpoints need.

See `UnifCurvatureJetsLow.md` for the E3 scope audit — in particular for why the
order-`≥ 1` *curvature* jets (`∇^a Rm`, `a ≥ 1`), and hence the `Fc` family and
the `j = 1` half of `Ksup`, are blocked on a missing upstream
curvature-difference asset rather than on anything in this layer.
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
/-- **Class-uniform connection-difference sup (`1 ≤ Λ < 2`), order `0`.**

The Levi-Civita connection difference `A = Γ(g₀) − Γ(gBase)` has `gBase`-fibre
length at most `C · √(gBase(v,v)) · √(gBase(w,w))` with `C` closed in
`(Λ, gBase)`: the order-`1` metric jet `‖∇^{gBase,1}(g₀ − gBase)‖ ≤ Λ` of the
class feeds the Koszul bound
`connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one` at radius `δ₀ = Λ − 1`.

This is the order-`0` half of the DeTurck vector-field envelope: the DeTurck
field `W = deTurckVF g₀ gBase` is the `g₀`-trace of `A`
(`deTurckVF_eq_orthoFrame_trace`). -/
theorem unifConnDiffSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
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
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 3
  obtain ⟨C, hC0, hC⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M)
      gBase (δ₀ := Λ - 1) hΛ1 (by linarith : Λ - 1 < 1)
  refine ⟨C * Λ, mul_nonneg hC0 hΛ0.le, ?_⟩
  intro x v w
  set N : ℝ := ‖((iteratedCovGrad (I := I) gBase 0 2 1
      (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)).toSection x :
        TensorRSSpace 0 3 I x)‖ with hN_def
  have hjetx : N ≤ Λ :=
    metricDiff_orderPos_bound (I := I) (M := M) gBase g₀ 0 hjet1 x
  have hstep := hC g₀ (metricDifferenceCcTensor (I := I) (M := M) gBase g₀)
    (fun y a b => metricDiff_tie (I := I) (M := M) gBase g₀ y a b) (δ := Λ - 1)
    (le_refl _) hΛ1
    (metricDiff_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp) x v w
  refine hstep.trans ?_
  have hvw : (0 : ℝ) ≤ Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmono : C * N ≤ C * Λ := mul_le_mul_of_nonneg_left hjetx hC0
  calc C * N * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w)
      = (C * N) * (Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w)) := by ring
    _ ≤ (C * Λ) * (Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w)) :=
        mul_le_mul_of_nonneg_right hmono hvw
    _ = C * Λ * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by ring

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Class-uniform connection-difference sup (`1 ≤ Λ < 2`), order `1`.**

The first `gBase`-covariant derivative `∇^{gBase}A` of the connection difference
obeys the `gBase`-quadratic bound with a constant closed in `(Λ, gBase)`,
obtained from `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope` at radius
`δ₀ = Λ − 1` and envelope `B = n(Λ−1) + 2Λ` through the same discharger triple.

This is the order-`1` half of the DeTurck vector-field envelope.  (An
`MetricUniformEquivalentOn`-currency sibling with the *explicit* constant
`(3/2)Λ⁴(Λ'' + ΛΛ'²)` and no `Λ < 2` gate is
`HCGCompactness.covDerivConnDiff_gJet_le`; this statement is the jet-envelope
face, matching the hypothesis package the other `Geometry/Curvature/` assets in
this lane consume.) -/
theorem unifCovConnDiffSup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
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
  classical
  have hΛ1 : (0 : ℝ) ≤ Λ - 1 := by linarith
  have hB0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hΛ1) (by linarith)
  obtain ⟨C, hC0, hC⟩ :=
    exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope (I := I) (M := M)
      gBase (δ₀ := Λ - 1) (by linarith : Λ - 1 < 1)
      ((Module.finrank ℝ E : ℝ) * (Λ - 1) + 2 * Λ) hB0
  refine ⟨C, hC0, ?_⟩
  intro x v w u
  exact hC g₀ (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) (δ := Λ - 1)
    (le_of_eq (max_eq_left hΛ1).symm)
    (metricDiff_gFibreOpBound (I := I) (M := M) gBase g₀ hΛ hcomp)
    (fun y a b => metricDiff_tie (I := I) (M := M) gBase g₀ y a b) x
    (metricDiff_jetEnvelope (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x) v w u

set_option linter.unusedSectionVars false in
/-- **Class-uniform Ricci bilinear bound (`1 ≤ Λ < 2`).**  The bilinear face of
`unifRicSup`, obtained by Cauchy–Schwarz against the defining property
`g₀(Ric♯v, w) = Ric(v, w)` of `ricEndoRaisedFib`.  This is the shape the E6
static-field fibre bound consumes: read on a `g₀`-orthonormal frame it bounds
every component of the Ricci summand of `deTurckRicciRHS gBase g₀`. -/
theorem unifRicBilin
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x),
        |ricciTensor (I := I) g₀ x v w| ≤
          C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    unifRicSup (I := I) (M := M) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2
  refine ⟨C, hC0, ?_⟩
  intro x v w
  set R : TangentSpace I x := ricEndoRaisedFib (I := I) g₀ x v with hR
  have hRic : ricciTensor (I := I) g₀ x v w = g₀.inner x R w :=
    (inner_ricEndoRaisedFib (I := I) g₀ x v w).symm
  have hcs : |g₀.inner x R w| ≤
      Real.sqrt (g₀.inner x R R) * Real.sqrt (g₀.inner x w w) :=
    abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x R w
  have hvv : (0 : ℝ) ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hRR : Real.sqrt (g₀.inner x R R) ≤ C * Real.sqrt (g₀.inner x v v) := by
    calc Real.sqrt (g₀.inner x R R)
        ≤ Real.sqrt (C ^ 2 * g₀.inner x v v) := Real.sqrt_le_sqrt (hC x v)
      _ = C * Real.sqrt (g₀.inner x v v) := by
          rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]
  rw [hRic]
  refine hcs.trans ?_
  exact le_of_eq_of_le rfl
    (le_trans (mul_le_mul_of_nonneg_right hRR (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))

end RicciFlow
end PDE
end DifferentialGeometry

end
