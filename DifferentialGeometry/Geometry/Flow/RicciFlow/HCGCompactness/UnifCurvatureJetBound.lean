import DifferentialGeometry.Geometry.Curvature.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff

/-!
# Uniform curvature-jet bound (item-6 brick 2a)

Downstream discharge of the class-uniform curvature-jet bound that the S1
Gårding constant (`UnifBochnerGap.lean`) consumes abstractly.  This file is the
`HCGCompactness` home of brick (2a); it imports the `Geometry/Curvature/`
difference/fixed assets (upstream of HCG, so importable) — see
`UnifCurvatureJetBound.md` for the ratified route (2a-0 → 2a-tel → 2a-hi → 2a-pkg)
and the asset inventory.

## This file (session 4, order-0 composition core)

`unifCurvatureSup_singleLink_of_diff` — the order-0 curvature sup bound assembled
from the order-0 Riemann *difference* bound (its conclusion, taken as a
hypothesis `hdiff`; discharged from the class jets by the frontier layer) and the
committed *fixed*-`gBase` curvature bound
(`exists_uniform_riemannOp_LeviCivita_gNorm_bound`), converted from the `gBase`
to the `g₀` inner product by `Λ`-comparability.  Explicit constant
`F = Λ²·(Cd + √Kbase)`.

The genuinely-missing infrastructure (constructing `P = g₀ − gBase` as a
`SmoothCcTensor gBase 0 2`, its `htie`, the comparability→`gFibreOpBound` bridge,
and the metric-jet envelope), together with the `convexComb` telescoping to the
full class `Λ ≥ 1`, is the named frontier recorded in `UnifCurvatureJetBound.md`.
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
/-- The `g`-norm triangle inequality on a fibre:
`√(g(a+b,a+b)) ≤ √(g(a,a)) + √(g(b,b))`.  (Local copy of the private
`gNorm_self_triangle` used in `PerturbedRiemannOpDifferenceBound`.) -/
private lemma gAddNorm_le
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have haa : 0 ≤ g.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g x a
  have hbb : 0 ≤ g.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g x b
  have hcs : g.inner x a b ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
    refine le_trans (le_abs_self _) ?_
    exact abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x a b
  have hexpand : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h1 : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      rw [map_add (g.inner x), ContinuousLinearMap.add_apply]
    have h2 : g.inner x a (a + b) = g.inner x a a + g.inner x a b :=
      map_add (g.inner x a) a b
    have h3 : g.inner x b (a + b) = g.inner x b a + g.inner x b b :=
      map_add (g.inner x b) a b
    have h4 : g.inner x b a = g.inner x a b := g.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hsum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) =
      Real.sqrt ((Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2) from
    (Real.sqrt_sq hsum_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand]
  have hsq : (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2 =
      g.inner x a a + 2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) +
        g.inner x b b := by
    rw [add_sq, Real.sq_sqrt haa, Real.sq_sqrt hbb]; ring
  rw [hsq]
  linarith [hcs]

/-- **Order-0 curvature sup bound, single-link (`Λ < 2`) regime.**

Given the order-0 Riemann *difference* bound `hdiff` (the conclusion of
`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope` at role
base = `gBase`, `g₁ = g₀`; discharged from the class metric jets by the frontier
layer) and `Λ`-comparability of `g₀` with `gBase`, the absolute Riemann operator
of `g₀` is bounded in the `g₀` inner product by `F²` with

  `F = Λ² · (Cd + √Kbase)`,

where `Kbase` is the fixed `gBase` curvature constant
(`exists_uniform_riemannOp_LeviCivita_gNorm_bound`).  This is the composition
spine of brick 2a-0; the full class `Λ ≥ 1` follows by `convexComb` telescoping
(2a-tel). -/
theorem unifCurvatureSup_singleLink_of_diff
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hdiff : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) g₀) x v w u -
            riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        g₀.inner x
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
          F ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  refine ⟨Λ ^ 2 * (Cd + Real.sqrt Kb),
    mul_nonneg (sq_nonneg _) (add_nonneg hCd (Real.sqrt_nonneg _)), ?_⟩
  intro x v w u
  set R0 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₀) x v w u with hR0
  set Rb : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) gBase) x v w u with hRb
  -- fibre quadratics in the base metric, all nonnegative
  have hbvv0 : 0 ≤ gBase.inner x v v := metric_inner_self_nonneg (I := I) (M := M) gBase x v
  have hbww0 : 0 ≤ gBase.inner x w w := metric_inner_self_nonneg (I := I) (M := M) gBase x w
  have hbuu0 : 0 ≤ gBase.inner x u u := metric_inner_self_nonneg (I := I) (M := M) gBase x u
  set P3 : ℝ := gBase.inner x v v * gBase.inner x w w * gBase.inner x u u with hP3
  have hP30 : 0 ≤ P3 := by
    rw [hP3]; exact mul_nonneg (mul_nonneg hbvv0 hbww0) hbuu0
  -- the two committed inputs, folded to `R0`/`Rb` and the single product `P3`
  have h := hdiff x v w u
  rw [← hR0, ← hRb] at h
  have hk := hKb x v w u
  rw [← hRb] at hk
  have hd3 : gBase.inner x (R0 - Rb) (R0 - Rb) ≤ Cd ^ 2 * P3 := by
    rw [hP3]
    calc gBase.inner x (R0 - Rb) (R0 - Rb)
        ≤ Cd ^ 2 * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := h
      _ = Cd ^ 2 * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  have hb3 : gBase.inner x Rb Rb ≤ Kb * P3 := by
    rw [hP3]
    calc gBase.inner x Rb Rb
        ≤ Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u := hk
      _ = Kb * (gBase.inner x v v * gBase.inner x w w * gBase.inner x u u) := by ring
  -- √ of each input
  have hnDiff : Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) ≤ Cd * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb))
        ≤ Real.sqrt (Cd ^ 2 * P3) := Real.sqrt_le_sqrt hd3
      _ = Cd * Real.sqrt P3 := by rw [Real.sqrt_mul (sq_nonneg Cd), Real.sqrt_sq hCd]
  have hnRb : Real.sqrt (gBase.inner x Rb Rb) ≤ Real.sqrt Kb * Real.sqrt P3 := by
    calc Real.sqrt (gBase.inner x Rb Rb)
        ≤ Real.sqrt (Kb * P3) := Real.sqrt_le_sqrt hb3
      _ = Real.sqrt Kb * Real.sqrt P3 := by rw [Real.sqrt_mul hKb0]
  -- triangle: `R0 = (R0 - Rb) + Rb`
  have hcancel : (R0 - Rb) + Rb = R0 := by abel
  have htri : Real.sqrt (gBase.inner x R0 R0) ≤
      (Cd + Real.sqrt Kb) * Real.sqrt P3 := by
    have htr := gAddNorm_le (I := I) (M := M) gBase x (R0 - Rb) Rb
    rw [hcancel] at htr
    calc Real.sqrt (gBase.inner x R0 R0)
        ≤ Real.sqrt (gBase.inner x (R0 - Rb) (R0 - Rb)) +
            Real.sqrt (gBase.inner x Rb Rb) := htr
      _ ≤ Cd * Real.sqrt P3 + Real.sqrt Kb * Real.sqrt P3 := add_le_add hnDiff hnRb
      _ = (Cd + Real.sqrt Kb) * Real.sqrt P3 := by ring
  -- square the triangle to get the base-metric curvature bound
  have hR0nn : 0 ≤ gBase.inner x R0 R0 :=
    metric_inner_self_nonneg (I := I) (M := M) gBase x R0
  have hbaseSq : gBase.inner x R0 R0 ≤ (Cd + Real.sqrt Kb) ^ 2 * P3 := by
    have hmm := mul_self_le_mul_self (Real.sqrt_nonneg _) htri
    rw [Real.mul_self_sqrt hR0nn] at hmm
    calc gBase.inner x R0 R0
        ≤ ((Cd + Real.sqrt Kb) * Real.sqrt P3) *
            ((Cd + Real.sqrt Kb) * Real.sqrt P3) := hmm
      _ = (Cd + Real.sqrt Kb) ^ 2 * (Real.sqrt P3 * Real.sqrt P3) := by ring
      _ = (Cd + Real.sqrt Kb) ^ 2 * P3 := by rw [Real.mul_self_sqrt hP30]
  -- convert the base-metric bound to the `g₀` inner product via comparability
  have hout : g₀.inner x R0 R0 ≤ Λ * gBase.inner x R0 R0 := (hcomp x R0).2
  have hcoeff_nn : 0 ≤ (Cd + Real.sqrt Kb) ^ 2 := sq_nonneg _
  -- input conversion: `gBase(z,z) ≤ Λ · g₀(z,z)` on the diagonal
  have hinConv : ∀ z : TangentSpace I x, gBase.inner x z z ≤ Λ * g₀.inner x z z := by
    intro z
    have hz := (hcomp x z).1
    have hz2 := mul_le_mul_of_nonneg_left hz hΛ0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz2
  have hg0vv0 : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hg0ww0 : 0 ≤ g₀.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have hΛg0vv : 0 ≤ Λ * g₀.inner x v v := mul_nonneg hΛ0.le hg0vv0
  have hΛg0ww : 0 ≤ Λ * g₀.inner x w w := mul_nonneg hΛ0.le hg0ww0
  have hstep1 : gBase.inner x v v * gBase.inner x w w ≤
      (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) :=
    mul_le_mul (hinConv v) (hinConv w) hbww0 hΛg0vv
  have hstep2 : P3 ≤ (Λ * g₀.inner x v v) * (Λ * g₀.inner x w w) * (Λ * g₀.inner x u u) := by
    rw [hP3]
    exact mul_le_mul hstep1 (hinConv u) hbuu0 (mul_nonneg hΛg0vv hΛg0ww)
  have hP3_conv : P3 ≤ Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u) := by
    refine le_trans hstep2 (le_of_eq ?_); ring
  -- assemble
  calc g₀.inner x R0 R0
      ≤ Λ * gBase.inner x R0 R0 := hout
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 * P3) :=
          mul_le_mul_of_nonneg_left hbaseSq hΛ0.le
    _ ≤ Λ * ((Cd + Real.sqrt Kb) ^ 2 *
          (Λ ^ 3 * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hP3_conv hcoeff_nn) hΛ0.le
    _ = (Λ ^ 2 * (Cd + Real.sqrt Kb)) ^ 2 *
          g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by ring

/-! ### P-construction tie API (session 5)

The metric-difference realization `metricDifferenceCcTensor gBase g₀`
(`RicciArmResidualCoefficientFields.lean:118`, reused) supplies the perturbation
`P` the order-0 difference asset consumes; these lemmas prove it satisfies the
asset's `htie` shape at role base = `gBase`, `g₁ = g₀`.  The two dischargers
(`gFibreOpBound` from comparability; the order-`≤2` jet envelope from
`MetricCovDerivOrderBoundOn`) are the remaining frontier — see
`UnifCurvatureJetBound.md`. -/

/-- The metric difference `metricDifferenceCcTensor gBase g₀` extracts, before
symmetrization, to the pointwise metric difference `g₀ − gBase`. -/
theorem metricDiff_ccBilin (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) gBase
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w =
      g₀.inner x v w - gBase.inner x v w := by
  have h : metricDifferenceCcTensor (I := I) (M := M) gBase g₀ =
      metricCcTensor (I := I) (M := M) gBase g₀ -
        metricCcTensor (I := I) (M := M) gBase gBase := rfl
  rw [h, ccTensorBilin_sub, metricCcTensor_apply, metricCcTensor_apply]

/-- The metric difference realizes `g₀ − gBase` after symmetrization as well:
the difference of two symmetric metrics is already symmetric. -/
theorem metricDiff_ccBilinSymm (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) gBase
        (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w =
      g₀.inner x v w - gBase.inner x v w := by
  rw [ccTensorBilinSymm_apply, metricDiff_ccBilin gBase g₀ x v w,
    metricDiff_ccBilin gBase g₀ x w v, gBase.symm x w v, g₀.symm x w v]
  ring

/-- **Tie identity — the asset `htie` shape (role base = `gBase`, `g₁ = g₀`).**
`g₀` is realized as `gBase` plus the symmetric perturbation
`ccTensorBilinSymm gBase (metricDifferenceCcTensor gBase g₀)`.  This discharges
the `htie` hypothesis of
`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`. -/
theorem metricDiff_tie (gBase g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g₀.inner x v w =
      gBase.inner x v w +
        ccTensorBilinSymm (I := I) gBase
          (metricDifferenceCcTensor (I := I) (M := M) gBase g₀) x v w := by
  rw [metricDiff_ccBilinSymm]; ring

end RicciFlow
end PDE
end DifferentialGeometry
