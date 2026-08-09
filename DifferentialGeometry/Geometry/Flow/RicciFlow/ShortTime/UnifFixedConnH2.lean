import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifDeTurckRHSOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifGagliardoNirenberg
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower

/-!
# Class-first fixed-background connection bound

This module packages the first three class-metric covariant jets of the fixed
background connection difference into a single dimension-three `H2` bound.
The coefficient is selected before the class metric varies.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The explicit class-first `H2` coefficient for the fixed-background
connection difference. -/
noncomputable def connFixH2C
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let R₁ := revJetOneC (E := E) Λ
  let R₂ := revJetTwoC (E := E) Λ
  let R₃ := revJetThreeC (E := E) Λ
  let A₀ := 3 / 2 * Λ ^ 3 * R₁
  let A₁ := 3 / 2 * Λ ^ 4 * (R₂ + Λ * R₁ ^ 2)
  let A₂ :=
    3 / 2 * Λ ^ 5 * R₃ +
      9 / 2 * Λ ^ 6 * R₁ * R₂ +
      3 * Λ ^ 7 * R₁ ^ 3
  Real.sqrt
    (((3 : ℝ) ^ 3 * A₀ ^ 2 + (3 : ℝ) ^ 4 * A₁ ^ 2 +
        (3 : ℝ) ^ 5 * A₂ ^ 2) *
      (volCompareC (E := E) Λ *
        ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal))

/-- The pointwise fixed-connection coefficient for the first three derivative
orders used by class-first coefficient factories. -/
noncomputable def connFixGridC (Λ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then connDiffZeroSqC (E := E) Λ
  else if j = 1 then connDiffOneSqC (E := E) Λ
  else connDiffTwoC (E := E) Λ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- The fixed-connection pointwise grid coefficient is nonnegative. -/
lemma connFixGridC_nonneg (Λ : ℝ) (j : ℕ) :
    0 ≤ connFixGridC (E := E) Λ j := by
  unfold connFixGridC
  split
  · unfold connDiffZeroSqC
    positivity
  · split
    · unfold connDiffOneSqC
      positivity
    · unfold connDiffTwoC
      positivity

/-- The first three fixed-background connection-difference jets admit one
pointwise coefficient family chosen before the class metric varies. -/
theorem connFix_grid_unif
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ F : ℕ → ℝ, (∀ j, 0 ≤ F j) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connDiffSection (I := I) gBase g₀)).toSection x) ≤
            F j := by
  refine ⟨connFixGridC (E := E) Λ, connFixGridC_nonneg (E := E) Λ, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 j hj x
  have hcomp : ∀ (y : M) (v : TangentSpace I y),
      Λ⁻¹ * gBase.inner y v v ≤ g₀.inner y v v ∧
        g₀.inner y v v ≤ Λ * gBase.inner y v v :=
    fun y v => hEq.2 y (Set.mem_univ y) v
  by_cases hj0 : j = 0
  · subst j
    simpa [connFixGridC] using
      (unifConnDiffZero (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 x)
  by_cases hj1 : j = 1
  · subst j
    simpa [connFixGridC] using
      (unifConnDiffOne (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x)
  have hj2 : j = 2 := by omega
  subst j
  simpa [connFixGridC] using
    (unifConnDiffTwo (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 hjet3 x)

/-- **Dimension-three class-first fixed-background connection bound.**

For every class metric uniformly equivalent to `gBase` whose first three
`gBase`-covariant metric jets are bounded by `Λ`, the `g₀`-Sobolev sum of
`connDiffSection gBase g₀` through order two is bounded by one coefficient
chosen solely from `(gBase, Λ)` before `g₀` varies. -/
theorem connFix_h2_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 2 j
            (connDiffSection (I := I) gBase g₀)‖ ^ 2) ≤ F ^ 2 := by
  classical
  let R₁ : ℝ := revJetOneC (E := E) Λ
  let R₂ : ℝ := revJetTwoC (E := E) Λ
  let R₃ : ℝ := revJetThreeC (E := E) Λ
  let A₀ : ℝ := 3 / 2 * Λ ^ 3 * R₁
  let A₁ : ℝ := 3 / 2 * Λ ^ 4 * (R₂ + Λ * R₁ ^ 2)
  let A₂ : ℝ :=
    3 / 2 * Λ ^ 5 * R₃ +
      9 / 2 * Λ ^ 6 * R₁ * R₂ +
      3 * Λ ^ 7 * R₁ ^ 3
  let C₀ : ℝ := (3 : ℝ) ^ 3 * A₀ ^ 2
  let C₁ : ℝ := (3 : ℝ) ^ 4 * A₁ ^ 2
  let C₂ : ℝ := (3 : ℝ) ^ 5 * A₂ ^ 2
  let V : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V, volCompareC]
    positivity
  refine ⟨connFixH2C (E := E) (I := I) (M := M) gBase Λ,
    Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3
  have hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v :=
    fun x v => hEq.2 x (Set.mem_univ x) v
  have hpt₀ := unifConnDiffZero (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1
  have hpt₁ := unifConnDiffOne (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2
  have hpt₂ := unifConnDiffTwo (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  have hpt₀' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 2 0
            (connDiffSection (I := I) gBase g₀)).toSection x) ≤ C₀ := by
    simpa only [C₀, A₀, R₁, connDiffZeroSqC, hDim] using hpt₀
  have hpt₁' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1
            (connDiffSection (I := I) gBase g₀)).toSection x) ≤ C₁ := by
    simpa only [C₁, A₁, R₁, R₂, connDiffOneSqC, hDim] using hpt₁
  have hpt₂' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connDiffSection (I := I) gBase g₀)).toSection x) ≤ C₂ := by
    simpa only [C₂, A₂, R₁, R₂, R₃, connDiffTwoC, hDim] using hpt₂
  have hvol := (volumeReal_cross (I := I) (M := M) gBase g₀ hEq).1
  have hvolV :
      ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ V := by
    simpa only [V] using hvol
  have hnorm₀ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 0
          (connDiffSection (I := I) gBase g₀)‖ ^ 2 ≤ C₀ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 0)
      (iteratedCovGrad (I := I) g₀ 1 2 0
        (connDiffSection (I := I) gBase g₀)) C₀ ?_).trans ?_
    · exact hpt₀'
    · exact mul_le_mul_of_nonneg_left hvolV hC₀
  have hnorm₁ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 1
          (connDiffSection (I := I) gBase g₀)‖ ^ 2 ≤ C₁ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 1)
      (iteratedCovGrad (I := I) g₀ 1 2 1
        (connDiffSection (I := I) gBase g₀)) C₁ ?_).trans ?_
    · exact hpt₁'
    · exact mul_le_mul_of_nonneg_left hvolV hC₁
  have hnorm₂ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 2
          (connDiffSection (I := I) gBase g₀)‖ ^ 2 ≤ C₂ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 2)
      (iteratedCovGrad (I := I) g₀ 1 2 2
        (connDiffSection (I := I) gBase g₀)) C₂ ?_).trans ?_
    · exact hpt₂'
    · exact mul_le_mul_of_nonneg_left hvolV hC₂
  let f : ℕ → ℝ := fun j =>
    ‖iteratedCovGrad (I := I) g₀ 1 2 j
      (connDiffSection (I := I) gBase g₀)‖ ^ 2
  change (∑ j ∈ Finset.range 3, f j) ≤
    connFixH2C (E := E) (I := I) (M := M) gBase Λ ^ 2
  have hf₀ : f 0 ≤ C₀ * V := by simpa only [f] using hnorm₀
  have hf₁ : f 1 ≤ C₁ * V := by simpa only [f] using hnorm₁
  have hf₂ : f 2 ≤ C₂ * V := by simpa only [f] using hnorm₂
  calc
    ∑ j ∈ Finset.range 3, f j = f 0 + f 1 + f 2 := by
      norm_num [Finset.sum_range_succ]
    _ ≤ C₀ * V + C₁ * V + C₂ * V :=
      add_le_add (add_le_add hf₀ hf₁) hf₂
    _ = (C₀ + C₁ + C₂) * V := by ring
    _ = connFixH2C (E := E) (I := I) (M := M) gBase Λ ^ 2 := by
      change (C₀ + C₁ + C₂) * V = Real.sqrt ((C₀ + C₁ + C₂) * V) ^ 2
      rw [Real.sq_sqrt (mul_nonneg (add_nonneg (add_nonneg hC₀ hC₁) hC₂) hV)]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
