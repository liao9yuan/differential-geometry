import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PhiMetSelfBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PhiMetSymmetry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifGagliardoNirenberg
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifAppH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifGradSlot

/-!
# Class-first fixed curvature coefficient

This module packages the zeroth-order curvature coefficient left by the
Ricci--DeTurck top-order symmetrization.  In dimension three, its first two
intrinsic jets have one class-first bound depending only on the fixed
background and the metric-class parameter.  The resulting coefficient acts
uniformly from spectral `H2` to spectral `H1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Dimension-three class-first curvature-coefficient jet bound.**

The coefficient is chosen from the fixed background and the metric-class
parameter before the class metric varies.  Only the class metric's first
three background-covariant jets are used. -/
theorem phiCurv_jet_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (phiMetCurvCoeff (I := I) g gBase g)‖ ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hgrad⟩ :=
    gradSlot_grid_unif (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    appRS_h2_unif (I := I) (M := M) hDim gBase hΛ 2 4 2
  let V : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let Ks : ℝ := ∑ i ∈ Finset.range 3, phiSelfC (E := E) i
  let Kg : ℝ := ∑ i ∈ Finset.range 2, Cg i
  let As : ℝ := Real.sqrt (Ks * V)
  let Ag : ℝ := Real.sqrt (Kg * V)
  let C : ℝ := (1 / 2 : ℝ) * Capp * As * Ag
  have hV : 0 ≤ V := by
    dsimp only [V, volCompareC]
    positivity
  have hKs : 0 ≤ Ks := by
    dsimp only [Ks]
    exact Finset.sum_nonneg fun i _ ↦ phiSelfC_nonneg (E := E) i
  have hKg : 0 ≤ Kg := by
    dsimp only [Kg]
    exact Finset.sum_nonneg fun i _ ↦ hCg i
  have hAs : 0 ≤ As := Real.sqrt_nonneg _
  have hAg : 0 ≤ Ag := Real.sqrt_nonneg _
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro g hEq hjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hvol := (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  have hvolV :
      ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤ V := by
    simpa only [V] using hvol
  let Φ : SmoothCcTensor g 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g gBase g -
      ricciArmPrincipalCoeffPure (I := I) (M := M) g g
  let G : SmoothCcTensor g 2 4 := gradSwapCurvCoeff (I := I) g
  let Y : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 4 2 Φ G
  have hΦnorm : ∀ i : ℕ, i < 3 →
      ‖iteratedCovGrad (I := I) g 4 2 i Φ‖ ^ 2 ≤
        phiSelfC (E := E) i * V := by
    intro i hi
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g 4 (2 + i)
      (iteratedCovGrad (I := I) g 4 2 i Φ)
      (phiSelfC (E := E) i) ?_).trans ?_
    · intro x
      simpa only [Φ] using phiSelf_grid (I := I) (M := M) g gBase i x
    · exact mul_le_mul_of_nonneg_left hvolV (phiSelfC_nonneg (E := E) i)
  have hΦ :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i Φ‖ ^ 2) ≤ As ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 3, phiSelfC (E := E) i * V :=
        Finset.sum_le_sum fun i hi ↦ hΦnorm i (Finset.mem_range.mp hi)
      _ = Ks * V := by simp only [Ks, Finset.sum_mul]
      _ = As ^ 2 := by
        dsimp only [As]
        exact (Real.sq_sqrt (mul_nonneg hKs hV)).symm
  have hGnorm : ∀ i : ℕ, i < 2 →
      ‖iteratedCovGrad (I := I) g 2 4 i G‖ ^ 2 ≤ Cg i * V := by
    intro i hi
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g 2 (4 + i)
      (iteratedCovGrad (I := I) g 2 4 i G) (Cg i) ?_).trans ?_
    · intro x
      simpa only [G, gradSwapCurvCoeff] using hgrad g hEq hjet i hi x
    · exact mul_le_mul_of_nonneg_left hvolV (hCg i)
  have hG :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 2 4 i G‖ ^ 2) ≤ Ag ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2, Cg i * V :=
        Finset.sum_le_sum fun i hi ↦ hGnorm i (Finset.mem_range.mp hi)
      _ = Kg * V := by simp only [Kg, Finset.sum_mul]
      _ = Ag ^ 2 := by
        dsimp only [Ag]
        exact (Real.sq_sqrt (mul_nonneg hKg hV)).symm
  have hY := happ g hEq hjet1 hjet2 Φ G As Ag hAs hAg hΦ hG
  have hφ : phiMetCurvCoeff (I := I) g gBase g = (1 / 2 : ℝ) • Y := by
    rfl
  have hYnorm :
      ‖(⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ≤ Capp * As * Ag := by
    simpa only [Y] using hY
  have hφnorm :
      ‖(⟨phiMetCurvCoeff (I := I) g gBase g⟩ :
          SmoothCcTensorH1 g 2 2)‖ ≤ C := by
    rw [hφ]
    change ‖(1 / 2 : ℝ) • (⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ≤ C
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simpa only [C, mul_assoc] using
      (mul_le_mul_of_nonneg_left hYnorm (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hjet_eq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (phiMetCurvCoeff (I := I) g gBase g)‖ ^ 2) =
        ‖(⟨phiMetCurvCoeff (I := I) g gBase g⟩ :
          SmoothCcTensorH1 g 2 2)‖ ^ 2 := by
    rw [h1_jet_sq (I := I) (M := M)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ]
  rw [hjet_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) hφnorm 2

/-- **Dimension-three class-first fixed-curvature action bound.**

The fixed curvature term left in the top-order split acts uniformly from
spectral `H2` to spectral `H1` over the whole order-three metric class. -/
theorem fixed_curv_h1_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (appCc (I := I) (M := M) g 2 2
                (phiMetCurvCoeff (I := I) g gBase g) U)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h1_unif (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Aφ, hAφ, hφ⟩ :=
    phiCurv_jet_unif (I := I) (M := M) hDim gBase hΛ
  refine ⟨Capp * Aφ, mul_nonneg hCapp hAφ, ?_⟩
  intro g hEq hjet U
  exact happ g hEq hjet (phiMetCurvCoeff (I := I) g gBase g) U
    Aφ hAφ (hφ g hEq hjet)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
