import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz

/-!
# Family-uniform Ricci--DeTurck right-hand-side bound

This module combines the family-uniform Ricci and Lie-summand chart estimates.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For a fixed DeTurck background, a metric-equivalent family with uniform
chart Gram bounds through order two has one full Ricci--DeTurck RHS Lipschitz
constant on every active partition-of-unity chart support. -/
theorem chartRHS_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₀ : ℝ) (hQ₀_nn : 0 ≤ Q₀)
    (hQ₀ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ a c : Fin (Module.finrank ℝ E),
          |chartGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ Q₀)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₁Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) gBase α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank ℝ E),
            |chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j (extChartAt I α b) -
              chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j (extChartAt I α b)| ≤
                C * chartMetricJet2DiffSup (I := I) (M := M)
                  (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨Cric, hCric_pos, hCric⟩ :=
    DeTurckCoefficients.chartRicci_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₁ hQ₁_nn hQ₁ Q₂ hQ₂_nn hQ₂
  obtain ⟨Clie, hClie_pos, hClie⟩ :=
    DeTurckCoefficients.chartLie_pou_lip
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
      Q₀ hQ₀_nn hQ₀ Q₁ hQ₁_nn hQ₁ hQ₁Base Q₂ hQ₂_nn hQ₂ hQ₂Base
  refine ⟨2 * Cric + Clie, by positivity, ?_⟩
  intro α hα k₁ k₂ b hb i j
  have hsplit :
      chartDeTurckRHSComp (I := I) gBase (gSeq k₁) α i j (extChartAt I α b) -
          chartDeTurckRHSComp (I := I) gBase (gSeq k₂) α i j (extChartAt I α b) =
        (-2 : ℝ) *
            (chartRicciTensor (I := I) (gSeq k₁) α i j (extChartAt I α b) -
              chartRicciTensor (I := I) (gSeq k₂) α i j (extChartAt I α b)) +
          (chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j (extChartAt I α b) -
            chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j (extChartAt I α b)) := by
    rw [chartDeTurckRHSComp_def, chartDeTurckRHSComp_def]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hric := hCric α hα k₁ k₂ b hb i j
  have hlie := hClie α hα k₁ k₂ b hb i j
  calc
    |(-2 : ℝ) *
          (chartRicciTensor (I := I) (gSeq k₁) α i j (extChartAt I α b) -
            chartRicciTensor (I := I) (gSeq k₂) α i j (extChartAt I α b))| +
        |chartLieDeTurckComp (I := I) (gSeq k₁) gBase α i j (extChartAt I α b) -
          chartLieDeTurckComp (I := I) (gSeq k₂) gBase α i j (extChartAt I α b)|
      ≤ 2 * (Cric * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b)) +
        Clie * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
        apply add_le_add
        · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
          have htwo : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left hric htwo
        · exact hlie
    _ = (2 * Cric + Clie) * chartMetricJet2DiffSup (I := I) (M := M)
          (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
