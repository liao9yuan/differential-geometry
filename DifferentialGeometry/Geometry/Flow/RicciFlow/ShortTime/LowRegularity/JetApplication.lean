import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.H2VectorBundle

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Spectral (appCcRS appCcRS_sub_left appCcRS_sub_right)
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem app_cc_rs_sub
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ₁ W₁ -
        appCcRS (I := I) (M := M) g a b c Φ₂ W₂ =
      appCcRS (I := I) (M := M) g a b c (Φ₁ - Φ₂) W₁ +
        appCcRS (I := I) (M := M) g a b c Φ₂ (W₁ - W₂) := by
  simp only [appCcRS]
  rw [appCcRS_sub_left, appCcRS_sub_right]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem low_jet_sq_app_cc_rs_sub_le
    (g : SmoothRiemannianMetric I M) (m a b c : ℕ)
    (C Xd YT XU Yd : ℝ) (hC : 0 ≤ C)
    (ΦT ΦU : SmoothCcTensor g b c) (WT WU : SmoothCcTensor g a b)
    (happ : ∀ (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b),
      lowJetSq (I := I) (M := M) g m
          (appCcRS (I := I) (M := M) g a b c Φ W) ≤
        C * lowJetSq (I := I) (M := M) g m Φ *
          lowJetSq (I := I) (M := M) g m W)
    (hΦd : lowJetSq (I := I) (M := M) g m (ΦT - ΦU) ≤ Xd)
    (hWT : lowJetSq (I := I) (M := M) g m WT ≤ YT)
    (hΦU : lowJetSq (I := I) (M := M) g m ΦU ≤ XU)
    (hWd : lowJetSq (I := I) (M := M) g m (WT - WU) ≤ Yd) :
    lowJetSq (I := I) (M := M) g m
        (appCcRS (I := I) (M := M) g a b c ΦT WT -
          appCcRS (I := I) (M := M) g a b c ΦU WU) ≤
      2 * (C * Xd * YT + C * XU * Yd) := by
  rw [app_cc_rs_sub]
  refine (jetAdd (I := I) (M := M) g m _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · refine (happ _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hΦd hC) hWT
      (jetNn (I := I) (M := M) (m := m) g _)
      (mul_nonneg hC ((jetNn (I := I) (M := M) (m := m) g _).trans hΦd))
  · refine (happ _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hΦU hC) hWd
      (jetNn (I := I) (M := M) (m := m) g _)
      (mul_nonneg hC ((jetNn (I := I) (M := M) (m := m) g _).trans hΦU))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
