import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSFirstDerivativeBound

/-!
# Family-uniform first derivative bound for the Ricci--DeTurck RHS

This module packages chart Gram bounds through order three into one uniform
bound for the first spatial chart derivatives of the Ricci--DeTurck right-hand
side on active partition-of-unity chart supports.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Uniform metric equivalence and chart Gram bounds through order three give
one bound for every first spatial chart derivative of the Ricci--DeTurck RHS
on every active partition-of-unity chart support. -/
theorem chartRHSD_pou_bnd
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
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₂Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) gBase α a c)) (extChartAt I α b)| ≤ Q₂)
    (Q₃ : ℝ) (hQ₃_nn : 0 ≤ Q₃)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃)
    (hQ₃Base : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) gBase α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d i j : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α i j)
                (extChartAt I α b)| ≤ C := by
  classical
  let gAll : Option ι → SmoothRiemannianMetric I M := fun k => k.elim gBase gSeq
  have hequivAll : ∀ k : Option ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gAll k).inner b v v ∧
        (gAll k).inner b v v ≤ Λ * gBase.inner b v v := by
    intro k b v
    cases k with
    | none =>
        have hnonneg : 0 ≤ gBase.inner b v v := by
          rcases eq_or_ne v 0 with rfl | hv
          · simp
          · exact (gBase.pos b v hv).le
        have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
        constructor
        · simpa [gAll] using mul_le_mul_of_nonneg_right
            ((inv_le_one₀ hΛpos).2 hΛ) hnonneg
        · simpa [gAll] using mul_le_mul_of_nonneg_right hΛ hnonneg
    | some k => simpa [gAll] using hequiv k b v
  have hQ₁All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gAll k) α a c)
              (extChartAt I α b)| ≤ Q₁ := by
    intro α hα k b hb m a c
    cases k with
    | none => simpa [gAll] using hQ₁Base α hα b hb m a c
    | some k => simpa [gAll] using hQ₁ α hα k b hb m a c
  have hQ₂All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gAll k) α a c)) (extChartAt I α b)| ≤ Q₂ := by
    intro α hα k b hb d m a c
    cases k with
    | none => simpa [gAll] using hQ₂Base α hα b hb d m a c
    | some k => simpa [gAll] using hQ₂ α hα k b hb d m a c
  have hQ₃All : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : Option ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gAll k) α a c))) (extChartAt I α b)| ≤ Q₃ := by
    intro α hα k b hb e d m a c
    cases k with
    | none => simpa [gAll] using hQ₃Base α hα b hb e d m a c
    | some k => simpa [gAll] using hQ₃ α hα k b hb e d m a c
  obtain ⟨Mb, hMb, hMbAll⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
  obtain ⟨T, hT, hTAll⟩ :=
    DeTurckCoefficients.invGramD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ hQ₁_nn hQ₂_nn hQ₁All hQ₂All
  obtain ⟨CΓ, hCΓ, hΓAll⟩ :=
    DeTurckCoefficients.christoffel_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll Q₁ hQ₁_nn hQ₁All
  obtain ⟨CdΓ, hCdΓ, hdΓAll⟩ :=
    DeTurckCoefficients.christoffelD_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ hQ₁_nn hQ₁All Q₂ hQ₂_nn hQ₂All
  obtain ⟨Cd2Γ, hCd2Γ, hd2ΓAll⟩ :=
    DeTurckCoefficients.christD2_pou_bnd
      (I := I) (M := M) gBase gAll Λ hΛ hequivAll
      Q₁ Q₂ Q₃ hQ₁_nn hQ₂_nn hQ₃_nn hQ₁All hQ₂All hQ₃All
  let n : ℝ := Module.finrank ℝ E
  let D : ℝ := n ^ 2 * Mb ^ 2 * Q₁
  let P : ℝ := 2 * CΓ
  let R : ℝ := 2 * CdΓ
  let S : ℝ := 2 * Cd2Γ
  let V : ℝ := n ^ 2 * Mb * P
  let DV : ℝ := n ^ 2 * (D * P + Mb * R)
  let D2V : ℝ := n ^ 2 * (T * P + 2 * D * R + Mb * S)
  let RicD : ℝ := n * (2 * Cd2Γ + 4 * n * (CΓ * CdΓ))
  let LieD : ℝ := n * (3 * DV * Q₁ + V * Q₂ + 2 * Q₀ * D2V)
  let C : ℝ := 2 * RicD + LieD + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hDV : 0 ≤ DV := by dsimp [DV]; positivity
  have hD2V : 0 ≤ D2V := by dsimp [D2V]; positivity
  have hRicD : 0 ≤ RicD := by dsimp [RicD]; positivity
  have hLieD : 0 ≤ LieD := by dsimp [LieD]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro α hα k b hb d i j
  have hbBase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hbSource : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hbBase
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hbSource
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hbSource)
  have hMbG : ∀ a c : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ Mb := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    simpa [gAll] using hMbAll α hα (some k) b hb a c
  have hDG : ∀ m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartInvGramOnE (I := I) (gSeq k) α a c) (extChartAt I α b)| ≤ D := by
    intro m a c
    simpa [D, n] using DeTurckCoefficients.invGramD_abs_le
      (I := I) (M := M) (gSeq k) α hy hMb.le hMbG
      (hQ₁ α hα k b hb) m a c
  have hTG : ∀ e m a c : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartInvGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ T := by
    intro e m a c
    simpa [gAll] using hTAll α hα (some k) b hb e m a c
  have hΓG : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα (some k) b hb a c l
  have hΓBase : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ CΓ := by
    intro a c l
    simpa [gAll] using hΓAll α hα none b hb a c l
  have hdΓG : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro m a c l
    simpa [gAll] using hdΓAll α hα (some k) b hb m a c l
  have hdΓBase : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ CdΓ := by
    intro m a c l
    simpa [gAll] using hdΓAll α hα none b hb m a c l
  have hd2ΓG : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e m a c l
    simpa [gAll] using hd2ΓAll α hα (some k) b hb e m a c l
  have hd2ΓBase : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ Cd2Γ := by
    intro e m a c l
    simpa [gAll] using hd2ΓAll α hα none b hb e m a c l
  have hΓdiff : ∀ a c l : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) (gSeq k) α a c l (extChartAt I α b) -
        chartChristoffel (I := I) gBase α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CΓ + CΓ := add_le_add (hΓG a c l) (hΓBase a c l)
      _ = P := by dsimp [P]; ring
  have hdΓdiff : ∀ m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
          (chartChristoffel (I := I) (gSeq k) α a c l) (extChartAt I α b) -
        partialDeriv (E := E) m
          (chartChristoffel (I := I) gBase α a c l) (extChartAt I α b)| ≤ R := by
    intro m a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ CdΓ + CdΓ := add_le_add (hdΓG m a c l) (hdΓBase m a c l)
      _ = R := by dsimp [R]; ring
  have hd2Γdiff : ∀ e m a c l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
          (partialDeriv (E := E) m
            (chartChristoffel (I := I) (gSeq k) α a c l)) (extChartAt I α b) -
        partialDeriv (E := E) e
          (partialDeriv (E := E) m
            (chartChristoffel (I := I) gBase α a c l)) (extChartAt I α b)| ≤ S := by
    intro e m a c l
    calc
      |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ Cd2Γ + Cd2Γ := add_le_add (hd2ΓG e m a c l) (hd2ΓBase e m a c l)
      _ = S := by dsimp [S]; ring
  have hVF : ∀ l : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) (gSeq k) gBase α l (extChartAt I α b)| ≤ V := by
    intro l
    simpa [V, n] using DeTurckCoefficients.deTurckVF_abs_le
      (I := I) (M := M) (gSeq k) gBase α (extChartAt I α b) l hMb.le hMbG
      (fun a c => hΓdiff a c l)
  have hVFD : ∀ m l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) m
        (chartDeTurckVFComp (I := I) (gSeq k) gBase α l) (extChartAt I α b)| ≤ DV := by
    intro m l
    simpa [DV, n] using DeTurckCoefficients.deTurckVFD_abs_le
      (I := I) (M := M) (gSeq k) gBase α hy m l hD hMb.le
      (fun a c => hDG m a c) (fun a c => hΓdiff a c l) hMbG
      (fun a c => hdΓdiff m a c l)
  have hVFD2 : ∀ e m l : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) e
        (partialDeriv (E := E) m
          (chartDeTurckVFComp (I := I) (gSeq k) gBase α l)) (extChartAt I α b)| ≤ D2V := by
    intro e m l
    simpa [D2V, n] using DeTurckCoefficients.deTurckVFD2_le
      (I := I) (M := M) (gSeq k) gBase α hy e m l hMb.le hD hT
      hMbG hDG hTG (fun a c => hΓdiff a c l)
      (fun r a c => hdΓdiff r a c l) (fun q r a c => hd2Γdiff q r a c l)
  have hRicci :
      |partialDeriv (E := E) d
        (chartRicciTensor (I := I) (gSeq k) α i j) (extChartAt I α b)| ≤ RicD := by
    simpa [RicD, n] using DeTurckCoefficients.chartRicciD_abs_le
      (I := I) (M := M) (gSeq k) α hy d i j hCΓ hCdΓ hΓG hdΓG hd2ΓG
  have hLie :
      |partialDeriv (E := E) d
        (chartLieDeTurckComp (I := I) (gSeq k) gBase α i j) (extChartAt I α b)| ≤ LieD := by
    simpa [LieD, n] using DeTurckCoefficients.chartLieD_abs_le
      (I := I) (M := M) (gSeq k) gBase α hy d i j
      hQ₀_nn hQ₁_nn hV hDV (hQ₀ α hα k b hb) (hQ₁ α hα k b hb)
      (hQ₂ α hα k b hb) hVF hVFD hVFD2
  refine (DeTurckCoefficients.chartRHSD_abs_le
    (I := I) (M := M) gBase (gSeq k) α d i j hy hRicci hLie).trans ?_
  dsimp [C]
  linarith

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
