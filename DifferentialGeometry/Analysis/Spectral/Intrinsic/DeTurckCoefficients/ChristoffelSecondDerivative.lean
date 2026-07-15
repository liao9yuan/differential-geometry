import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.InverseGramSecondDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.PartialDerivIteratedFDerivOrderBridge
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin

/-!
# Second chart derivatives of Christoffel symbols

This file differentiates the first-partial Christoffel formula and gives
entrywise and partition-of-unity-family bounds from chart Gram derivatives
through order three.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The second derivative of the metric bracket in two chart directions. -/
noncomputable def gramBracketDeriv2 (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))) y +
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) y -
    partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))) y

omit [NeZero (Module.finrank ℝ E)] in
/-- Uniform third-partial Gram entry bounds control the twice-differentiated
metric bracket. -/
theorem gramBracketD2_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) (y : E) {Q : ℝ}
    (hQ : ∀ d m c a b, |partialDeriv (E := E) d
      (partialDeriv (E := E) m
        (partialDeriv (E := E) c (chartGramOnE (I := I) g α a b))) y| ≤ Q)
    (d m i j l : Fin (Module.finrank ℝ E)) :
    |gramBracketDeriv2 (I := I) g α d m i j l y| ≤ 3 * Q := by
  unfold gramBracketDeriv2
  calc
    |_ + _ - _| ≤ |_| + |_| + |_| := by
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Q + Q + Q := add_le_add
      (add_le_add (hQ d m i l j) (hQ d m j l i)) (hQ d m l i j)
    _ = 3 * Q := by ring

private lemma invD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α a b)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

private lemma inv_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y := by
  have h := (chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

private lemma gramD1_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m (chartGramOnE (I := I) g α a b)) y := by
  have h := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
  exact (h.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

private lemma gramD2_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartGramOnE (I := I) g α a b))) y := by
  have h1 := partialDeriv_contDiffOn_of_isOpen isOpen_interior
    ((chartGramOnE_contDiffOn (I := I) g α a b).mono interior_subset) m
  have h2 := partialDeriv_contDiffOn_of_isOpen isOpen_interior h1 d
  exact (h2.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

private lemma bracket_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (gramBracket (I := I) g α i j l) y := by
  exact ((gramD1_diffAt (I := I) g α i l j hy).add
    (gramD1_diffAt (I := I) g α j l i hy)).sub
      (gramD1_diffAt (I := I) g α l i j hy)

private lemma bracketD_diffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (gramBracketDeriv (I := I) g α m i j l) y := by
  exact ((gramD2_diffAt (I := I) g α m i l j hy).add
    (gramD2_diffAt (I := I) g α m j l i hy)).sub
      (gramD2_diffAt (I := I) g α m l i j hy)

/-- Differentiating `gramBracketDeriv` produces `gramBracketDeriv2`. -/
lemma partial_gramBracketD
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d (gramBracketDeriv (I := I) g α m i j l) y =
      gramBracketDeriv2 (I := I) g α d m i j l y := by
  have h1 := gramD2_diffAt (I := I) g α m i l j hy
  have h2 := gramD2_diffAt (I := I) g α m j l i hy
  have h3 := gramD2_diffAt (I := I) g α m l i j hy
  unfold gramBracketDeriv gramBracketDeriv2
  rw [partialDeriv_sub (i := d)
      (fun z => partialDeriv (E := E) m
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) z +
        partialDeriv (E := E) m
          (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i)) z)
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)))
      (h1.add h2) h3,
    partialDeriv_add (i := d)
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)))
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))) h1 h2]

/-- The second chart partial of a Christoffel symbol is the four-term
Leibniz expansion of its inverse-Gram/bracket formula. -/
theorem partial2_christ_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (d m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k)) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y) := by
  classical
  let s : Set E := interior (extChartAt I α).target
  have hs_open : IsOpen s := isOpen_interior
  have hEqOn : Set.EqOn
      (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k))
      (fun z => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
            gramBracket (I := I) g α i j l z +
          chartInvGramOnE (I := I) g α k l z *
            gramBracketDeriv (I := I) g α m i j l z)) s := by
    intro z hz
    exact partialDeriv_chartChristoffel_eq (I := I) g α m i j k hz
  have hCongr := partialDerivWithin_congr_of_eqOn_of_mem
    (E := E) (i := d) hEqOn hy
  rw [partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy,
    partialDerivWithin_eq_partialDeriv_of_isOpen hs_open hy] at hCongr
  rw [hCongr]
  have hSummand : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
          gramBracket (I := I) g α i j l z +
        chartInvGramOnE (I := I) g α k l z *
          gramBracketDeriv (I := I) g α m i j l z) y := by
    intro l
    exact ((invD_diffAt (I := I) g α m k l hy).mul
      (bracket_diffAt (I := I) g α i j l hy)).add
        ((inv_diffAt (I := I) g α k l hy).mul
          (bracketD_diffAt (I := I) g α m i j l hy))
  rw [partialDeriv_const_mul (i := d) (1 / 2 : ℝ) _
    (DifferentiableAt.fun_sum fun l _ => hSummand l)]
  congr 1
  rw [partialDeriv_sum (i := d) Finset.univ
    (fun l z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
        gramBracket (I := I) g α i j l z +
      chartInvGramOnE (I := I) g α k l z *
        gramBracketDeriv (I := I) g α m i j l z)
    (fun l _ => hSummand l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hInvD := invD_diffAt (I := I) g α m k l hy
  have hBracket := bracket_diffAt (I := I) g α i j l hy
  have hInv := inv_diffAt (I := I) g α k l hy
  have hBracketD := bracketD_diffAt (I := I) g α m i j l hy
  rw [partialDeriv_add (i := d)
      (fun z => partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) z *
        gramBracket (I := I) g α i j l z)
      (fun z => chartInvGramOnE (I := I) g α k l z *
        gramBracketDeriv (I := I) g α m i j l z)
      (hInvD.mul hBracket) (hInv.mul hBracketD),
    partialDeriv_mul (i := d)
      (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l))
      (gramBracket (I := I) g α i j l) hInvD hBracket,
    partialDeriv_mul (i := d) (chartInvGramOnE (I := I) g α k l)
      (gramBracketDeriv (I := I) g α m i j l) hInv hBracketD,
    partialDeriv_gramBracket_eq (I := I) g α d i j l hy,
    partial_gramBracketD (I := I) g α d m i j l hy]
  ring

/-- Entrywise bounds for inverse-Gram derivatives and metric brackets control
a second chart partial of a Christoffel symbol. -/
theorem christD2_abs_le
    (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d m i j k : Fin (Module.finrank ℝ E))
    {M_b D T P R U : ℝ} (hMb_nn : 0 ≤ M_b) (hD_nn : 0 ≤ D) (hT_nn : 0 ≤ T)
    (hMb : ∀ l, |chartInvGramOnE (I := I) g α k l y| ≤ M_b)
    (hD : ∀ e l, |partialDeriv (E := E) e
      (chartInvGramOnE (I := I) g α k l) y| ≤ D)
    (hT : ∀ e r l, |partialDeriv (E := E) e
      (partialDeriv (E := E) r (chartInvGramOnE (I := I) g α k l)) y| ≤ T)
    (hP : ∀ l, |gramBracket (I := I) g α i j l y| ≤ P)
    (hR : ∀ e l, |gramBracketDeriv (I := I) g α e i j l y| ≤ R)
    (hU : ∀ e r l, |gramBracketDeriv2 (I := I) g α e r i j l y| ≤ U) :
    |partialDeriv (E := E) d
      (partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k)) y| ≤
        (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
          (T * P + 2 * D * R + M_b * U) := by
  classical
  rw [partial2_christ_eq (I := I) g α d m i j k hy, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsum :
      |∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y)| ≤
        ∑ _l : Fin (Module.finrank ℝ E), (T * P + 2 * D * R + M_b * U) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    calc
      |_ + _ + _ + _| ≤ ((|_| + |_|) + |_|) + |_| := by
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ ((T * P + D * R) + D * R) + M_b * U := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (by rw [abs_mul]; exact mul_le_mul (hT d m l) (hP l) (abs_nonneg _) hT_nn)
              (by rw [abs_mul]; exact mul_le_mul (hD m l) (hR d l) (abs_nonneg _) hD_nn))
            (by rw [abs_mul]; exact mul_le_mul (hD d l) (hR m l) (abs_nonneg _) hD_nn))
          (by rw [abs_mul]; exact mul_le_mul (hMb l) (hU d m l) (abs_nonneg _) hMb_nn)
      _ = T * P + 2 * D * R + M_b * U := by ring
  calc
    (1 / 2 : ℝ) * |∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l)) y *
            gramBracket (I := I) g α i j l y +
          partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α d i j l y +
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
            gramBracketDeriv (I := I) g α m i j l y +
          chartInvGramOnE (I := I) g α k l y *
            gramBracketDeriv2 (I := I) g α d m i j l y)|
      ≤ (1 / 2 : ℝ) * ∑ _l : Fin (Module.finrank ℝ E),
          (T * P + 2 * D * R + M_b * U) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
          (T * P + 2 * D * R + M_b * U) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Uniform ellipticity and chart Gram bounds through order three give one
second-Christoffel-partial bound on all active POU chart supports. -/
theorem christD2_pou_bnd
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ Q₂ Q₃ : ℝ) (hQ₁_nn : 0 ≤ Q₁) (hQ₂_nn : 0 ≤ Q₂) (hQ₃_nn : 0 ≤ Q₃)
    (hQ₁ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (hQ₂ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ Q₂)
    (hQ₃ : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ e d m a c : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) e
            (partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α a c))) (extChartAt I α b)| ≤ Q₃) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d m i j l : Fin (Module.finrank ℝ E),
            |partialDeriv (E := E) d
              (partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k) α i j l)) (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let T : ℝ := 2 * (Module.finrank ℝ E : ℝ) ^ 4 * (M_b ^ 3 * Q₁ ^ 2) +
    (Module.finrank ℝ E : ℝ) ^ 2 * (M_b ^ 2 * Q₂)
  let P : ℝ := 3 * Q₁
  let R : ℝ := 3 * Q₂
  let U : ℝ := 3 * Q₃
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (T * P + 2 * D * R + M_b * U)
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hT_nn : 0 ≤ T := by dsimp [T]; positivity
  have hC_nn : 0 ≤ C := by dsimp [C, T, D, P, R, U]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb d m i j l
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMbOnE : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k) α a c (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb a c
  have hDOnE : ∀ e a c,
      |partialDeriv (E := E) e
        (chartInvGramOnE (I := I) (gSeq k) α a c) (extChartAt I α b)| ≤ D := by
    intro e a c
    exact invGramD_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le hMbOnE
      (hQ₁ α hα k b hb) e a c
  have hTOnE : ∀ e r a c,
      |partialDeriv (E := E) e
        (partialDeriv (E := E) r
          (chartInvGramOnE (I := I) (gSeq k) α a c)) (extChartAt I α b)| ≤ T := by
    intro e r a c
    exact invGramD2_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le hQ₁_nn
      hMbOnE (hQ₁ α hα k b hb) (hQ₂ α hα k b hb) e r a c
  have hPOnE : ∀ r,
      |gramBracket (I := I) (gSeq k) α i j r (extChartAt I α b)| ≤ P := by
    intro r
    exact gramBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₁ α hα k b hb) i j r
  have hROnE : ∀ e r,
      |gramBracketDeriv (I := I) (gSeq k) α e i j r (extChartAt I α b)| ≤ R := by
    intro e r
    exact gramBracketD_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₂ α hα k b hb) e i j r
  have hUOnE : ∀ e r a,
      |gramBracketDeriv2 (I := I) (gSeq k) α e r i j a (extChartAt I α b)| ≤ U := by
    intro e r a
    exact gramBracketD2_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (hQ₃ α hα k b hb) e r i j a
  exact christD2_abs_le (I := I) (M := M) (gSeq k) α hy d m i j l hM_b.le hD_nn hT_nn
    (fun a => hMbOnE l a) (fun e a => hDOnE e l a) (fun e r a => hTOnE e r l a)
    hPOnE hROnE hUOnE

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
