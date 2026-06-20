import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

structure HasChartJetLipBall
    (𝒢 : Set (SmoothRiemannianMetric I M)) (α : M) (K : Set E)
    (F : SmoothRiemannianMetric I M → E → ℝ) (d : ℕ) (N_max : ℕ) : Prop where
  
  contDiff : ∀ g ∈ 𝒢, ContDiffOn ℝ ∞ (F g) (interior (extChartAt I α).target)
  
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ 𝒢, ∀ y ∈ K, ∀ m : ℕ, m ≤ N_max →
    ‖iteratedFDerivWithin ℝ m (F g) (interior (extChartAt I α).target) y‖ ≤ B
  
  lip : ∀ N : ℕ, N ≤ N_max → ∃ C : ℝ, 0 < C ∧ ∀ g₁ ∈ 𝒢, ∀ g₂ ∈ 𝒢, ∀ y ∈ K,
    ‖iteratedFDerivWithin ℝ N (fun z => F g₁ z - F g₂ z)
        (interior (extChartAt I α).target) y‖ ≤
      C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α
        (interior (extChartAt I α).target) y

theorem HasChartJetLipBall.congr
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    {F F' : SmoothRiemannianMetric I M → E → ℝ} {d N_max : ℕ}
    (hF : HasChartJetLipBall 𝒢 α K F d N_max)
    (hFF' : ∀ g, F g = F' g) :
    HasChartJetLipBall 𝒢 α K F' d N_max := by
  have hrw : F' = F := by funext g; exact (hFF' g).symm
  rw [hrw]; exact hF

theorem HasChartJetLipBall.of_le
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d d' N_max : ℕ} (hd : d ≤ d')
    (hF : HasChartJetLipBall 𝒢 α K F d N_max) :
    HasChartJetLipBall 𝒢 α K F d' N_max := by
  refine ⟨hF.contDiff, hF.bound, fun N hN => ?_⟩
  obtain ⟨C, hC_pos, hC⟩ := hF.lip N hN
  refine ⟨C, hC_pos, fun g₁ hg₁ g₂ hg₂ y hy => (hC g₁ hg₁ g₂ hg₂ y hy).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC_pos.le
  exact chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α _ y

theorem HasChartJetLipBall.of_le_Nmax
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d N_max N_max' : ℕ} (hN : N_max' ≤ N_max)
    (hF : HasChartJetLipBall 𝒢 α K F d N_max) :
    HasChartJetLipBall 𝒢 α K F d N_max' := by
  refine ⟨hF.contDiff, ?_, fun N hN' => hF.lip N (hN'.trans hN)⟩
  obtain ⟨B, hB_nn, hB⟩ := hF.bound
  exact ⟨B, hB_nn, fun g hg y hy m hm => hB g hg y hy m (hm.trans hN)⟩

theorem HasChartJetLipBall.seminorm_le
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d N_max : ℕ}
    (hF : HasChartJetLipBall 𝒢 α K F d N_max) (N : ℕ) (hN : N ≤ N_max) :
    ∃ C : ℝ, 0 < C ∧ ∀ g₁ ∈ 𝒢, ∀ g₂ ∈ 𝒢, ∀ y ∈ K,
      iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z)
          (interior (extChartAt I α).target) y ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hper : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧ (l ≤ N → ∀ g₁ ∈ 𝒢, ∀ g₂ ∈ 𝒢, ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ l (fun z => F g₁ z - F g₂ z) s y‖ ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (l + d) g₁ g₂ α s y) := by
    intro l
    by_cases hl : l ≤ N
    · obtain ⟨C, hC_pos, hC⟩ := hF.lip l (hl.trans hN)
      exact ⟨C, hC_pos, fun _ => hC⟩
    · exact ⟨1, one_pos, fun h => absurd h hl⟩
  choose Cl hCl_pos hCl using hper
  refine ⟨∑ l ∈ Finset.range (N + 1), Cl l, ?_, fun g₁ hg₁ g₂ hg₂ y hy => ?_⟩
  · refine Finset.sum_pos (fun l _ => hCl_pos l) ⟨0, Finset.mem_range.mpr (by omega)⟩
  · have hsem_nn : 0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α s y
    unfold iteratedFDerivSeminorm
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlN : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    refine (hCl l hlN g₁ hg₁ g₂ hg₂ y hy).trans ?_
    have hmono : chartGramJetDiffSeminormSum (I := I) (M := M) (l + d) g₁ g₂ α s y ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α s y
    exact mul_le_mul_of_nonneg_left hmono (hCl_pos l).le

theorem HasChartJetLipBall.const_smul
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {d N_max : ℕ}
    (hF : HasChartJetLipBall 𝒢 α K F d N_max) (c : ℝ) :
    HasChartJetLipBall 𝒢 α K (fun g => fun z => c * F g z) d N_max := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  have hsmul : ∀ (g : SmoothRiemannianMetric I M), g ∈ 𝒢 → ∀ (m : ℕ) {y : E}, y ∈ s →
      iteratedFDerivWithin ℝ m (fun z => c * F g z) s y =
        c • iteratedFDerivWithin ℝ m (F g) s y := by
    intro g hg m y hy
    have hfun : (fun z => c * F g z) = (c • F g) := by funext z; rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact iteratedFDerivWithin_const_smul_apply
      (((hF.contDiff g hg).contDiffWithinAt hy).of_le (by exact_mod_cast le_top))
      hs_open.uniqueDiffOn hy
  refine ⟨fun g hg => contDiffOn_const.mul (hF.contDiff g hg), ?_, fun N hN => ?_⟩
  · obtain ⟨B, hB_nn, hB⟩ := hF.bound
    refine ⟨|c| * B, mul_nonneg (abs_nonneg _) hB_nn, fun g hg y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    rw [hsmul g hg m hyS]
    refine (norm_smul_le c _).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB g hg y hy m hm) (abs_nonneg _)
  · obtain ⟨C, hC_pos, hC⟩ := hF.lip N hN
    refine ⟨|c| * C + 1, by positivity, fun g₁ hg₁ g₂ hg₂ y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hdiff : (fun z => c * F g₁ z - c * F g₂ z) =
        (c • (fun w => F g₁ w - F g₂ w)) := by
      funext z; rw [Pi.smul_apply, smul_eq_mul, mul_sub]
    have hsem_nn : 0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α s y
    rw [hdiff]
    rw [iteratedFDerivWithin_const_smul_apply
      ((((hF.contDiff g₁ hg₁).sub (hF.contDiff g₂ hg₂)).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS]
    refine (norm_smul_le c _).trans ?_
    rw [Real.norm_eq_abs]
    calc |c| * ‖iteratedFDerivWithin ℝ N (fun w => F g₁ w - F g₂ w) s y‖
        ≤ |c| * (C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (hC g₁ hg₁ g₂ hg₂ y hy) (abs_nonneg _)
      _ = (|c| * C) * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y := by ring
      _ ≤ (|c| * C + 1) * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

theorem HasChartJetLipBall.add
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F G : SmoothRiemannianMetric I M → E → ℝ} {dF dG NF NG : ℕ}
    (hF : HasChartJetLipBall 𝒢 α K F dF NF) (hG : HasChartJetLipBall 𝒢 α K G dG NG) :
    HasChartJetLipBall 𝒢 α K (fun g => fun z => F g z + G g z) (max dF dG) (min NF NG) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  have hF' := hF.of_le (le_max_left dF dG)
  have hG' := hG.of_le (le_max_right dF dG)
  refine ⟨fun g hg => (hF.contDiff g hg).add (hG.contDiff g hg), ?_, fun N hN => ?_⟩
  · obtain ⟨BF, hBF_nn, hBF⟩ := hF.bound
    obtain ⟨BG, hBG_nn, hBG⟩ := hG.bound
    refine ⟨BF + BG, by linarith, fun g hg y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hadd : iteratedFDerivWithin ℝ m (fun z => F g z + G g z) s y =
        iteratedFDerivWithin ℝ m (F g) s y + iteratedFDerivWithin ℝ m (G g) s y :=
      iteratedFDerivWithin_add_apply (((hF.contDiff g hg).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) (((hG.contDiff g hg).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add (hBF g hg y hy m (hm.trans (min_le_left _ _)))
      (hBG g hg y hy m (hm.trans (min_le_right _ _))))
  · obtain ⟨CF, hCF_pos, hCF⟩ := hF'.lip N (hN.trans (min_le_left _ _))
    obtain ⟨CG, hCG_pos, hCG⟩ := hG'.lip N (hN.trans (min_le_right _ _))
    refine ⟨CF + CG, by linarith, fun g₁ hg₁ g₂ hg₂ y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hdiff : (fun z => (F g₁ z + G g₁ z) - (F g₂ z + G g₂ z)) =
        (fun z => (fun w => F g₁ w - F g₂ w) z + (fun w => G g₁ w - G g₂ w) z) := by
      funext z; ring
    rw [hdiff]
    have hadd : iteratedFDerivWithin ℝ N
          (fun z => (fun w => F g₁ w - F g₂ w) z + (fun w => G g₁ w - G g₂ w) z) s y =
        iteratedFDerivWithin ℝ N (fun w => F g₁ w - F g₂ w) s y +
          iteratedFDerivWithin ℝ N (fun w => G g₁ w - G g₂ w) s y :=
      iteratedFDerivWithin_add_apply
        ((((hF.contDiff g₁ hg₁).sub (hF.contDiff g₂ hg₂)).contDiffWithinAt hyS).of_le
          (by exact_mod_cast le_top))
        ((((hG.contDiff g₁ hg₁).sub (hG.contDiff g₂ hg₂)).contDiffWithinAt hyS).of_le
          (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS
    rw [hadd]
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (hCF g₁ hg₁ g₂ hg₂ y hy) (hCG g₁ hg₁ g₂ hg₂ y hy)).trans ?_
    rw [← add_mul]

theorem HasChartJetLipBall.mul
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F G : SmoothRiemannianMetric I M → E → ℝ} {dF dG NF NG : ℕ}
    (hF : HasChartJetLipBall 𝒢 α K F dF NF) (hG : HasChartJetLipBall 𝒢 α K G dG NG) :
    HasChartJetLipBall 𝒢 α K (fun g => fun z => F g z * G g z) (max dF dG) (min NF NG) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  obtain ⟨BF, hBF_nn, hBF⟩ := hF.bound
  obtain ⟨BG, hBG_nn, hBG⟩ := hG.bound
  refine ⟨fun g hg => (hF.contDiff g hg).mul (hG.contDiff g hg), ?_, fun N hN => ?_⟩
  · refine ⟨2 ^ (min NF NG) * (BF * BG), by positivity, fun g hg y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    refine (norm_iteratedFDerivWithin_mul_le (hF.contDiff g hg) (hG.contDiff g hg)
      hs_open.uniqueDiffOn hyS (by exact_mod_cast le_top)).trans ?_
    refine (Finset.sum_le_sum (g := fun k => (m.choose k : ℝ) * BF * BG)
      (fun k hk => ?_)).trans ?_
    · have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      refine mul_le_mul (mul_le_mul_of_nonneg_left
        (hBF g hg y hy k ((hkm.trans hm).trans (min_le_left _ _))) (by positivity))
        (hBG g hg y hy (m - k) (((Nat.sub_le m k).trans hm).trans (min_le_right _ _)))
        (norm_nonneg _) ?_
      exact mul_nonneg (by positivity) hBF_nn
    · rw [← Finset.sum_mul]
      have hsum : (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * BF) = 2 ^ m * BF := by
        rw [← Finset.sum_mul]
        congr 1
        calc (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ))
            = ((∑ k ∈ Finset.range (m + 1), m.choose k : ℕ) : ℝ) := by push_cast; rfl
          _ = ((2 ^ m : ℕ) : ℝ) := by rw [Nat.sum_range_choose]
          _ = 2 ^ m := by push_cast; ring
      rw [hsum]
      have h2m : (2 : ℝ) ^ m ≤ 2 ^ (min NF NG) := pow_le_pow_right₀ (by norm_num) hm
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right h2m (mul_nonneg hBF_nn hBG_nn)
  · set B : ℝ := max BF BG with hB_def
    have hB_nn : 0 ≤ B := le_max_of_le_left hBF_nn
    obtain ⟨CF, hCF_pos, hCF⟩ := hF.seminorm_le N (hN.trans (min_le_left _ _))
    obtain ⟨CG, hCG_pos, hCG⟩ := hG.seminorm_le N (hN.trans (min_le_right _ _))
    refine ⟨2 ^ N * B * (CF + CG) + 1, by positivity, fun g₁ hg₁ g₂ hg₂ y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hbnd := norm_iteratedFDerivWithin_two_prod_sub_le (s := s) hs_open
      (hF.contDiff g₁ hg₁) (hG.contDiff g₁ hg₁) (hF.contDiff g₂ hg₂) (hG.contDiff g₂ hg₂)
      hKsub hB_nn N
      (fun y' hy' m hm => le_trans
        (hBG g₁ hg₁ y' hy' m ((hm.trans hN).trans (min_le_right _ _))) (le_max_right _ _))
      (fun y' hy' m hm => le_trans
        (hBF g₂ hg₂ y' hy' m ((hm.trans hN).trans (min_le_left _ _))) (le_max_left _ _))
      hy
    refine hbnd.trans ?_
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y
    have hF_le : iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z) s y ≤
        CF * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
      refine (hCF g₁ hg₁ g₂ hg₂ y hy).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCF_pos.le
      exact chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α s y
    have hG_le : iteratedFDerivSeminorm N (fun z => G g₁ z - G g₂ z) s y ≤
        CG * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
      refine (hCG g₁ hg₁ g₂ hg₂ y hy).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCG_pos.le
      exact chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α s y
    calc 2 ^ N * B *
          (iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z) s y +
            iteratedFDerivSeminorm N (fun z => G g₁ z - G g₂ z) s y)
        ≤ 2 ^ N * B *
            (CF * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y +
              CG * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (add_le_add hF_le hG_le) (by positivity)
      _ = (2 ^ N * B * (CF + CG)) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by ring
      _ ≤ (2 ^ N * B * (CF + CG) + 1) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

theorem HasChartJetLipBall.partialDeriv
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {d N_max : ℕ} (hNmax : 1 ≤ N_max)
    (hF : HasChartJetLipBall 𝒢 α K F d N_max) (i : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall 𝒢 α K
      (fun g => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g))
      (d + 1) (N_max - 1) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  obtain ⟨B, hB_nn, hB⟩ := hF.bound
  refine ⟨fun g hg => partialDeriv_contDiffOn_of_isOpen hs_open (hF.contDiff g hg) i,
    ?_, fun N hN => ?_⟩
  · refine ⟨‖(chartModelBasis E) i‖ * B,
      mul_nonneg (norm_nonneg _) hB_nn, fun g hg y hy m hm => ?_⟩
    have hm1 : m + 1 ≤ N_max := by omega
    have hyS : y ∈ s := hKsub hy
    refine (norm_iteratedFDerivWithin_partialDeriv_le hs_open (hF.contDiff g hg) i m hyS).trans ?_
    exact mul_le_mul_of_nonneg_left (hB g hg y hy (m + 1) hm1) (norm_nonneg _)
  · obtain ⟨C, hC_pos, hC⟩ := hF.lip (N + 1) (by omega)
    refine ⟨‖(chartModelBasis E) i‖ * C + 1, by positivity, fun g₁ hg₁ g₂ hg₂ y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hEqOn : EqOn
        (fun z => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g₁) z -
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g₂) z)
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
          (fun z => F g₁ z - F g₂ z)) s :=
      partialDeriv_sub_eqOn hs_open (hF.contDiff g₁ hg₁) (hF.contDiff g₂ hg₂) i
    rw [iteratedFDerivWithin_congr hEqOn hyS N]
    refine (norm_iteratedFDerivWithin_partialDeriv_le hs_open
      ((hF.contDiff g₁ hg₁).sub (hF.contDiff g₂ hg₂)) i N hyS).trans ?_
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y
    have hN1d : N + 1 + d = N + (d + 1) := by omega
    calc ‖(chartModelBasis E) i‖ *
            ‖iteratedFDerivWithin ℝ (N + 1) (fun z => F g₁ z - F g₂ z) s y‖
        ≤ ‖(chartModelBasis E) i‖ *
            (C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 1 + d) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (hC g₁ hg₁ g₂ hg₂ y hy) (norm_nonneg _)
      _ = (‖(chartModelBasis E) i‖ * C) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y := by
          rw [hN1d]; ring
      _ ≤ (‖(chartModelBasis E) i‖ * C + 1) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

theorem hasChartJetLipBall_const
    (𝒢 : Set (SmoothRiemannianMetric I M)) (α : M) {N_max : ℕ}
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {f₀ : E → ℝ}
    (hf₀ : ContDiffOn ℝ ∞ f₀ (interior (extChartAt I α).target))
    (hFconst : ∀ g, F g = f₀) :
    HasChartJetLipBall 𝒢 α K F 0 N_max := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g _ => by rw [hFconst g]; exact hf₀, ?_, fun N hN => ?_⟩
  · obtain ⟨B, hB_nn, hB⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open hf₀ hK hKsub N_max
    refine ⟨B, hB_nn, fun g _ y hy m hm => ?_⟩
    rw [hFconst g]
    exact hB y hy m hm
  · refine ⟨1, one_pos, fun g₁ _ g₂ _ y hy => ?_⟩
    have hzero : (fun z => F g₁ z - F g₂ z) = (fun _ : E => (0 : ℝ)) := by
      funext z; rw [hFconst g₁, hFconst g₂, sub_self]
    rw [hzero, iteratedFDerivWithin_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg one_pos.le
      (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + 0) g₁ g₂ α s y)

theorem HasChartJetLipBall.sum
    {𝒢 : Set (SmoothRiemannianMetric I M)} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {ι : Type*} (u : Finset ι)
    {F : ι → SmoothRiemannianMetric I M → E → ℝ} {d N_max : ℕ}
    (hF : ∀ j ∈ u, HasChartJetLipBall 𝒢 α K (F j) d N_max) :
    HasChartJetLipBall 𝒢 α K (fun g => fun z => ∑ j ∈ u, F j g z) d N_max := by
  classical
  induction u using Finset.induction with
  | empty =>
    refine ⟨fun g _ => by simpa using (contDiffOn_const (c := (0 : ℝ))),
      ⟨0, le_refl 0, fun g _ y hy m hm => ?_⟩,
      fun N hN => ⟨1, one_pos, fun g₁ _ g₂ _ y hy => ?_⟩⟩
    · simp only [Finset.sum_empty]
      rw [show (fun _ : E => (0 : ℝ)) = (fun z => (0 : ℝ)) from rfl,
        iteratedFDerivWithin_fun_zero]; simp
    · simp only [Finset.sum_empty, sub_self]
      rw [iteratedFDerivWithin_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg one_pos.le
        (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α _ y)
  | insert a u ha IH =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hF
    have hhead := hF.1
    have hIH := IH hF.2
    have hsumeq : (fun g => fun z => ∑ j ∈ insert a u, F j g z) =
        (fun g => fun z => F a g z + (∑ j ∈ u, F j g z)) := by
      funext g z; rw [Finset.sum_insert ha]
    rw [hsumeq]
    have := (hhead.add (G := fun g => fun z => ∑ j ∈ u, F j g z) hKsub hIH)
    simpa only [max_self, min_self] using this

def realizedFibreSmallBall (g₀ : SmoothRiemannianMetric I M) (R : ℝ) (jmax : ℕ) :
    Set (SmoothRiemannianMetric I M) :=
  {g | ∃ (T : SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
      g = tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ ∧
        ∀ j : ℕ, j ≤ jmax → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R}

theorem tensorSectionRealizeMetric_mem_realizedFibreSmallBall
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ}
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTball : ∀ j : ℕ, j ≤ jmax → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) :
    tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ ∈
      realizedFibreSmallBall (I := I) (M := M) g₀ R jmax :=
  ⟨T, δ, hδ_lt, hδ, rfl, hTball⟩

theorem hasChartJetLipBall_chartGramOnE
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (a b : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => chartGramOnE (I := I) g α a b) 0 jmax := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  refine ⟨fun g _ => chartGramOnE_contDiffOn_int (I := I) g α a b, ?_, fun N _ => ?_⟩
  · sorry
  · refine ⟨1, one_pos, fun g₁ _ g₂ _ y _ => ?_⟩
    rw [one_mul, Nat.add_zero]
    have hNle : ‖iteratedFDerivWithin ℝ N
        (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y‖ ≤
        iteratedFDerivSeminorm N
          (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y :=
      norm_iteratedFDerivWithin_le_seminorm (le_refl N) _ s y
    refine hNle.trans ?_
    have hinner : iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y ≤
        ∑ b' : Fin (Module.finrank ℝ E), iteratedFDerivSeminorm N
          (fun z => chartGramOnE (I := I) g₁ α a b' z - chartGramOnE (I := I) g₂ α a b' z) s y :=
      Finset.single_le_sum
        (f := fun b' => iteratedFDerivSeminorm N
          (fun z => chartGramOnE (I := I) g₁ α a b' z - chartGramOnE (I := I) g₂ α a b' z) s y)
        (fun b' _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    refine hinner.trans ?_
    unfold chartGramJetDiffSeminormSum
    exact Finset.single_le_sum
      (f := fun a' => ∑ b' : Fin (Module.finrank ℝ E), iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a' b' z - chartGramOnE (I := I) g₂ α a' b' z) s y)
      (fun a' _ => Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)

theorem hasChartJetLipBall_chartInvGramOnE
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (k l : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => chartInvGramOnE (I := I) g α k l) 0 jmax := by
  classical
  refine ⟨fun g _ => chartInvGramOnE_contDiffOn_int (I := I) g α k l, ?_, ?_⟩
  · sorry
  · sorry

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_gramBracket
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 1 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => gramBracket (I := I) g α i j l) 1 (jmax - 1) := by
  have hbr : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => fun z =>
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
            (chartGramOnE (I := I) g α l j) z +
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
            (chartGramOnE (I := I) g α l i) z) +
        (-1 : ℝ) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv l
            (chartGramOnE (I := I) g α i j) z) 1 (jmax - 1) := by
    have h1 := (hasChartJetLipBall_chartGramOnE g₀ α hK hKsub l j (R := R) (jmax := jmax)).partialDeriv hKsub hjmax i
    have h2 := (hasChartJetLipBall_chartGramOnE g₀ α hK hKsub l i (R := R) (jmax := jmax)).partialDeriv hKsub hjmax j
    have h3 := (hasChartJetLipBall_chartGramOnE g₀ α hK hKsub i j (R := R) (jmax := jmax)).partialDeriv hKsub hjmax l
    have h3' := h3.const_smul hKsub (-1 : ℝ)
    have h12 := (h1.add hKsub h2)
    have h123 := h12.add hKsub h3'
    simpa only [max_self, min_self, zero_add] using h123
  refine hbr.congr ?_
  intro g
  funext z
  simp only [gramBracket]
  ring

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartChristoffel
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 1 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => chartChristoffel (I := I) g α i j k) 1 (jmax - 1) := by
  have hprodL : ∀ l : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartInvGramOnE (I := I) g α k l z *
          gramBracket (I := I) g α i j l z) 1 (jmax - 1) := by
    intro l
    have hinv := hasChartJetLipBall_chartInvGramOnE g₀ α hK hKsub k l (R := R) (jmax := jmax)
    have hbr := hasChartJetLipBall_gramBracket g₀ hjmax α hK hKsub i j l (R := R) (jmax := jmax)
    have := hinv.mul hKsub hbr
    simpa only [max_eq_right (Nat.zero_le 1), min_eq_right (Nat.sub_le jmax 1)] using this
  have hsum := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun l g => fun z => chartInvGramOnE (I := I) g α k l z *
      gramBracket (I := I) g α i j l z) (fun l _ => hprodL l)
  have hsmul := hsum.const_smul hKsub (1 / 2 : ℝ)
  refine hsmul.congr ?_
  intro g
  funext z
  rw [chartChristoffel_eq_sum_invGramOnE_bracket]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartDeTurckVFComp
    (g₀ g_bg : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 1 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (k : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z) 1 (jmax - 1) := by
  have hbgconst : ∀ a b : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun _ => fun z => chartChristoffel (I := I) g_bg α a b k z) 0 (jmax - 1) := by
    intro a b
    refine hasChartJetLipBall_const _ α hK hKsub
      (f₀ := fun z => chartChristoffel (I := I) g_bg α a b k z)
      (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k)
      (fun _ => rfl)
  have hprodAB : ∀ a b : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z)) 1 (jmax - 1) := by
    intro a b
    have hinv := hasChartJetLipBall_chartInvGramOnE g₀ α hK hKsub a b (R := R) (jmax := jmax)
    have hΓ := hasChartJetLipBall_chartChristoffel g₀ hjmax α hK hKsub a b k (R := R) (jmax := jmax)
    have hΓbg := hbgconst a b
    have hΓbg' := hΓbg.const_smul hKsub (-1 : ℝ)
    have hΓdiff := (hΓ.add hKsub hΓbg')
    have hΓdiff1 : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z) 1 (jmax - 1) := by
      have hd : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
          (fun g => fun z => chartChristoffel (I := I) g α a b k z +
            (-1 : ℝ) * chartChristoffel (I := I) g_bg α a b k z) (max 1 0) (min (jmax - 1) (jmax - 1)) :=
        hΓdiff
      have hd' := hd
      simp only [max_eq_left (Nat.zero_le 1), min_self] at hd'
      refine hd'.congr ?_
      intro g; funext z; ring
    have := hinv.mul hKsub hΓdiff1
    simpa only [max_eq_right (Nat.zero_le 1), min_eq_right (Nat.sub_le jmax 1)] using this
  have hsumB : ∀ a : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b z *
            (chartChristoffel (I := I) g α a b k z -
              chartChristoffel (I := I) g_bg α a b k z)) 1 (jmax - 1) :=
    fun a => HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (F := fun b g => fun z => chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z)) (fun b _ => hprodAB a b)
  have hsumA := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun a g => fun z => ∑ b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z)) (fun a _ => hsumB a)
  refine hsumA.congr ?_
  intro g
  funext z
  rw [chartDeTurckVFComp_def]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartRiemannTensor
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 2 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j k l : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => fun z => chartRiemannTensor (I := I) g α i j k l z) 2 (jmax - 2) := by
  have hjmax1 : 1 ≤ jmax := by omega
  have hjmaxs : 1 ≤ jmax - 1 := by omega
  have hdΓ1 : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
        (chartChristoffel (I := I) g α i k l)) 2 (jmax - 2) := by
    have := (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub i k l
      (R := R) (jmax := jmax)).partialDeriv hKsub hjmaxs j
    simpa only [Nat.sub_sub] using this
  have hdΓ2 : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => fun z => (-1 : ℝ) *
        DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
          (chartChristoffel (I := I) g α i j l) z) 2 (jmax - 2) := by
    have h := (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub i j l
      (R := R) (jmax := jmax)).partialDeriv hKsub hjmaxs k
    have h' := h.const_smul hKsub (-1 : ℝ)
    simpa only [Nat.sub_sub] using h'
  have hprodM : ∀ m : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z +
          (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z)) 2 (jmax - 1) := by
    intro m
    have hA := (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub j m l (R := R) (jmax := jmax)).mul hKsub
      (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub i k m (R := R) (jmax := jmax))
    have hB := (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub k m l (R := R) (jmax := jmax)).mul hKsub
      (hasChartJetLipBall_chartChristoffel g₀ hjmax1 α hK hKsub i j m (R := R) (jmax := jmax))
    have hB' := hB.const_smul hKsub (-1 : ℝ)
    have hAB := (hA.add hKsub hB')
    have hAB' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
        (max (max 1 1) (max 1 1)) (min (min (jmax - 1) (jmax - 1)) (min (jmax - 1) (jmax - 1))) := hAB
    simp only [max_self, min_self] at hAB'
    exact (hAB'.of_le (by norm_num)).congr (fun g => rfl)
  have hsumM := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun m g => fun z => chartChristoffel (I := I) g α j m l z *
        chartChristoffel (I := I) g α i k m z +
      (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
        chartChristoffel (I := I) g α i j m z)) (fun m _ => hprodM m)
  have htotal := ((hdΓ1.add hKsub hdΓ2).add hKsub hsumM)
  have htotal' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
      (max (max 2 2) 2) (min (min (jmax - 2) (jmax - 2)) (jmax - 1)) := htotal
  have hmineq : min (min (jmax - 2) (jmax - 2)) (jmax - 1) = jmax - 2 := by
    rw [min_self]; exact min_eq_left (by omega)
  rw [hmineq] at htotal'
  refine (htotal'.of_le (by norm_num)).congr ?_
  intro g
  funext z
  rw [chartRiemannTensor_def]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z +
          (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z))) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z -
          chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z) from by
    refine Finset.sum_congr rfl (fun m _ => by ring)]
  ring

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartRicciTensor
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 2 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => chartRicciTensor (I := I) g α i k) 2 (jmax - 2) := by
  have hsum := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun j g => fun z => chartRiemannTensor (I := I) g α i j k j z)
    (fun j _ => hasChartJetLipBall_chartRiemannTensor g₀ hjmax α hK hKsub i j k j (R := R) (jmax := jmax))
  refine hsum.congr ?_
  intro g
  funext z
  rw [chartRicciTensor_def]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartLieDeTurckComp
    (g₀ g_bg : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 2 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => chartLieDeTurckComp (I := I) g g_bg α i j) 2 (jmax - 2) := by
  have hjmax1 : 1 ≤ jmax := by omega
  have hjmaxs : 1 ≤ jmax - 1 := by omega
  have hgroup0 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
            (chartGramOnE (I := I) g α i j) z) 2 (jmax - 2) := by
    intro k
    have hW := hasChartJetLipBall_chartDeTurckVFComp g₀ g_bg hjmax1 α hK hKsub k (R := R) (jmax := jmax)
    have hdG := (hasChartJetLipBall_chartGramOnE g₀ α hK hKsub i j (R := R) (jmax := jmax)).partialDeriv hKsub hjmax1 k
    have hmul := hW.mul hKsub hdG
    have hmul' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
        (max 1 1) (min (jmax - 1) (jmax - 1)) := hmul
    simp only [max_self, min_self] at hmul'
    exact (hmul'.of_le (by norm_num)).of_le_Nmax (by omega)
  have hgroup1 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartGramOnE (I := I) g α k j z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
            (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) 2 (jmax - 2) := by
    intro k
    have hG := hasChartJetLipBall_chartGramOnE g₀ α hK hKsub k j (R := R) (jmax := jmax)
    have hdW := (hasChartJetLipBall_chartDeTurckVFComp g₀ g_bg hjmax1 α hK hKsub k
      (R := R) (jmax := jmax)).partialDeriv hKsub hjmaxs i
    have hmul := hG.mul hKsub hdW
    have hmul' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
        (max 0 (1 + 1)) (min jmax (jmax - 1 - 1)) := hmul
    rw [show min jmax (jmax - 1 - 1) = jmax - 2 by rw [Nat.sub_sub]; exact min_eq_right (by omega)] at hmul'
    exact (hmul'.of_le (by norm_num))
  have hgroup2 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
        (fun g => fun z => chartGramOnE (I := I) g α i k z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
            (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) 2 (jmax - 2) := by
    intro k
    have hG := hasChartJetLipBall_chartGramOnE g₀ α hK hKsub i k (R := R) (jmax := jmax)
    have hdW := (hasChartJetLipBall_chartDeTurckVFComp g₀ g_bg hjmax1 α hK hKsub k
      (R := R) (jmax := jmax)).partialDeriv hKsub hjmaxs j
    have hmul := hG.mul hKsub hdW
    have hmul' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
        (max 0 (1 + 1)) (min jmax (jmax - 1 - 1)) := hmul
    rw [show min jmax (jmax - 1 - 1) = jmax - 2 by rw [Nat.sub_sub]; exact min_eq_right (by omega)] at hmul'
    exact (hmul'.of_le (by norm_num))
  have hsum0 := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
        (chartGramOnE (I := I) g α i j) z) (fun k _ => hgroup0 k)
  have hsum1 := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartGramOnE (I := I) g α k j z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
        (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) (fun k _ => hgroup1 k)
  have hsum2 := HasChartJetLipBall.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartGramOnE (I := I) g α i k z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
        (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) (fun k _ => hgroup2 k)
  have htotal := ((hsum0.add hKsub hsum1).add hKsub hsum2)
  have htotal' : HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K _
      (max (max 2 2) 2) (min (min (jmax - 2) (jmax - 2)) (jmax - 2)) := htotal
  simp only [max_self, min_self] at htotal'
  refine (htotal'.of_le (by norm_num)).congr ?_
  intro g
  funext z
  rw [chartLieDeTurckComp_def]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem hasChartJetLipBall_chartDeTurckRicciRHS
    (g₀ g_bg : SmoothRiemannianMetric I M) {R : ℝ} {jmax : ℕ} (hjmax : 2 ≤ jmax) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) :
    HasChartJetLipBall (realizedFibreSmallBall (I := I) (M := M) g₀ R jmax) α K
      (fun g => fun z => chartDeTurckRicciRHS (I := I) g g_bg α i k z) 2 (jmax - 2) := by
  have hRic := (hasChartJetLipBall_chartRicciTensor g₀ hjmax α hK hKsub i k (R := R) (jmax := jmax)).const_smul
    hKsub (-2 : ℝ)
  have hLie := hasChartJetLipBall_chartLieDeTurckComp g₀ g_bg hjmax α hK hKsub i k (R := R) (jmax := jmax)
  have hAdd := HasChartJetLipBall.add hKsub hRic hLie
  have hmax : max 2 2 = 2 := by norm_num
  rw [hmax, min_self] at hAdd
  refine hAdd.congr ?_
  intro g
  funext z
  rw [chartDeTurckRicciRHS_def]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in

theorem chartDeTurckRicciRHS_realize_seminorm_le_bareChartJetContentOnE_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) {R : ℝ} (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ N + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ N + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ y ∈ K,
        iteratedFDerivSeminorm N
            (fun z => chartDeTurckRicciRHS (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α i k z -
              chartDeTurckRicciRHS (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α i k z)
            (interior (extChartAt I α).target) y ≤
          C * bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (N + 2) y := by
  classical
  obtain ⟨C, hC_pos, hC⟩ :=
    (hasChartJetLipBall_chartDeTurckRicciRHS (I := I) (M := M) g₀ g_bg (R := R) (jmax := N + 2)
      (by omega) α hK hKsub i k).seminorm_le N (by omega)
  refine ⟨C * ((Module.finrank ℝ E) : ℝ), by positivity, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball y hy
  have hyint : y ∈ interior (extChartAt I α).target := hKsub hy
  have hg₁mem : tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ ∈
      realizedFibreSmallBall (I := I) (M := M) g₀ R (N + 2) :=
    tensorSectionRealizeMetric_mem_realizedFibreSmallBall (I := I) (M := M) g₀ T hδ_lt hδ hTball
  have hg₂mem : tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' ∈
      realizedFibreSmallBall (I := I) (M := M) g₀ R (N + 2) :=
    tensorSectionRealizeMetric_mem_realizedFibreSmallBall (I := I) (M := M) g₀ T' hδ'_lt hδ' hT'ball
  refine (hC _ hg₁mem _ hg₂mem y hy).trans ?_
  have hgram := chartGramJetDiffSeminormSum_realize_le_bareChartJetContentOnE (I := I) (M := M)
    g₀ T T' hδ_lt hδ hδ'_lt hδ' α (N + 2) hyint
  calc C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α
        (interior (extChartAt I α).target) y
      ≤ C * (((Module.finrank ℝ E) : ℝ) *
          bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (N + 2) y) :=
        mul_le_mul_of_nonneg_left hgram hC_pos.le
    _ = (C * ((Module.finrank ℝ E) : ℝ)) *
          bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (N + 2) y := by ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
