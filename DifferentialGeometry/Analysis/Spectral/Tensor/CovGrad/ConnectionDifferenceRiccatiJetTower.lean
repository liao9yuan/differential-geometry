import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnDiffCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricSharpEndomorphismJetBound

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound
    ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma succ_sq_le_four_pow (m : ℕ) : (m + 1) ^ 2 ≤ 4 ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have h : (k + 2) ^ 2 ≤ 4 * (k + 1) ^ 2 := by nlinarith [Nat.zero_le k]
    calc (k + 1 + 1) ^ 2 = (k + 2) ^ 2 := by ring
      _ ≤ 4 * (k + 1) ^ 2 := h
      _ ≤ 4 * 4 ^ k := by gcongr
      _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

private lemma diagGrid_genConst_closure (c B0 F : ℝ) (hc4 : 4 ≤ c) (hcB : c ≤ B0 ^ 2)
    (hB0 : (4 : ℝ) ≤ B0) (hF1 : (1 : ℝ) ≤ F) (hFB : 4 * F ^ 2 ≤ B0 ^ 2) (m : ℕ) :
    c * B0 ^ m *
        (∑ i ∈ Finset.range (m + 1),
          F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
            ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) := by
  have hB1 : (1 : ℝ) ≤ B0 := by linarith
  have hB0nn : (0 : ℝ) ≤ B0 := by linarith
  have hF0 : (0 : ℝ) ≤ F := by linarith
  have hcnn : (0 : ℝ) ≤ c := by linarith
  have hpts : ∀ i ∈ Finset.range (m + 1),
      F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
          ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
        ≤ ((m : ℝ) + 1) * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2)) := by
    intro i hi
    have him : i ≤ m := by rw [Finset.mem_range] at hi; omega
    have hinner : ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
        ≤ ((m : ℝ) + 1) * (F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2)) := by
      have hterm : ∀ l ∈ Finset.range (m + 1 - i),
          F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
            ≤ F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2) := by
        intro l hl
        have hlmi : l ≤ m - i := by rw [Finset.mem_range] at hl; omega
        have hF : F ^ (3 + l) ≤ F ^ (3 + (m - i)) := pow_le_pow_right₀ hF1 (by omega)
        have hle2 : 2 * (l + 1) ^ 2 ≤ 2 * (m - i + 1) ^ 2 := by gcongr
        have hB : B0 ^ (2 * (l + 1) ^ 2) ≤ B0 ^ (2 * (m - i + 1) ^ 2) :=
          pow_le_pow_right₀ hB1 hle2
        exact mul_le_mul hF hB (by positivity) (by positivity)
      calc ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
          ≤ (Finset.range (m + 1 - i)).card •
              (F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2)) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((m + 1 - i : ℕ) : ℝ) * (F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2)) := by
            rw [Finset.card_range, nsmul_eq_mul]
        _ ≤ ((m : ℝ) + 1) * (F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hle2 : (m + 1 - i : ℕ) ≤ m + 1 := by omega
            calc ((m + 1 - i : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hle2
              _ = (m : ℝ) + 1 := by push_cast; ring
    have hprod : F ^ (3 + i) * F ^ (3 + (m - i)) *
          (B0 ^ (2 * (i + 1) ^ 2) * B0 ^ (2 * (m - i + 1) ^ 2))
        = F ^ (6 + m) * B0 ^ (2 * (i + 1) ^ 2 + 2 * (m - i + 1) ^ 2) := by
      rw [← pow_add, ← pow_add, show 3 + i + (3 + (m - i)) = 6 + m from by omega]
    have hexp : 2 * (i + 1) ^ 2 + 2 * (m - i + 1) ^ 2 ≤ 2 * (m + 1) ^ 2 + 2 := by
      have hkey : (i + 1) ^ 2 + (m - i + 1) ^ 2 ≤ (m + 1) ^ 2 + 1 := by
        obtain ⟨d, hd⟩ : ∃ d, m = i + d := ⟨m - i, by omega⟩
        subst hd
        simp only [Nat.add_sub_cancel_left]
        nlinarith [Nat.zero_le (i * d)]
      calc 2 * (i + 1) ^ 2 + 2 * (m - i + 1) ^ 2
          = 2 * ((i + 1) ^ 2 + (m - i + 1) ^ 2) := by ring
        _ ≤ 2 * ((m + 1) ^ 2 + 1) := by gcongr
        _ = 2 * (m + 1) ^ 2 + 2 := by ring
    calc F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
            ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
        ≤ F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
            (((m : ℝ) + 1) * (F ^ (3 + (m - i)) * B0 ^ (2 * (m - i + 1) ^ 2))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = ((m : ℝ) + 1) * (F ^ (3 + i) * F ^ (3 + (m - i)) *
            (B0 ^ (2 * (i + 1) ^ 2) * B0 ^ (2 * (m - i + 1) ^ 2))) := by ring
      _ = ((m : ℝ) + 1) * (F ^ (6 + m) *
            B0 ^ (2 * (i + 1) ^ 2 + 2 * (m - i + 1) ^ 2)) := by rw [hprod]
      _ ≤ ((m : ℝ) + 1) * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ hB1 hexp
  have hsum : ∑ i ∈ Finset.range (m + 1),
        F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
          ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
      ≤ ((m : ℝ) + 1) ^ 2 * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2)) := by
    calc ∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)
        ≤ ∑ _i ∈ Finset.range (m + 1),
            ((m : ℝ) + 1) * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2)) :=
          Finset.sum_le_sum hpts
      _ = (Finset.range (m + 1)).card •
            (((m : ℝ) + 1) * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2))) := by
          rw [Finset.sum_const]
      _ = ((m : ℝ) + 1) ^ 2 * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2)) := by
          rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hmsq : ((m : ℝ) + 1) ^ 2 ≤ B0 ^ m := by
    have hn : (m + 1) ^ 2 ≤ 4 ^ m := succ_sq_le_four_pow m
    calc ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 ^ m : ℕ) : ℝ) := by exact_mod_cast hn
      _ = (4 : ℝ) ^ m := by push_cast; ring
      _ ≤ B0 ^ m := pow_le_pow_left₀ (by norm_num) hB0 m
  have hF2 : F ^ 2 ≤ B0 ^ 2 := by nlinarith [hFB, sq_nonneg F]
  have hfinal : c * ((m : ℝ) + 1) ^ 2 * F ^ 2 ≤ B0 ^ (3 * m + 4) := by
    have step : c * ((m : ℝ) + 1) ^ 2 * F ^ 2 ≤ B0 ^ 2 * B0 ^ m * B0 ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul hcB hmsq (by positivity) (by positivity)
      · exact hF2
      · positivity
      · positivity
    calc c * ((m : ℝ) + 1) ^ 2 * F ^ 2 ≤ B0 ^ 2 * B0 ^ m * B0 ^ 2 := step
      _ = B0 ^ (2 + m + 2) := by rw [← pow_add, ← pow_add]
      _ ≤ B0 ^ (3 * m + 4) := pow_le_pow_right₀ hB1 (by omega)
  have hFsplit : F ^ (6 + m) = F ^ 2 * F ^ (m + 4) := by rw [← pow_add]; congr 1; omega
  calc c * B0 ^ m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ c * B0 ^ m * (((m : ℝ) + 1) ^ 2 * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (c * ((m : ℝ) + 1) ^ 2 * F ^ 2) *
          (F ^ (m + 4) * (B0 ^ m * B0 ^ (2 * (m + 1) ^ 2 + 2))) := by rw [hFsplit]; ring
    _ = (c * ((m : ℝ) + 1) ^ 2 * F ^ 2) *
          (F ^ (m + 4) * B0 ^ (m + (2 * (m + 1) ^ 2 + 2))) := by rw [← pow_add]
    _ ≤ B0 ^ (3 * m + 4) * (F ^ (m + 4) * B0 ^ (m + (2 * (m + 1) ^ 2 + 2))) :=
        mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = F ^ (m + 4) * B0 ^ ((3 * m + 4) + (m + (2 * (m + 1) ^ 2 + 2))) := by
        rw [pow_add B0 (3 * m + 4) (m + (2 * (m + 1) ^ 2 + 2))]; ring
    _ = F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) := by
        rw [show m + 4 = 3 + (m + 1) from by omega,
          show (3 * m + 4) + (m + (2 * (m + 1) ^ 2 + 2)) = 2 * (m + 2) ^ 2 from by ring]

private lemma inverseEndo_genConst_succ_closure (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (c : ℝ) (hc4 : 4 ≤ c) (hcB : c ≤ inverseEndoBase (E := E) R δ ^ 2) (m : ℕ) :
    c * appCcGdiag (E := E) m *
        (∑ i ∈ Finset.range (m + 1),
          inverseEndoJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
      ≤ inverseEndoJetBound (E := E) R δ (m + 1) := by
  have hB0 : (4 : ℝ) ≤ inverseEndoBase (E := E) R δ := four_le_inverseEndoBase R δ hR hδ0 hδ1
  have hF1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hFB : 4 * (Module.finrank ℝ E : ℝ) ^ 2 ≤ inverseEndoBase (E := E) R δ ^ 2 :=
    four_finrankSq_le_inverseEndoBaseSq R δ hR hδ0 hδ1
  have hgrid_le : appCcGdiag (E := E) m ≤ inverseEndoBase (E := E) R δ ^ m := by
    rw [appCcGdiag]
    exact pow_le_pow_left₀ (by positivity)
      (finrankFactor_le_inverseEndoBase R δ hR hδ0 hδ1) m
  simp only [inverseEndoJetBound]
  set B0 := inverseEndoBase (E := E) R δ with hB0def
  set F := (Module.finrank ℝ E : ℝ) with hFdef
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (m + 1),
      F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
        ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2) := by
    apply Finset.sum_nonneg; intro i _
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro l _; positivity
  have hcnn : (0 : ℝ) ≤ c := by linarith
  calc c * appCcGdiag (E := E) m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ c * B0 ^ m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ hsum_nn
        exact mul_le_mul_of_nonneg_left hgrid_le hcnn
    _ ≤ F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) :=
        diagGrid_genConst_closure c B0 F hc4 hcB hB0 hF1 hFB m

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffSection_iteratedCovGrad_rfns_tight_order0_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((connDiffSection (I := I) g₁ g₀).toSection x) ≤
      inverseEndoJetBound (E := E) R δ 0 := by
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have hne : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hrk_eq : raisedKoszul (I := I) g₀ g₁ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1 (koszulCovecCc (I := I) g₀ T) :=
    raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie
  have hiso0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (koszulCovecCc (I := I) g₀ T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((koszulCovecCc (I := I) g₀ T).toSection x) := by
    have h := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (koszulCovecCc (I := I) g₀ T) 0 x
    simpa using h
  have hrk0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤ 10 * R ^ 2 := by
    rw [hrk_eq, hiso0]
    have h := rfns_iteratedCovGrad_koszulCovecCc_le (I := I) (M := M) g₀ a T hTjet 0
      (Nat.zero_le a) x
    simpa using h
  have hsf0 := rfns_sharpFlatEndoCc_le_of_lt_one (I := I) (M := M) g₀ (δ₀ := δ) hδ0 hδ1 g₁ T htie
    (le_refl δ) hδ0 hδ x
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁,
    appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
    ((raisedKoszul (I := I) g₀ g₁).toSection x)
    ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
  have hsf_nn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _
  have hrk_nn : (0 : ℝ) ≤ (10 : ℝ) * R ^ 2 := by positivity
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x ((raisedKoszul (I := I) g₀ g₁).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
          ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
      ≤ (10 * R ^ 2) * ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2) :=
        mul_le_mul hrk0 hsf0 hsf_nn hrk_nn
    _ ≤ inverseEndoJetBound (E := E) R δ 0 := by
        rw [inverseEndoJetBound]
        have hexp : (Module.finrank ℝ E : ℝ) ^ (3 + 0) *
            inverseEndoBase (E := E) R δ ^ (2 * (0 + 1) ^ 2)
            = (Module.finrank ℝ E : ℝ) ^ 3 * inverseEndoBase (E := E) R δ ^ 2 := by norm_num
        rw [hexp, inverseEndoBase]
        have hkey : 10 * R ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2 := by
          nlinarith [hfr, hR, sq_nonneg R, mul_nonneg (sub_nonneg.mpr hfr) hR,
            mul_nonneg (mul_nonneg (sub_nonneg.mpr hfr) (sub_nonneg.mpr hfr)) hR]
        have hF2K2_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 := by
          positivity
        calc (10 * R ^ 2) * ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2)
            ≤ (4 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2) *
                ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2) :=
              mul_le_mul_of_nonneg_right hkey hF2K2_nn
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
                (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))) ^ 2 := by ring

private def connDiffArmField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff)⟩

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem appCcRS_slotExtend_raisedKoszul_flatArmCc_false_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    appCcRS (I := I) (M := M) g₀ 1 2 3
        (slotExtend (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
        (flatArmCc (I := I) g₀ g₁ false) =
      - appCcRS (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmField (I := I) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀) := by
  sorry

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffSection_covGrad_eq_clean_sub_connArmFeedback
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) =
      (appCcRS (I := I) (M := M) g₀ 1 1 3
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁)
        + appCcRS (I := I) (M := M) g₀ 1 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
          (flatArmCc (I := I) g₀ g₁ true))
        - appCcRS (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmField (I := I) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀) := by
  rw [show covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
        = covGrad (I := I) (M := M) g₀ 1 2
          (appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
            (sharpFlatEndoCc (I := I) g₀ g₁)) from by
    rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
      (sharpFlatEndoCc (I := I) g₀ g₁)]
  rw [covGrad_sharpFlatEndoCc_eq_arms (I := I) g₀ g₁]
  rw [appCcRS_add_right (I := I) (M := M) g₀ 1 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
      (flatArmCc (I := I) g₀ g₁ true) (flatArmCc (I := I) g₀ g₁ false)]
  rw [appCcRS_slotExtend_raisedKoszul_flatArmCc_false_eq_neg (I := I) (M := M) g₀ g₁]
  abel

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem rfns_iteratedCovGrad_armSlotEndoPassZeroCc_connDiffArmField_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmField (I := I) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) :=
  sorry

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem rfns_iteratedCovGrad_trueArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (j : ℕ) (hj : j + 1 ≤ a) (y : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) y
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (appCcRS (I := I) (M := M) g₀ 1 2 3
            (slotExtend (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
            (flatArmCc (I := I) g₀ g₁ true))).toSection y) ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1), ((Module.finrank ℝ E : ℝ) * (10 * R ^ 2)) *
          ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l :=
  sorry

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffSection_covGrad_quadratic_decomp_repr
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∃ (P : SmoothCcTensor g₀ 1 3) (K₁ : SmoothCcTensor g₀ 2 3),
      covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
          = P - appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ (connDiffSection (I := I) g₁ g₀)
      ∧ (∀ (j : ℕ), j + 1 ≤ a → ∀ (y : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) y
              ((iteratedCovGrad (I := I) g₀ 1 3 j P).toSection y) ≤
            appCcGdiag (E := E) j *
              ∑ i ∈ Finset.range (j + 1),
                ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (10 * R ^ 2)) *
                ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
      ∧ (∀ (j : ℕ), j ≤ a → ∀ (y : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) y
              ((iteratedCovGrad (I := I) g₀ 2 3 j K₁).toSection y) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) y
                ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection y)) := by
  refine ⟨appCcRS (I := I) (M := M) g₀ 1 1 3
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁)
        + appCcRS (I := I) (M := M) g₀ 1 2 3
          (slotExtend (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
          (flatArmCc (I := I) g₀ g₁ true),
      armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmField (I := I) g₀ g₁),
      connDiffSection_covGrad_eq_clean_sub_connArmFeedback (I := I) (M := M) g₀ g₁, ?_, ?_⟩
  · intro j hj y
    have hsrc : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) y
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (appCcRS (I := I) (M := M) g₀ 1 1 3
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁))).toSection y) ≤
        appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1), (10 * R ^ 2) *
            ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ j 1 1 3
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) y) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg j)
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have hΦ : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) y
          ((iteratedCovGrad (I := I) g₀ 1 3 i
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))).toSection y) ≤ 10 * R ^ 2 :=
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) y
                ((iteratedCovGrad (I := I) g₀ 1 3 i
                  (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁))).toSection y)
            = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) y
                ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁)).toSection y) :=
              rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
                (raisedKoszul (I := I) g₀ g₁) y
          _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) y
                ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
                  (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
                    (koszulCovecCc (I := I) g₀ T))).toSection y) := by
              rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie]
          _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (i + 1)) y
                ((iteratedCovGrad (I := I) g₀ 0 3 (i + 1)
                  (koszulCovecCc (I := I) g₀ T)).toSection y) :=
              rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
                (koszulCovecCc (I := I) g₀ T) (i + 1) y
          _ ≤ 10 * R ^ 2 :=
              rfns_iteratedCovGrad_koszulCovecCc_le (I := I) g₀ a T hTjet (i + 1) (by omega) y
      have hWsum : ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) y
              ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection y)
          ≤ ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        rw [Finset.mem_range] at hl
        exact rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
          hTjet l (by omega) y
      exact mul_le_mul hΦ hWsum
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) y _)) (by positivity)
    have htrue := rfns_iteratedCovGrad_trueArm_le (I := I) (M := M) g₀ g₁ a T htie hR hδ0 hδ1 hδ
      hTjet j hj y
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + j) y _ _) ?_
    have key : 2 * (appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1), (10 * R ^ 2) *
              ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
          + 2 * (appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1), ((Module.finrank ℝ E : ℝ) * (10 * R ^ 2)) *
              ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
        = appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1),
              ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (10 * R ^ 2)) *
              ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l := by
      rw [show 2 * (appCcGdiag (E := E) j *
              ∑ i ∈ Finset.range (j + 1), (10 * R ^ 2) *
                ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
            = appCcGdiag (E := E) j * (2 *
              ∑ i ∈ Finset.range (j + 1), (10 * R ^ 2) *
                ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l) from by ring,
        show 2 * (appCcGdiag (E := E) j *
              ∑ i ∈ Finset.range (j + 1), ((Module.finrank ℝ E : ℝ) * (10 * R ^ 2)) *
                ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
            = appCcGdiag (E := E) j * (2 *
              ∑ i ∈ Finset.range (j + 1), ((Module.finrank ℝ E : ℝ) * (10 * R ^ 2)) *
                ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l) from by ring,
        ← mul_add]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [← key]
    exact add_le_add (mul_le_mul_of_nonneg_left hsrc (by norm_num))
      (mul_le_mul_of_nonneg_left htrue (by norm_num))
  · intro j _ y
    exact rfns_iteratedCovGrad_armSlotEndoPassZeroCc_connDiffArmField_le (I := I) (M := M) g₀ g₁ j y

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffSection_succ_iteratedCovGrad_rfns_quadratic_recursion_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (m : ℕ) (hm : m + 1 ≤ a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * (appCcGdiag (E := E) m *
          ∑ i ∈ Finset.range (m + 1),
            ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (10 * R ^ 2)) *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
      + 2 * (appCcGdiag (E := E) m *
          ∑ i ∈ Finset.range (m + 1),
            (Module.finrank ℝ E : ℝ) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) *
            ∑ l ∈ Finset.range (m + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
  obtain ⟨P, K₁, hPK, hP, hK₁⟩ :=
    connDiffSection_covGrad_quadratic_decomp_repr (I := I) (M := M) g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet
  set cds := connDiffSection (I := I) g₁ g₀ with hcds
  have hgd_nn : (0 : ℝ) ≤ appCcGdiag (E := E) m := appCcGdiag_nonneg m
  have hSnn : ∀ i : ℕ, (0 : ℝ) ≤ ∑ l ∈ Finset.range (m + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x) :=
    fun i => Finset.sum_nonneg (fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 m cds x]
  have hval : (iteratedCovGrad (I := I) g₀ 1 3 m
        (covGrad (I := I) (M := M) g₀ 1 2 cds)).toSection x
      = (iteratedCovGrad (I := I) g₀ 1 3 m P).toSection x
          - (iteratedCovGrad (I := I) g₀ 1 3 m
              (appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ cds)).toSection x := by
    rw [hPK, iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hval]
  set uP := (iteratedCovGrad (I := I) g₀ 1 3 m P).toSection x with huP
  set u1 := (iteratedCovGrad (I := I) g₀ 1 3 m
    (appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ cds)).toSection x with hu1
  have hrP : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x uP ≤
      appCcGdiag (E := E) m *
        ∑ i ∈ Finset.range (m + 1),
          ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (10 * R ^ 2)) *
          ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l := by
    rw [huP]; exact hP m (by omega) x
  have hr1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x u1 ≤
      appCcGdiag (E := E) m *
        ∑ i ∈ Finset.range (m + 1),
          (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 2 i cds).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x) := by
    rw [hu1]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ m 1 2 3 K₁ cds x) ?_
    refine mul_le_mul_of_nonneg_left ?_ hgd_nn
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact mul_le_mul_of_nonneg_right (hK₁ i (by omega) x) (hSnn i)
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + m) x uP u1) ?_
  linarith [hrP, hr1]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffSection_inverseEndoJetBound_succ_step
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (m : ℕ) (hm : m + 1 ≤ a) (x : M)
    (hIH : ∀ j : ℕ, j ≤ m →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ j) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      inverseEndoJetBound (E := E) R δ (m + 1) := by
  refine le_trans (connDiffSection_succ_iteratedCovGrad_rfns_quadratic_recursion_le
    (I := I) (M := M) g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet m hm x) ?_
  have hB4 : (4 : ℝ) ≤ inverseEndoBase (E := E) R δ := four_le_inverseEndoBase R δ hR hδ0 hδ1
  have hB1 : (1 : ℝ) ≤ inverseEndoBase (E := E) R δ := by linarith
  have hBnn : (0 : ℝ) ≤ inverseEndoBase (E := E) R δ := by linarith
  have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by linarith
  have hIEnn : ∀ k, 0 ≤ inverseEndoJetBound (E := E) R δ k :=
    fun k => inverseEndoJetBound_nonneg R δ hR hδ1 k
  have hgdnn : (0 : ℝ) ≤ appCcGdiag (E := E) m := appCcGdiag_nonneg m
  have hgd1 : (1 : ℝ) ≤ appCcGdiag (E := E) m := by
    rw [appCcGdiag]
    apply one_le_pow₀
    linarith
  have hmono : ∀ i j : ℕ, i ≤ j →
      inverseEndoJetBound (E := E) R δ i ≤ inverseEndoJetBound (E := E) R δ j := by
    intro i j hij
    simp only [inverseEndoJetBound]
    apply mul_le_mul
    · exact pow_le_pow_right₀ hfr (by omega)
    · exact pow_le_pow_right₀ hB1 (by nlinarith [hij, Nat.zero_le i, Nat.zero_le j])
    · positivity
    · positivity
  have hRB : R ≤ inverseEndoBase (E := E) R δ := by
    rw [inverseEndoBase]
    have hr1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ (by linarith)]; linarith
    have h2n1 : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
    nlinarith [hr1, h2n1, hR, mul_nonneg (by linarith : (0:ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1))
      (by linarith : (0:ℝ) ≤ 1 + R)]
  have h10_zero : 10 * R ^ 2 ≤ inverseEndoJetBound (E := E) R δ 0 := by
    rw [inverseEndoJetBound]
    have hexp : (Module.finrank ℝ E : ℝ) ^ (3 + 0) *
        inverseEndoBase (E := E) R δ ^ (2 * (0 + 1) ^ 2)
        = (Module.finrank ℝ E : ℝ) ^ 3 * inverseEndoBase (E := E) R δ ^ 2 := by norm_num
    rw [hexp, inverseEndoBase]
    have hkey : 10 * R ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2 := by
      nlinarith [hfr, hR, sq_nonneg R, mul_nonneg (sub_nonneg.mpr hfr) hR,
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hfr) (sub_nonneg.mpr hfr)) hR]
    have hr1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ (by linarith)]; linarith
    have hr1sq : (1 : ℝ) ≤ (1 / (1 - δ)) ^ 2 := by nlinarith [hr1]
    have hmul1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 := by
      have hF2 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := one_le_pow₀ hfr
      have := mul_le_mul hF2 hr1sq (by norm_num) (by positivity)
      simpa using this
    calc 10 * R ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2 := hkey
      _ = (4 * (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2) * 1 := (mul_one _).symm
      _ ≤ (4 * (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (1 + R) ^ 2) *
            ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hmul1 (by positivity)
      _ = (Module.finrank ℝ E : ℝ) ^ 3 *
            (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))) ^ 2 := by ring
  have h10 : ∀ i : ℕ, 10 * R ^ 2 ≤ inverseEndoJetBound (E := E) R δ i :=
    fun i => le_trans h10_zero (hmono 0 i (Nat.zero_le i))
  set G : ℝ := ∑ i ∈ Finset.range (m + 1), inverseEndoJetBound (E := E) R δ i *
      ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l with hGdef
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hIEnn i)
      (Finset.sum_nonneg (fun l _ => hIEnn l)))
  have hPterm : appCcGdiag (E := E) m *
        (∑ i ∈ Finset.range (m + 1),
          ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (10 * R ^ 2)) *
          ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
      ≤ (2 + 2 * (Module.finrank ℝ E : ℝ)) * (appCcGdiag (E := E) m * G) := by
    rw [show (2 + 2 * (Module.finrank ℝ E : ℝ)) * (appCcGdiag (E := E) m * G)
        = appCcGdiag (E := E) m * ((2 + 2 * (Module.finrank ℝ E : ℝ)) * G) from by ring]
    apply mul_le_mul_of_nonneg_left _ hgdnn
    rw [hGdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [show (2 + 2 * (Module.finrank ℝ E : ℝ)) *
          (inverseEndoJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
        = ((2 + 2 * (Module.finrank ℝ E : ℝ)) * inverseEndoJetBound (E := E) R δ i) *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l from by ring]
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun l _ => hIEnn l))
    exact mul_le_mul_of_nonneg_left (h10 i) (by positivity)
  have hK1term : appCcGdiag (E := E) m *
        (∑ i ∈ Finset.range (m + 1),
          (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
      ≤ (Module.finrank ℝ E : ℝ) * (appCcGdiag (E := E) m * G) := by
    rw [show (Module.finrank ℝ E : ℝ) * (appCcGdiag (E := E) m * G)
        = appCcGdiag (E := E) m * ((Module.finrank ℝ E : ℝ) * G) from by ring]
    apply mul_le_mul_of_nonneg_left _ hgdnn
    rw [hGdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show (Module.finrank ℝ E : ℝ) *
          (inverseEndoJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
        = ((Module.finrank ℝ E : ℝ) * inverseEndoJetBound (E := E) R δ i) *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l from by ring]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hIH i (by omega)) hfr0
    · exact Finset.sum_le_sum (fun l hl => hIH l (by rw [Finset.mem_range] at hl; omega))
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)
    · exact mul_nonneg hfr0 (hIEnn i)
  have hff : 2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ inverseEndoBase (E := E) R δ :=
    finrankFactor_le_inverseEndoBase R δ hR hδ0 hδ1
  have hc16f : (4 : ℝ) ≤ 16 * (Module.finrank ℝ E : ℝ) := by nlinarith [hfr]
  have hcB : 16 * (Module.finrank ℝ E : ℝ) ≤ inverseEndoBase (E := E) R δ ^ 2 := by
    have h1 : (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ 2 ≤ inverseEndoBase (E := E) R δ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hff 2
    nlinarith [h1, sq_nonneg ((Module.finrank ℝ E : ℝ) - 1), hfr]
  have hclosure := inverseEndo_genConst_succ_closure R δ hR hδ0 hδ1
    (16 * (Module.finrank ℝ E : ℝ)) hc16f hcB m
  rw [← hGdef] at hclosure
  have hAnn : (0 : ℝ) ≤ appCcGdiag (E := E) m * G := mul_nonneg hgdnn hGnn
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left hPterm (by norm_num))
    (mul_le_mul_of_nonneg_left hK1term (by norm_num))) ?_
  have h16 : 2 * ((2 + 2 * (Module.finrank ℝ E : ℝ)) * (appCcGdiag (E := E) m * G))
        + 2 * ((Module.finrank ℝ E : ℝ) * (appCcGdiag (E := E) m * G))
      ≤ 16 * (Module.finrank ℝ E : ℝ) * appCcGdiag (E := E) m * G := by
    nlinarith [hAnn, mul_nonneg hAnn (sub_nonneg.mpr hfr), hfr]
  exact le_trans h16 hclosure

theorem rfns_iteratedCovGrad_connDiffSection_inverseEndoJetBound_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i hstrong =>
    intro hi_le x
    match i, hi_le with
    | 0, _ =>
        simpa using connDiffSection_iteratedCovGrad_rfns_tight_order0_le (I := I) (M := M)
          g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet x
    | (m + 1), hm =>
        exact connDiffSection_inverseEndoJetBound_succ_step (I := I) (M := M) g₀ g₁ a T htie hR
          hδ0 hδ1 hδ hTjet m hm x (fun j hj => hstrong j (by omega) (by omega) x)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
