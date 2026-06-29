import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnDiffCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound

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

private def connDiffRiccatiSource (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 1 3 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
    (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ T))

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem connDiffRiccatiSource_iteratedCovGrad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (j : ℕ) (hj : j + 1 ≤ a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (connDiffRiccatiSource (I := I) g₀ T)).toSection x) ≤
      R ^ 2 := by
  have hiso : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j (connDiffRiccatiSource (I := I) g₀ T)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + j)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (2 + j) (symmS (I := I) g₀ T)).toSection x) :=
    (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ T)) j x).trans
      (rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 j (symmS (I := I) g₀ T) x)
  rw [hiso]
  exact rfns_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ a T hTjet (2 + j) (by omega) x

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
    ∃ (P : SmoothCcTensor g₀ 1 3) (K₁ K₂ : SmoothCcTensor g₀ 2 3),
      covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
          = P - appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ (connDiffSection (I := I) g₁ g₀)
            - appCcRS (I := I) (M := M) g₀ 1 2 3 K₂ (connDiffSection (I := I) g₁ g₀)
      ∧ (∀ (j : ℕ), j + 1 ≤ a → ∀ (y : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) y
              ((iteratedCovGrad (I := I) g₀ 1 3 j P).toSection y) ≤ (9 / 4 : ℝ) * R ^ 2)
      ∧ (∀ (j : ℕ), j ≤ a → ∀ (y : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) y
              ((iteratedCovGrad (I := I) g₀ 2 3 j K₁).toSection y) ≤ 10 * R ^ 2)
      ∧ (∀ (j : ℕ), j ≤ a → ∀ (y : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) y
              ((iteratedCovGrad (I := I) g₀ 2 3 j K₂).toSection y) ≤
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) y
                ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection y)) :=
  sorry

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
      9 * R ^ 2
      + 4 * (appCcGdiag (E := E) m *
          ∑ i ∈ Finset.range (m + 1), (10 * R ^ 2) *
            ∑ l ∈ Finset.range (m + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
      + 4 * (appCcGdiag (E := E) m *
          ∑ i ∈ Finset.range (m + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) *
            ∑ l ∈ Finset.range (m + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x)) := by
  obtain ⟨P, K₁, K₂, hPK, hP, hK₁, hK₂⟩ :=
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
              (appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ cds)).toSection x
          - (iteratedCovGrad (I := I) g₀ 1 3 m
              (appCcRS (I := I) (M := M) g₀ 1 2 3 K₂ cds)).toSection x := by
    rw [hPK, iteratedCovGrad_sub, iteratedCovGrad_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hval]
  set uP := (iteratedCovGrad (I := I) g₀ 1 3 m P).toSection x with huP
  set u1 := (iteratedCovGrad (I := I) g₀ 1 3 m
    (appCcRS (I := I) (M := M) g₀ 1 2 3 K₁ cds)).toSection x with hu1
  set u2 := (iteratedCovGrad (I := I) g₀ 1 3 m
    (appCcRS (I := I) (M := M) g₀ 1 2 3 K₂ cds)).toSection x with hu2
  have hrP : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x uP ≤ (9 / 4 : ℝ) * R ^ 2 := by
    rw [huP]; exact hP m (by omega) x
  have hr1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x u1 ≤
      appCcGdiag (E := E) m *
        ∑ i ∈ Finset.range (m + 1), (10 * R ^ 2) *
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
  have hr2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x u2 ≤
      2 * (appCcGdiag (E := E) m *
        ∑ i ∈ Finset.range (m + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i cds).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x)) := by
    rw [hu2]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ m 1 2 3 K₂ cds x) ?_
    have hbnd : appCcGdiag (E := E) m *
          ∑ i ∈ Finset.range (m + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 3 i K₂).toSection x) *
              ∑ l ∈ Finset.range (m + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x)
        ≤ appCcGdiag (E := E) m *
            ∑ i ∈ Finset.range (m + 1),
              (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i cds).toSection x)) *
                ∑ l ∈ Finset.range (m + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x) := by
      refine mul_le_mul_of_nonneg_left ?_ hgd_nn
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      exact mul_le_mul_of_nonneg_right (hK₂ i (by omega) x) (hSnn i)
    refine le_trans hbnd (le_of_eq ?_)
    have hcongr : (∑ i ∈ Finset.range (m + 1),
          (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i cds).toSection x)) *
            ∑ l ∈ Finset.range (m + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x))
        = 2 * ∑ i ∈ Finset.range (m + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i cds).toSection x) *
            ∑ l ∈ Finset.range (m + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l cds).toSection x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcongr]; ring
  have hsi : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x (uP - u1)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x uP
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x u1 :=
    riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + m) x uP u1
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + m) x (uP - u1) u2) ?_
  linarith [hsi, hrP, hr1, hr2]

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
  have hb2 : appCcGdiag (E := E) m *
        (∑ i ∈ Finset.range (m + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
      ≤ appCcGdiag (E := E) m * G := by
    apply mul_le_mul_of_nonneg_left _ hgdnn
    rw [hGdef]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    apply mul_le_mul (hIH i (by omega))
    · apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_range] at hl
      exact hIH l (by omega)
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)
    · exact hIEnn i
  have hb1 : appCcGdiag (E := E) m *
        (∑ i ∈ Finset.range (m + 1), (10 * R ^ 2) *
          ∑ l ∈ Finset.range (m + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
      ≤ appCcGdiag (E := E) m * G := by
    apply mul_le_mul_of_nonneg_left _ hgdnn
    rw [hGdef]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    apply mul_le_mul (h10 i)
    · apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_range] at hl
      exact hIH l (by omega)
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)
    · exact hIEnn i
  have hsrc : 9 * R ^ 2 ≤ appCcGdiag (E := E) m * G := by
    have hG0 : inverseEndoJetBound (E := E) R δ 0 * inverseEndoJetBound (E := E) R δ 0 ≤ G := by
      rw [hGdef]
      have hmem : (0 : ℕ) ∈ Finset.range (m + 1) := by rw [Finset.mem_range]; omega
      have hterm : inverseEndoJetBound (E := E) R δ 0 *
          ∑ l ∈ Finset.range (m + 1 - 0), inverseEndoJetBound (E := E) R δ l
          ≤ ∑ i ∈ Finset.range (m + 1), inverseEndoJetBound (E := E) R δ i *
              ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l := by
        apply Finset.single_le_sum
          (f := fun i => inverseEndoJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (m + 1 - i), inverseEndoJetBound (E := E) R δ l)
        · intro i _
          exact mul_nonneg (hIEnn i) (Finset.sum_nonneg (fun l _ => hIEnn l))
        · exact hmem
      refine le_trans ?_ hterm
      apply mul_le_mul_of_nonneg_left _ (hIEnn 0)
      have hmem0 : (0 : ℕ) ∈ Finset.range (m + 1 - 0) := by rw [Finset.mem_range]; omega
      exact Finset.single_le_sum (f := fun l => inverseEndoJetBound (E := E) R δ l)
        (fun l _ => hIEnn l) hmem0
    have h9le : 9 * R ^ 2 ≤
        inverseEndoJetBound (E := E) R δ 0 * inverseEndoJetBound (E := E) R δ 0 := by
      have h1 : 9 * R ^ 2 ≤ 10 * R ^ 2 := by nlinarith [sq_nonneg R]
      have h2 : 10 * R ^ 2 ≤ inverseEndoJetBound (E := E) R δ 0 := h10_zero
      have h3 : (1 : ℝ) ≤ inverseEndoJetBound (E := E) R δ 0 := by
        rw [inverseEndoJetBound]
        have hexp : (Module.finrank ℝ E : ℝ) ^ (3 + 0) *
            inverseEndoBase (E := E) R δ ^ (2 * (0 + 1) ^ 2)
            = (Module.finrank ℝ E : ℝ) ^ 3 * inverseEndoBase (E := E) R δ ^ 2 := by norm_num
        rw [hexp]
        have hF3 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := one_le_pow₀ hfr
        have hB2 : (1 : ℝ) ≤ inverseEndoBase (E := E) R δ ^ 2 := one_le_pow₀ hB1
        nlinarith [hF3, hB2]
      nlinarith [h1, h2, h3, sq_nonneg R, hIEnn 0]
    calc 9 * R ^ 2 ≤ inverseEndoJetBound (E := E) R δ 0 * inverseEndoJetBound (E := E) R δ 0 := h9le
      _ ≤ G := hG0
      _ = 1 * G := (one_mul _).symm
      _ ≤ appCcGdiag (E := E) m * G := mul_le_mul_of_nonneg_right hgd1 hGnn
  have hcB16 : (16 : ℝ) ≤ inverseEndoBase (E := E) R δ ^ 2 := by nlinarith [hB4]
  have hclosure := inverseEndo_genConst_succ_closure R δ hR hδ0 hδ1 16 (by norm_num) hcB16 m
  rw [← hGdef] at hclosure
  calc 9 * R ^ 2
        + 4 * (appCcGdiag (E := E) m *
            ∑ i ∈ Finset.range (m + 1), (10 * R ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
        + 4 * (appCcGdiag (E := E) m *
            ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) *
              ∑ l ∈ Finset.range (m + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x))
      ≤ appCcGdiag (E := E) m * G + 4 * (appCcGdiag (E := E) m * G) + 4 * (appCcGdiag (E := E) m * G) := by
        exact add_le_add (add_le_add hsrc (mul_le_mul_of_nonneg_left hb1 (by norm_num)))
          (mul_le_mul_of_nonneg_left hb2 (by norm_num))
    _ = 9 * (appCcGdiag (E := E) m * G) := by ring
    _ ≤ 16 * (appCcGdiag (E := E) m * G) := by
        apply mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hgdnn hGnn)
    _ = 16 * appCcGdiag (E := E) m * G := by ring
    _ ≤ inverseEndoJetBound (E := E) R δ (m + 1) := hclosure

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
