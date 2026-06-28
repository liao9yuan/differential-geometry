import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound

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

noncomputable def inverseEndoBase (R δ : ℝ) : ℝ :=
  2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))

noncomputable def inverseEndoJetBound (R δ : ℝ) (l : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (3 + l) * inverseEndoBase (E := E) R δ ^ (2 * (l + 1) ^ 2)

set_option linter.unusedSectionVars false in
lemma inverseEndoBase_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) :
    0 ≤ inverseEndoBase (E := E) R δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold inverseEndoBase
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · linarith
  · exact div_nonneg zero_le_one h1.le

set_option linter.unusedSectionVars false in
lemma four_le_inverseEndoBase (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (4 : ℝ) ≤ inverseEndoBase (E := E) R δ := by
  have hr_pos : 0 < 1 - δ := by linarith
  have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h2 : (4 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
  have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hr1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hr_pos]; linarith
  unfold inverseEndoBase
  have hstep : (4 : ℝ) * 1 * 1 ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) := by
    apply mul_le_mul _ hr1 (by norm_num) (by positivity)
    apply mul_le_mul h2 hR1 (by norm_num) (by linarith)
  linarith

set_option linter.unusedSectionVars false in
lemma finrankFactor_le_inverseEndoBase (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ inverseEndoBase (E := E) R δ := by
  have hr_pos : 0 < 1 - δ := by linarith
  have hr1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hr2 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hr_pos]; linarith
  have hnn : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by positivity
  unfold inverseEndoBase
  calc 2 * ((Module.finrank ℝ E : ℝ) + 1)
      = 2 * ((Module.finrank ℝ E : ℝ) + 1) * 1 * 1 := by ring
    _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) := by
        apply mul_le_mul _ hr2 (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_left hr1 hnn

lemma inverseEndoJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (l : ℕ) :
    0 ≤ inverseEndoJetBound (E := E) R δ l :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_nonneg (inverseEndoBase_nonneg R δ hR hδ1) _)

set_option linter.unusedSectionVars false in
lemma four_finrankSq_le_inverseEndoBaseSq (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    4 * (Module.finrank ℝ E : ℝ) ^ 2 ≤ inverseEndoBase (E := E) R δ ^ 2 := by
  have hfin2 : 2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ inverseEndoBase (E := E) R δ :=
    finrankFactor_le_inverseEndoBase R δ hR hδ0 hδ1
  have h0 : (0 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by positivity
  have hsq : (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ 2 ≤ inverseEndoBase (E := E) R δ ^ 2 :=
    pow_le_pow_left₀ h0 hfin2 2
  have hF0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  nlinarith [hsq, hF0]

private lemma self_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by norm_num)
    calc k + 1 + 1 ≤ 2 ^ (k + 1) + 1 := by omega
      _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

private lemma diagGrid_quadratic_closure (B0 F : ℝ) (hB0 : (4 : ℝ) ≤ B0) (hF1 : (1 : ℝ) ≤ F)
    (hFB : 4 * F ^ 2 ≤ B0 ^ 2) (m : ℕ) :
    4 * B0 ^ m *
        (∑ i ∈ Finset.range (m + 1),
          F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
            ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) := by
  have hB1 : (1 : ℝ) ≤ B0 := by linarith
  have hB0nn : (0 : ℝ) ≤ B0 := by linarith
  have hF0 : (0 : ℝ) ≤ F := by linarith
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
  have hfinal : 4 * ((m : ℝ) + 1) ^ 2 * F ^ 2 ≤ B0 ^ (3 * m + 4) := by
    have hnat : (m + 1) ^ 2 ≤ 4 ^ (m + 1) := by
      have hself : m + 1 ≤ 2 ^ (m + 1) := self_succ_le_two_pow m
      calc (m + 1) ^ 2 ≤ (2 ^ (m + 1)) ^ 2 := Nat.pow_le_pow_left hself 2
        _ = 2 ^ ((m + 1) * 2) := (pow_mul 2 (m + 1) 2).symm
        _ = 2 ^ (2 * (m + 1)) := by rw [Nat.mul_comm]
        _ = (2 ^ 2) ^ (m + 1) := pow_mul 2 2 (m + 1)
        _ = 4 ^ (m + 1) := by norm_num
    have hcast : ((m : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ (m + 1) := by exact_mod_cast hnat
    have hstep1 : 4 * ((m : ℝ) + 1) ^ 2 * F ^ 2 ≤ ((m : ℝ) + 1) ^ 2 * B0 ^ 2 := by
      nlinarith [sq_nonneg ((m : ℝ) + 1), hFB]
    have h4B : (4 : ℝ) ^ (m + 1) ≤ B0 ^ (m + 1) := pow_le_pow_left₀ (by norm_num) hB0 (m + 1)
    calc 4 * ((m : ℝ) + 1) ^ 2 * F ^ 2
        ≤ ((m : ℝ) + 1) ^ 2 * B0 ^ 2 := hstep1
      _ ≤ (4 : ℝ) ^ (m + 1) * B0 ^ 2 := by
          apply mul_le_mul_of_nonneg_right hcast (by positivity)
      _ ≤ B0 ^ (m + 1) * B0 ^ 2 := by apply mul_le_mul_of_nonneg_right h4B (by positivity)
      _ = B0 ^ (m + 3) := by rw [← pow_add]
      _ ≤ B0 ^ (3 * m + 4) := pow_le_pow_right₀ hB1 (by omega)
  have hFsplit : F ^ (6 + m) = F ^ 2 * F ^ (m + 4) := by rw [← pow_add]; congr 1; omega
  calc 4 * B0 ^ m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ 4 * B0 ^ m * (((m : ℝ) + 1) ^ 2 * (F ^ (6 + m) * B0 ^ (2 * (m + 1) ^ 2 + 2))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (4 * ((m : ℝ) + 1) ^ 2 * F ^ 2) *
          (F ^ (m + 4) * (B0 ^ m * B0 ^ (2 * (m + 1) ^ 2 + 2))) := by rw [hFsplit]; ring
    _ = (4 * ((m : ℝ) + 1) ^ 2 * F ^ 2) *
          (F ^ (m + 4) * B0 ^ (m + (2 * (m + 1) ^ 2 + 2))) := by rw [← pow_add]
    _ ≤ B0 ^ (3 * m + 4) * (F ^ (m + 4) * B0 ^ (m + (2 * (m + 1) ^ 2 + 2))) :=
        mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = F ^ (m + 4) * B0 ^ ((3 * m + 4) + (m + (2 * (m + 1) ^ 2 + 2))) := by
        rw [pow_add B0 (3 * m + 4) (m + (2 * (m + 1) ^ 2 + 2))]; ring
    _ = F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) := by
        rw [show m + 4 = 3 + (m + 1) from by omega,
          show (3 * m + 4) + (m + (2 * (m + 1) ^ 2 + 2)) = 2 * (m + 2) ^ 2 from by ring]

private lemma inverseEndo_succ_closure (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (m : ℕ) :
    4 * appCcGdiag (E := E) m *
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
  calc 4 * appCcGdiag (E := E) m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2))
      ≤ 4 * B0 ^ m *
          (∑ i ∈ Finset.range (m + 1),
            F ^ (3 + i) * B0 ^ (2 * (i + 1) ^ 2) *
              ∑ l ∈ Finset.range (m + 1 - i), F ^ (3 + l) * B0 ^ (2 * (l + 1) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ hsum_nn
        exact mul_le_mul_of_nonneg_left hgrid_le (by norm_num)
    _ ≤ F ^ (3 + (m + 1)) * B0 ^ (2 * (m + 2) ^ 2) :=
        diagGrid_quadratic_closure B0 F hB0 hF1 hFB m

private theorem rfns_iteratedCovGrad_flatArmCoeffCc_base
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (kind : Bool) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 2 0
          (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) ≤
      inverseEndoJetBound (E := E) R δ 0 := by
  sorry

private theorem rfns_iteratedCovGrad_flatArmCoeffCc_succ_step
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (kind : Bool) (m : ℕ) (hm : m + 1 ≤ a) (x : M)
    (hIH : ∀ j : ℕ, j ≤ m →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j
            (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ j) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 2 (m + 1)
          (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) ≤
      inverseEndoJetBound (E := E) R δ (m + 1) := by
  sorry

theorem rfns_iteratedCovGrad_flatArmCoeffCc_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (kind : Bool) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i hstrong =>
    intro hi_le x
    match i, hi_le with
    | 0, _ =>
        exact rfns_iteratedCovGrad_flatArmCoeffCc_base (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
          hTjet kind x
    | (m + 1), hm =>
        exact rfns_iteratedCovGrad_flatArmCoeffCc_succ_step (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
          hTjet kind m hm x (fun j hj => hstrong j (by omega) (by omega) x)

private theorem rfns_iteratedCovGrad_sharpFlatEndoCc_allOrders
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a + 1) (x : M) :
    ∀ k : ℕ, k ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 1 k
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k hstrong =>
    intro hk_le
    match k, hk_le with
    | 0, _ =>
        have hbase := rfns_sharpFlatEndoCc_le_of_lt_one (I := I) g₀ hδ0 hδ1 g₁ T htie
          (le_refl δ) hδ0 hδ x
        have hb2 : (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 ≤
            inverseEndoJetBound (E := E) R δ 0 := by
          have hr2_nn : 0 ≤ (1 / (1 - δ)) ^ 2 := sq_nonneg _
          have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
            have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
          have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by linarith
          have hb_old : (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 ≤
              (inverseEndoBase (E := E) R δ) ^ 2 := by
            rw [inverseEndoBase]
            have h1 : (Module.finrank ℝ E : ℝ)
                ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) := by nlinarith [hfr, hR]
            have hfactor : (Module.finrank ℝ E : ℝ) ^ 2
                ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R)) ^ 2 :=
              pow_le_pow_left₀ h0 h1 2
            calc (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2
                ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R)) ^ 2 * (1 / (1 - δ)) ^ 2 :=
                  mul_le_mul_of_nonneg_right hfactor hr2_nn
              _ = (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))) ^ 2 := by ring
          have hQ0 : inverseEndoJetBound (E := E) R δ 0
              = (Module.finrank ℝ E : ℝ) ^ 3 * (inverseEndoBase (E := E) R δ) ^ 2 := by
            unfold inverseEndoJetBound; norm_num
          rw [hQ0]
          have hBsq_nn : 0 ≤ (inverseEndoBase (E := E) R δ) ^ 2 := sq_nonneg _
          have hF3 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by
            simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hfr 3
          calc (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2
              ≤ (inverseEndoBase (E := E) R δ) ^ 2 := hb_old
            _ = 1 * (inverseEndoBase (E := E) R δ) ^ 2 := by ring
            _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (inverseEndoBase (E := E) R δ) ^ 2 :=
                mul_le_mul_of_nonneg_right hF3 hBsq_nn
        rw [iteratedCovGrad_zero]
        exact le_trans hbase hb2
    | (m + 1), hk_le =>
        have hm1_le_i : m + 1 ≤ i := hk_le
        have hIH : ∀ j : ℕ, j ≤ m →
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
                ((iteratedCovGrad (I := I) g₀ 1 1 j
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
              inverseEndoJetBound (E := E) R δ j :=
          fun j hj => hstrong j (by omega) (by omega)
        have harm := rfns_iteratedCovGrad_sharpFlatEndoCc_succ_le_arms (I := I) g₀ g₁ m x
        have hkind : ∀ kind : Bool,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 1 2 m
                  (flatArmCc (I := I) g₀ g₁ kind)).toSection x) ≤
              appCcGdiag (E := E) m *
                ∑ i' ∈ Finset.range (m + 1),
                  inverseEndoJetBound (E := E) R δ i' *
                    ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l := by
          intro kind
          rw [flatArmCc_eq_appCcRS_flatArmCoeffCc (I := I) g₀ g₁ kind]
          refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
            (I := I) g₀ m 1 1 2 (flatArmCoeffCc (I := I) g₀ g₁ kind)
            (sharpFlatEndoCc (I := I) g₀ g₁) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) m)
          refine Finset.sum_le_sum ?_
          intro i' hi'
          have hi'm : i' ≤ m := by rw [Finset.mem_range] at hi'; omega
          have hcoeff := rfns_iteratedCovGrad_flatArmCoeffCc_le (I := I) g₀ g₁ a T htie hR
            hδ0 hδ1 hδ hTjet kind i' (by omega) x
          have hcoeff_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 1 2 i'
                (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) :=
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i') x _
          have hQsum_nn : 0 ≤ ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l :=
            Finset.sum_nonneg (fun l _ => inverseEndoJetBound_nonneg R δ hR hδ1 l)
          have hinner : ∑ l ∈ Finset.range (m + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 l
                    (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
              ≤ ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hlm : l ≤ m := by rw [Finset.mem_range] at hl; omega
            exact hIH l hlm
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i'
                    (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) *
                ∑ l ∈ Finset.range (m + 1 - i'),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l
                      (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
              ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
                    ((iteratedCovGrad (I := I) g₀ 1 2 i'
                      (flatArmCoeffCc (I := I) g₀ g₁ kind)).toSection x) *
                  ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l :=
                mul_le_mul_of_nonneg_left hinner hcoeff_nn
            _ ≤ inverseEndoJetBound (E := E) R δ i' *
                  ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l :=
                mul_le_mul_of_nonneg_right hcoeff hQsum_nn
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
                ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
            ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + m) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 m
                    (flatArmCc (I := I) g₀ g₁ true)).toSection x) +
                2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + m) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 m
                    (flatArmCc (I := I) g₀ g₁ false)).toSection x) := harm
          _ ≤ 2 * (appCcGdiag (E := E) m *
                  ∑ i' ∈ Finset.range (m + 1), inverseEndoJetBound (E := E) R δ i' *
                    ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l) +
                2 * (appCcGdiag (E := E) m *
                  ∑ i' ∈ Finset.range (m + 1), inverseEndoJetBound (E := E) R δ i' *
                    ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (hkind true) (by norm_num)
              · exact mul_le_mul_of_nonneg_left (hkind false) (by norm_num)
          _ = 4 * appCcGdiag (E := E) m *
                  ∑ i' ∈ Finset.range (m + 1), inverseEndoJetBound (E := E) R δ i' *
                    ∑ l ∈ Finset.range (m + 1 - i'), inverseEndoJetBound (E := E) R δ l := by ring
          _ ≤ inverseEndoJetBound (E := E) R δ (m + 1) :=
              inverseEndo_succ_closure R δ hR hδ0 hδ1 m

theorem rfns_iteratedCovGrad_sharpFlatEndoCc_uniform_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ l : ℕ, l ≤ a + 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        inverseEndoJetBound (E := E) R δ l := by
  intro l hl x
  exact rfns_iteratedCovGrad_sharpFlatEndoCc_allOrders (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
    hTjet l hl x l (le_refl l)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
