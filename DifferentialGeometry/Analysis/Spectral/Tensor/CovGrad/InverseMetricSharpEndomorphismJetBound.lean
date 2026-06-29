import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 6400000

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

private noncomputable def invSharpBase (R δ : ℝ) : ℝ :=
  2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))

private noncomputable def invSharpJetBound (R δ : ℝ) (l : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (3 + l) * invSharpBase (E := E) R δ ^ (2 * (l + 1) ^ 2)

set_option linter.unusedSectionVars false in
private lemma invSharpBase_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) :
    0 ≤ invSharpBase (E := E) R δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold invSharpBase
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · linarith
  · exact div_nonneg zero_le_one h1.le

private lemma invSharpJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (l : ℕ) :
    0 ≤ invSharpJetBound (E := E) R δ l :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_nonneg (invSharpBase_nonneg R δ hR hδ1) _)

set_option linter.unusedSectionVars false in
private lemma four_le_invSharpBase (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (4 : ℝ) ≤ invSharpBase (E := E) R δ := by
  have hr_pos : 0 < 1 - δ := by linarith
  have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h2 : (4 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
  have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hr1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hr_pos]; linarith
  unfold invSharpBase
  have hstep : (4 : ℝ) * 1 * 1 ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) := by
    apply mul_le_mul _ hr1 (by norm_num) (by positivity)
    apply mul_le_mul h2 hR1 (by norm_num) (by linarith)
  linarith

set_option linter.unusedSectionVars false in
private lemma finrankFactor_le_invSharpBase (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ invSharpBase (E := E) R δ := by
  have hr_pos : 0 < 1 - δ := by linarith
  have hr1 : (1 : ℝ) ≤ 1 + R := by linarith
  have hr2 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hr_pos]; linarith
  have hnn : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by positivity
  unfold invSharpBase
  calc 2 * ((Module.finrank ℝ E : ℝ) + 1)
      = 2 * ((Module.finrank ℝ E : ℝ) + 1) * 1 * 1 := by ring
    _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) := by
        apply mul_le_mul _ hr2 (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_left hr1 hnn

set_option linter.unusedSectionVars false in
private lemma four_finrankSq_le_invSharpBaseSq (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    4 * (Module.finrank ℝ E : ℝ) ^ 2 ≤ invSharpBase (E := E) R δ ^ 2 := by
  have hfin2 : 2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ invSharpBase (E := E) R δ :=
    finrankFactor_le_invSharpBase R δ hR hδ0 hδ1
  have h0 : (0 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by positivity
  have hsq : (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ 2 ≤ invSharpBase (E := E) R δ ^ 2 :=
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

set_option linter.unusedSectionVars false in
private lemma invSharp_leibniz_closure (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (m : ℕ) :
    (Module.finrank ℝ E : ℝ) ^ (m + 1) * invSharpJetBound (E := E) R δ 0 *
        ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k * R ^ 2) *
            invSharpJetBound (E := E) R δ k)
      ≤ invSharpJetBound (E := E) R δ (m + 1) := by
  have hF1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hF0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by linarith
  have hrpos : (0 : ℝ) < 1 - δ := by linarith
  have hu1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hrpos]; linarith
  have hRv : (0 : ℝ) ≤ 1 + R := by linarith
  have hB_ge : 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) ≤ invSharpBase (E := E) R δ := by
    rw [invSharpBase]
    exact le_mul_of_one_le_right
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hRv) hu1
  have hB4 : (4 : ℝ) ≤ invSharpBase (E := E) R δ := four_le_invSharpBase R δ hR hδ0 hδ1
  have hB1 : (1 : ℝ) ≤ invSharpBase (E := E) R δ := by linarith
  have hB0 : (0 : ℝ) ≤ invSharpBase (E := E) R δ := by linarith
  set F := (Module.finrank ℝ E : ℝ) with hFdef
  set B := invSharpBase (E := E) R δ with hBdef
  have hF1pos : (0 : ℝ) ≤ F + 1 := by linarith
  -- key reduced inequality
  have hnat : (m + 1) ^ 2 ≤ 4 ^ (m + 1) := by
    have hself : m + 1 ≤ 2 ^ (m + 1) := self_succ_le_two_pow m
    calc (m + 1) ^ 2 ≤ (2 ^ (m + 1)) ^ 2 := Nat.pow_le_pow_left hself 2
      _ = 2 ^ ((m + 1) * 2) := (pow_mul 2 (m + 1) 2).symm
      _ = 2 ^ (2 * (m + 1)) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ (m + 1) := pow_mul 2 2 (m + 1)
      _ = 4 ^ (m + 1) := by norm_num
  have hcast : ((m : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ (m + 1) := by exact_mod_cast hnat
  have hkey : ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2 * F ^ (2 * m + 3) ≤ B ^ (4 * m + 4) := by
    have hstep1 : ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2 * F ^ (2 * m + 3)
        ≤ 4 ^ (m + 1) * 4 ^ (m + 1) * (1 + R) ^ 2 * (F + 1) ^ (2 * m + 3) := by
      have hR2 : R ^ 2 ≤ (1 + R) ^ 2 := by nlinarith [sq_nonneg R]
      have hFF : F ^ (2 * m + 3) ≤ (F + 1) ^ (2 * m + 3) :=
        pow_le_pow_left₀ hF0 (by linarith) _
      have hA : ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) ≤ 4 ^ (m + 1) * 4 ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      have hB' : ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2
          ≤ 4 ^ (m + 1) * 4 ^ (m + 1) * (1 + R) ^ 2 :=
        mul_le_mul hA hR2 (sq_nonneg R) (by positivity)
      exact mul_le_mul hB' hFF (pow_nonneg hF0 _) (by positivity)
    have hstep2 : 4 ^ (m + 1) * 4 ^ (m + 1) * (1 + R) ^ 2 * (F + 1) ^ (2 * m + 3)
        ≤ 2 ^ (4 * m + 4) * (F + 1) ^ (4 * m + 4) * (1 + R) ^ (4 * m + 4) := by
      have h2 : (4 : ℝ) ^ (m + 1) * 4 ^ (m + 1) = 2 ^ (4 * m + 4) := by
        rw [← pow_add, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul]
        congr 1; omega
      have hFexp : (F + 1) ^ (2 * m + 3) ≤ (F + 1) ^ (4 * m + 4) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hRexp : (1 + R) ^ 2 ≤ (1 + R) ^ (4 * m + 4) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      rw [h2]
      calc 2 ^ (4 * m + 4) * (1 + R) ^ 2 * (F + 1) ^ (2 * m + 3)
          ≤ 2 ^ (4 * m + 4) * (1 + R) ^ (4 * m + 4) * (F + 1) ^ (4 * m + 4) := by
            gcongr
        _ = 2 ^ (4 * m + 4) * (F + 1) ^ (4 * m + 4) * (1 + R) ^ (4 * m + 4) := by ring
    have hstep3 : 2 ^ (4 * m + 4) * (F + 1) ^ (4 * m + 4) * (1 + R) ^ (4 * m + 4)
        ≤ B ^ (4 * m + 4) := by
      have hbase : (2 : ℝ) * (F + 1) * (1 + R) ≤ B := hB_ge
      have hbnn : (0 : ℝ) ≤ 2 * (F + 1) * (1 + R) :=
        mul_nonneg (mul_nonneg (by norm_num) hF1pos) hRv
      calc 2 ^ (4 * m + 4) * (F + 1) ^ (4 * m + 4) * (1 + R) ^ (4 * m + 4)
          = (2 * (F + 1) * (1 + R)) ^ (4 * m + 4) := by rw [mul_pow, mul_pow]
        _ ≤ B ^ (4 * m + 4) := pow_le_pow_left₀ hbnn hbase _
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  -- sum bound
  have hsum : (∑ k ∈ Finset.range (m + 1),
        (4 ^ (m + 1) * F ^ k * R ^ 2) * invSharpJetBound (E := E) R δ k)
      ≤ (m + 1 : ℝ) *
        (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2))) := by
    have hterm : ∀ k ∈ Finset.range (m + 1),
        (4 ^ (m + 1) * F ^ k * R ^ 2) * invSharpJetBound (E := E) R δ k
          ≤ 4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2)) := by
      intro k hk
      have hkm : k ≤ m := by rw [Finset.mem_range] at hk; omega
      rw [invSharpJetBound]
      have e1 : F ^ k ≤ F ^ m := pow_le_pow_right₀ hF1 hkm
      have e2 : F ^ (3 + k) ≤ F ^ (3 + m) := pow_le_pow_right₀ hF1 (by omega)
      have e3 : B ^ (2 * (k + 1) ^ 2) ≤ B ^ (2 * (m + 1) ^ 2) :=
        pow_le_pow_right₀ hB1 (by gcongr)
      gcongr
    calc (∑ k ∈ Finset.range (m + 1),
            (4 ^ (m + 1) * F ^ k * R ^ 2) * invSharpJetBound (E := E) R δ k)
        ≤ (Finset.range (m + 1)).card •
            (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2))) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (m + 1 : ℝ) *
            (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2))) := by
          rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
  -- assemble
  have hQ0 : invSharpJetBound (E := E) R δ 0 = F ^ 3 * B ^ 2 := by
    rw [hFdef, hBdef, invSharpJetBound]; norm_num
  have ha_nn : (0 : ℝ) ≤ F ^ (m + 1) * invSharpJetBound (E := E) R δ 0 := by
    rw [hQ0]
    exact mul_nonneg (pow_nonneg hF0 _) (mul_nonneg (pow_nonneg hF0 _) (pow_nonneg hB0 _))
  have hmono : (m + 1 : ℝ) *
        (∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * F ^ k * R ^ 2) * invSharpJetBound (E := E) R δ k)
      ≤ (m + 1 : ℝ) *
        ((m + 1 : ℝ) *
          (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2)))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hmain : F ^ (m + 1) * invSharpJetBound (E := E) R δ 0 *
        ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * F ^ k * R ^ 2) * invSharpJetBound (E := E) R δ k)
      ≤ F ^ (m + 1) * invSharpJetBound (E := E) R δ 0 *
        ((m + 1 : ℝ) * ((m + 1 : ℝ) *
          (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2))))) :=
    mul_le_mul_of_nonneg_left hmono ha_nn
  refine le_trans hmain ?_
  rw [hQ0]
  have hFc : F ^ (m + 1) * F ^ 3 * F ^ m * F ^ (3 + m) = F ^ (m + 4) * F ^ (2 * m + 3) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hBc : B ^ 2 * B ^ (2 * (m + 1) ^ 2) = B ^ (2 + 2 * (m + 1) ^ 2) := by rw [← pow_add]
  have hLHS_eq : F ^ (m + 1) * (F ^ 3 * B ^ 2) *
        ((m + 1 : ℝ) * ((m + 1 : ℝ) *
          (4 ^ (m + 1) * F ^ m * R ^ 2 * (F ^ (3 + m) * B ^ (2 * (m + 1) ^ 2)))))
      = ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2 *
          (F ^ (m + 1) * F ^ 3 * F ^ m * F ^ (3 + m)) * (B ^ 2 * B ^ (2 * (m + 1) ^ 2)) := by
    ring
  rw [hLHS_eq, hFc, hBc]
  have hQm1 : invSharpJetBound (E := E) R δ (m + 1)
      = F ^ (m + 4) * B ^ (2 + 2 * (m + 1) ^ 2) * B ^ (4 * m + 4) := by
    rw [invSharpJetBound, mul_assoc, ← pow_add]
    congr 1
    · congr 1; omega
    · congr 1; ring
  rw [hQm1]
  have hLHS_eq2 : ((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2 *
        (F ^ (m + 4) * F ^ (2 * m + 3)) * B ^ (2 + 2 * (m + 1) ^ 2)
      = F ^ (m + 4) * B ^ (2 + 2 * (m + 1) ^ 2) *
          (((m : ℝ) + 1) ^ 2 * 4 ^ (m + 1) * R ^ 2 * F ^ (2 * m + 3)) := by ring
  rw [hLHS_eq2]
  exact mul_le_mul_of_nonneg_left hkey
    (mul_nonneg (pow_nonneg hF0 _) (pow_nonneg hB0 _))

set_option linter.unusedVariables false in
private lemma rfns_iteratedCovGrad_sharpFlatEndoCc_leibniz_grid_bound
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (m : ℕ) (hm : m + 1 ≤ a + 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ (m + 1) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) *
        ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k * R ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
              ((iteratedCovGrad (I := I) g₀ 1 1 k
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) := by
  sorry

set_option linter.unusedVariables false in
private theorem rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_succ_step
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (m : ℕ) (hm : m + 1 ≤ a + 1) (x : M)
    (hIH : ∀ j : ℕ, j ≤ m →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        invSharpJetBound (E := E) R δ j) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      invSharpJetBound (E := E) R δ (m + 1) := by
  have hgrid := rfns_iteratedCovGrad_sharpFlatEndoCc_leibniz_grid_bound (I := I) g₀ g₁ a T htie
    hR hδ0 hδ1 hδ hTjet m hm x
  refine le_trans hgrid ?_
  refine le_trans ?_ (invSharp_leibniz_closure (E := E) R δ hR hδ0 hδ1 m)
  have hb0 := hIH 0 (Nat.zero_le m)
  have hc_nn : (0 : ℝ) ≤ (m + 1 : ℝ) *
      ∑ k ∈ Finset.range (m + 1),
        (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k * R ^ 2) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
            ((iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _)
  have hb_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ (m + 1) * invSharpJetBound (E := E) R δ 0 :=
    mul_nonneg (by positivity) (invSharpJetBound_nonneg R δ hR hδ1 0)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hb0 (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := by rw [Finset.mem_range] at hk; omega
    exact mul_le_mul_of_nonneg_left (hIH k hkm) (by positivity)
  · exact hc_nn
  · exact hb_nn

private theorem rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_base
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 1 0
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      invSharpJetBound (E := E) R δ 0 := by
  rw [iteratedCovGrad_zero]
  have hbase := rfns_sharpFlatEndoCc_le_of_lt_one (I := I) g₀ (δ₀ := δ) hδ0 hδ1 g₁ T htie
    (le_refl δ) hδ0 hδ x
  have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by linarith
  have hr2_nn : 0 ≤ (1 / (1 - δ)) ^ 2 := sq_nonneg _
  have hb_old : (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 ≤
      (invSharpBase (E := E) R δ) ^ 2 := by
    rw [invSharpBase]
    have h1 : (Module.finrank ℝ E : ℝ)
        ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) := by nlinarith [hfr, hR]
    have hfactor : (Module.finrank ℝ E : ℝ) ^ 2
        ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R)) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    calc (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2
        ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R)) ^ 2 * (1 / (1 - δ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor hr2_nn
      _ = (2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))) ^ 2 := by ring
  have hQ0 : invSharpJetBound (E := E) R δ 0
      = (Module.finrank ℝ E : ℝ) ^ 3 * (invSharpBase (E := E) R δ) ^ 2 := by
    unfold invSharpJetBound; norm_num
  rw [hQ0]
  have hBsq_nn : 0 ≤ (invSharpBase (E := E) R δ) ^ 2 := sq_nonneg _
  have hF3 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hfr 3
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ)) ^ 2 := hbase
    _ ≤ (invSharpBase (E := E) R δ) ^ 2 := hb_old
    _ = 1 * (invSharpBase (E := E) R δ) ^ 2 := by ring
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (invSharpBase (E := E) R δ) ^ 2 :=
        mul_le_mul_of_nonneg_right hF3 hBsq_nn

theorem rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_le
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
        invSharpJetBound (E := E) R δ l := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l hstrong =>
    intro hl x
    match l, hl with
    | 0, _ =>
        exact rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_base (I := I) g₀ g₁ T htie hR hδ0 hδ1
          hδ x
    | (m + 1), hm =>
        exact rfns_iteratedCovGrad_sharpFlatEndoCc_jetBound_succ_step (I := I) g₀ g₁ a T htie hR
          hδ0 hδ1 hδ hTjet m hm x (fun j hj => hstrong j (by omega) (by omega) x)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
