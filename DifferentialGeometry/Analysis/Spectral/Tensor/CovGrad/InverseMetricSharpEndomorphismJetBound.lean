import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 6400000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
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

set_option linter.unusedSectionVars false in
private lemma rfns_neg_fib (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [show (-(TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
        (x := x) v)) = ((-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v) from by rw [neg_one_smul]]
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma slotExtendFib_comp (g : SmoothRiemannianMetric I M) (p q r : ℕ) (x : M)
    (A : Tensor0SSpace p I x →L[ℝ] Tensor0SSpace q I x)
    (B : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace p I x) :
    (slotExtendFib (I := I) (M := M) g p q x A).comp
        (slotExtendFib (I := I) (M := M) g r p x B) =
      slotExtendFib (I := I) (M := M) g r q x (A.comp B) := by
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  rw [slotExtendFib_apply, slotExtendFib_apply, slotExtendFib_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.comp_assoc]

set_option linter.unusedSectionVars false in
private lemma slotExtendFib_id_eq (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    slotExtendFib (I := I) (M := M) g r r x (ContinuousLinearMap.id ℝ (Tensor0SSpace r I x)) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace (r + 1) I x) := by
  apply ContinuousLinearMap.ext
  intro D
  rw [slotExtendFib_apply, ContinuousLinearMap.id_comp,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

set_option linter.unusedSectionVars false in
private lemma appCcLeibnizPsi_diag_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ i i =
      slotExtendIter (I := I) (M := M) g b c i Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hss : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          (if i + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (i + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (i + 1))
            else 0) +
            castSrcCc g (c + (i + 1)) (by omega : (b + i) + 1 = b + (i + 1))
              (castRankCc_db g ((b + i) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + i) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i))) := rfl
      rw [hss, if_neg (by omega : ¬ i + 1 < i + 1), zero_add]
      rw [show castSrcCc g (c + (i + 1)) (by omega : (b + i) + 1 = b + (i + 1))
            (castRankCc_db g ((b + i) + 1) (by omega : (c + i) + 1 = c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + i) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i))) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) from by
        rw [castRankCc_db, castSrcCc]]
      rw [show slotExtendIter (I := I) (M := M) g b c (i + 1) Φ =
            slotExtend (I := I) (M := M) g (b + i) (c + i)
              (slotExtendIter (I := I) (M := M) g b c i Φ) from rfl, ih]

set_option linter.unusedSectionVars false in
private lemma sharpFlatEndoCc_self_comp_eq_id (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace 1 I x) := by
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.id_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x om) from by
    rw [sharpFlatEndoCc_toSection]; rfl]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om]

set_option linter.unusedSectionVars false in
private lemma omRecoverEndoCc_comp_sharpFlatEndoCc_self (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x).comp
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace 1 I x) := by
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from by
    rw [sharpFlatEndoCc_toSection]; rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x)
        (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)) =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x
        (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om))) from by
    rw [omRecoverEndoCc_toSection]; rfl]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₁ x om]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_omRecover_sharpFlat_eq_idEndo (g₀ g₁ : SmoothRiemannianMetric I M) :
    appCcRS (I := I) (M := M) g₀ 1 1 1
        (omRecoverEndoCc (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) =
      sharpFlatEndoCc (I := I) g₀ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection]
  rw [omRecoverEndoCc_comp_sharpFlatEndoCc_self (I := I) g₀ g₁ x]
  exact (sharpFlatEndoCc_self_comp_eq_id (I := I) g₀ x).symm

set_option backward.isDefEq.respectTransparency false in
private lemma flatArmVec_self_eq_zero' (g₀ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₀ kind x om v0 = 0 := by
  have hcd : PDE.DeTurck.connDiff (I := I) g₀ g₀ x = 0 := by
    rw [PDE.DeTurck.connDiff_self]; rfl
  cases kind with
  | true =>
      simp only [flatArmVec, if_true, hcd, ContinuousLinearMap.zero_apply, neg_zero]
  | false =>
      simp only [flatArmVec, if_neg (by decide : ¬ (false = true)), hcd]
      simp

set_option backward.isDefEq.respectTransparency false in
private lemma flatArmFib_self_eq_zero' (g₀ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) :
    flatArmFib (I := I) g₀ g₀ kind x = (0 : TensorRSSpace 1 2 I x) := by
  apply tensorRSSpace_ext 1 2 x
  intro om
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (0 : TensorRSSpace 1 2 I x)) om = (0 : Tensor0SSpace 2 I x) from rfl]
  rw [flatArmFib_apply]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [flatArmPairing_apply, flatArmVec_self_eq_zero', map_zero, ContinuousLinearMap.zero_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma flatArmCc_self_eq_zero' (g₀ : SmoothRiemannianMetric I M) (kind : Bool) :
    flatArmCc (I := I) g₀ g₀ kind = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [flatArmCc_toSection, flatArmFib_self_eq_zero']
  simp

private lemma covGrad_sharpFlatEndoCc_self_eq_zero' (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1 (sharpFlatEndoCc (I := I) g₀ g₀) = 0 := by
  rw [covGrad_sharpFlatEndoCc_eq_arms (I := I) g₀ g₀]
  rw [flatArmCc_self_eq_zero', flatArmCc_self_eq_zero', add_zero]

private lemma iteratedCovGrad_zero_tensor' (g₀ : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s m (0 : SmoothCcTensor g₀ r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

private lemma iteratedCovGrad_eq_zero_of_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (X : SmoothCcTensor g₀ r s)
    (hX : covGrad (I := I) (M := M) g₀ r s X = 0) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s (m + 1) X = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; exact hX
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

private lemma iteratedCovGrad_sharpFlatEndoCc_self_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1) (sharpFlatEndoCc (I := I) g₀ g₀) = 0 :=
  iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) g₀ 1 1
    (sharpFlatEndoCc (I := I) g₀ g₀) (covGrad_sharpFlatEndoCc_self_eq_zero' (I := I) g₀) m

set_option linter.unusedSectionVars false in
private lemma sharpFlatEndoCc_comp_omRecoverEndoCc_self (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x).comp
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace 1 I x) := by
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) from by
    rw [omRecoverEndoCc_toSection]; rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        (g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om)) =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om))) from by
    rw [sharpFlatEndoCc_toSection]; rfl]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om]

set_option linter.unusedSectionVars false in
private lemma slotExtendIter_sharpFlat_omRecover_comp_eq_id (g₀ g₁ : SmoothRiemannianMetric I M)
    (w : ℕ) (x : M) :
    (show Tensor0SSpace (1 + w) I x →L[ℝ] Tensor0SSpace (1 + w) I x from
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x).comp
      (show Tensor0SSpace (1 + w) I x →L[ℝ] Tensor0SSpace (1 + w) I x from
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w
          (omRecoverEndoCc (I := I) g₀ g₁)).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace (1 + w) I x) := by
  induction w with
  | zero => exact sharpFlatEndoCc_comp_omRecoverEndoCc_self (I := I) g₀ g₁ x
  | succ w ih =>
      rw [show slotExtendIter (I := I) (M := M) g₀ 1 1 (w + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁) =
          slotExtend (I := I) (M := M) g₀ (1 + w) (1 + w)
            (slotExtendIter (I := I) (M := M) g₀ 1 1 w (sharpFlatEndoCc (I := I) g₀ g₁)) from rfl]
      rw [show slotExtendIter (I := I) (M := M) g₀ 1 1 (w + 1)
            (omRecoverEndoCc (I := I) g₀ g₁) =
          slotExtend (I := I) (M := M) g₀ (1 + w) (1 + w)
            (slotExtendIter (I := I) (M := M) g₀ 1 1 w (omRecoverEndoCc (I := I) g₀ g₁)) from rfl]
      rw [slotExtend_toSection, slotExtend_toSection, slotExtendFib_comp, ih]
      exact slotExtendFib_id_eq (I := I) (M := M) g₀ (1 + w) x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma master_isolation (g₀ g₁ : SmoothRiemannianMetric I M) (w : ℕ)
    (X : SmoothCcTensor g₀ 1 (1 + w)) :
    appCcRS (I := I) (M := M) g₀ 1 (1 + w) (1 + w)
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w (sharpFlatEndoCc (I := I) g₀ g₁))
        (appCcRS (I := I) (M := M) g₀ 1 (1 + w) (1 + w)
          (slotExtendIter (I := I) (M := M) g₀ 1 1 w (omRecoverEndoCc (I := I) g₀ g₁)) X) = X := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [slotExtendIter_sharpFlat_omRecover_comp_eq_id (I := I) g₀ g₁ w x]
  rw [ContinuousLinearMap.id_comp]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_exp_congr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) {e₁ e₂ : ℕ} (h : e₁ = e₂) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + e₁) x
        ((iteratedCovGrad (I := I) g r s e₁ Φ).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + e₂) x
        ((iteratedCovGrad (I := I) g r s e₂ Φ).toSection x) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
  (ccTensorBilin ccTensorModel ccTensorMultilinear ccTensorBilin_apply) in
set_option linter.unusedSectionVars false in
private lemma unitModel_eq_ccTensorBilin_loc (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma omRecoverEndoCc_eq_idEndo_add_raise
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    omRecoverEndoCc (I := I) g₀ g₁ =
      sharpFlatEndoCc (I := I) g₀ g₀ +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ T) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  rw [show (sharpFlatEndoCc (I := I) g₀ g₀ +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ T)).toSection x =
      (sharpFlatEndoCc (I := I) g₀ g₀).toSection x +
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ T)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((sharpFlatEndoCc (I := I) g₀ g₀).toSection x +
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ T)).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om +
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ T)).toSection x) om from rfl]
  have hL : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [omRecoverEndoCc_toSection]; rfl
  have hS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [sharpFlatEndoCc_toSection]; rfl
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) om) w =
      cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om) w +
        cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) om) w from by
    rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
      ← cotangentToDualLinear_apply, map_add, LinearMap.add_apply]]
  rw [hL, cotangentToDual_g0FlatCLM]
  rw [hS, cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (inverseMetricSharpFib (I := I) g₀ x om) w from by
    rw [cotangentToDual_apply]
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (symmS (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (symmS (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)))
          (fun _ : Fin 1 => w) from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
          (symmS (I := I) (M := M) g₀ T).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun _ : Fin 1 => (show E from w))) =
        unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
          ![inverseMetricSharpFib (I := I) g₀ x om, w] from by
      rw [unitModel]
      congr 1
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Fin.cons_zero, Matrix.cons_val_zero]
      · simp only [Fin.cons_succ]
        fin_cases j
        rfl]
    rw [unitModel_eq_ccTensorBilin_loc, ccTensorBilin_symmS]]
  rw [htie]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_omRecoverEndoCc_succ_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ}
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (j : ℕ) (hj : j + 1 ≤ a + 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (omRecoverEndoCc (I := I) g₀ g₁)).toSection x) ≤ R ^ 2 := by
  rw [omRecoverEndoCc_eq_idEndo_add_raise (I := I) (M := M) g₀ g₁ T htie, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 1 (j + 1) (sharpFlatEndoCc (I := I) g₀ g₀) +
        iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ T))).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 1 (j + 1) (sharpFlatEndoCc (I := I) g₀ g₀)).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ T))).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [iteratedCovGrad_sharpFlatEndoCc_self_eq_zero (I := I) g₀ j]
  rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (j + 1))).toSection x) =
      (0 : TensorRSSpace 1 (1 + (j + 1)) I x) from by rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [zero_add]
  refine le_trans (le_of_eq ?_)
    (rfns_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ a T hTjet (j + 1) hj x)
  exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (symmS (I := I) (M := M) g₀ T) (j + 1) x

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_appCcLeibnizPsi_le
    (g : SmoothRiemannianMetric I M) (b c : ℕ) (Φ : SmoothCcTensor g b c) (x : M) :
    ∀ i k p d : ℕ, k + d = i →
      riemannianFiberNormSq (I := I) (M := M) g (b + k) ((c + i) + p) x
          ((iteratedCovGrad (I := I) g (b + k) (c + i) p
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k)).toSection x) ≤
        (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ k *
          riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
            ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
  intro i
  induction i with
  | zero =>
    intro k p d hkd
    obtain rfl : k = 0 := by omega
    obtain rfl : d = 0 := by omega
    have happ : appCcLeibnizPsi (I := I) (M := M) g b c Φ 0 0 = Φ := rfl
    rw [happ]
    simp only [pow_zero, one_mul]
    exact le_of_eq rfl
  | succ i ih =>
    intro k p d hkd
    match k, hkd with
    | 0, hkd =>
      obtain rfl : d = i + 1 := by omega
      have h0 : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) 0 =
          covGrad (I := I) (M := M) g (b + 0) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) := rfl
      rw [h0]
      have hcomm : riemannianFiberNormSq (I := I) (M := M) g (b + 0) ((c + (i + 1)) + p) x
            ((iteratedCovGrad (I := I) g (b + 0) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + 0) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g (b + 0) ((c + i) + (p + 1)) x
            ((iteratedCovGrad (I := I) g (b + 0) (c + i) (p + 1)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0)).toSection x) :=
        rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g (b + 0) (c + i) p
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) x
      rw [hcomm]
      have hih := ih 0 (p + 1) i (by omega)
      rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g b c Φ x
        (show (p + 1) + i = p + (i + 1) by omega)] at hih
      refine le_trans hih ?_
      refine mul_le_mul_of_nonneg_right ?_
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + (p + (i + 1))) x _)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    | (j + 1), hkd =>
      have hjd : j + d = i := by omega
      have hrec : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
          (if j + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
            else 0) +
            slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
        rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
            (if j + 1 < i + 1 then
                covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
              else 0) +
              castSrcCc g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
                (castRankCc_db g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                  (slotExtend (I := I) (M := M) g (b + j) (c + i)
                    (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
        rw [show castSrcCc g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
              (castRankCc_db g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) =
            slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) from by
          rw [castRankCc_db, castSrcCc]]
      rw [hrec]
      by_cases hji : j < i
      · rw [if_pos (by omega : j + 1 < i + 1)]
        rw [iteratedCovGrad_add]
        rw [show ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))) +
            iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (slotExtend (I := I) (M := M) g (b + j) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) =
            (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x +
              (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g (b + (j + 1))
          ((c + (i + 1)) + p) x _ _) ?_
        obtain ⟨e, he⟩ : ∃ e, (j + 1) + e = i := ⟨i - (j + 1), by omega⟩
        have hcommA : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + i) + (p + 1)) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + i) (p + 1)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))).toSection x) :=
          rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g (b + (j + 1)) (c + i) p
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)) x
        have bA : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x) ≤
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
          rw [hcommA]
          have hihA := ih (j + 1) (p + 1) e he
          rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g b c Φ x
            (show (p + 1) + e = p + d by omega)] at hihA
          exact hihA
        have hsl : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g (b + j) ((c + i) + p) x
                ((iteratedCovGrad (I := I) g (b + j) (c + i) p
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j)).toSection x) :=
          rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (b + j) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) p x
        have bB : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
          refine le_trans hsl ?_
          refine le_trans (mul_le_mul_of_nonneg_left (ih j p d hjd) (by positivity))
            (le_of_eq ?_)
          rw [pow_succ]; ring
        rw [show (4 : ℝ) ^ (i + 1) * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) =
            4 * ((4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x)) from by
          rw [pow_succ]; ring]
        linarith [bA, bB]
      · have hji' : ¬ (j + 1 < i + 1) := by omega
        rw [if_neg hji', zero_add]
        have hsl : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g (b + j) ((c + i) + p) x
                ((iteratedCovGrad (I := I) g (b + j) (c + i) p
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j)).toSection x) :=
          rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (b + j) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) p x
        refine le_trans hsl ?_
        refine le_trans (mul_le_mul_of_nonneg_left (ih j p d hjd) (by positivity)) ?_
        rw [show (Module.finrank ℝ E : ℝ) *
              ((4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ j *
                riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                  ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x)) =
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) from by
          rw [pow_succ]; ring]
        refine mul_le_mul_of_nonneg_right ?_
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + (p + d)) x _)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

set_option linter.unusedVariables false in
private lemma rfns_appCcLeibnizPsi_omRecover_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (m : ℕ) (hm : m + 1 ≤ a + 1) (k : ℕ) (hk : k ≤ m) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (1 + k) (1 + (m + 1)) x
        ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1
          (omRecoverEndoCc (I := I) g₀ g₁) (m + 1) k).toSection x) ≤
      4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k * R ^ 2 := by
  have hkey := rfns_iteratedCovGrad_appCcLeibnizPsi_le (I := I) (M := M) g₀ 1 1
    (omRecoverEndoCc (I := I) g₀ g₁) x (m + 1) k 0 ((m + 1) - k) (by omega)
  refine le_trans (le_of_eq ?_) (le_trans hkey ?_)
  · rfl
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g₀ 1 1
      (omRecoverEndoCc (I := I) g₀ g₁) x (show 0 + ((m + 1) - k) = (m - k) + 1 by omega)]
    exact rfns_iteratedCovGrad_omRecoverEndoCc_succ_le (I := I) g₀ g₁ a T htie hTjet (m - k)
      (by omega) x

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
  have hleib := iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 1
    (omRecoverEndoCc (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) (m + 1)
  rw [appCcRS_omRecover_sharpFlat_eq_idEndo (I := I) g₀ g₁,
    iteratedCovGrad_sharpFlatEndoCc_self_eq_zero (I := I) g₀ m,
    Finset.sum_range_succ,
    appCcLeibnizPsi_diag_eq (I := I) (M := M) g₀ 1 1
      (omRecoverEndoCc (I := I) g₀ g₁) (m + 1)] at hleib
  set sigSum := ∑ k ∈ Finset.range (m + 1), appCcRS (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
    (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 (omRecoverEndoCc (I := I) g₀ g₁) (m + 1) k)
    (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁)) with hsigDef
  have hdiag : appCcRS (I := I) (M := M) g₀ 1 (1 + (m + 1)) (1 + (m + 1))
        (slotExtendIter (I := I) (M := M) g₀ 1 1 (m + 1) (omRecoverEndoCc (I := I) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 1 1 (m + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) = -sigSum :=
    eq_neg_of_add_eq_zero_right hleib.symm
  have hmi := master_isolation (I := I) g₀ g₁ (m + 1)
    (iteratedCovGrad (I := I) g₀ 1 1 (m + 1) (sharpFlatEndoCc (I := I) g₀ g₁))
  rw [hdiag] at hmi
  have hsigToSection : (sigSum.toSection x : TensorRSSpace 1 (1 + (m + 1)) I x) =
      ∑ k ∈ Finset.range (m + 1),
        ((appCcRS (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 (omRecoverEndoCc (I := I) g₀ g₁) (m + 1) k)
          (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x) := by
    rw [hsigDef, SmoothCcTensor.toSection_sum_apply]
  have hSigmaBound : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x (sigSum.toSection x) ≤
      (m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
        (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k * R ^ 2) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
            ((iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
    rw [hsigToSection]
    refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
      (Finset.range (m + 1)) (fun k => (appCcRS (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
        (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 (omRecoverEndoCc (I := I) g₀ g₁) (m + 1) k)
        (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ?_
    rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := by rw [Finset.mem_range] at hk; omega
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + k)
      (1 + (m + 1)) x _ _) ?_
    apply mul_le_mul_of_nonneg_right
      (rfns_appCcLeibnizPsi_omRecover_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet m hm k hkm x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _)
  rw [← hmi, appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + (m + 1))
    (1 + (m + 1)) x _ _) ?_
  rw [rfns_slotExtendIter_eq (I := I) (M := M) g₀ 1 1 (m + 1) (sharpFlatEndoCc (I := I) g₀ g₁) x]
  rw [show ((-sigSum).toSection x : TensorRSSpace 1 (1 + (m + 1)) I x) = -(sigSum.toSection x) from by
    rw [SmoothCcTensor.toSection_neg]; rfl]
  rw [rfns_neg_fib]
  exact mul_le_mul_of_nonneg_left hSigmaBound
    (mul_nonneg (by positivity) (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _))

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
