import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound

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

noncomputable def raisedKoszulJetBase (R δ : ℝ) : ℝ :=
  2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))

noncomputable def raisedKoszulComponentBound (R δ : ℝ) (i : ℕ) : ℝ :=
  raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2)

noncomputable def raisedKoszulJetBound (R δ : ℝ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (3 + i) * raisedKoszulComponentBound (E := E) R δ i

set_option linter.unusedSectionVars false in
lemma raisedKoszulJetBase_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) :
    0 ≤ raisedKoszulJetBase (E := E) R δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold raisedKoszulJetBase
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · linarith
  · exact div_nonneg zero_le_one h1.le

set_option linter.unusedSectionVars false in
lemma raisedKoszulComponentBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ raisedKoszulComponentBound (E := E) R δ i := by
  unfold raisedKoszulComponentBound
  exact pow_nonneg (raisedKoszulJetBase_nonneg R δ hR hδ1) _

set_option linter.unusedSectionVars false in
lemma raisedKoszulJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ raisedKoszulJetBound (E := E) R δ i := by
  unfold raisedKoszulJetBound
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (raisedKoszulComponentBound_nonneg R δ hR hδ1 i)

set_option linter.unusedSectionVars false in
lemma ten_R_sq_le_raisedKoszulComponentBound {R : ℝ} (hR : 0 ≤ R) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (i : ℕ) :
    10 * R ^ 2 ≤ raisedKoszulComponentBound (E := E) R δ i := by
  rw [raisedKoszulComponentBound]
  have hden : (0 : ℝ) < 1 - δ := by linarith
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have hne : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hinv1 : (1 : ℝ) ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ hden]; linarith
  have hBR : (0 : ℝ) ≤ 1 + R := by linarith
  have hA : (4 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
  have hbase_ge : 4 * (1 + R) ≤ raisedKoszulJetBase (E := E) R δ := by
    unfold raisedKoszulJetBase
    calc 4 * (1 + R) = 4 * (1 + R) * 1 := (mul_one _).symm
      _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hA hBR) hinv1 (by norm_num) (by positivity)
  have h4R0 : (0 : ℝ) ≤ 4 * (1 + R) := by positivity
  have hbase_sq : (4 * (1 + R)) ^ 2 ≤ raisedKoszulJetBase (E := E) R δ ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self h4R0 hbase_ge
  have h10 : 10 * R ^ 2 ≤ (4 * (1 + R)) ^ 2 := by nlinarith [sq_nonneg R, hR]
  have h4Rge1 : (1 : ℝ) ≤ 4 * (1 + R) := by nlinarith [hR]
  have hbase1 : (1 : ℝ) ≤ raisedKoszulJetBase (E := E) R δ := le_trans h4Rge1 hbase_ge
  have hexp : 2 ≤ 2 * (i + 1) ^ 2 := by
    have h1 : 1 ≤ (i + 1) ^ 2 := Nat.one_le_pow 2 (i + 1) (by omega)
    omega
  have hpow : raisedKoszulJetBase (E := E) R δ ^ 2 ≤
      raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2) :=
    pow_le_pow_right₀ hbase1 hexp
  calc 10 * R ^ 2 ≤ (4 * (1 + R)) ^ 2 := h10
    _ ≤ raisedKoszulJetBase (E := E) R δ ^ 2 := hbase_sq
    _ ≤ raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2) := hpow

set_option linter.unusedVariables false in
private lemma fiberNormSqComponent_sq_iteratedCovGrad_raisedKoszul_le_koszul_rfns
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin (2 + i) → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
        n e K J) ^ 2 ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) :=
  sorry

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_raisedKoszul_perComponent_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin (2 + i) → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
        n e K J) ^ 2 ≤
      raisedKoszulComponentBound (E := E) R δ i := by
  calc (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
          n e K J) ^ 2
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) :=
        fiberNormSqComponent_sq_iteratedCovGrad_raisedKoszul_le_koszul_rfns
          (I := I) g₀ g₁ T htie i x e hn horth K J
    _ ≤ 10 * R ^ 2 :=
        rfns_iteratedCovGrad_koszulCovecCc_le (I := I) g₀ a T hTjet i hi x
    _ ≤ raisedKoszulComponentBound (E := E) R δ i :=
        ten_R_sq_le_raisedKoszulComponentBound (E := E) hR hδ0 hδ1 i

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_raisedKoszul_le
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
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        raisedKoszulJetBound (E := E) R δ i := by
  intro i hi x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    e bse hnE hbse horth]
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
            n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          raisedKoszulComponentBound (E := E) R δ i :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ =>
          rfns_iteratedCovGrad_raisedKoszul_perComponent_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
            hTjet i hi x e hnE horth K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin (2 + i) → Fin n) : ℝ) *
          raisedKoszulComponentBound (E := E) R δ i := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = raisedKoszulJetBound (E := E) R δ i := by
        rw [raisedKoszulJetBound]
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) *
              (Fintype.card (Fin (2 + i) → Fin n) : ℝ)
            = (Module.finrank ℝ E : ℝ) ^ (3 + i) := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          rw [← hnE]
          push_cast
          rw [← pow_add, show 1 + (2 + i) = 3 + i from by omega]
        rw [hcard]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
