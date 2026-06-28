import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ricciArmPrincipalCoeff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def curvatureCoeffJetBase (R δ : ℝ) : ℝ :=
  2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))

noncomputable def curvatureCoeffComponentBound (R δ : ℝ) (i : ℕ) : ℝ :=
  curvatureCoeffJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2)

noncomputable def curvatureCoeffJetBound (R δ : ℝ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (6 + i) * curvatureCoeffComponentBound (E := E) R δ i

set_option linter.unusedSectionVars false in
lemma curvatureCoeffJetBase_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) :
    0 ≤ curvatureCoeffJetBase (E := E) R δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold curvatureCoeffJetBase
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · linarith
  · exact div_nonneg zero_le_one h1.le

set_option linter.unusedSectionVars false in
lemma curvatureCoeffComponentBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ curvatureCoeffComponentBound (E := E) R δ i := by
  unfold curvatureCoeffComponentBound
  exact pow_nonneg (curvatureCoeffJetBase_nonneg R δ hR hδ1) _

set_option linter.unusedSectionVars false in
lemma curvatureCoeffJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ curvatureCoeffJetBound (E := E) R δ i := by
  unfold curvatureCoeffJetBound
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (curvatureCoeffComponentBound_nonneg R δ hR hδ1 i)

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmPrincipalCoeff_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a + 1) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) :
    (∑ J : Fin (2 + i) → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x)
        n e K J) ^ 2) ≤
      curvatureCoeffComponentBound (E := E) R δ i :=
  sorry

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmPrincipalCoeff_perComponent_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a + 1) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin (2 + i) → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 4 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x)
        n e K J) ^ 2 ≤
      curvatureCoeffComponentBound (E := E) R δ i := by
  refine le_trans (Finset.single_le_sum
      (f := fun J' : Fin (2 + i) → Fin n =>
        (fiberNormSqComponent (I := I) (M := M) g₀ x 4 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x) n e K J') ^ 2)
      (fun J' _ => sq_nonneg _) (Finset.mem_univ J))
    (rfns_iteratedCovGrad_ricciArmPrincipalCoeff_Ksum_sq_le
      (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet i hi x e hn horth K)

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmPrincipalCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a + 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
        curvatureCoeffJetBound (E := E) R δ i := by
  intro i hi x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 4 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 4 2 i
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x)
    e bse hnE hbse horth]
  calc ∑ K : Fin 4 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 4 (2 + i)
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)).toSection x)
            n e K J) ^ 2
      ≤ ∑ K : Fin 4 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          curvatureCoeffComponentBound (E := E) R δ i :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ =>
          rfns_iteratedCovGrad_ricciArmPrincipalCoeff_perComponent_le (I := I) g₀ g₁ a T htie hR
            hδ0 hδ1 hδ hTjet i hi x e hnE horth K J))
    _ = (Fintype.card (Fin 4 → Fin n) : ℝ) * (Fintype.card (Fin (2 + i) → Fin n) : ℝ) *
          curvatureCoeffComponentBound (E := E) R δ i := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = curvatureCoeffJetBound (E := E) R δ i := by
        rw [curvatureCoeffJetBound]
        have hcard : (Fintype.card (Fin 4 → Fin n) : ℝ) *
              (Fintype.card (Fin (2 + i) → Fin n) : ℝ)
            = (Module.finrank ℝ E : ℝ) ^ (6 + i) := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          rw [← hnE]
          push_cast
          rw [← pow_add, show 4 + (2 + i) = 6 + i from by omega]
        rw [hcard]

end DifferentialGeometry.Integral.Connection

end
