import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Integrate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegBaseForce

/-!
# Order-zero refold assembly

Internal assembly layer for the low-regularity order-zero refold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace LowRegBgC0Core

noncomputable def refoldData
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowBaseActionData g where
  C0 := lowZeroAInt (I := I) (M := M)
      g T hT hδ_lt hδ hδZ +
    phiMetCurvCoeff (I := I) g g g
  C1 := lowOneAInt (I := I) (M := M) g T hδ_lt hδ hδZ +
    DeTurckCoefficients.rhsLow1PathIntegral (I := I) (M := M)
      g g T 0 hδ_lt hδ hδ_lt hδZ
  C2 := (lowBaseData (I := I) (M := M)
    g g T hδ_lt hδ hδZ).C2

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem refoldC0_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let A := refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      lowJetSq (I := I) (M := M) g 2 A.C0 ≤ (B R) ^ 2 := by
  obtain ⟨ρ, Bz, hρ, hBz, hz⟩ :=
    lowZeroAInt_h2 (I := I) (M := M) hDim g
  let J : ℝ := lowJetSq (I := I) (M := M) g 2
    (phiMetCurvCoeff (I := I) g g g)
  let L : ℝ → ℝ := fun R => 2 * (Bz R ^ 2 + J)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ : 0 ≤ J := jetNn (I := I) (M := M) (m := 2) g _
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg (Bz R)) hJ)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn
  dsimp only
  have hzero := hz T hT hδ_le hδ0 hδT hδZ R hR hT2 hTn
  rw [refoldData]
  refine (jetAdd (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (lowJetSq (I := I) (M := M) g 2
          (lowZeroAInt (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) +
        lowJetSq (I := I) (M := M) g 2
          (phiMetCurvCoeff (I := I) g g g)) ≤
      2 * (Bz R ^ 2 + J) :=
        mul_le_mul_of_nonneg_left (add_le_add hzero le_rfl) (by norm_num)
    _ = L R := by rfl
    _ = B R ^ 2 := by
      simpa only [B] using (Real.sq_sqrt (hL R hR)).symm

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
theorem refoldC1_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      lowJetSq (I := I) (M := M) g 2 F.C1 ≤
        (B R * (1 + A ^ 2) ^ 3) ^ 2 := by
  obtain ⟨ρ, Bl, hρ, hBl, hnew⟩ :=
    lowOneAInt_h2 (I := I) (M := M) hDim g
  obtain ⟨K, hK, hold⟩ := lowData_a1_coeff (I := I) (M := M) hDim g
  let L : ℝ → ℝ := fun R => 2 * (2 * Bl R ^ 2 + K)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg (Bl R))) hK)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  let X : ℝ := 1 + A ^ 2
  have hX0 : 0 ≤ X := add_nonneg (by norm_num) (sq_nonneg A)
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith [sq_nonneg A]
  have hX16 : X ^ 1 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by omega)
  have hXpow : X ≤ X ^ 6 := by simpa only [pow_one] using hX16
  have hlin : (1 + A) ^ 2 ≤ 2 * X ^ 6 := by
    calc
      (1 + A) ^ 2 ≤ 2 * X := by
        simp only [X]
        nlinarith [sq_nonneg (A - 1)]
      _ ≤ 2 * X ^ 6 := mul_le_mul_of_nonneg_left hXpow (by norm_num)
  have hn := hnew T hT hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3 hTn
  have hn' : lowJetSq (I := I) (M := M) g 2
      (lowOneAInt (I := I) (M := M) g T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
      2 * Bl R ^ 2 * X ^ 6 := by
    calc
      _ ≤ (Bl R * (1 + A)) ^ 2 := hn
      _ = Bl R ^ 2 * (1 + A) ^ 2 := by ring
      _ ≤ Bl R ^ 2 * (2 * X ^ 6) :=
        mul_le_mul_of_nonneg_left hlin (sq_nonneg (Bl R))
      _ = 2 * Bl R ^ 2 * X ^ 6 := by ring
  have holdSum := hold T hT hδ_le hδ0 hδT hδZ
  dsimp only at holdSum
  let F₀ : LowBaseActionData g := lowBaseData (I := I) (M := M)
    g g T (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
  have holdC1 : lowJetSq (I := I) (M := M) g 2 F₀.C1 ≤
      K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6 := by
    have hC0 := jetNn (I := I) (M := M) (m := 2) g F₀.C0
    simpa only [F₀] using
      (show lowJetSq (I := I) (M := M) g 2 F₀.C1 ≤
          K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6 by
        nlinarith [holdSum])
  have hstate :
      (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6 ≤ X ^ 6 := by
    exact pow_le_pow_left₀
      (by linarith [jetNn (I := I) (M := M) (m := 3) g T])
      (by simpa only [X] using add_le_add le_rfl hT3) 6
  have holdC1' : lowJetSq (I := I) (M := M) g 2 F₀.C1 ≤
      K * X ^ 6 :=
    holdC1.trans (mul_le_mul_of_nonneg_left hstate hK)
  have holdPath : lowJetSq (I := I) (M := M) g 2
      (DeTurckCoefficients.rhsLow1PathIntegral (I := I) (M := M)
        g g T 0 (lt_of_le_of_lt hδ_le (by norm_num)) hδT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδZ) ≤
      K * X ^ 6 := by
    simpa only [F₀, lowBaseData] using holdC1'
  rw [refoldData]
  refine (jetAdd (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (lowJetSq (I := I) (M := M) g 2
          (lowOneAInt (I := I) (M := M) g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) +
        lowJetSq (I := I) (M := M) g 2
          (DeTurckCoefficients.rhsLow1PathIntegral (I := I) (M := M)
            g g T 0 (lt_of_le_of_lt hδ_le (by norm_num)) hδT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)) ≤
      2 * (2 * Bl R ^ 2 * X ^ 6 + K * X ^ 6) :=
        mul_le_mul_of_nonneg_left (add_le_add hn' holdPath) (by norm_num)
    _ = L R * X ^ 6 := by simp only [L]; ring
    _ = (B R * X ^ 3) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      rw [mul_pow, hBR]
      ring

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem refoldCoeff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      lowJetSq (I := I) (M := M) g 2 F.C0 +
          lowJetSq (I := I) (M := M) g 2 F.C1 ≤
        (B R * (1 + A ^ 2) ^ 3) ^ 2 := by
  obtain ⟨ρ0, B0, hρ0, hB0, hC0⟩ :=
    refoldC0_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ1, B1, hρ1, hB1, hC1⟩ :=
    refoldC1_h2 (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ0 ρ1
  let L : ℝ → ℝ := fun R => B0 R ^ 2 + B1 R ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρ0 hρ1
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact add_nonneg (sq_nonneg (B0 R)) (sq_nonneg (B1 R))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  have h0 := hC0 T hT hδ_le hδ0 hδT hδZ R hR hT2
    (hTn.trans (min_le_left _ _))
  have h1 := hC1 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
    (hTn.trans (min_le_right _ _))
  let X : ℝ := 1 + A ^ 2
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith [sq_nonneg A]
  have hX16 : X ^ 1 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by omega)
  have hXpow : X ≤ X ^ 6 := by simpa only [pow_one] using hX16
  have hX6 : 1 ≤ X ^ 6 := hX1.trans hXpow
  have h0' : lowJetSq (I := I) (M := M) g 2
      (refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C0 ≤
      B0 R ^ 2 * X ^ 6 := by
    calc
      _ ≤ B0 R ^ 2 := h0
      _ = B0 R ^ 2 * 1 := by ring
      _ ≤ B0 R ^ 2 * X ^ 6 :=
        mul_le_mul_of_nonneg_left hX6 (sq_nonneg (B0 R))
  calc
    lowJetSq (I := I) (M := M) g 2
          (refoldData (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C0 +
        lowJetSq (I := I) (M := M) g 2
          (refoldData (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C1 ≤
      B0 R ^ 2 * X ^ 6 + (B1 R * X ^ 3) ^ 2 := add_le_add h0' h1
    _ = L R * X ^ 6 := by simp only [L]; ring
    _ = (B R * X ^ 3) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      rw [mul_pow, hBR]
      ring

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem refoldA1_hl
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      (∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 2
            (F.a1 (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            lowJetSq (I := I) (M := M) g 3 W) ∧
      ∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 1
            (F.a1 (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨ρ, Bc, hρ, hBc, hcoeff⟩ :=
    refoldCoeff_h2 (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhigh⟩ := a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ := a1_h2_h1 (I := I) (M := M) hDim g
  let C : ℝ := Ch + Cl
  let B : ℝ → ℝ := fun R => C * Bc R
  have hC : 0 ≤ C := add_nonneg hCh hCl
  refine ⟨ρ, B, hρ, fun R hR => mul_nonneg hC (hBc R hR), ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  let F := refoldData (I := I) (M := M) g T hT
    (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
  let X : ℝ := 1 + A ^ 2
  let Q : ℝ := Bc R * X ^ 3
  have hX : 0 ≤ X := add_nonneg (by norm_num) (sq_nonneg A)
  have hQ : 0 ≤ Q := mul_nonneg (hBc R hR) (pow_nonneg hX 3)
  have hcoef : lowJetSq (I := I) (M := M) g 2 F.C0 +
      lowJetSq (I := I) (M := M) g 2 F.C1 ≤ Q ^ 2 := by
    simpa only [F, Q, X] using
      hcoeff T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  constructor
  · intro W
    let D : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 3 W)
    have hJW : 0 ≤ lowJetSq (I := I) (M := M) g 3 W :=
      jetNn (I := I) (M := M) (m := 3) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq : D ^ 2 = lowJetSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hhigh F W Q D hQ hD hcoef (by rw [hDsq])
    have hlead : Ch * Q * D ≤ C * Q * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCl) hQ) hD
    calc
      lowJetSq (I := I) (M := M) g 2
          (F.a1 (I := I) (M := M) W) ≤ (Ch * Q * D) ^ 2 := hraw
      _ ≤ (C * Q * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCh hQ) hD) hlead 2
      _ = (B R * X ^ 3) ^ 2 *
          lowJetSq (I := I) (M := M) g 3 W := by
        rw [show C * Q * D = B R * X ^ 3 * D by
          simp only [B, Q]; ring, mul_pow, hDsq]
  · intro W
    let D : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    have hJW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      jetNn (I := I) (M := M) (m := 2) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq : D ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hlow F W Q D hQ hD hcoef (by rw [hDsq])
    have hlead : Cl * Q * D ≤ C * Q * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCh) hQ) hD
    calc
      lowJetSq (I := I) (M := M) g 1
          (F.a1 (I := I) (M := M) W) ≤ (Cl * Q * D) ^ 2 := hraw
      _ ≤ (C * Q * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCl hQ) hD) hlead 2
      _ = (B R * X ^ 3) ^ 2 *
          lowJetSq (I := I) (M := M) g 2 W := by
        rw [show C * Q * D = B R * X ^ 3 * D by
          simp only [B, Q]; ring, mul_pow, hDsq]

/- The isolated order-zero self-action after moving its derivative-bearing
factors into one additional first-order passenger coefficient. -/
noncomputable def c0Data
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowBaseActionData g where
  C0 := lowZeroAInt (I := I) (M := M)
      g T hT hδ_lt hδ hδZ +
    phiMetCurvCoeff (I := I) g g g
  C1 := lowOneAInt (I := I) (M := M) g T hδ_lt hδ hδZ
  C2 := 0

theorem c0Data_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    appCc (I := I) (M := M) g 2 2
        (lowBaseData (I := I) (M := M)
          g g T hδ_lt hδ hδZ).C0 T =
      (c0Data (I := I) (M := M)
        g T hT hδ_lt hδ hδZ).a1 (I := I) (M := M) T := by
  rw [LowBaseInternal.c0_eq (I := I) (M := M)
    g g T hδ_lt hδ hδZ]
  rw [LowBaseActionData.a1]
  simp only [c0Data, appCc_add_left]
  rw [self_aff_int (I := I) (M := M) g T hT hδ_lt hδ hδZ]
  abel

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
theorem c0DataPairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 Ca : ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ Ca ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := c0Data (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      let AU := c0Data (I := I) (M := M) g U hU
        (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ
      let Q0 := B0 * (1 + R) * (D2 + N)
      let Q1 := B1 R * (1 + A) * (D3 + D2 + A * D2 + N)
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          Ca * Real.sqrt (Q0 ^ 2 + Q1 ^ 2) ∧
        ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          Ca * Real.sqrt (Q0 ^ 2 + Q1 ^ 2) := by
  obtain ⟨ρ0, B0, hρ0, hB0, hzero⟩ :=
    lowZeroIntPair (I := I) (M := M) hDim g
  obtain ⟨ρ1, B1, hρ1, hB1, hone⟩ :=
    lowOneIntPairH2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, hact⟩ := a1_diff (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ0 ρ1
  refine ⟨ρ, B0, Ca, B1, lt_min hρ0 hρ1, hB0, hCa, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  dsimp only
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let AT : LowBaseActionData g :=
    c0Data (I := I) (M := M) g T hT hδ_lt hδT hδZ
  let AU : LowBaseActionData g :=
    c0Data (I := I) (M := M) g U hU hδ_lt hδU hδZ
  let Q0 : ℝ := B0 * (1 + R) * (D2 + N)
  let Q1 : ℝ := B1 R * (1 + A) * (D3 + D2 + A * D2 + N)
  let Q : ℝ := Q0 ^ 2 + Q1 ^ 2
  let Qt : ℝ := Real.sqrt Q
  have hM0 := hzero T U hT hU hδ_le hδT hδU hδZ
    R D2 N hR hD2 hN hT2 hU2 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hone T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hQ0 : 0 ≤ Q0 :=
    mul_nonneg (mul_nonneg hB0 (add_nonneg (by norm_num) hR))
      (add_nonneg hD2 hN)
  have hQ1 : 0 ≤ Q1 :=
    mul_nonneg (mul_nonneg (hB1 R hR) (add_nonneg (by norm_num) hA))
      (add_nonneg (add_nonneg (add_nonneg hD3 hD2)
        (mul_nonneg hA hD2)) hN)
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg Q0) (sq_nonneg Q1)
  have hQt : 0 ≤ Qt := Real.sqrt_nonneg _
  have hC0eq : AT.C0 - AU.C0 =
      lowZeroAInt (I := I) (M := M) g T hT hδ_lt hδT hδZ -
        lowZeroAInt (I := I) (M := M) g U hU hδ_lt hδU hδZ := by
    simp only [AT, AU, c0Data]
    module
  have hj0 : lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) ≤
      Q0 ^ 2 := by
    rw [hC0eq]
    simpa only [Q0] using hM0
  have hj1 : lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
      Q1 ^ 2 := by
    simpa only [AT, AU, c0Data, Q1] using hM1
  have hcoeff :
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) +
          lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
        Qt ^ 2 := by
    calc
      _ ≤ Q0 ^ 2 + Q1 ^ 2 := add_le_add hj0 hj1
      _ = Qt ^ 2 := by
        change Q = Real.sqrt Q ^ 2
        exact (Real.sq_sqrt hQ).symm
  have hop := hact AT AU Qt hQt hcoeff
  simpa only [AT, AU, Qt, Q, Q0, Q1] using hop

omit [BoundarylessManifold I M] in
theorem zero_fb_c0
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem incl32_c0
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine tensorHs.ext ?_
  funext i
  simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

theorem sqrt_scale_c0
    (q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    Real.sqrt (q * d ^ 2) = Real.sqrt q * d := by
  rw [Real.sqrt_mul hq, Real.sqrt_sq hd]


end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
