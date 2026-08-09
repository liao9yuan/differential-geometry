import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0PairDA

/-!
# Order-zero Ricci pair estimate

Internal derivative-estimate layer for the low-regularity order-zero refold.
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

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
theorem ricciOnePairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
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
      lowJetSq (I := I) (M := M) g 2
          (ricciOne (I := I) (M := M) g gT T -
            ricciOne (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Ba, hρ, hBa, haa⟩ :=
    aaOnePairH2 (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hda⟩ :=
    daOnePairH2 (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 2 * (Ba R + Bd R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg (hBa R hR) (hBd R hR))
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let Q : ℝ := D3 + D2 + A * D2
  let D : ℝ := Q + N
  let x : ℝ := Ba R * (1 + A) * D
  let y : ℝ := Bd R * (1 + A) * D
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hD : 0 ≤ D := add_nonneg hQ hN
  have hQD : Q ≤ D := le_add_of_nonneg_right hN
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg (hBa R hR) h1A) hD
  have hy0 : 0 ≤ y := mul_nonneg (mul_nonneg (hBd R hR) h1A) hD
  have hsymmT : symmS (I := I) (M := M) g T = T :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT
  have hsymmU : symmS (I := I) (M := M) g U = U :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g U hU
  have haa' : lowJetSq (I := I) (M := M) g 2
      (aaOne (I := I) (M := M) g gT T -
        aaOne (I := I) (M := M) g gU U) ≤ x ^ 2 := by
    simpa only [x, D, Q, add_assoc] using
      haa gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hda0 := hda gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδU hδZ R A D2 D3
    hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  have hscale : 0 ≤ Bd R * (1 + A) := mul_nonneg (hBd R hR) h1A
  have hda' : lowJetSq (I := I) (M := M) g 2
      (LowBaseInternal.ricciDAOne (I := I) (M := M) g gT T -
        LowBaseInternal.ricciDAOne (I := I) (M := M) g gU U) ≤ y ^ 2 := by
    refine hda0.trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hscale hQ)
      (mul_le_mul_of_nonneg_left hQD hscale) 2
  have hsplit :
      ricciOne (I := I) (M := M) g gT T -
          ricciOne (I := I) (M := M) g gU U =
        (aaOne (I := I) (M := M) g gT T -
          aaOne (I := I) (M := M) g gU U) +
        (LowBaseInternal.ricciDAOne (I := I) (M := M) g gT T -
          LowBaseInternal.ricciDAOne (I := I) (M := M) g gU U) := by
    simp only [ricciOne, hsymmT, hsymmU]
    module
  rw [hsplit]
  refine (jetAdd (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (lowJetSq (I := I) (M := M) g 2
          (aaOne (I := I) (M := M) g gT T -
            aaOne (I := I) (M := M) g gU U) +
        lowJetSq (I := I) (M := M) g 2
          (LowBaseInternal.ricciDAOne (I := I) (M := M) g gT T -
            LowBaseInternal.ricciDAOne (I := I) (M := M) g gU U)) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add haa' hda') (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0]
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      simp only [B, x, y, D, Q]
      ring


end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
