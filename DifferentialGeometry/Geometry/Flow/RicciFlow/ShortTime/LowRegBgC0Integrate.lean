import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0CoeffPair

/-!
# Order-zero path-integral identities

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

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
theorem lowOneAInt_h2
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
      lowJetSq (I := I) (M := M) g 2
          (lowOneAInt (I := I) (M := M) g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    lowOneA_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    (lowOneA (I := I) (M := M) g T hδT hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen hSI
    (lowOneA_joint (I := I) (M := M) g T hδT hδZ)
    (B := B R * (1 + A))
    (mul_nonneg (hB R hR) (add_nonneg (by norm_num) hA))
    (fun s hs => by
      simpa only [lowJetSq, Nat.reduceAdd] using
        hpoint T hT hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3 hTn hs)
  simpa only [lowOneAInt, lowJetSq, Nat.reduceAdd] using hpath

theorem self_int
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
        (LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      appCc (I := I) (M := M) g 2 2
          (lowZeroInt (I := I) (M := M) g T hδ_lt hδ hδZ) T +
        appCc (I := I) (M := M) g 3 2
          (lowOneInt (I := I) (M := M) g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    LowBaseInternal.rhsSelfLow (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    lowZero (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    lowOne (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjΨ : C0Joint (I := I) g 2 2 S Ψ := by
    simpa only [C0Joint, S, Ψ] using
      LowBaseInternal.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : C0Joint (I := I) g 2 2 S L := by
    simpa only [S, L] using
      lowZero_joint (I := I) (M := M) g T hδ hδZ
  have hjQ : C0Joint (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      lowOne_joint (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S realizedSmallSet_isOpen hSI hjΨ := rfl
  have hPiL :
      lowZeroInt (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S realizedSmallSet_isOpen hSI hjL := rfl
  have hPiQ :
      lowOneInt (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S realizedSmallSet_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 Ψ T S
      realizedSmallSet_isOpen hSI hjΨ hcΨ x v]
  rw [unit_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 L T S
      realizedSmallSet_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      realizedSmallSet_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := self_one (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (LowBaseInternal.rhsSelfLow (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (appCc (I := I) (M := M) g 2 2
            (lowZero (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (appCc (I := I) (M := M) g 3 2
            (lowOne (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, unit_add (I := I) (M := M) g,
    iteratedCovGrad_succ, iteratedCovGrad_zero]

theorem self_aff_int
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
        (LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      appCc (I := I) (M := M) g 2 2
          (lowZeroAInt (I := I) (M := M)
            g T hT hδ_lt hδ hδZ) T +
        appCc (I := I) (M := M) g 3 2
          (lowOneAInt (I := I) (M := M)
            g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    LowBaseInternal.rhsSelfLow (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    lowZeroA (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    lowOneA (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjΨ : C0Joint (I := I) g 2 2 S Ψ := by
    simpa only [C0Joint, S, Ψ] using
      LowBaseInternal.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : C0Joint (I := I) g 2 2 S L := by
    simpa only [S, L] using
      lowZeroA_joint (I := I) (M := M) g T hT hδ hδZ
  have hjQ : C0Joint (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      lowOneA_joint (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S realizedSmallSet_isOpen hSI hjΨ := rfl
  have hPiL :
      lowZeroAInt (I := I) (M := M)
          g T hT hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S realizedSmallSet_isOpen hSI hjL := rfl
  have hPiQ :
      lowOneAInt (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S realizedSmallSet_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 Ψ T S
      realizedSmallSet_isOpen hSI hjΨ hcΨ x v]
  rw [unit_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 L T S
      realizedSmallSet_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      realizedSmallSet_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := self_aff_one (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (LowBaseInternal.rhsSelfLow (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (appCc (I := I) (M := M) g 2 2
            (lowZeroA (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (appCc (I := I) (M := M) g 3 2
            (lowOneA (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, unit_add (I := I) (M := M) g,
    iteratedCovGrad_succ, iteratedCovGrad_zero]


end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
