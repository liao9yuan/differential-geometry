import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

/-!
# Compatible completions of the low-base first-order action

This module completes the single smooth-core formula
`LowBaseActionData.a1` on the adjacent Sobolev scales used by the
low-regularity Ricci--DeTurck bootstrap.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem jet3_le_hs
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 3 W ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (3 : ℝ) W‖) ^ 2 := by
  obtain ⟨C, hC, hjet⟩ :=
    hsJet_le (I := I) (M := M) g 2 3
  refine ⟨C, hC, fun W => ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 3 W ≤
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j W‖) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j W))
    _ ≤ (C * ‖ccTensorToHs (I := I) (M := M)
        g 2 (3 : ℝ) W‖) ^ 2 :=
      pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j W)))
        (by simpa only [Nat.reduceAdd] using hjet W) 2

private theorem jet2_le_hs
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 2 W ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) W‖) ^ 2 := by
  obtain ⟨C, hC, hjet⟩ :=
    hsJet_le (I := I) (M := M) g 2 2
  refine ⟨C, hC, fun W => ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 2 W ≤
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j W‖) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j W))
    _ ≤ (C * ‖ccTensorToHs (I := I) (M := M)
        g 2 (2 : ℝ) W‖) ^ 2 :=
      pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j W)))
        (by simpa only [Nat.reduceAdd] using hjet W) 2

private theorem hs2_of_jet
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Y : SmoothCcTensor g 0 2) (Q : ℝ), 0 ≤ Q →
        lowJetSq (I := I) (M := M) g 2 Y ≤ Q ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
          C * Q := by
  obtain ⟨C0, hC0, hs⟩ :=
    hs_le_jet (I := I) (M := M) g 2 2
  refine ⟨3 * C0, mul_nonneg (by norm_num) hC0, ?_⟩
  intro Y Q hQ hY
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          lowJetSq (I := I) (M := M) g 2 Y := by
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hY,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 3 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * Q := by norm_num
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        C0 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
      simpa only [Nat.cast_one] using hs Y
    _ ≤ C0 * (3 * Q) :=
      mul_le_mul_of_nonneg_left hsum hC0
    _ = (3 * C0) * Q := by ring

private theorem hs1_of_jet
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Y : SmoothCcTensor g 0 2) (Q : ℝ), 0 ≤ Q →
        lowJetSq (I := I) (M := M) g 1 Y ≤ Q ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
          C * Q := by
  obtain ⟨C0, hC0, hs⟩ :=
    hs_le_jet (I := I) (M := M) g 2 1
  refine ⟨2 * C0, mul_nonneg (by norm_num) hC0, ?_⟩
  intro Y Q hQ hY
  have hterm : ∀ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          lowJetSq (I := I) (M := M) g 1 Y := by
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hY,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hsum :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 2 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 2, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 2 * Q := by norm_num
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
        C0 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
      have h := hs Y
      have hcast : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
      rw [hcast] at h
      exact h
    _ ≤ C0 * (2 * Q) :=
      mul_le_mul_of_nonneg_left hsum hC0
    _ = (2 * C0) * Q := by ring

private theorem a1_spec_hi
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          lowJetSq (I := I) (M := M) g 2
              (A.a1 (I := I) (M := M) W) ≤
            Q * lowJetSq (I := I) (M := M) g 3 W) →
        ∀ W : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.a1 (I := I) (M := M) W)‖ ≤
            C * Real.sqrt Q *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
  obtain ⟨Co, hCo, hout⟩ := hs2_of_jet (I := I) (M := M) g
  obtain ⟨Ci, hCi, hin⟩ := jet3_le_hs (I := I) (M := M) g
  refine ⟨Co * Ci, mul_nonneg hCo hCi, ?_⟩
  intro A Q hQ hact W
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖
  let D : ℝ := Ci * N
  let R : ℝ := Real.sqrt Q * D
  have hN : 0 ≤ N := norm_nonneg _
  have hD : 0 ≤ D := mul_nonneg hCi hN
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hD
  have hR2 : R ^ 2 = Q * D ^ 2 := by
    simp only [R]
    rw [mul_pow, Real.sq_sqrt hQ]
  have hY :
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤ R ^ 2 := by
    calc
      _ ≤ Q * lowJetSq (I := I) (M := M) g 3 W := hact W
      _ ≤ Q * D ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [D, N] using hin W) hQ
      _ = R ^ 2 := hR2.symm
  have hbound := hout
    (A.a1 (I := I) (M := M) W) R hR hY
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.a1 (I := I) (M := M) W)‖ ≤ Co * R := hbound
    _ = (Co * Ci) * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
      simp only [R, D, N]
      ring

private theorem a1_spec_lo
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          lowJetSq (I := I) (M := M) g 1
              (A.a1 (I := I) (M := M) W) ≤
            Q * lowJetSq (I := I) (M := M) g 2 W) →
        ∀ W : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.a1 (I := I) (M := M) W)‖ ≤
            C * Real.sqrt Q *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
  obtain ⟨Co, hCo, hout⟩ := hs1_of_jet (I := I) (M := M) g
  obtain ⟨Ci, hCi, hin⟩ := jet2_le_hs (I := I) (M := M) g
  refine ⟨Co * Ci, mul_nonneg hCo hCi, ?_⟩
  intro A Q hQ hact W
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖
  let D : ℝ := Ci * N
  let R : ℝ := Real.sqrt Q * D
  have hN : 0 ≤ N := norm_nonneg _
  have hD : 0 ≤ D := mul_nonneg hCi hN
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hD
  have hR2 : R ^ 2 = Q * D ^ 2 := by
    simp only [R]
    rw [mul_pow, Real.sq_sqrt hQ]
  have hY :
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤ R ^ 2 := by
    calc
      _ ≤ Q * lowJetSq (I := I) (M := M) g 2 W := hact W
      _ ≤ Q * D ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [D, N] using hin W) hQ
      _ = R ^ 2 := hR2.symm
  have hbound := hout
    (A.a1 (I := I) (M := M) W) R hR hY
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.a1 (I := I) (M := M) W)‖ ≤ Co * R := hbound
    _ = (Co * Ci) * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
      simp only [R, D, N]
      ring

private noncomputable def lowA1Core
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (σ : ℝ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      tensorHs (I := I) (M := M) g 0 2 σ where
  toFun := fun W =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (A.a1 (I := I) (M := M) W)
  map_add' := fun W V => by
    simp only [LowBaseActionData.a1, iteratedCovGrad_add,
      appCc_add_right, ccTensorToHs_add]
    module
  map_smul' := fun c W => by
    simp only [RingHom.id_apply, LowBaseActionData.a1,
      iteratedCovGrad_smul, appCc_smul_right, ccTensorToHs_add,
      ccTensorToHs_smul, smul_add]

/-- The first-order low-base action completed from spectral `H3` to `H2`. -/
noncomputable def LowBaseActionData.a1Hi
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g) :
    tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  (lowA1Core (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

/-- The same first-order low-base action completed from spectral `H2` to
spectral `H1`. -/
noncomputable def LowBaseActionData.a1Lo
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (lowA1Core (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))

/-- One pair of smooth-core jet estimates yields bounded adjacent-scale
completions of the same first-order action and their commuting square. -/
theorem a1_pair
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (Q : ℝ), 0 ≤ Q →
        (∀ W : SmoothCcTensor g 0 2,
          lowJetSq (I := I) (M := M) g 2
              (A.a1 (I := I) (M := M) W) ≤
            Q * lowJetSq (I := I) (M := M) g 3 W) →
        (∀ W : SmoothCcTensor g 0 2,
          lowJetSq (I := I) (M := M) g 1
              (A.a1 (I := I) (M := M) W) ≤
            Q * lowJetSq (I := I) (M := M) g 2 W) →
        ‖A.a1Hi (I := I) (M := M)‖ ≤ C * Real.sqrt Q ∧
        ‖A.a1Lo (I := I) (M := M)‖ ≤ C * Real.sqrt Q ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a1Hi (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.a1 (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a1Lo (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.a1 (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.a1Hi (I := I) (M := M)) =
          (A.a1Lo (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨Ch, hCh, hhigh⟩ := a1_spec_hi (I := I) (M := M) g
  obtain ⟨Cl, hCl, hlow⟩ := a1_spec_lo (I := I) (M := M) g
  refine ⟨Ch + Cl, add_nonneg hCh hCl, ?_⟩
  intro A Q hQ hHi hLo
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hhi := hhigh A Q hQ hHi
  have hlo := hlow A Q hQ hLo
  have hHiNorm :
      ‖A.a1Hi (I := I) (M := M)‖ ≤ Ch * Real.sqrt Q := by
    unfold LowBaseActionData.a1Hi
    exact LinearMap.opNorm_extendOfNorm_le
      hdense3 (mul_nonneg hCh (Real.sqrt_nonneg _)) hhi
  have hLoNorm :
      ‖A.a1Lo (I := I) (M := M)‖ ≤ Cl * Real.sqrt Q := by
    unfold LowBaseActionData.a1Lo
    exact LinearMap.opNorm_extendOfNorm_le
      hdense2 (mul_nonneg hCl (Real.sqrt_nonneg _)) hlo
  have hHiCore (W : SmoothCcTensor g 0 2) :
      A.a1Hi (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (A.a1 (I := I) (M := M) W) := by
    change
      ((lowA1Core (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
        (lowA1Core (I := I) (M := M) g A (2 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Ch * Real.sqrt Q, hhi⟩
  have hLoCore (W : SmoothCcTensor g 0 2) :
      A.a1Lo (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.a1 (I := I) (M := M) W) := by
    change
      ((lowA1Core (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) W) =
        (lowA1Core (I := I) (M := M) g A (1 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense2
    exact ⟨Cl * Real.sqrt Q, hlo⟩
  have hHiNorm' :
      ‖A.a1Hi (I := I) (M := M)‖ ≤
        (Ch + Cl) * Real.sqrt Q :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCl) (Real.sqrt_nonneg _))
  have hLoNorm' :
      ‖A.a1Lo (I := I) (M := M)‖ ≤
        (Ch + Cl) * Real.sqrt Q :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hCh) (Real.sqrt_nonneg _))
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.a1Hi (I := I) (M := M))
  let R :=
    (A.a1Lo (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num))
  have hfun : (L : _ → _) = R :=
    hdense3.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W := by
        apply tensorHs.ext
        funext i
        simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
      rw [hin, hLoCore]
      apply tensorHs.ext
      funext i
      simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro W
  exact congrFun hfun W

/-- The zero-based low-base split together with the two compatible completed
realizations of its first-order action. -/
theorem remainder_low_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ K C : ℝ, 0 ≤ κ ∧ 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      ∃ A : LowBaseActionData g,
        deTurckSmoothRemainder (I := I) g g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g g
              (0 : SmoothCcTensor g 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.C2.toSection x) ≤
            (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
        ‖A.a1Hi (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6) ∧
        ‖A.a1Lo (I := I) (M := M)‖ ≤
          C * Real.sqrt
            (K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a1Hi (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.a1 (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a1Lo (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.a1 (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.a1Hi (I := I) (M := M)) =
          (A.a1Lo (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨κ, K, hκ, hK, hrem⟩ :=
    remainder_low_split (I := I) (M := M) hDim g
  obtain ⟨C, hC, hpair⟩ := a1_pair (I := I) (M := M) g
  refine ⟨κ, K, C, hκ, hK, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  obtain ⟨A, hsplit, hcap, hHi, hLo⟩ :=
    hrem T hT hδ_le hδ0 hδ hδZ
  let Q : ℝ :=
    K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 6
  have hjet : 0 ≤ lowJetSq (I := I) (M := M) g 3 T := by
    unfold lowJetSq
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQ : 0 ≤ Q := by
    exact mul_nonneg hK (pow_nonneg (by linarith) 6)
  obtain ⟨hHiNorm, hLoNorm, hHiCore, hLoCore, hcompat⟩ :=
    hpair A Q hQ
      (by simpa only [Q] using hHi)
      (by simpa only [Q] using hLo)
  refine ⟨A, hsplit, hcap, ?_, ?_, hHiCore, hLoCore, hcompat⟩
  · simpa only [Q] using hHiNorm
  · simpa only [Q] using hLoNorm

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
