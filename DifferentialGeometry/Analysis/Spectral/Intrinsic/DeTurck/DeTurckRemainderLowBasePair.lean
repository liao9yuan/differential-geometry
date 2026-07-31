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

/-- The covariant jet-square through order three is controlled by the
spectral `H3` norm. -/
theorem jet3_le_hs
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

/-- The covariant jet-square through order two is controlled by the
spectral `H2` norm. -/
theorem jet2_le_hs
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

theorem a1_spec_lo
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

private noncomputable def a1Delta
    {g : SmoothRiemannianMetric I M}
    (A B : LowBaseActionData g) : LowBaseActionData g where
  C0 := A.C0 - B.C0
  C1 := A.C1 - B.C1
  C2 := 0

private theorem a1Delta_apply
    {g : SmoothRiemannianMetric I M}
    (A B : LowBaseActionData g) (W : SmoothCcTensor g 0 2) :
    (a1Delta A B).a1 (I := I) (M := M) W =
      A.a1 (I := I) (M := M) W -
        B.a1 (I := I) (M := M) W := by
  simp only [a1Delta, LowBaseActionData.a1, appCc_sub_left]
  module

private theorem a1Hi_core_any
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a1Hi (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.a1 (I := I) (M := M) W) := by
  obtain ⟨Ca, _, haction⟩ :=
    a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cs, _, hspec⟩ :=
    a1_spec_hi (I := I) (M := M) g
  let J : ℝ :=
    lowJetSq (I := I) (M := M) g 2 A.C0 +
      lowJetSq (I := I) (M := M) g 2 A.C1
  let B : ℝ := Real.sqrt J
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hQ : 0 ≤ Q := sq_nonneg _
  have hact : ∀ V : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) V) ≤
        Q * lowJetSq (I := I) (M := M) g 3 V := by
    intro V
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 3 V)
    have hV : 0 ≤ lowJetSq (I := I) (M := M) g 3 V :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 3 V := by
      simpa only [D] using Real.sq_sqrt hV
    calc
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) V) ≤
          (Ca * B * D) ^ 2 := by
        apply haction A V B D hB hD
        · rw [hBsq]
        · rw [hDsq]
      _ = Q * lowJetSq (I := I) (M := M) g 3 V := by
        rw [show (Ca * B * D) ^ 2 = (Ca * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((lowA1Core (I := I) (M := M) g A (2 : ℝ)).extendOfNorm
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
      (lowA1Core (I := I) (M := M) g A (2 : ℝ)) W
  apply LinearMap.extendOfNorm_eq hdense3
  exact ⟨Cs * Real.sqrt Q, hspec A Q hQ hact⟩

/-- The low adjacent-scale realization of the first-order action agrees with
the smooth first-order action on the dense smooth core.  This is the `a1`
sibling of `a2Lo_core`. -/
theorem a1Lo_core_any
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a1Lo (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.a1 (I := I) (M := M) W) := by
  obtain ⟨Ca, _, haction⟩ :=
    a1_h2_h1 (I := I) (M := M) hDim g
  obtain ⟨Cs, _, hspec⟩ :=
    a1_spec_lo (I := I) (M := M) g
  let J : ℝ :=
    lowJetSq (I := I) (M := M) g 2 A.C0 +
      lowJetSq (I := I) (M := M) g 2 A.C1
  let B : ℝ := Real.sqrt J
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hQ : 0 ≤ Q := sq_nonneg _
  have hact : ∀ V : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) V) ≤
        Q * lowJetSq (I := I) (M := M) g 2 V := by
    intro V
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 V)
    have hV : 0 ≤ lowJetSq (I := I) (M := M) g 2 V :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 2 V := by
      simpa only [D] using Real.sq_sqrt hV
    calc
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) V) ≤
          (Ca * B * D) ^ 2 := by
        apply haction A V B D hB hD
        · rw [hBsq]
        · rw [hDsq]
      _ = Q * lowJetSq (I := I) (M := M) g 2 V := by
        rw [show (Ca * B * D) ^ 2 = (Ca * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  change
    ((lowA1Core (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) W) =
      (lowA1Core (I := I) (M := M) g A (1 : ℝ)) W
  apply LinearMap.extendOfNorm_eq hdense2
  exact ⟨Cs * Real.sqrt Q, hspec A Q hQ hact⟩

private theorem grad_jet1_pair
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      lowJetSq (I := I) (M := M) g 2 W := by
  have h0 := icg_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := icg_comp_norm (I := I) (M := M) g s 1 1 W
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖W‖]

/-- A one-jet bound on the zeroth-order coefficient and a two-jet bound on
the first-order coefficient control the completed `H2 → H1` action
difference. -/
theorem a1Lo_diff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowBaseActionData g) (R0 R1 : ℝ),
        0 ≤ R0 → 0 ≤ R1 →
        lowJetSq (I := I) (M := M) g 1 (A.C0 - B.C0) ≤ R0 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (A.C1 - B.C1) ≤ R1 ^ 2 →
        ‖A.a1Lo (I := I) (M := M) -
            B.a1Lo (I := I) (M := M)‖ ≤ C * (R0 + R1) := by
  obtain ⟨C0, hC0, happ0⟩ :=
    appRS_h1_h2_h1 (I := I) (M := M) hDim g 0 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g 0 3 2
  obtain ⟨Cs, hCs, hspec⟩ :=
    a1_spec_lo (I := I) (M := M) g
  let Ca : ℝ := 2 * (C0 + C1)
  let C : ℝ := Cs * Ca
  have hCa : 0 ≤ Ca :=
    mul_nonneg (by norm_num) (add_nonneg hC0 hC1)
  refine ⟨C, mul_nonneg hCs hCa, ?_⟩
  intro A B R0 R1 hR0 hR1 hA0 hA1
  let D : LowBaseActionData g := a1Delta A B
  let R : ℝ := R0 + R1
  let Q : ℝ := (Ca * R) ^ 2
  have hR : 0 ≤ R := add_nonneg hR0 hR1
  have hQ : 0 ≤ Q := sq_nonneg _
  have hD0 :
      lowJetSq (I := I) (M := M) g 1 D.C0 ≤ R0 ^ 2 := by
    simpa only [D, a1Delta] using hA0
  have hD1 :
      lowJetSq (I := I) (M := M) g 2 D.C1 ≤ R1 ^ 2 := by
    simpa only [D, a1Delta] using hA1
  have hact : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (D.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    let Y0 : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 2 2 D.C0 W
    let Y1 : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 3 2 D.C1
        (iteratedCovGrad (I := I) g 0 2 1 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    have hGW :
        lowJetSq (I := I) (M := M) g 1
            (iteratedCovGrad (I := I) g 0 2 1 W) ≤ S ^ 2 := by
      rw [hSsq]
      exact grad_jet1_pair (I := I) (M := M) g W
    have hY0 :
        ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          C0 * R0 * S := by
      simpa only [Y0, appCcRS_zero_eq_appCc, lowJetSq,
        Nat.reduceAdd] using
        happ0 D.C0 W R0 S hR0 hS
          (by simpa only [lowJetSq, Nat.reduceAdd] using hD0)
          (by
            rw [hSsq]
            exact le_rfl)
    have hY1 :
        ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          C1 * R1 * S := by
      simpa only [Y1, appCcRS_zero_eq_appCc, lowJetSq,
        Nat.reduceAdd] using
        happ1 D.C1
          (iteratedCovGrad (I := I) g 0 2 1 W)
          R1 S hR1 hS
          (by simpa only [lowJetSq, Nat.reduceAdd] using hD1)
          (by simpa only [lowJetSq, Nat.reduceAdd] using hGW)
    have hsum :
        ‖(⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
          Ca * R * S := by
      calc
        ‖(⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤
            ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ +
              ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ := norm_add_le _ _
        _ ≤ C0 * R0 * S + C1 * R1 * S := add_le_add hY0 hY1
        _ ≤ Ca * R * S := by
          simp only [Ca, R]
          nlinarith [mul_nonneg hC0 hR0, mul_nonneg hC1 hR1,
            mul_nonneg hC0 hR1, mul_nonneg hC1 hR0]
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y0 + Y1⟩ : SmoothCcTensorH1 g 0 2))
      hsum 2
    rw [h1_jet_sq (I := I) (M := M) g 0 2 (Y0 + Y1)] at hsq
    have hjet :
        lowJetSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
          (Ca * R * S) ^ 2 := by
      simpa only [lowJetSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, Nat.reduceAdd,
        iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
    change lowJetSq (I := I) (M := M) g 1 (Y0 + Y1) ≤ _
    calc
      lowJetSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
          (Ca * R * S) ^ 2 := hjet
      _ = Q * lowJetSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hDlo :
      ‖D.a1Lo (I := I) (M := M)‖ ≤
        Cs * Real.sqrt Q := by
    unfold LowBaseActionData.a1Lo
    exact LinearMap.opNorm_extendOfNorm_le
      hdense2 (mul_nonneg hCs (Real.sqrt_nonneg _))
        (hspec D Q hQ hact)
  have hsqrtQ : Real.sqrt Q = Ca * R := by
    rw [show Q = (Ca * R) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hCa hR)]
  have hbound :
      ‖D.a1Lo (I := I) (M := M)‖ ≤ C * (R0 + R1) := by
    calc
      ‖D.a1Lo (I := I) (M := M)‖ ≤
          Cs * Real.sqrt Q := hDlo
      _ = C * (R0 + R1) := by
        rw [hsqrtQ]
        simp only [C, R]
        ring
  have hLo :
      D.a1Lo (I := I) (M := M) =
        A.a1Lo (I := I) (M := M) -
          B.a1Lo (I := I) (M := M) := by
    let L := D.a1Lo (I := I) (M := M)
    let P := A.a1Lo (I := I) (M := M) -
      B.a1Lo (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense2.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          ContinuousLinearMap.sub_apply]
        rw [a1Lo_core_any (I := I) (M := M) hDim g D W,
          a1Lo_core_any (I := I) (M := M) hDim g A W,
          a1Lo_core_any (I := I) (M := M) hDim g B W,
          a1Delta_apply (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (A.a1 (I := I) (M := M) W)
            (B.a1 (I := I) (M := M) W))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  rwa [← hLo]

/-- A two-jet bound on the difference of the first-order coefficients controls
the differences of both adjacent-scale completed actions. -/
theorem a1_diff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowBaseActionData g) (R : ℝ), 0 ≤ R →
        lowJetSq (I := I) (M := M) g 2 (A.C0 - B.C0) +
            lowJetSq (I := I) (M := M) g 2 (A.C1 - B.C1) ≤ R ^ 2 →
        ‖A.a1Hi (I := I) (M := M) -
            B.a1Hi (I := I) (M := M)‖ ≤ C * R ∧
        ‖A.a1Lo (I := I) (M := M) -
            B.a1Lo (I := I) (M := M)‖ ≤ C * R := by
  obtain ⟨Cp, hCp, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    a1_h2_h1 (I := I) (M := M) hDim g
  let Ca : ℝ := Ch + Cl
  let C : ℝ := Cp * Ca
  refine ⟨C, mul_nonneg hCp (add_nonneg hCh hCl), ?_⟩
  intro A B R hR hcoeff
  let D : LowBaseActionData g := a1Delta A B
  let Q : ℝ := (Ca * R) ^ 2
  have hCa : 0 ≤ Ca := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hDcoeff :
      lowJetSq (I := I) (M := M) g 2 D.C0 +
          lowJetSq (I := I) (M := M) g 2 D.C1 ≤ R ^ 2 := by
    simpa only [D, a1Delta] using hcoeff
  have hHiAct : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          (D.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 3 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = lowJetSq (I := I) (M := M) g 3 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 2
          (D.a1 (I := I) (M := M) W) ≤
          (Ch * R * S) ^ 2 :=
        hhigh D W R S hR hS hDcoeff (by rw [hSsq])
      _ ≤ (Ca * R * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hR) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hR) hS) 2
      _ = Q * lowJetSq (I := I) (M := M) g 3 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hLoAct : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (D.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq :
        S ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 1
          (D.a1 (I := I) (M := M) W) ≤
          (Cl * R * S) ^ 2 :=
        hlow D W R S hR hS hDcoeff (by rw [hSsq])
      _ ≤ (Ca * R * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hR) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hR) hS) 2
      _ = Q * lowJetSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * R * S) ^ 2 = (Ca * R) ^ 2 * S ^ 2 by ring,
          hSsq]
  obtain ⟨hDhi, hDlo, hDhiCore, hDloCore, _⟩ :=
    hpair D Q hQ hHiAct hLoAct
  have hsqrtQ : Real.sqrt Q = Ca * R := by
    rw [show Q = (Ca * R) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hCa hR)]
  have hDhi' :
      ‖D.a1Hi (I := I) (M := M)‖ ≤ C * R := by
    calc
      ‖D.a1Hi (I := I) (M := M)‖ ≤ Cp * Real.sqrt Q := hDhi
      _ = C * R := by rw [hsqrtQ]; simp only [C]; ring
  have hDlo' :
      ‖D.a1Lo (I := I) (M := M)‖ ≤ C * R := by
    calc
      ‖D.a1Lo (I := I) (M := M)‖ ≤ Cp * Real.sqrt Q := hDlo
      _ = C * R := by rw [hsqrtQ]; simp only [C]; ring
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense2 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHi :
      D.a1Hi (I := I) (M := M) =
        A.a1Hi (I := I) (M := M) -
          B.a1Hi (I := I) (M := M) := by
    let L := D.a1Hi (I := I) (M := M)
    let P := A.a1Hi (I := I) (M := M) -
      B.a1Hi (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense3.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          ContinuousLinearMap.sub_apply]
        rw [hDhiCore,
          a1Hi_core_any (I := I) (M := M) hDim g A W,
          a1Hi_core_any (I := I) (M := M) hDim g B W,
          a1Delta_apply (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
            (A.a1 (I := I) (M := M) W)
            (B.a1 (I := I) (M := M) W))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  have hLo :
      D.a1Lo (I := I) (M := M) =
        A.a1Lo (I := I) (M := M) -
          B.a1Lo (I := I) (M := M) := by
    let L := D.a1Lo (I := I) (M := M)
    let P := A.a1Lo (I := I) (M := M) -
      B.a1Lo (I := I) (M := M)
    have hfun : (L : _ → _) = P :=
      hdense2.equalizer L.continuous P.continuous (by
        funext W
        simp only [Function.comp_apply, L, P, ccToHsLin_apply,
          ContinuousLinearMap.sub_apply]
        rw [hDloCore,
          a1Lo_core_any (I := I) (M := M) hDim g A W,
          a1Lo_core_any (I := I) (M := M) hDim g B W,
          a1Delta_apply (I := I) (M := M) A B W]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (A.a1 (I := I) (M := M) W)
            (B.a1 (I := I) (M := M) W))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  constructor
  · rwa [← hHi]
  · rwa [← hLo]

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
