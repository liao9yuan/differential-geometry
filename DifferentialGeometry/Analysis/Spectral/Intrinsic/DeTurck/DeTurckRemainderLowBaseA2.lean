import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.AppD2Hs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

/-!
# Compatible completions of the low-base second-order action

This module completes the single smooth-core formula
`LowBaseActionData.a2` on the adjacent Sobolev scales used by the
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private noncomputable def lowA2Core
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (σ : ℝ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      tensorHs (I := I) (M := M) g 0 2 σ where
  toFun := fun W =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (A.a2 (I := I) (M := M) W)
  map_add' := fun W V => by
    simp only [LowBaseActionData.a2, iteratedCovGrad_add,
      appCc_add_right, ccTensorToHs_add]
  map_smul' := fun c W => by
    simp only [RingHom.id_apply, LowBaseActionData.a2,
      iteratedCovGrad_smul, appCc_smul_right, ccTensorToHs_smul]

/-- The complete low-base second-order action on the high adjacent scale. -/
noncomputable def LowBaseActionData.a2Hi
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g) :
    tensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  appD2Hs (I := I) (M := M) g 2 2 A.C2

/-- The same low-base second-order action on the lower adjacent scale. -/
noncomputable def LowBaseActionData.a2Lo
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g) :
    tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (lowA2Core (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

/-- Pointwise and two-jet bounds on one coefficient give compatible
`H4 → H2` and `H3 → H1` completions of its second-order action. -/
theorem a2_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (B : ℝ), 0 ≤ B →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.C2.toSection x) ≤ B ^ 2) →
        lowJetSq (I := I) (M := M) g 2 A.C2 ≤ B ^ 2 →
        ‖A.a2Hi (I := I) (M := M)‖ ≤ C * B ∧
        ‖A.a2Lo (I := I) (M := M)‖ ≤ C * B ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a2Hi (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (A.a2 (I := I) (M := M) W)) ∧
        (∀ W : SmoothCcTensor g 0 2,
          A.a2Lo (I := I) (M := M)
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (A.a2 (I := I) (M := M) W)) ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.a2Hi (I := I) (M := M)) =
          (A.a2Lo (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    appD2Hs_norm (I := I) (M := M) hDim g 2 2
  obtain ⟨Cl, hCl, hlow⟩ :=
    appCc_h2_h3_h1 (I := I) (M := M) hDim g 2 2
  let C : ℝ := Ch + Cl
  refine ⟨C, add_nonneg hCh hCl, ?_⟩
  intro A B hB hsup hjet
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hlowMap :
      ∀ W : SmoothCcTensor g 0 2,
        ‖lowA2Core (I := I) (M := M) g A (1 : ℝ) W‖ ≤
          (Cl * B) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
    intro W
    simpa only [lowA2Core, LowBaseActionData.a2, lowJetSq,
      Nat.reduceAdd] using hlow A.C2 W B hB hsup hjet
  have hHiNorm :
      ‖A.a2Hi (I := I) (M := M)‖ ≤ Ch * B := by
    simpa only [LowBaseActionData.a2Hi, lowJetSq] using
      hhigh A.C2 B hB hjet
  have hLoNorm :
      ‖A.a2Lo (I := I) (M := M)‖ ≤ Cl * B := by
    unfold LowBaseActionData.a2Lo
    exact LinearMap.opNorm_extendOfNorm_le
      hdense3 (mul_nonneg hCl hB) hlowMap
  have hHiCore (W : SmoothCcTensor g 0 2) :
      A.a2Hi (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (A.a2 (I := I) (M := M) W) := by
    simpa only [LowBaseActionData.a2Hi, LowBaseActionData.a2] using
      appD2Hs_core (I := I) (M := M) hDim g 2 2 A.C2 W
  have hLoCore (W : SmoothCcTensor g 0 2) :
      A.a2Lo (I := I) (M := M)
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.a2 (I := I) (M := M) W) := by
    change
      ((lowA2Core (I := I) (M := M) g A (1 : ℝ)).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) W) =
        (lowA2Core (I := I) (M := M) g A (1 : ℝ)) W
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Cl * B, hlowMap⟩
  have hHiNorm' :
      ‖A.a2Hi (I := I) (M := M)‖ ≤ C * B :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hCl) hB)
  have hLoNorm' :
      ‖A.a2Lo (I := I) (M := M)‖ ≤ C * B :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hCh) hB)
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.a2Hi (I := I) (M := M))
  let R :=
    (A.a2Lo (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hfun : (L : _ → _) = R :=
    hdense4.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W := by
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

private noncomputable def a2Delta
    {g : SmoothRiemannianMetric I M}
    (A B : LowBaseActionData g) : LowBaseActionData g where
  C0 := 0
  C1 := 0
  C2 := A.C2 - B.C2

/-- The high adjacent-scale realization agrees with the smooth second-order
action on the dense smooth core. -/
theorem a2Hi_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a2Hi (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.a2 (I := I) (M := M) W) := by
  simpa only [LowBaseActionData.a2Hi, LowBaseActionData.a2] using
    appD2Hs_core (I := I) (M := M) hDim g 2 2 A.C2 W

/-- The low adjacent-scale realization agrees with the same smooth
second-order action on the dense smooth core. -/
theorem a2Lo_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) :
    A.a2Lo (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.a2 (I := I) (M := M) W) := by
  obtain ⟨C, hC, hpair⟩ := a2_pair (I := I) (M := M) hDim g
  obtain ⟨K, hK, hpoint⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 4 2 A.C2
  let J : ℝ := lowJetSq (I := I) (M := M) g 2 A.C2
  let B : ℝ := Real.sqrt (K + J)
  have hJ : 0 ≤ J := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : 0 ≤ K + J := add_nonneg hK hJ
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = K + J := by
    simpa only [B] using Real.sq_sqrt hsum
  have hpointB : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (A.C2.toSection x) ≤ B ^ 2 := by
    intro x
    rw [hBsq]
    exact (hpoint x).trans (le_add_of_nonneg_right hJ)
  have hjetB :
      lowJetSq (I := I) (M := M) g 2 A.C2 ≤ B ^ 2 := by
    rw [hBsq]
    exact le_add_of_nonneg_left hK
  exact (hpair A B hB hpointB hjetB).2.2.2.1 W

/-- The two adjacent-scale realizations of one second-order action commute
with the canonical Sobolev inclusions. -/
theorem a2_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.a2Hi (I := I) (M := M)) =
      (A.a2Lo (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  let L :=
    (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (A.a2Hi (I := I) (M := M))
  let R :=
    (A.a2Lo (I := I) (M := M)).comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hfun : (L : _ → _) = R :=
    hdense4.equalizer L.continuous R.continuous (by
      funext W
      simp only [Function.comp_apply, L, R, ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [a2Hi_core (I := I) (M := M) hDim g A]
      have hin :
          tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W := by
        apply tensorHs.ext
        funext i
        simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
      rw [hin, a2Lo_core (I := I) (M := M) hDim g A]
      apply tensorHs.ext
      funext i
      simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro W
  exact congrFun hfun W

/-- A two-jet bound on the difference of two second-order coefficients
controls the differences of both adjacent-scale completed actions. -/
theorem a2_diff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B : LowBaseActionData g) (R : ℝ), 0 ≤ R →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((A.C2 - B.C2).toSection x) ≤ R ^ 2) →
        lowJetSq (I := I) (M := M) g 2 (A.C2 - B.C2) ≤ R ^ 2 →
        ‖A.a2Hi (I := I) (M := M) -
            B.a2Hi (I := I) (M := M)‖ ≤ C * R ∧
        ‖A.a2Lo (I := I) (M := M) -
            B.a2Lo (I := I) (M := M)‖ ≤ C * R := by
  obtain ⟨C, hC, hpair⟩ := a2_pair (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro A B R hR hpoint hjet
  let D : LowBaseActionData g := a2Delta A B
  have hDpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (D.C2.toSection x) ≤ R ^ 2 := by
    simpa only [D, a2Delta] using hpoint
  have hDjet :
      lowJetSq (I := I) (M := M) g 2 D.C2 ≤ R ^ 2 := by
    simpa only [D, a2Delta] using hjet
  obtain ⟨hDhi, hDlo, hDhiCore, hDloCore, _⟩ :=
    hpair D R hR hDpoint hDjet
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHi :
      D.a2Hi (I := I) (M := M) =
        A.a2Hi (I := I) (M := M) -
          B.a2Hi (I := I) (M := M) := by
    let L := D.a2Hi (I := I) (M := M)
    let Q := A.a2Hi (I := I) (M := M) -
      B.a2Hi (I := I) (M := M)
    have hfun : (L : _ → _) = Q :=
      hdense4.equalizer L.continuous Q.continuous (by
        funext W
        simp only [Function.comp_apply, L, Q, ccToHsLin_apply,
          ContinuousLinearMap.sub_apply]
        rw [hDhiCore,
          a2Hi_core (I := I) (M := M) hDim g A W,
          a2Hi_core (I := I) (M := M) hDim g B W]
        simp only [D, a2Delta, LowBaseActionData.a2, appCc_sub_left]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
            (appCc (I := I) (M := M) g 4 2 A.C2
              (iteratedCovGrad (I := I) g 0 2 2 W))
            (appCc (I := I) (M := M) g 4 2 B.C2
              (iteratedCovGrad (I := I) g 0 2 2 W)))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  have hLo :
      D.a2Lo (I := I) (M := M) =
        A.a2Lo (I := I) (M := M) -
          B.a2Lo (I := I) (M := M) := by
    let L := D.a2Lo (I := I) (M := M)
    let Q := A.a2Lo (I := I) (M := M) -
      B.a2Lo (I := I) (M := M)
    have hfun : (L : _ → _) = Q :=
      hdense3.equalizer L.continuous Q.continuous (by
        funext W
        simp only [Function.comp_apply, L, Q, ccToHsLin_apply,
          ContinuousLinearMap.sub_apply]
        rw [hDloCore,
          a2Lo_core (I := I) (M := M) hDim g A W,
          a2Lo_core (I := I) (M := M) hDim g B W]
        simp only [D, a2Delta, LowBaseActionData.a2, appCc_sub_left]
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (1 : ℝ))
            (appCc (I := I) (M := M) g 4 2 A.C2
              (iteratedCovGrad (I := I) g 0 2 2 W))
            (appCc (I := I) (M := M) g 4 2 B.C2
              (iteratedCovGrad (I := I) g 0 2 2 W)))
    apply ContinuousLinearMap.ext
    intro W
    exact congrFun hfun W
  constructor
  · rwa [← hHi]
  · rwa [← hLo]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
