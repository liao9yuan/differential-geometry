import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSZeroRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSThreeArmCancel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathIntegral
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ThreeArmJointAlgebra

/-!
# Refolded Ricci--DeTurck slope arms

This module combines the exact order-zero refold with the complete three-arm
Ricci--DeTurck slope.  It is purely algebraic: no Sobolev or high-jet
hypothesis is introduced.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The complete second-order coefficient after the order-zero Palatini and
DeTurck pair-trace pieces have been returned to the top arm. -/
def rhsRefoldTop
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  rhsRefold2 (I := I) (M := M) g T hδ hδZ s +
    deTurckPhiMetTotal (I := I) (M := M) g g_bg
      (realizedFam (I := I) g T 0 hδ hδZ s)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- The DeTurck second-order refold is jointly smooth on the realized metric
segment. The finite jet radius used to project the existing quantitative
theorem is chosen inside the proof and does not occur in this interface. -/
theorem lieRefold2_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (lieRefold2 (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  classical
  let a := 2 * Module.finrank ℝ E + 10
  let R : ℝ :=
    Finset.sum (Finset.range (a + 3))
      (fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
  have ha : 2 * Module.finrank ℝ E + 10 ≤ a := by
    simp [a]
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hball :
      ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ R := by
    intro j hj
    dsimp [R]
    exact Finset.single_le_sum
      (fun k _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T))
      (Finset.mem_range.mpr (by omega))
  have hε : ∀ i, |lieRefoldEps i| ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [lieRefoldEps]
  obtain ⟨K, hK, hmain⟩ :=
    exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow
      (I := I) (M := M) g a ha hR hδ_lt lieRefoldQ lieRefoldEps hε
  simpa only [lieRefold2] using
    (hmain T le_rfl hδ hδZ hball).1

/-- The complete refolded top coefficient is jointly smooth along the realized
metric segment, with no theorem-facing high-jet hypothesis. -/
theorem rhsRefoldTop_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (rhsRefoldTop (I := I) (M := M) g g_bg T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hRic0 :=
    riemannPalatiniRefoldC2Family_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ ricciRefoldQA ricciRefoldQB
  have hRic := threeArmJoint_smul (I := I) (M := M) g (2 : ℝ) _ hRic0
  have hLie := lieRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hRefold := threeArmJoint_add (I := I) (M := M) g _ _ hRic hLie
  have hTop := rhsTop_path_joint (I := I) (M := M) g g_bg T 0 hδ hδZ
  have hAll := threeArmJoint_add (I := I) (M := M) g _ _ hRefold hTop
  simpa only [rhsRefoldTop, rhsRefold2, ricciRefold2, lieRefold2] using hAll

omit [BoundarylessManifold I M] in
private theorem zero_symm (g : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
  rw [h0]
  simp only [ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, zero_mul]

/-- Along the segment from the carrier to a symmetric metric deviation, the
complete Ricci--DeTurck slope is exactly the refolded zero-, one-, and
two-order background-covariant expression. -/
theorem rhsSlope_refold
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g g_bg T 0 hδ_lt hδ hδ_lt hδZ x v w s =
      unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
            (rhsRefold0 (I := I) (M := M) g g_bg T hδ hδZ s) T +
          appCc (I := I) (M := M) g 3 2
            (rhsLow1Coeff (I := I) (M := M) g g_bg T 0 hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          appCc (I := I) (M := M) g 4 2
            (rhsRefoldTop (I := I) (M := M) g g_bg T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 2 T)) x ![v, w] := by
  rw [rhsSlope_eq_arms (I := I) (M := M) g g_bg T 0 hT
    (zero_symm (I := I) (M := M) g) hδ_lt hδ hδ_lt hδZ x v w hs]
  simp only [sub_zero, iteratedCovGrad_zero]
  rw [rhsLow0_refold (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  simp only [rhsRefoldTop, appCc_add_left]
  apply congrArg (fun Z : SmoothCcTensor g 0 2 =>
    unitModel (I := I) (M := M) g 2 Z x ![v, w])
  abel

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
