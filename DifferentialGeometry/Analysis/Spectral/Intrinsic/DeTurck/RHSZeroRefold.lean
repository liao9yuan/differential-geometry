import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RefoldPairingCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSLowCoeff

/-!
# Low-regularity order-zero Ricci--DeTurck refold

The raw order-zero Ricci--DeTurck coefficient contains second derivatives of
the moving metric.  This file removes those derivatives by exact Palatini
pairing before any Sobolev estimate is taken.  The resulting order-zero and
order-two coefficients are explicit and require no high-jet hypotheses.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The first canonical Palatini permutation family for the Ricci refold. -/
def ricciRefoldQA : Fin 4 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1]

/-- The paired canonical Palatini permutation family for the Ricci refold. -/
def ricciRefoldQB : Fin 4 → Equiv.Perm (Fin 4) :=
  fun k => Equiv.swap (0 : Fin 4) 1 * ricciRefoldQA k

/-- The canonical permutation family for the DeTurck covariant-derivative
refold. -/
def lieRefoldQ : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
    Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
      Equiv.swap (0 : Fin 4) 1,
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]

/-- The signs of the three canonical DeTurck refold monomials. -/
def lieRefoldEps : Fin 3 → ℝ := ![(-1 : ℝ), -1, 1]

/-- The explicit lower Ricci coefficient after the Palatini second-derivative
piece has been removed. -/
def ricciRefold0
    (g g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciArmOrder0RiemannCoeff (I := I) (M := M) g g +
    (2 : ℝ) •
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g g₁ +
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g₁ -
              ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g)
            (ccInputSlotSwapField (I := I) (M := M) g) +
          (1 / 2 : ℝ) •
            ricciArmSharpGradKoszulResidualField (I := I) (M := M) g g₁ P -
          ricciArmRicciFoldRemainderField (I := I) (M := M) g g₁ P))

/-- The Ricci second-order coefficient carrying the derivatives removed from
`ricciRefold0`. -/
def ricciRefold2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  (2 : ℝ) • riemannPalatiniRefoldC2Family
    (I := I) (M := M) g T hδ hδZ ricciRefoldQA ricciRefoldQB s

/-- The lower DeTurck covariant-derivative coefficient after its second-order
pair trace has been removed. -/
def lieRefold0
    (g g₁ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  deTurckLieCovDerivArmField (I := I) (M := M) g g₁ g_bg -
    edgeLiePairFam (I := I) (M := M) g T hδ hδZ
      lieRefoldQ lieRefoldEps s

/-- The DeTurck second-order coefficient carrying the derivatives removed
from `lieRefold0`. -/
def lieRefold2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  deTurckLieCovDerivRefoldC2Family
    (I := I) (M := M) g T hδ hδZ lieRefoldQ lieRefoldEps s

/-- The complete lower order-zero coefficient after the Ricci and DeTurck
second-derivative pieces have been refolded. -/
def rhsRefold0
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let g₁ := realizedFam (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • edgeRicciHalf (I := I) (M := M) g g₁ +
    ricciRefold0 (I := I) (M := M) g g₁ (s • T) +
    (lieRefold0 (I := I) (M := M) g g₁ g_bg T hδ hδZ s +
      deTurckLieEndoArmField (I := I) (M := M) g g₁ g_bg +
      lieCorr0Field (I := I) (M := M) g g₁ g_bg)

/-- The complete second-order coefficient produced by the order-zero
Ricci--DeTurck refold. -/
def rhsRefold2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  ricciRefold2 (I := I) (M := M) g T hδ hδZ s +
    lieRefold2 (I := I) (M := M) g T hδ hδZ s

omit [BoundarylessManifold I M] in
private lemma bilin_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (c • S) x v w =
      c * ccTensorBilin (I := I) g S x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

private lemma symmS_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g S x v w =
        ccTensorBilin (I := I) g S x w v) :
    symmS (I := I) (M := M) g S = S := by
  exact foldSymmS_eq_self (I := I) (M := M) g S hS

private lemma ricciRefold2_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    ricciRefold2 (I := I) (M := M) g T hδ hδZ s =
      (2 * s : ℝ) • curvatureRefoldKernelCoeffField
        (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g T)
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  have hsymm : symmS (I := I) (M := M) g T = T :=
    symmS_eq_self (I := I) (M := M) g T hT
  rw [ricciRefold2,
    riemannC2_eq_kernel (I := I) (M := M) g T hδ hδZ
      ricciRefoldQA ricciRefoldQB (fun _ => rfl) s,
    hsymm, smul_smul]
  rfl

/-- The Ricci order-zero action is exactly its lower refold plus the new
second-order action. -/
theorem ricciRefold_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s)) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciRefold0 (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ s) (s • T)) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciRefold2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g T 0 hδ hδZ s).inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g (s • T) y v w := by
    intro y v w
    rw [← show convexPerturbation (I := I) g T 0 s = s • T by
      rw [convexPerturbation, smul_zero, zero_add]]
    exact realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ hs_mem y v w
  have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (s • T) x v w =
        ccTensorBilin (I := I) g (s • T) x w v := by
    intro x v w
    rw [bilin_smul (I := I) (M := M), bilin_smul (I := I) (M := M), hT x v w]
  have hprim :=
    ricciArmOrder0RiemannHalfBgDiff_appCc_eq_residualFieldSum_add_refoldKernelSecondGrad
      (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) (s • T) htie hPsymm T
  have hC2 := ricciRefold2_eq (I := I) (M := M) g T hT hδ hδZ s
  rw [ricciRefold0, hC2, appCc_add_left, appCc_smul_left,
    appCc_smul_left]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real,
    appCc_smul_right] at hprim
  have htwice :
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ s)) T -
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g) T =
      (2 : ℝ) • ((1 / 2 : ℝ) •
        (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ s)) T -
          operatorFieldApply (I := I) (M := M) g 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g) T)) := by
    rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  rw [hprim] at htwice
  rw [sub_eq_iff_eq_add] at htwice
  rw [htwice]
  module

/-- The DeTurck covariant-derivative action is exactly its lower pair-trace
remainder plus the new second-order action. -/
theorem lieRefold_app
    (g g₁ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (deTurckLieCovDerivArmField (I := I) (M := M) g g₁ g_bg) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lieRefold0 (I := I) (M := M) g g₁ g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (lieRefold2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [lieRefold0, lieRefold2, foldAppCc_sub_left,
    edgeLiePair_apply (I := I) (M := M) g T hδ hδZ lieRefoldQ lieRefoldEps s]
  abel

/-- The actual order-zero Ricci--DeTurck path coefficient, applied to the
metric deviation, is the sum of a genuinely lower coefficient and an
explicit second-order coefficient.  No high-regularity radius is assumed. -/
theorem rhsLow0_refold
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (DeTurckCoefficients.rhsLow0Coeff
          (I := I) (M := M) g g_bg T 0 hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsRefold0 (I := I) (M := M) g g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsRefold2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  have hRic := ricciRefold_app (I := I) (M := M) g T hT hδ_lt hδ hδZ hs
  have hLie := lieRefold_app (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) g_bg T hδ hδZ s
  rw [DeTurckCoefficients.rhsLow0Coeff, rhsRefold0, rhsRefold2,
    deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
    edgeRicciHalf]
  change
    operatorFieldApply (I := I) (M := M) g 2 2
        ((-2 : ℝ) •
            linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ s) +
          (deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ s) g_bg +
            deTurckLieEndoArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ s) g_bg +
            lieCorr0Field (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ s) g_bg)) T =
      _
  simp only [appCc_add_left, appCc_smul_left]
  rw [hRic, hLie]
  module

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
