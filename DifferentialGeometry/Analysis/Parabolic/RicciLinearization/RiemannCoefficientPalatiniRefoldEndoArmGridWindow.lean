import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in

theorem covDerivArmField_eq_dLaCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem endoArmField_eq_dLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem threeArmHjoint_add_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option linter.unusedSectionVars false in

theorem threeArmHjoint_sub_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

set_option linter.unusedSectionVars false in

theorem covDerivArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have h := dLaBiContrFib_realizedFam_jointContMDiffOn (I := I) (M := M)
    g₀ T 0 hδ hδZ g_bg
  refine h.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem endoArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieEndoArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have hC := deTurckLieCoeffField_realizedFam_jointContMDiff (I := I)
    g₀ T 0 hδ hδZ g_bg
  have hA := covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M)
    g₀ T hδ hδZ g_bg
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (deTurckLieCovDerivArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    hC hA
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  show (deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1 =
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
      - (deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
  have hsplit : deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg
        - deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (deTurckLieCoeffField_eq_covDerivArm_add_endoArm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).symm
  rw [hsplit, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

set_option linter.unusedSectionVars false in

theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
theorem bdExists_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

set_option linter.unusedSectionVars false in
lemma bdRfns_iCG_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

set_option linter.unusedSectionVars false in
private lemma bdAppCcRS_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g a b c Φ W₁ - appCcRS (I := I) (M := M) g a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₁ -
        appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (appCcRS (I := I) (M := M) g a b c Φ W₁).toSection x -
        (appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

set_option linter.unusedSectionVars false in
private def bdVFSec (g₁ gA gB : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ gA : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) -
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

set_option linter.unusedSectionVars false in
private lemma bdVFSec_apply (g₁ gA gB : SmoothRiemannianMetric I M) (b : M) :
    bdVFSec (I := I) (M := M) g₁ gA gB b =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b -
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b := by
  rw [bdVFSec, ContMDiffSection.coe_sub, Pi.sub_apply]

private def bdXiFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  connDiffLoweredCc (I := I) g₀ g₀ - connDiffLoweredCc (I := I) g₀ g_bg

private def bdOmegaGen (g₀ g₁ gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc)

private def bdOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg)

set_option linter.unusedSectionVars false in
private lemma bdOmega_eq_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    bdOmega (I := I) (M := M) g₀ g₁ g_bg =
      bdOmegaGen (I := I) (M := M) g₀ g₁ g_bg - bdOmegaGen (I := I) (M := M) g₀ g₁ g₀ := by
  rw [bdOmegaGen, bdOmegaGen, ← bdAppCcRS_sub_right, bdOmega]
  congr 1
  rw [bdXiFix]
  abel

set_option linter.unusedSectionVars false in
lemma bdUnitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
lemma bdUnitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma bdConnDiffLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
lemma bdConnDiffLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [bdConnDiffLoweredCc_unitModel]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdXiGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x (m 0) (m 1)) (m 2) := by
  rw [bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdConnDiffLoweredCc_unitModel_apply, bdConnDiffLoweredCc_unitModel_apply]
  rw [show g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, ContinuousLinearMap.sub_apply]]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ gc x (m 0) (m 1)]

set_option linter.unusedSectionVars false in
private lemma bdOmegaGen_toSection_unit (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmegaGen (I := I) (M := M) g₀ g₁ gc).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [bdOmegaGen, appCcRS_toSection]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdOmegaGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmegaGen (I := I) (M := M) g₀ g₁ gc) x
        (fun _ : Fin 1 => z) =
      g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) z := by
  classical
  rw [unitModel, bdOmegaGen_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) (fun _ : Fin 1 => z) =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x) (vs := fun _ : Fin 1 => z)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
        (fun _ : Fin 1 => (show E from z)))]
    have hm : Tensor0SSpace.toModel D
        (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
          (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
            (fun _ : Fin 1 => (show E from z)))) =
        unitModel (I := I) (M := M) g₀ 3
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x
          ![smoothOrthoFrame (I := I) g₁ x i x, smoothOrthoFrame (I := I) g₁ x i x, z] := by
      rw [unitModel, ← hD]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hm, bdXiGen_unitModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, ContinuousLinearMap.sum_apply]]
  rw [← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gc x]

set_option linter.unusedSectionVars false in
private lemma bdOmega_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => z) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) z := by
  rw [bdOmega_eq_sub, bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdOmegaGen_unitModel_apply, bdOmegaGen_unitModel_apply, bdVFSec_apply]
  rw [map_sub, ContinuousLinearMap.sub_apply]

private def bdAlphaA (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg))

private def bdCA (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (connDiffLoweredCc (I := I) g₀ g₁))

private def bdAlphaB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  appCcRS (I := I) (M := M) g₀ 0 1 2 (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg)

private def bdAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  bdAlphaA (I := I) (M := M) g₀ g₁ g_bg + bdAlphaB (I := I) (M := M) g₀ g₁ g_bg

set_option linter.unusedSectionVars false in
private lemma bdTensor0SCovDeriv01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (Y x) (fun i => Fin.elim0 i)) =
      directionalDeriv (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v)
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) (m 0) :=
    bdOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x (m 0)
  rw [hL]
  have hR : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)) (m 0) := by
    rw [cotangentToDual_apply]
    rfl
  rw [hR, cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdUnitEvalSection_bdOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) z := by
  rw [unitEvalSection_apply]
  rw [show (unitZeroSec (I := I) (M := M) b) = unitTensor (I := I) (M := M) b from rfl]
  rw [bdOmega_toSection_unit_eq_flat]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (fun _ : Fin 1 => (show E from z))
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
private lemma bdAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [bdAlphaA, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, w] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![w, u] from by
    funext i; fin_cases i <;> simp]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x) ![w, u]]
  rw [show (![w, u] : Fin 2 → TangentSpace I x) 0 = w from rfl]
  rw [show Matrix.vecTail (![w, u] : Fin 2 → TangentSpace I x) = ![u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x w]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons (Y x) (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [bdTensor0SCovDeriv01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (Y b) (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (Y b)) := by
    funext b
    exact bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDeriv_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (W := fun b => Y b)
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀).contMDiff Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w)
        (fun i => Fin.elim0 i)) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

set_option linter.unusedSectionVars false in
lemma bdInterior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdAlphaB_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) u := by
  classical
  rw [unitModel, bdAlphaB, appCcRS_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [bdOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [bdCA, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (Fin.cons (show E from bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        (fun k : Fin 2 => (show E from (![u, w] : Fin 2 → TangentSpace I x) k))) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁)) x
        ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] := by
    rw [unitModel, ← hD]
    rfl
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] :
        Fin 3 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, w, u] from by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

set_option linter.unusedSectionVars false in
private lemma bdLeviCivita_toFun_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    (LeviCivita (I := I) g₀).toFun (fun b => A b - B b) x w =
      (LeviCivita (I := I) g₀).toFun (fun b => A b) x w -
        (LeviCivita (I := I) g₀).toFun (fun b => B b) x w := by
  have hsub : (fun b : M => A b - B b) =
      (fun b : M => A b) + (fun b : M => ((-1 : ℝ) • B) b) := by
    funext b
    rw [Pi.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply, neg_one_smul,
      sub_eq_add_neg]
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => A b) (σ' := fun b : M => ((-1 : ℝ) • B) b) (x := x)
    (A.mdifferentiableAt (x := x)) (((-1 : ℝ) • B).mdifferentiableAt (x := x))
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => B b) (a := (-1 : ℝ)) (x := x) (B.mdifferentiableAt (x := x))
  have hcoe : (fun b : M => ((-1 : ℝ) • B) b) = (-1 : ℝ) • (fun b : M => B b) := by
    funext b
    rw [ContMDiffSection.coe_smul]
  rw [hsub, hadd]
  rw [hcoe, hsmul]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, neg_one_smul,
    sub_eq_add_neg]

set_option linter.unusedSectionVars false in
private lemma bdWEndo_eq_covDeriv_add_connDiff (g₀ g₁ gc : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
  have hcd := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀
    (σ := fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) (x := x)
    (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯).mdifferentiableAt w
  have hEndo : deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₁).toFun
        (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := rfl
  rw [hEndo, hcd]
  abel

set_option linter.unusedSectionVars false in
private lemma bdWEndo_sub_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w := by
  rw [bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g_bg x w,
    bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g₀ x w]
  have hLC : (LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w -
        (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := by
    have h := bdLeviCivita_toFun_sub (I := I) (M := M) g₀
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x w
    rw [← h]
    rfl
  have hcd : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
    rw [bdVFSec_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [hLC, hcd]
  abel

set_option linter.unusedSectionVars false in
lemma bdCotangentToDual_slotInsertEndoFib (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k; fin_cases k; simp]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdCotangentToDual_cometricRaise_bdAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (bdAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) x
        ![inverseMetricSharpFib (I := I) g₀ x om, w] := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => w) from rfl]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

set_option linter.unusedSectionVars false in
private theorem bdWEndoInsert_sub_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [bdCotangentToDual_cometricRaise_bdAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x -
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om -
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g₀ x) om from rfl]
  rw [show cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om -
          slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w =
      cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om) w -
        cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w from by
    rw [show cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) =
        cotangentToDualLinear (I := I) (x := x)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) from rfl]
    rw [map_sub]
    rfl]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g_bg x) om w]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g₀ x) om w]
  rw [show cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g_bg x w) -
        cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g₀ x w) =
      cotangentToDual (I := I) om
        (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) from by
    rw [show cotangentToDual (I := I) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) =
        cotangentToDualLinear (I := I) (x := x) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w)
        from rfl]
    rw [map_sub]
    rfl]
  rw [bdWEndo_sub_eq (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [bdAlpha, bdUnitModel_add, ContinuousMultilinearMap.add_apply,
    bdAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    bdAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
          PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show ∀ v : TangentSpace I x, cotangentToDual (I := I) om v =
        cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
    exact map_add _ _ _]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from by
    rw [show cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
        cotangentToDualLinear (I := I) (x := x) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w)]

set_option linter.unusedSectionVars false in
lemma bdICG_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option linter.unusedSectionVars false in
lemma bdRfns_zero_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((0 : SmoothCcTensor g₀ r s).toSection x) = 0 := by
  rw [show ((0 : SmoothCcTensor g₀ r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ r s x

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdCometricCastG0_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
            ((iteratedCovGrad (I := I) g₀ 3 1 j
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 1) := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 3 1
    (cometricDoubleTraceField (I := I) g₀ 1)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => 2 * cfix 0 +
      2 * (appCcGdiag (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)),
    fun j => by
      have h1 := hcfix_nn 0
      have h2 : 0 ≤ appCcGdiag (E := E) j *
          (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
          (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hW1 : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by linarith
  rw [cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) (M := M) g₀ g₁]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 3 1 j
    (cometricDoubleTraceField (I := I) g₀ 1)
    (appCcRS (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
    x) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := by
    match j with
    | 0 => exact hcfix 0 x
    | (m + 1) =>
        rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
        rw [bdRfns_zero_toSection]
        exact hcfix_nn 0
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (appCcRS (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      (appCcGdiag (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 3 3 1
      (cometricDoubleTraceField (I := I) g₀ 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
      rw [bdRfns_zero_toSection, zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
            ((iteratedCovGrad (I := I) g₀ 3 1 0
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hslot : (∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
        (∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
        rw [show j + 1 - 0 = j + 1 from rfl, Finset.sum_mul]
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
        have h2 := hCD g₁ P htie hδ_le hδ0 hbound l x
        calc (Module.finrank ℝ E : ℝ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (slotInsertEndoCc (I := I) (M := M) g₀ 0
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
            ≤ fr ^ 2 * (CD l * ∑ n ∈ Finset.range (l + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
                  ∏ m : Fin n, b (e m)) := by
              rw [← hfr_def]
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGrid b l := by
              rw [Combinatorics.antidiagonalTupleGrid]
              ring
          _ ≤ (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (by positivity) (hCD_nn l))
              exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
    have hfix0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 3 1 0
          (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := hcfix 0 x
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + l) x _
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hfix0 hslot hsum_nn (hcfix_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
    rw [← mul_assoc, ← mul_assoc]
    rw [mul_assoc (appCcGdiag (E := E) j) (cfix 0)]
  have hA' : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤
      cfix 0 * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans hA ?_
    nlinarith [hcfix_nn 0]
  have hB_nn : (0 : ℝ) ≤ appCcGdiag (E := E) j *
      (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
    mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
      (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
  nlinarith [hA', hB, hW_nn, hcfix_nn 0]

set_option linter.unusedSectionVars false in
private lemma bdConnDiffSection_eq_cometricRaise (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

set_option linter.unusedSectionVars false in
lemma bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [bdConnDiffSection_eq_cometricRaise]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdCA_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨CA, hCA_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j
        (bdCA (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
            (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) := by
    rw [bdCA]
    exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)) j x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 3 j
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 3) 2) (connDiffLoweredCc (I := I) g₀ g₁) j x
  rw [h1, h2, bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ j x]
  refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound j x) ?_
  rw [show Combinatorics.antidiagonalTupleGridWindow b (j + 2) =
      ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k from rfl]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdOmega_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 1 l
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 1) := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ := bdCometricCastG0_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨cxi, hcxi_nn, hcxi⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 3
    (bdXiFix (I := I) (M := M) g₀ g_bg)
  refine ⟨fun l => appCcGdiag (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l',
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCg_nn i')
        (Finset.sum_nonneg fun l' _ => hcxi_nn l')), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 1) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 1)
  rw [bdOmega]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ l 0 3 1
    (cometricCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 1 i'
            (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) ≤
      (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
        ((iteratedCovGrad (I := I) g₀ 3 1 i'
          (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
        Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
      refine le_trans (hCg g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCg_nn i')
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
      Finset.sum_le_sum fun l' _ => hcxi l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 3 l'
                (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)
        ≤ (Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1)) *
            ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
          mul_le_mul hA1 hA2 hsum_nn (mul_nonneg (hCg_nn i') hW_nn)
      _ = (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdAlphaA_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => Cω (i + 1), fun i => hCω_nn (i + 1), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  rw [bdAlphaA]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) i x]
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x]
  exact hCω g₁ P htie hδ_le hδ0 hbound (i + 1) x

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdAlphaB_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := bdCA_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l',
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCA_nn i')
        (Finset.sum_nonneg fun l' _ => mul_nonneg (hCω_nn l')
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  rw [bdAlphaB]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 1 2
    (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 1 2 i'
            (bdCA (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 1 l'
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i'
          (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      hCA g₁ P htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (i + 1 - i'),
          Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1) :=
      Finset.sum_le_sum fun l' _ => hCω g₁ P htie hδ_le hδ0 hbound l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (1 + l') x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      mul_nonneg (hCA_nn i') (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 2))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) =
        ∑ l' ∈ Finset.range (i + 1 - i'),
          (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l' hl' => ?_
    rw [Finset.mem_range] at hl'
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
        Combinatorics.antidiagonalTupleGridWindow b (l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
          Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) := by
      have h := Combinatorics.antidiagonalTupleGridWindow_mul_le b hb (i' + 1) l'
      rw [show i' + 1 + 1 = i' + 2 from rfl] at h
      exact h
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
      Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
          (Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1))
        = (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (l' + 1)) := by ring
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCA_nn i') (hCω_nn l')
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (hCA_nn i') (hCω_nn l'))
          refine mul_le_mul_of_nonneg_left hmono ?_
          exact Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _
      _ = (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdWEndoInsertDiff_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CAa, hCAa_nn, hCAa⟩ := bdAlphaA_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CAb, hCAb_nn, hCAb⟩ := bdAlphaB_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => 2 * CAa i + 2 * CAb i,
    fun i => by have h1 := hCAa_nn i; have h2 := hCAb_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  rw [bdWEndoInsert_sub_eq_cometricRaise (I := I) (M := M) g₀ g₁ g_bg]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) i x]
  rw [bdAlpha]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 2 i
    (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)
    (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have h1 := hCAa g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hCAb g₁ P htie hδ_le hδ0 hbound i x
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  nlinarith [h1, h2, hW_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)]

set_option linter.unusedSectionVars false in
private theorem bdDLb_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D
      = deTurckLieDLbFib (I := I) g₁ g_bg x D from rfl]
  rw [deTurckLieDLbFib_toModel (I := I) g₁ g_bg x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((slotInsertEndoCc (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (deTurckLieWEndo (I := I) g₁ g_bg x
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1 (deTurckLieWEndo (I := I) g₁ g_bg x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]

set_option linter.unusedSectionVars false in
private lemma bdSlotInsertEndoCc_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s A - slotInsertEndoCc (I := I) (M := M) g₀ s B =
      slotInsertEndoCc (I := I) (M := M) g₀ s (A - B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by rw [ContMDiffSection.coe_sub]; rfl]
  rw [slotInsertEndoFib_sub_left]

set_option linter.unusedSectionVars false in
private lemma bdReindexSwap_sub (g₀ : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g₀ 2 2) :
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1) =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (X - Y))
        (Equiv.swap (0 : Fin 2) 1) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1)).toSection x -
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  have hpt : ∀ (Z : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Z.toSection x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))))
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) := by
    intro Z
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              Z).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply]
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          Z).toSection x) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            (Z.toSection x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show Tensor0SSpace.toModel
      (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m from by
    rw [show (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) -
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]]
  rw [hpt X, hpt Y, hpt (X - Y)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (X - Y).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Y.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) from by
    rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private def bdWEndoSecDiff (g₁ g_bg g₀' : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg -
    deTurckLieWEndoSection (I := I) (M := M) g₁ g₀'

set_option linter.unusedSectionVars false in
private theorem bdDLbDiff_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg,
    bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g₀]
  rw [show (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1))
      - (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        - slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))
      + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)
        - reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) from by abel]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rw [bdReindexSwap_sub (I := I) (M := M) g₀
    (slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
    (slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdSlotInsertZero_bdWEndoSecDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) =
      deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ := by
  rw [deTurckLieWEndoInsert, deTurckLieWEndoInsert]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 0
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem bdEndoArmDiff_pointwise_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CW, hCW_nn, hCW⟩ := bdWEndoInsertDiff_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 2 * (fr * CW i) + 2 * (fr * CW i),
    fun i => by have h := mul_nonneg hfr_nn (hCW_nn i); linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hbase : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    rw [bdSlotInsertZero_bdWEndoSecDiff (I := I) (M := M) g₀ g₁ g_bg]
    exact hCW g₁ P htie hδ_le hδ0 hbound i x
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
      (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) i x
    rw [pow_one] at h
    refine le_trans h ?_
    rw [← hfr_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase hfr_nn
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have heq := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)) i x
    rw [heq]
    exact hA
  rw [bdDLbDiff_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 2 2 i _ _ x) ?_
  nlinarith [hA, hB,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem bdL2_tameEnvelope_of_gridWindow (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kg : ℕ → ℝ, (∀ k, 0 ≤ Kg k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ) (C : ℝ), 0 ≤ C → ∀ (V : SmoothCcTensor g₀ 2 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
          C * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2)) →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i V‖ ^ 2 ≤
          (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kg, hKg_nn, ?_⟩
  intro P hPball i C hC V hpt
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
        C * ∑ k ∈ Finset.range (i + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
    intro x
    refine le_trans (hpt x) (le_of_eq ?_)
    congr 1
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ k ∈ Finset.range (i + 2),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum _
      (fun k hk => (hKg P hPball k).1)).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i V)
    (fun x => C * ∑ k ∈ Finset.range (i + 2),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    hF_int hpt'
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
  have hsum_le : ∑ k ∈ Finset.range (i + 2),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 2), Kg k) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hKg P hPball k).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
    have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hk
      omega
    linarith
  calc C * ∑ k ∈ Finset.range (i + 2),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ C * ((∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_le hC
    _ = (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
