import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferencePrincipalEndomorphismTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceSymmetrizedReindexedCoeff

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in

private theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in

theorem iteratedCovGrad_symmS_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) := by
  rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

private theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeff_appCc_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (R₂ : SmoothCcTensor g₀ 4 2) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2, ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂'
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  classical

  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) S 2
  refine ⟨(1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ', fun x v => ?_⟩

  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R₂ σ')
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huRein

  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        ((1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ')
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]

  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeff_appCc_eq (I := I) (M := M) g₀ R₂ σ'
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [hLHS, hRHS]

noncomputable def reindexCoeffFibGen (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x) :
    Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in

theorem reindexCoeffFibGen_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x)
    (D : Tensor0SBundle.Tensor0SSpace r I x) :
    reindexCoeffFibGen (I := I) r s σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFibGen, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeffFibGen_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (φ := fun x => reindexCoeffFibGen (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x t)
    (reindexCoeffFibGen_apply (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x) (Y x)).symm

noncomputable def reindexCoeffGen (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace r s I x from
          reindexCoeffFibGen (I := I) r s σ' x
            (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFibGen_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem reindexCoeffGen_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace r s I x from
        reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeffGen_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (R : SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r))
    (W W' : SmoothCcTensor g₀ 0 r)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ r W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ r W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ r 2 (reindexCoeffGen (I := I) (M := M) g₀ r 2 R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection]
  rw [reindexCoeffFibGen_apply (I := I) r 2 σ' x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ r W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ r W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ r W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

noncomputable def symmAbsorbedCoeff (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i))) : SmoothCcTensor g₀ (2 + i) 2 :=
  (1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ'

set_option linter.unusedSectionVars false in

theorem symmAbsorbedCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (S : SmoothCcTensor g₀ 0 2) (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i)))
    (hσ' : ∀ x : M, unitModel (I := I) (M := M) g₀ (2 + i)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S)) x =
      ContinuousMultilinearMap.domDomCongr σ'
        (unitModel (I := I) (M := M) g₀ (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i S) x))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ')
          (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 R
          (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v := by
  classical
  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]
  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2 R (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2
      (reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
      (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huRein
  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2
        ((1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
        (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]
  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeffGen_appCc_eq (I := I) (M := M) g₀ (2 + i) R σ'
        (iteratedCovGrad (I := I) g₀ 0 2 i S)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [symmAbsorbedCoeff, hLHS, hRHS]

set_option linter.unusedSectionVars false in

theorem inverseMetricSharpFib_sub_inner_g1
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      cotangentToDualLinear (I := I) (x := x) α w
        - g₁.inner x (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [map_sub, ContinuousLinearMap.sub_apply,
      inverseMetricSharpFib_inner (I := I) g₁ x α w]

set_option linter.unusedSectionVars false in

theorem inverseMetricSharpFib_sub_inner_g1_realize
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (x : M) (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      - ccTensorBilinSymm (I := I) g₀ (T - T') x
          (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [inverseMetricSharpFib_sub_inner_g1 (I := I) g₁ g₁' x α w]
  rw [← inverseMetricSharpFib_inner (I := I) g₁' x α w]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁' x α with hu
  rw [hg₁' x u w, hg₁ x u w]
  have hbsub : ∀ (a c : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x a c =
        ccTensorBilin (I := I) g₀ T x a c - ccTensorBilin (I := I) g₀ T' x a c := by
    intro a c
    rw [show T - T' = T + (-1 : ℝ) • T' from by rw [neg_one_smul]; abel,
      ccTensorBilin_add (I := I) (M := M) g₀ T ((-1 : ℝ) • T') x a c,
      ccTensorBilin_smul (I := I) (M := M) g₀ (-1 : ℝ) T' x a c]
    ring
  have hsub : ccTensorBilinSymm (I := I) g₀ (T - T') x u w =
      ccTensorBilinSymm (I := I) g₀ T x u w - ccTensorBilinSymm (I := I) g₀ T' x u w := by
    rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
      hbsub u w, hbsub w u]
    ring
  rw [hsub]; ring

set_option linter.unusedSectionVars false in

theorem cotangentCov_leviCivita_diff_endpoint
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₁')).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v) := by
  have h1 := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ v w
  have h1' := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁' hθ v w

  have hcocycle : PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v := by
    classical
    set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
    have hY := smoothExtensionTangent_mdiff (I := I) x w x
    have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
    have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
    have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
    rw [hYx] at e1 e2 e3
    rw [e1, e2, e3]; abel
  rw [hcocycle, map_sub]
  linarith [h1, h1']

set_option linter.unusedSectionVars false in

theorem oArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
        - inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
          - inverseMetricSharpFib (I := I) g₁' x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)))
        + inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
              - dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) := by
  rw [map_sub]
  abel

set_option linter.unusedSectionVars false in

theorem oArm_leg_eq_connDiff (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
        - dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁')).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir) =
      dualToCotangent (I := I)
        (-((cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₁' x).flip dir)).toLinearMap) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁' Z Y x
  rw [← dualToCotangent_subC]
  congr 1
  ext w
  have hbridge := cotangentCov_leviCivita_diff_endpoint (I := I) (M := M) g₀ g₁ g₁' hθ dir w
  rw [LinearMap.sub_apply]
  simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_coe]
  exact hbridge

set_option linter.unusedSectionVars false in

theorem connDiff_endpoint_cocycle (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v := by
  classical
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
  have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
  have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
  rw [hYx] at e1 e2 e3
  rw [e1, e2, e3]; abel

set_option linter.unusedSectionVars false in

theorem csArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (a a' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x a dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x a' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (a - a') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x a' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x a' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

set_option linter.unusedSectionVars false in

theorem quadArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (q q' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x q dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x q' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q - q') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x q' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x q' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

set_option linter.unusedSectionVars false in

theorem combinedLowerArm_extension_free
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                          ((chartModelBasis E) i)))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
          ) + (
        (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x (v 0),
                                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))) i)
            - (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                                smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x (v 0) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
          ) + (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i))
        + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
              (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
              (⟨smoothExtensionTangent (I := I) x (v 0),
                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
              (⟨smoothExtensionTangent (I := I) x (v 1),
                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x
            - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
                (⟨smoothExtensionTangent (I := I) x (v 0),
                  smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                (⟨smoothExtensionTangent (I := I) x (v 1),
                  smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x)) =
        ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1)
          - unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 4 2 R₂'
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₂', hR₂'⟩ := symmAbsorbedPrincipalCoeff_appCc_eq (I := I) (M := M) g₀ (T - T')
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
  refine ⟨R₂', fun x v => ?_⟩
  set Zv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hZv
  set Yw : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYw
  have hZvx : Zv x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYwx : Yw x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hcons : (![v 0, v 1] : Fin 2 → TangentSpace I x) = v := by
    funext k; fin_cases k <;> rfl

  have htel : ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i) := by
    have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x (v 0) (v 1)
    have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x (v 0) (v 1)
    rw [show ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
        (ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1))
          - (ricciTensor (I := I) g₁' x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1)) from by
      ring]
    rw [h₁, h₁']

  have hgradX : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁'
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁'
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ Yw Zv x)
  have hgradZ : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁' (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁' Zv Yw
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ x)

  have hregroup :
      ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x (v 0),
                          smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                      ((chartModelBasis E) i)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
        ) + (
      (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i))
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
        ) := by
    rw [htel]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [← Finsupp.sub_apply, ← Finsupp.add_apply, ← map_sub, ← map_add]
    refine congrArg (fun t => (chartModelBasis E).repr t i) ?_
    rw [hgradX i, hgradZ i]
    simp only [hZv, hYw, ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
    abel

  have hPX := palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' hg₁ hg₁' Zv Yw x
  have hPZ := palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' Zv Yw x
  have hR₂'v := hR₂' x v
  rw [hZvx, hYwx, hcons] at hPX hPZ
  have huXZ : unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v
      - unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v := by
    rw [show ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          + (-1 : ℝ) • ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring

  have hP :
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)) =
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 R₂'
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
          + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x
              - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                  (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x) := by
    rw [hPX, hPZ, hR₂'v]
    linarith [huXZ]
  rw [hregroup]
  simp only [← hZv, ← hYw]
  linarith [hP]

set_option linter.unusedSectionVars false in

def lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((g₁'.inner x (v + v')).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = (g₁'.inner x v).toLinearMap + (g₁'.inner x v').toLinearMap := by
          ext w; simp [map_add]
        rw [h, dualToCotangent_addC]
      map_smul' := fun c v => by
        have h : ((g₁'.inner x (c • v)).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = c • (g₁'.inner x v).toLinearMap := by
          ext w; simp [map_smul]
        rw [h, dualToCotangent_smulC]; rfl }

@[simp] lemma lowerFlatCLM_apply (g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    lowerFlatCLM (I := I) g₁' x v =
      dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap := by
  rw [lowerFlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl

set_option linter.unusedSectionVars false in

@[simp] lemma cotangentToDual_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (lowerFlatCLM (I := I) g₁' x v) w = g₁'.inner x v w := by
  rw [lowerFlatCLM_apply, cotangentToDual_dualToCotangent]; rfl

set_option linter.unusedSectionVars false in

lemma inverseMetricSharpFib_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v) = v := by
  have hkey : (g₁'.inner x (inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₁'.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_lowerFlatCLM]

  have hinj : Function.Injective
      (fun u : TangentSpace I x => (g₁'.inner x u : TangentSpace I x →L[ℝ] ℝ)) := by
    intro a b hab
    have hval : ∀ w, g₁'.inner x a w = g₁'.inner x b w := fun w => by
      have := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ w) hab
      simpa using this
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := g₁'.pos x (a - b) hsub
    have hzero : g₁'.inner x (a - b) (a - b) = 0 := by
      have hsymm₁ : g₁'.inner x (a - b) (a - b)
          = g₁'.inner x (a - b) a - g₁'.inner x (a - b) b := by rw [← map_sub]
      rw [hsymm₁, g₁'.symm x (a - b) a, g₁'.symm x (a - b) b]
      have e1 : g₁'.inner x a (a - b) = g₁'.inner x b (a - b) := hval (a - b)
      rw [e1]; ring
    exact absurd hzero (ne_of_gt hpos)
  exact hinj hkey

set_option linter.unusedSectionVars false in

lemma inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁'.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, lowerFlatCLM_apply]
  rw [show cotangentToDualLinear (I := I)
        (dualToCotangent (I := I) (g₁'.inner x v).toLinearMap)
        = (g₁'.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]

def combinedLowerRaisedEndo0 (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (lowerFlatCLM (I := I) g₁' x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)

@[simp] lemma combinedLowerRaisedEndo0_apply (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) - v := by
  rw [combinedLowerRaisedEndo0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

set_option linter.unusedSectionVars false in

@[simp] lemma combinedLowerRaisedEndo0_self (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁' g₁' x v = 0 := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM, sub_self]

set_option linter.unusedSectionVars false in

lemma combinedLowerRaisedEndo0_eq_metricSharp_flatDiff
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp]
  have hv : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁.inner x v).toLinearMap = v := by
    rw [← inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp (I := I) g₁ g₁ x v]
    exact inverseMetricSharpFib_lowerFlatCLM (I := I) g₁ x v
  have hsharp_sub : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁'.inner x v).toLinearMap
        - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁.inner x v).toLinearMap := by
    rw [DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_sub]
  rw [hsharp_sub, hv]

set_option linter.unusedSectionVars false in

theorem metricFlat_chartComponent_contMDiffOn_local (g : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (g.inner b (Y b)).toLinearMap
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h_total : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g.inner b (Y b)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) γ).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g.contMDiff.contMDiffOn Y.contMDiff.contMDiffOn
      (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn (I := I) γ j)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I) γ
  rw [hbase_eq] at h_total
  intro b hb
  have hpb := h_total b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

set_option linter.unusedSectionVars false in

theorem metricFlatDiff_chartComponent_contMDiffOn_local (g₁ g₁' : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap)
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h0 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁' Y γ j
  have h1 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁ Y γ j
  refine (h0.sub h1).congr ?_
  intro b hb
  rw [LinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

theorem combinedLowerRaisedEndo0_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ b
          ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap))) := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlatDiff_chartComponent_contMDiffOn_local (I := I) g₁ g₁' Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [combinedLowerRaisedEndo0_eq_metricSharp_flatDiff (I := I) g₁ g₁' x (Y x)]

set_option backward.isDefEq.respectTransparency false in

def lowerSlotInsert0Fib (x : M) (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_add]
        ext m
        simp
      map_smul' := fun c A => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_smul,
          RingHom.id_apply]
        ext m
        simp }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

lemma lowerSlotInsert0Fib_apply_eval (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m 0 (Λ (m 0))) := by
  rw [lowerSlotInsert0Fib, LinearMap.coe_toContinuousLinearMap']
  change (Tensor0SSpace.toModel ((Tensor0SSpace.ofModel
      ((Tensor0SSpace.toModel A).compContinuousLinearMap
        (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))) :
      Tensor0SSpace 2 I x)) m = _
  rw [Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin 2 =>
      (if i = 0 then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m 0 (Λ (m 0)) := by
    funext i
    by_cases h : i = 0
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne h]; rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

lemma lowerSlotInsert0Fib_curry (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) :
    lowerSlotInsert0Fib (I := I) (M := M) x Λ A =
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ) := by
  have hcurry : Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) =
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply Tensor0SSpace.toModel_injective (I := I)
    ext vt
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M),
      lowerSlotInsert0Fib_apply_eval, ContinuousLinearMap.comp_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in

def combinedLowerCoeff0Fib (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lowerSlotInsert0Fib (I := I) (M := M) x (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)

set_option linter.unusedSectionVars false in

lemma combinedLowerCoeff0Fib_apply_eval (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (combinedLowerCoeff0Fib (I := I) g₁ g₁' x A) m =
      Tensor0SSpace.toModel A
        (Function.update m 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (m 0))) := by
  rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_apply_eval]

set_option backward.isDefEq.respectTransparency false in

theorem combinedLowerCoeff0Fib_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (Tensor0SBundle.TensorRSSpace.ofCLM (combinedLowerCoeff0Fib (I := I) g₁ g₁' x))) := by
  set φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x with hφdef
  have hφ := combinedLowerRaisedEndo0_contMDiff (I := I) g₁ g₁'
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x => combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      (combinedLowerCoeff0Fib (I := I) g₁ g₁' x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)))) := by
    funext x
    rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_curry]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x))) :=
    fun x => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (φ := fun x => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x) (φ x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) hG

noncomputable def combinedLowerCoeff0 (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
      contMDiff_toFun := combinedLowerCoeff0Fib_contMDiff (I := I) g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem combinedLowerCoeff0_toSection (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x) := rfl

set_option linter.unusedSectionVars false in

theorem combinedLowerCoeff0_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁') W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
        (Function.update v 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (v 0))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [combinedLowerCoeff0_toSection]
  rw [combinedLowerCoeff0Fib_apply_eval]
  rfl

set_option linter.unusedSectionVars false in

theorem connDiff_g1g1'_order_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Y x) (X x) =
      (inverseMetricSharpFib (I := I) g₁ x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x)
          - inverseMetricSharpFib (I := I) g₁' x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x))
        + inverseMetricSharpFib (I := I) g₁' x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x (Y x) (X x)]
  rw [connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x,
      connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁' X Y x]
  rw [map_sub (inverseMetricSharpFib (I := I) g₁' x)]
  abel

set_option linter.unusedSectionVars false in

theorem order1CocycleLeg_flat_eq_explicit
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (hbil' : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = g₁'.inner b u w - g₀.inner b u w)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    g₁'.inner x
        (inverseMetricSharpFib (I := I) g₁' x
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
            - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x)) ζ =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ (S - S')
            (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
            (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
            (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          + covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          - covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              x) := by
  classical
  set Xe : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩ with hXe
  set Ye : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩ with hYe
  set Ze : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩ with hZe
  have hXex : Xe x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hYex : Ye x = Y x := smoothExtensionTangent_eq (I := I) x (Y x)
  have hZex : Ze x = ζ := smoothExtensionTangent_eq (I := I) x ζ

  rw [inverseMetricSharpFib_inner (I := I) g₁' x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
          - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ,
      cotangentToDualLinear_apply,
      show cotangentToDual (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ =
          cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ
            - cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ from by
        rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
            ← cotangentToDualLinear_apply, map_sub, LinearMap.sub_apply]]

  rw [show ζ = Ze x from hZex.symm]
  rw [koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil X Y Ze x,
      koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁' S' hbil' X Y Ze x]

  have hcg : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      covGradEval (I := I) (M := M) g₀ S P Q R x
          - covGradEval (I := I) (M := M) g₀ S' P Q R x =
        covGradEval (I := I) (M := M) g₀ (S - S') P Q R x := by
    intro P Q R
    simp only [covGradEval]
    rw [covGrad_sub (I := I) (M := M) g₀ 0 2 S S', SmoothCcTensor.toSection_sub]
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
        Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  have hval : ∀ (W : SmoothCcTensor g₀ 0 2)
      (P₁ P₂ Q₁ Q₂ R₁ R₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      P₁ x = P₂ x → Q₁ x = Q₂ x → R₁ x = R₂ x →
        covGradEval (I := I) (M := M) g₀ W P₁ Q₁ R₁ x =
          covGradEval (I := I) (M := M) g₀ W P₂ Q₂ R₂ x := by
    intro W P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR
    simp only [covGradEval, hP, hQ, hR]

  have eXY := (hcg X Y Ze).trans (hval (S - S') X Xe Y Ye Ze Ze hXex.symm hYex.symm rfl)
  have eYX := (hcg Y X Ze).trans (hval (S - S') Y Ye X Xe Ze Ze hYex.symm hXex.symm rfl)
  have eZXY := (hcg Ze X Y).trans (hval (S - S') Ze Ze X Xe Y Ye rfl hXex.symm hYex.symm)
  linarith [eXY, eYX, eZXY]

noncomputable def ricciArmSubleadingCoeff (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
    - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁'
        - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁')

set_option linter.unusedSectionVars false in

theorem ricciArmSubleadingCoeff_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmSubleadingCoeff (I := I) (M := M) g₀ g₁ g₁') W) x v =
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) -
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁' x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) := by
  classical
  have hsub : ∀ (A B : SmoothCcTensor g₀ 4 2),
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (A - B) W) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 A W) x v -
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 B W) x v := by
    intro A B
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul]; abel,
      appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, neg_one_smul]
    rw [← sub_eq_add_neg]
  rw [ricciArmSubleadingCoeff, hsub, hsub, hsub,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v]

noncomputable def ricciArmOrder0CurvCoeffFibSlot (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 k x (ricEndoRaisedFib (I := I) g₁ x)

noncomputable def ricciArmOrder0CurvCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 0 x +
    ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 1 x

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffFibSlot_toModel (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update v k (ricEndoRaisedFib (I := I) g₁ x (v k))) := by
  rw [ricciArmOrder0CurvCoeffFibSlot]
  exact slotInsertEndoFib_apply_eval (I := I) (M := M) 2 k x
    (ricEndoRaisedFib (I := I) g₁ x) D v

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmOrder0CurvCoeffFib (I := I) g₁ x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [ricciArmOrder0CurvCoeffFib, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem ricciArmOrder0CurvCoeffFibSlot_contMDiff (g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))) := by
  exact slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 k
    (fun x : M => ricEndoRaisedFib (I := I) g₁ x)
    (ricEndoRaisedFib_contMDiff (I := I) g₁)

noncomputable def ricciArmOrder0CurvCoeffSlot (g₀ g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))
      contMDiff_toFun := ricciArmOrder0CurvCoeffFibSlot_contMDiff (I := I) g₁ k }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffSlot_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ k).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x)) := rfl

noncomputable def ricciArmOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 +
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) := by
  rw [ricciArmOrder0CurvCoeff, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ricciArmOrder0CurvCoeffSlot_toSection, ricciArmOrder0CurvCoeffSlot_toSection]
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      ricciArmOrder0CurvCoeffFib (I := I) g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeffFib_toModel]
  rfl

def riemannKernelBilin (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

@[simp] theorem riemannKernelBilin_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannKernelBilin (I := I) g₁ x p q v0 v1 =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def riemannSummandFib (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannKernelBilin (I := I) g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem riemannSummandFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannSummandFib (I := I) g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannBiContrFibFixedFrame (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannSummandFib (I := I) g₁ x (B a x) (B b x)

theorem riemannBiContrFibFixedFrame_toModel (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannSummandFib_toModel]
  ring

def innerPairBilin (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (Dd X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

theorem innerPairBilin_apply (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K Dd X Y Y' = K X Y * Dd X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip Dd (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

theorem outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * Dd X' (chartModelBasis E l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            Dd (chartModelBasis E n) (chartModelBasis E l))) := by
  classical

  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilin (I := I) g x K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]

  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K Dd) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * Dd (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K Dd B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K Dd C hC]

theorem contMDiff_bilinSection_of_chartScalar
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hscalar : ∀ (x₀ : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  let d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b
    (fun x => Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel (TangentSpace I x) (Hb x)))).mpr fun σ x₀ => ?_
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
      (chartAt H x₀).source := hscalar x₀ σ
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    (chartAt H x₀).open_source.mem_nhds hx₀_src
  refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
  have h_base_nhd : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
  filter_upwards [h_base_nhd] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x) (bilinFormToModel (TangentSpace I x) (Hb x)))
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (Hb x)
    (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j)))

theorem kernelScalar_global (g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

theorem riemannKernelBilin_homSection_contMDiff (g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannKernelBilin (I := I) g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := kernelScalar_global (I := I) g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannKernelBilin (I := I) g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannKernelBilin_apply]
  rfl

theorem contMDiff_bilinSection_of_homSection
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x (Hb x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  refine contMDiff_bilinSection_of_chartScalar (I := I) Hb (fun x₀ σ => ?_)
  have hcf_0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 0) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 0) x hx
  have hcf_1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 1) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 1) x hx
  have happ1 := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z →L[ℝ] ℝ)
    (b := id) hHb.contMDiffOn hcf_0
  have happ := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun _ : M => ℝ)
    (b := id) happ1 hcf_1
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

theorem riemannBiContrFibFixedFrame_apply_section_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannBiContrFibFixedFrame (I := I) g₁ B x (Y x))) := by
  classical

  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannKernelBilin (I := I) g₁ x (B a x) (B b x))
      (riemannKernelBilin_homSection_contMDiff (I := I) g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (riemannKernelBilin (I := I) g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl

  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem riemannBiContrFibFixedFrame_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannBiContrFibFixedFrame (I := I) g₁ B x)
  intro Y
  exact riemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ B hB Y

def frameRiemannKernel (g₁ : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₁.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

theorem frameRiemannKernel_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannKernel (I := I) g₁ x v0 v1 p q =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannBiContrFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x

theorem riemannBiContrFib_eq_fixedFrame_on_nbhd (g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannBiContrFib (I := I) g₁ y =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannKernel (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannKernel_apply (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRiemannKernel (I := I) g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem riemannBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    riemannBiContrFibFixedFrame_contMDiff (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ x₀ hy))

def ricciArmOrder0RiemannCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      contMDiff_toFun := riemannBiContrFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem ricciArmOrder0RiemannCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

theorem exists_ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ R_Rm : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Rm W) x v =
          2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (LeviCivita (I := I) g₁) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
              unitModel (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                  else smoothOrthoFrame (I := I) g₁ x b x) :=
  by
  classical
  refine ⟨ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

noncomputable def ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁

@[simp] theorem ricciArmOrder0RiemannCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

noncomputable def symmAbsorbedPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 2
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeffPure_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 S
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2)) x v

noncomputable def symmAbsorbedOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0CurvCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

noncomputable def symmAbsorbedOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

noncomputable def deTurckLieCovDerivA (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₁).toFun (fun b => Y b) x (X x)) (Z x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x)
        ((LeviCivita (I := I) g₁).toFun (fun b => Z b) x (X x))

noncomputable def deTurckLieCovDerivW (g₁ g_bg : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x (X x)

theorem connDiffOp_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))
  intro Z
  exact PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg Y.contMDiff Z.contMDiff

theorem connDiffOp_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) x :=
  (connDiffOp_homSection_contMDiff (I := I) g₁ g_bg).contMDiffAt.mdifferentiableAt (by simp)

theorem connDiff_pairing_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x := by
  have h1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun b => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))) x :=
    MDifferentiableAt.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun z : M => TangentSpace I z)
      (E₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
      (b := fun b : M => b)
      (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b) (v := fun b => Y b)
      (connDiffOp_mdiffAt (I := I) g₁ g_bg x) hY
  exact MDifferentiableAt.clm_bundle_apply
    (F₁ := E) (F₂ := E)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z)
    (b := fun b : M => b)
    (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b)) (v := fun b => Z b) h1 hZ

theorem deTurckLieCovDerivA_tensorialAt_Y (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Z : Π b : M, TangentSpace I b) (x : M)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    TensorialAt I E
      (fun Y : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Y} hf hY := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfYG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (f b • Y b) (Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (f • Y) x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((f • Y) x) (cov.toFun Z x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfYG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hY hf (Set.mem_univ x)]
    have hfY_x : (f • Y) x = f x • Y x := rfl
    rw [hfY_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Y Y'} hY hY' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY' hZ
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b + Y' b) (Z b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (Y + Y') x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Y + Y') x) (cov.toFun Z x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y' x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y' x) (cov.toFun Z x (X x)))
    rw [hadd_fun, hcovOn.add hGY hGY' (Set.mem_univ x)]
    rw [hcovOn.add hY hY' (Set.mem_univ x)]
    have hYY'_x : (Y + Y') x = Y x + Y' x := rfl
    rw [hYY'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

theorem deTurckLieCovDerivA_tensorialAt_Z (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (x : M)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x) :
    TensorialAt I E
      (fun Z : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Z} hf hZ := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfZG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (f b • Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((f • Z) x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (f • Z) x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfZG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hZ hf (Set.mem_univ x)]
    have hfZ_x : (f • Z) x = f x • Z x := rfl
    rw [hfZ_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Z Z'} hZ hZ' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGZ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ'
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b + Z' b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)
      rw [ContinuousLinearMap.map_add]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((Z + Z') x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (Z + Z') x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z' x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z' x (X x)))
    rw [hadd_fun, hcovOn.add hGZ hGZ' (Set.mem_univ x)]
    rw [hcovOn.add hZ hZ' (Set.mem_univ x)]
    have hZZ'_x : (Z + Z') x = Z x + Z' x := rfl
    rw [hZZ'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

noncomputable def dLaCovKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (A := TangentSpace I x)
    (fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x) x
    (fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)

theorem dLaCovKernel_apply_extend (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 p q =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x p)
        (smoothExtensionTangent (I := I) x q) x := by
  have hp := smoothExtensionTangent_mdiff (I := I) x p x
  have hq := smoothExtensionTangent_mdiff (I := I) x q x
  have h := TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := smoothExtensionTangent (I := I) x p)
    (τ := smoothExtensionTangent (I := I) x q) hp hq
  rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq] at h
  exact h

theorem dLaCovKernel_apply_field (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) (V_field W_field : Π b : M, TangentSpace I b)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0) V_field W_field x :=
  TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := V_field) (τ := W_field) hV hW

theorem deTurckLieCovDerivA_X_congr (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) (hXX : X x = X' x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  rw [deTurckLieCovDerivA, deTurckLieCovDerivA, hXX]

theorem deTurckLieCovDerivA_X_add (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) :
    deTurckLieCovDerivA (I := I) g₁ g_bg (X + X') Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x +
        deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  have h : (X + X') x = X x + X' x := rfl
  unfold deTurckLieCovDerivA
  rw [h]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

theorem deTurckLieCovDerivA_X_smul (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z cX : Π b : M, TangentSpace I b) (c : ℝ) (x : M) (hcX : cX x = c • X x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg cX Y Z x =
      c • deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x := by
  unfold deTurckLieCovDerivA
  rw [hcX]
  simp only [map_smul, ContinuousLinearMap.smul_apply]
  rw [smul_sub, smul_sub]

theorem dLaCovKernel_add_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v0' p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (v0 + v0') p q =
      dLaCovKernel (I := I) g₁ g_bg x v0 p q + dLaCovKernel (I := I) g₁ g_bg x v0' p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x (v0 + v0'))
      (smoothExtensionTangent (I := I) x v0 + smoothExtensionTangent (I := I) x v0')
      _ _ x (by
        change smoothExtensionTangent (I := I) x (v0 + v0') x =
          smoothExtensionTangent (I := I) x v0 x + smoothExtensionTangent (I := I) x v0' x
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq, smoothExtensionTangent_eq])]
  rw [deTurckLieCovDerivA_X_add]

theorem dLaCovKernel_smul_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (c • v0) p q = c • dLaCovKernel (I := I) g₁ g_bg x v0 p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_smul (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) _ _
      (smoothExtensionTangent (I := I) x (c • v0)) c x (by
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq])]

def dLaKernelBilin (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q)
      map_add' := fun v0 v0' => by
        rw [dLaCovKernel_add_left, map_add]
      map_smul' := fun c v0 => by
        rw [dLaCovKernel_smul_left, map_smul, RingHom.id_apply] }

@[simp] theorem dLaKernelBilin_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilin (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 := by
  rw [dLaKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def dLaKernelBilinSym (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  dLaKernelBilin (I := I) g₁ g_bg x p q +
    ContinuousLinearMap.flip (dLaKernelBilin (I := I) g₁ g_bg x p q)

@[simp] theorem dLaKernelBilinSym_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilinSym (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [dLaKernelBilinSym, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, dLaKernelBilin_apply, dLaKernelBilin_apply]

def dLaSummandFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (dLaKernelBilinSym (I := I) g₁ g_bg x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem dLaSummandFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaSummandFib (I := I) g₁ g_bg x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) p q) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) p q) (v 0)) := by
  rw [dLaSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rw [dLaKernelBilinSym]
  rfl

def dLaBiContrFibFixedFrame (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x)

theorem dLaBiContrFibFixedFrame_toModel (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) (B a x) (B b x)) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) (B a x) (B b x)) (v 0)) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [dLaBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, dLaSummandFib_toModel]
  ring

theorem deTurckLieCovDerivA_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 p q : Π b : M, TangentSpace I b)
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b)) := by
  have hcd_pq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hq
  have hterm1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0
        (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y)) b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hcd_pq
  have hcovV0p : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 p b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hp
  have hcovV0q : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 q b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hq
  have hterm2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (covApply (LeviCivita (I := I) g₁) V0 p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hcovV0p hq
  have hterm3 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (p b)
        (covApply (LeviCivita (I := I) g₁) V0 q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hcovV0q
  refine ((hterm1.sub_section hterm2).sub_section hterm3).congr (fun b => ?_)
  rfl

theorem dLaCovKernel_apply_field3 (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (V0 V_field W_field : Π b : M, TangentSpace I b)
    (_hV0 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V0 b)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x (V0 x) (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg V0 V_field W_field x := by
  rw [dLaCovKernel_apply_field (I := I) g₁ g_bg x (V0 x) V_field W_field hV hW]
  exact deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
    (smoothExtensionTangent (I := I) x (V0 x)) V0 V_field W_field x
    (smoothExtensionTangent_eq (I := I) x (V0 x))

theorem dLaKernelScalar_global (g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

theorem dLaKernelBilinSym_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x) (V0 x))
  intro W
  have h_scalar0 := dLaKernelScalar_global (I := I) g₁ g_bg V0.contMDiff W.contMDiff hp hq
  have h_scalar1 := dLaKernelScalar_global (I := I) g₁ g_bg W.contMDiff V0.contMDiff hp hq
  have h_scalar := h_scalar0.add h_scalar1
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change dLaKernelBilinSym (I := I) g₁ g_bg y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [dLaKernelBilinSym_apply]
  rfl

theorem dLaBiContrFibFixedFrame_apply_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))
      (dLaKernelBilinSym_homSection_contMDiff (I := I) g₁ g_bg (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [dLaBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem dLaBiContrFibFixedFrame_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x)
  intro Y
  exact dLaBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ g_bg B hB Y

def frameDLaKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        ContinuousLinearMap.comp ((g₁.inner x).flip v1) (dLaCovKernel (I := I) g₁ g_bg x v0 p) +
        ContinuousLinearMap.comp ((g₁.inner x).flip v0) (dLaCovKernel (I := I) g₁ g_bg x v1 p)
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          (dLaCovKernel (I := I) g₁ g_bg x v0).map_add p p',
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_add p p', ContinuousLinearMap.add_apply,
          map_add]
        ring
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, (dLaCovKernel (I := I) g₁ g_bg x v0).map_smul c p,
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_smul c p, map_smul,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

theorem frameDLaKernel_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameDLaKernel (I := I) g₁ g_bg x v0 v1 p q =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [frameDLaKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def dLaBiContrFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x

theorem dLaBiContrFib_eq_fixedFrame_on_nbhd (g₁ g_bg : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    dLaBiContrFib (I := I) g₁ g_bg y =
      dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, dLaBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 0) (Bf a) (Bf b)) (v 1) +
          g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 1) (Bf a) (Bf b)) (v 0)) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameDLaKernel_apply (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem dLaBiContrFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    dLaBiContrFibFixedFrame_contMDiff (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (dLaBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ g_bg x₀ hy))

def deTurckLieWEndo (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x

theorem deTurckLieWEndo_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x v =
      deTurckLieCovDerivW (I := I) g₁ g_bg (smoothExtensionTangent (I := I) x v) x := by
  rw [deTurckLieWEndo, deTurckLieCovDerivW, smoothExtensionTangent_eq]

theorem deTurckLieWEndo_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (deTurckLieWEndo (I := I) g₁ g_bg x)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => deTurckLieWEndo (I := I) g₁ g_bg x)
  intro Y
  have hdvf : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
        : Π b : M, TangentSpace I b) b)) :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hcov := covApply_contMDiff (cov := LeviCivita (I := I) g₁)
    (X := fun b => Y b)
    (T := fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
      : Π b : M, TangentSpace I b) b)
    Y.contMDiff hdvf
  exact hcov

def deTurckLieDLbFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (deTurckLieWEndo (I := I) g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (deTurckLieWEndo (I := I) g₁ g_bg x)

theorem deTurckLieDLbFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (deTurckLieWEndo (I := I) g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (deTurckLieWEndo (I := I) g₁ g_bg x (v 1))) := by
  rw [deTurckLieDLbFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

theorem deTurckLieDLbFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 0
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 1
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieDLbFib]
  rfl

def deTurckLieFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFib (I := I) g₁ g_bg x + deTurckLieDLbFib (I := I) g₁ g_bg x

theorem deTurckLieFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))) := by
  classical
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)))
    (dLaBiContrFib_contMDiff (I := I) g₁ g_bg)
    (deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg)
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieFib]
  rfl

def deTurckLieCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem deTurckLieCoeffField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

theorem exists_ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ∃ R_Lie : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Lie W) x v =
          (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                    else smoothOrthoFrame (I := I) g₁ x b x) *
                (g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
                  + g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
            + (unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then
                    deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0)) x
                    else v 1)
                + unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then v 0
                    else deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  classical
  refine ⟨deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]

  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp

noncomputable def ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg

@[simp] theorem ricciArmOrder0DeTurckLieCoeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg) W)
        x v =
      (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
        + (unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then
                deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0)) x
                else v 1)
            + unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then v 0
                else deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0DeTurckLieCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp

noncomputable def symmAbsorbedOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

set_option linter.unusedSectionVars false in

theorem connDiffQuad_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q r : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) r
      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) r
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r := by
  rw [csArm_split (I := I) g₀ g₁ g₁' x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x p q]

set_option linter.unusedSectionVars false in

theorem block3LegSummand_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (Xv0 Xv1 Xei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xei Xv1 x) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xei Xv1 x) (Xv0 x)) =
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xv0 x)) (Xei x)
          + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xei x)) (Xv0 x)
            + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) := by
  have h1 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xv0 x) (Xei x)
  have h2 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xei x) (Xv0 x)
  change (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xei x)) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) = _
  rw [sub_sub_sub_comm, h1, h2]

def connDiffBiKernelBilin (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp
    ((PDE.DeTurck.connDiff (I := I) gj g₀ x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q))

@[simp] theorem connDiffBiKernelBilin_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q v0 v1 =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [connDiffBiKernelBilin, ContinuousLinearMap.comp_apply]

def connDiffBiSummandFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem connDiffBiSummandFib_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) (v 0)) (v 1) := by
  rw [connDiffBiSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffBiContrFibFixedFrame (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x)

theorem connDiffBiContrFibFixedFrame_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (B a x) (B b x)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [connDiffBiContrFibFixedFrame, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffBiSummandFib_toModel]
  ring

theorem connDiffBiKernelBilin_homSection_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x) (V0 x))
  intro W
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₁' hp hq
  have houter : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gj g₀ hinner V0.contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (p x) (q x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b), houter⟩
      ⟨fun b => W b, W.contMDiff⟩
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffBiKernelBilin_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_apply_section_contMDiff
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))
      (connDiffBiKernelBilin_homSection_contMDiff (I := I) gj g₀ g₁ g₁' (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connDiffBiContrFibFixedFrame, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x)
  intro Y
  exact connDiffBiContrFibFixedFrame_apply_section_contMDiff (I := I) gj g₀ g₁ g₁' B hB Y

def frameConnDiffBiKernel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((PDE.DeTurck.connDiff (I := I) gj g₀ x).flip v0 |>.comp
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_smul c p, map_smul] }

theorem frameConnDiffBiKernel_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' x v0 v1 p q =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [frameConnDiffBiKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def connDiffBiContrFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x) x

theorem connDiffBiContrFib_eq_fixedFrame_on_nbhd (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffBiContrFib (I := I) gj g₀ g₁ g₁' y =
      connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel,
    connDiffBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (PDE.DeTurck.connDiff (I := I) gj g₀ y
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' y (Bf a) (Bf b)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffBiKernel_apply (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

theorem connDiffBiContrFib_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    connDiffBiContrFibFixedFrame_contMDiff (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffBiContrFib_eq_fixedFrame_on_nbhd (I := I) gj g₀ g₁ g₁' x₀ hy))

def connDiffBiContrCoeffField (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))
      contMDiff_toFun := connDiffBiContrFib_contMDiff (I := I) gj g₀ g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem connDiffBiContrCoeffField_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x : M) :
    (connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

noncomputable def connDiffBiContrCoeff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁'

@[simp] theorem connDiffBiContrCoeff_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem connDiffBiContrCoeff_appCc_eq (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁') W)
        x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connDiff (I := I) gj g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₀ x b x)) (v 0)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
              else smoothOrthoFrame (I := I) g₀ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
