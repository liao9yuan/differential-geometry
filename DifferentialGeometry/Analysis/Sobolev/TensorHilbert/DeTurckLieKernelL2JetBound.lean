import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (dLaBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckLieCovDerivA connDiff_pairing_mdiffAt dLaCovKernel dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieDLaCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieDLaCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieDLbCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieDLbCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl

set_option linter.unusedSectionVars false in
theorem deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieDLaCoeffField_toSection, deTurckLieDLbCoeffField_toSection,
    deTurckLieCoeffField_toSection]
  rfl

set_option linter.unusedSectionVars false in
theorem connDiff_cocycle (gA gB gC : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v + PDE.DeTurck.connDiff (I := I) gB gC x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v := by
  classical
  have hσ := smoothExtensionTangent_mdiff (I := I) x u x
  have hu : smoothExtensionTangent (I := I) x u x = u :=
    smoothExtensionTangent_eq (I := I) x u
  rw [← hu]
  rw [PDE.DeTurck.connDiff_apply (I := I) gA gB hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gB gC hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gA gC hσ v]
  abel

set_option linter.unusedSectionVars false in
theorem deTurckLieCovDerivA_backgroundSplit
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (X P Q : Π b : M, TangentSpace I b) (x : M)
    (hP : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (P b)) x)
    (hQ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Q b)) x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg X P Q x =
      covDerivConnDiff (I := I) g₀ g₁ X Q P x
        - covDerivConnDiff (I := I) g₀ g_bg X Q P x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) := by
  classical
  have hσ := connDiff_pairing_mdiffAt (I := I) g₁ g_bg hP hQ
  have hσB := connDiff_pairing_mdiffAt (I := I) g_bg g₀ hP hQ
  have hsum : (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
        + (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) := by
    funext b
    change PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)
    exact (connDiff_cocycle (I := I) g₁ g_bg g₀ b (P b) (Q b)).symm
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
    (σ' := fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) hσ hσB
  have hsplit : (LeviCivita (I := I) g₀).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
    have h3 : (LeviCivita (I := I) g₀).toFun
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          + (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
      rw [hsum]
      have h2 := congrArg (fun L => L (X x)) hadd
      simpa using h2
    rw [h3]
    abel
  have hout' : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        = (LeviCivita (I := I) g₁).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          - (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b : M =>
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) hσ (X x)
    rw [h]
    abel
  have hinnP' : (LeviCivita (I := I) g₁).toFun P x (X x)
      = (LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)
        = (LeviCivita (I := I) g₁).toFun P x (X x)
          - (LeviCivita (I := I) g₀).toFun P x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := P) hP (X x)
    rw [h]
    abel
  have hinnQ' : (LeviCivita (I := I) g₁).toFun Q x (X x)
      = (LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)
        = (LeviCivita (I := I) g₁).toFun Q x (X x)
          - (LeviCivita (I := I) g₀).toFun Q x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Q) hQ (X x)
    rw [h]
    abel
  have hsplitT2 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x) := by
    rw [map_add]
    rfl
  have hsplitT3 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) :=
    map_add _ _ _
  have hT2c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
    rw [← h]
    abel
  have hT3c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x)) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
    rw [← h]
    abel
  have hA : covDerivConnDiff (I := I) g₀ g₁ X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  have hB : covDerivConnDiff (I := I) g₀ g_bg X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₁).toFun P x (X x)) (Q x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₁).toFun Q x (X x)) = _
  rw [hout', hinnP', hinnQ', hsplitT2, hsplitT3, hT2c, hT3c, hsplit, hA, hB]
  abel

set_option linter.unusedSectionVars false in
theorem dLaCovKernel_backgroundSplit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 p q =
      covDerivConnDiff (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v0)
          (smoothExtensionTangent (I := I) x q)
          (smoothExtensionTangent (I := I) x p) x
        - covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v0)
            (smoothExtensionTangent (I := I) x q)
            (smoothExtensionTangent (I := I) x p) x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x p q) v0
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x p
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) := by
  rw [dLaCovKernel_apply_extend (I := I) g₁ g_bg x v0 p q]
  rw [deTurckLieCovDerivA_backgroundSplit (I := I) g₀ g₁ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x p)
    (smoothExtensionTangent (I := I) x q) x
    (smoothExtensionTangent_mdiff (I := I) x p x)
    (smoothExtensionTangent_mdiff (I := I) x q x)]
  simp only [smoothExtensionTangent_eq]

end DifferentialGeometry.Integral.Connection

end
