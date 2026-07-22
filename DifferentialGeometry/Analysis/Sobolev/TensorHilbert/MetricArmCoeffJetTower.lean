import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricInverseDifferenceSlotCoefficient


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open TensorMultilinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
def connArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (metricComparisonEndo (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connArmEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v0 := by
  rw [connArmEndo, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

def sharpArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x
    - connArmEndo (I := I) g₀ g₁ x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpArmEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    connArmEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma endoCov_eq_connArm_add_sharpArm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0 =
      connArmEndo (I := I) g₀ g₁ x v0 + sharpArmEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [ContinuousLinearMap.add_apply, connArmEndo_apply, sharpArmEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem leviCivitaSection_contMDiff_aux (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  rw [← contMDiffOn_univ]
  exact LeviCivita_section_contMDiffOn_univ (I := I) g hσ'

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem connArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
      (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connArmEndo_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem sharpArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((gInvDiffRaisedEndoField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connArmEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x)
      - connArmEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rfl

set_option backward.isDefEq.respectTransparency false in
def connArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
def connArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

private local instance tangentEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x) (σ₁₂ := RingHom.id ℝ)

private local instance tangentBilinearEndomorphismNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] TangentSpace I x)
    (σ₁₂ := RingHom.id ℝ)

private local instance tensor0STotalSpaceTopology (s : ℕ) :
    TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s

def bilinEndoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] E))
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

instance bilinEndoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (bilinEndoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Arm y) (Y y)) x v -
        (Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Arm Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem armField_inner_contMDiff
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Arm x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Arm x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

set_option backward.isDefEq.respectTransparency false in
def armSlotEndoCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Arm x)
          (fun V0 W => armField_inner_contMDiff (I := I) (M := M) Arm V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma armSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem bilinEndoField_contMDiff
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Arm x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Arm x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Arm x (V0 x)))
  intro W
  exact harm V0 W

def connArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connArmEndo (I := I) g₀ g₁ x)
      (connArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

def sharpArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
      (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connArmEndoField (I := I) g₀ g₁ x = connArmEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpArmEndoField (I := I) g₀ g₁ x = sharpArmEndo (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmEndoCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmEndoCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curry_armSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Arm A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) A := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  rw [tensor0S_curry_apply_eval, armSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem armSlotEndoCc_curry_apply (g : SmoothRiemannianMetric I M)
    (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (A : Tensor0SSpace (s + 1) I x) (u : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x) A)) u =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) u) A := by
  rw [armSlotEndoCc_toSection]
  change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
    (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) A)) u = _
  exact curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) A u

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_sub_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ - Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ -
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) = ((-1 : ℝ)) • Λ₂ from by
    rw [neg_one_smul]]
  rw [slotInsertEndoFib_add_left (I := I) (M := M) s k x Λ₁ ((-1 : ℝ) • Λ₂)]
  rw [slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ₂]
  rw [neg_one_smul]

private theorem add_sub_sub_cancel_right {A : Type*} [AddCommGroup A]
    (a b c : A) : a + c - b - c = a - b := by
  abel

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem tensorCovDerivAt_apply_section (g : SmoothRiemannianMetric I M)
    (r q : ℕ) (S : SmoothCcTensor g r q)
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (x : M) (v : E) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
        tensorCovDerivAt (I := I) (M := M) g r q S x v) (W x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
          (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace q I y from
            S.toSection y) (W y)) x v
        - (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
            S.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
            W x v) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r
  let w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨W, hW⟩
  rw [tensorCovDerivAt_def (I := I) (M := M) g r q S x v]
  exact tensorRSCovariantDerivative_apply (I := I) (M := M) r q
    (LeviCivita (I := I) g) S.toSection w x v

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem tensorCovDerivAt_section_apply_add
    (g : SmoothRiemannianMetric I M) (r q : ℕ) (S : SmoothCcTensor g r q)
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (x : M) (v : E) :
    Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
        (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace q I y from
          S.toSection y) (W y)) x v =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
          tensorCovDerivAt (I := I) (M := M) g r q S x v) (W x)
        + (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace q I x from
            S.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r
            (LeviCivita (I := I) g) W x v) := by
  have h := tensorCovDerivAt_apply_section (I := I) (M := M) g r q S W hW x v
  rw [eq_sub_iff_add_eq] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem tensorCovDerivAt_curried_apply_section
    (g : SmoothRiemannianMetric I M) (r q : ℕ)
    (S : SmoothCcTensor g r (q + 1))
    (W : ∀ y : M, Tensor0SSpace r I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) q x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (q + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g r (q + 1) S x v) (W x))) (Y x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M q (LeviCivita (I := I) g)
          (fun y : M => Tensor0SNabla.curriedSection I M
            (fun z : M => (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace (q + 1) I z from
              S.toSection z) (W z)) y (Y y)) x v
        - Tensor0SNabla.curriedSection I M
            (fun z : M => (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace (q + 1) I z from
              S.toSection z) (W z)) x
            ((LeviCivita (I := I) g) (fun y => Y y) x v)
        - (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) q x
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (q + 1) I x from
              S.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r
                (LeviCivita (I := I) g) W x v))) (Y x) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r
  let w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨W, hW⟩
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (q + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (q + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (q + 1) I z) y
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
          S.toSection y) (W y))) :=
    ContMDiff.clm_bundle_apply (b := id) S.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (q + 1)
      (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
        S.toSection y) (W y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hCL := tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (I := I) (M := M) g q
    (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (q + 1) I y from
      S.toSection y) (W y)) (x := x) hU_at Y v
  have hT := tensorCovDerivAt_apply_section (I := I) (M := M) g r
    (q + 1) S W hW x v
  rw [hT, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL.symm]

private def bilinEndoAppliedSection
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
  ⟨fun y : M => (Arm y) (Y y),
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff Y.contMDiff⟩

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem armSlotEndoCc_curriedSection_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) :
    (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I z from
          (armSlotEndoCc (I := I) (M := M) g s Arm).toSection z) (W z)) y (Y y)) =
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ]
        Tensor0SSpace (s + 1) I y from
        (endoSlotZeroCcTensor (I := I) (M := M) g s
          (bilinEndoAppliedSection (I := I) (M := M) Arm Y)).toSection y) (W y)) := by
  funext y
  rw [Tensor0SNabla.curriedSection_apply, slotInsertEndoCc_toSection]
  exact armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm y (W y) (Y y)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_curve
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          ((endoCovariantDerivative (I := I) (M := M) g)
            (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v) (W x)
        - slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
            ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v)) (W x) := by
  have hbridge := armSlotEndoCc_curriedSection_eq (I := I) (M := M) g s Arm W Y
  have hEndoSI := tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s
    (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v
  set Lw : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g) W x v with hLw
  set NY : TangentSpace I x :=
    (LeviCivita (I := I) g) (fun y => Y y) x v with hNY
  have hT := tensorCovDerivAt_curried_apply_section (I := I) (M := M)
    g (s + 1) (s + 1) (armSlotEndoCc (I := I) (M := M) g s Arm) W hW Y x v
  rw [hT, hbridge, ← hNY, ← hLw]
  have hSI := tensorCovDerivAt_section_apply_add (I := I) (M := M)
    g (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g s
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y)) W hW x v
  rw [hSI, hEndoSI, slotInsertEndoCc_toSection,
    Tensor0SNabla.curriedSection_apply,
    armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm x (W x) NY,
    armSlotEndoCc_curry_apply (I := I) (M := M) g s Arm x Lw (Y x)]
  exact add_sub_sub_cancel_right
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (W x))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_apply_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : ∀ y : M, Tensor0SSpace (s + 1) I y)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W y)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) (W x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x)) (W x) := by
  rw [tensorCovDerivAt_armSlotEndoCc_curry_curve (I := I) (M := M)
    g s Arm W hW Y x v]
  rw [← ContinuousLinearMap.sub_apply
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g)
        (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v))) (W x)]
  rw [← slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
    ((endoCovariantDerivative (I := I) (M := M) g)
      (bilinEndoAppliedSection (I := I) (M := M) Arm Y) x v)
    ((Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v))]
  congr 1
  rw [bilinEndoCovariantDerivative_apply (I := I) (M := M) g Arm Y x v]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) v0) D := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  rw [← hw, ← hY]
  exact tensorCovDerivAt_armSlotEndoCc_curry_apply_sections (I := I) (M := M)
    g s Arm (fun y => w y) w.contMDiff Y x v

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_armSlotEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (armSlotEndoCc (I := I) (M := M) g s Arm) x v) =
      bilinearSlotInsertCLM (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [armSlotFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
        (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib (I := I) (M := M) g s Arm x v D (m 0)]
  simp only [Fin.cons_zero]
  rw [show Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)) = Matrix.vecTail m from by
    funext k; rfl]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_armSlotEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((bilinearSlotInsertCLM (I := I) (M := M) s x
            ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1 + 1)
    (armSlotEndoCc (I := I) (M := M) g s Arm) x D v]
  rw [tensorCovDerivAt_armSlotEndoCc_eq (I := I) (M := M) g s Arm x (v 0)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_eq_slotInsert_section
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁).toSection x) =
      (connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      ((connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connArmCc (I := I) g₀ g₁).toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (sharpArmCc (I := I) g₀ g₁).toSection x) D from rfl]
  change Tensor0SSpace.toModel _ v = Tensor0SSpace.toModel (_ + _) v
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [covGrad_gInvDiffSlotCoeff_toSection_eval (I := I) (M := M) g₀ g₁ x D v]
  rw [connArmCc_toSection, sharpArmCc_toSection]
  change _ = Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x) D) v +
    Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x) D) v
  rw [armSlotFib_apply_eval, armSlotFib_apply_eval]
  rw [endoCov_eq_connArm_add_sharpArm (I := I) g₀ g₁ x (v 0)]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_gInvDiffSlotCoeff_succ_le_arms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (m + 1) (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (connArmCc (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (sharpArmCc (I := I) g₀ g₁)).toSection x) := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 2 2 m
    (gInvDiffSlotCoeff (I := I) g₀ g₁) x]
  rw [covGrad_gInvDiffSlotCoeff_eq_slotInsert_section (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 ((2 + 1) + m) x _ _

section NormedDomReindexing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (tensorRS_domDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => tensorRS_domDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => tensorRS_domDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      tensorRS_domDomCongr σ (R.toSection x) := rfl

end NormedDomReindexing

def armSlotEndoPassZeroCc (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g 2 3 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 3 (finRotate 3)
    (armSlotEndoCc (I := I) (M := M) g 1 Arm)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma armSlotEndoPassZeroCc_toSection (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x =
      tensorRS_domDomCongr (finRotate 3)
        ((armSlotEndoCc (I := I) (M := M) g 1 Arm).toSection x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem toModel_appCcRS_armSlotEndoPassZeroCc_eval (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : SmoothCcTensor g 1 2) (x : M) (om : Tensor0SSpace 1 I x)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
        (fun j : Fin 2 => if j = 0 then Arm x (v 1) (v 2) else v 0) := by
  classical
  have hcomp : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) := by
    rw [appCcRS_toSection]
    rfl
  rw [hcomp, armSlotEndoPassZeroCc_toSection]
  rw [toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [armSlotEndoCc_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) from rfl]
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  have hr0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have hr1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have hr2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, if_pos rfl]
    change Arm x (v (finRotate 3 0)) (v (finRotate 3 1)) = Arm x (v 1) (v 2)
    rw [hr0, hr1]
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Function.update_of_ne (Fin.succ_ne_zero 0), if_neg (Fin.succ_ne_zero 0)]
    change v (finRotate 3 2) = v 0
    rw [hr2]

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) :
    ∃ τ : Equiv.Perm (Fin (3 + j)), ∀ (x : M) (d : Tensor0SSpace 2 I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
            (iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
              (iteratedCovGrad (I := I) g 2 3 j
                (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) d)) := by
  induction j with
  | zero =>
    refine ⟨finRotate 3, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero, armSlotEndoPassZeroCc_toSection,
      toModel_rsDomDomCongr_apply]
  | succ j ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g 2 (3 + j) τ
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoCc (I := I) (M := M) g 1 Arm))
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoPassZeroCc (I := I) (M := M) g Arm))
      hτ x d v

theorem riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (I := I) (M := M) g Arm j
  have hsec : (iteratedCovGrad (I := I) g 2 3 j
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x =
      tensorRS_domDomCongr τ
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          (iteratedCovGrad (I := I) g 2 3 j
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          tensorRS_domDomCongr τ
            ((iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g 2 (3 + j) x τ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricCovDeriv_symm_right
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricCovDeriv (I := I) g cov X Y Z x = metricCovDeriv (I := I) g cov X Z Y x := by
  unfold metricCovDeriv
  rw [show (fun b : M => g.inner b (Z b) (Y b)) = (fun b : M => g.inner b (Y b) (Z b)) from by
    funext b; rw [g.symm b (Z b) (Y b)]]
  rw [g.symm x (cov.toFun Y x (X x)) (Z x), g.symm x (Y x) (cov.toFun Z x (X x))]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDiffCovDeriv_symm_right
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ X Z Y x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_symm_right (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x,
    metricCovDeriv_symm_right (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endoCovariantDerivative_gInvDiffRaisedEndoField_resolvent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - metricDiffCovDeriv (I := I) g₁ g₀
          (fun y : M => V y)
          (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
          (fun y : M => Z y) x := by
  classical
  have hg1gir : ∀ u : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x (W x)) u = g₀.inner x (W x) u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have hpair : g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V x)) (Z x)
        - g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) := by
    rw [endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x (V x) (W x)]
    rw [map_add, ContinuousLinearMap.add_apply, map_neg, ContinuousLinearMap.neg_apply,
      inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show (cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (W x)))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
          g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) from
      cotangentToDual_g0FlatCLM (I := I) g₀ x (W x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
    ring
  have hk1 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
    (Z := fun y : M => Z y) V.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
    Z.mdifferentiableAt
  have hk2 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => Z y)
    (Z := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) V.mdifferentiableAt
    Z.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
  have hsym := metricDiffCovDeriv_symm_right (I := I) g₁ g₀
    (fun y : M => V y) (fun y : M => Z y)
    (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) x
  have hconv : g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))
        (metricComparisonEndo (I := I) g₀ g₁ x (W x)) := by
    rw [← hg1gir (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)),
      g₁.symm x (metricComparisonEndo (I := I) g₀ g₁ x (W x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
  rw [hpair, hconv]
  simp only [] at hk1 hk2
  linarith [hk1, hk2, hsym]

section NormedReindexingNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem rfns_iteratedCovGrad_rsDomDomCongr_both_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (reindexCoeffGen (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ' i x]
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g r s σ R
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

theorem rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ))).toSection x) := by
      rw [slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ s Λ]
      exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)) i x
    rw [hA]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 1 i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
          rw [pow_succ]; ring

end NormedReindexingNorm

end Connection
end Integral
end DifferentialGeometry

end
