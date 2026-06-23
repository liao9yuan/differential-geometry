import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

set_option linter.unusedSectionVars false in
theorem norm_le_of_pointwise_fiberNormSq_bound_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (B : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ B) :
    ‖C‖ ^ 2 ≤ B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∫ _x, B ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine MeasureTheory.integral_mono hint (MeasureTheory.integrable_const B)
          (fun x => hpt x)
    _ = B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul,
          MeasureTheory.measureReal_def, mul_comm]

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_gInvDiffSlotCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hbase := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) (M := M) g₀ g₁
    (ccTensorBilinSymm g₀ T) (fun y v w => h y v w) hδ1 hδ0 hbound x
  have hcoeff : (0 : ℝ) < 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 1 := by
    rw [div_le_one hcoeff]; linarith
  have hratio0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hmono : ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
    have : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ≤ (Module.finrank ℝ E : ℝ) := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hfr0
        _ = (Module.finrank ℝ E : ℝ) := by rw [mul_one]
    nlinarith [mul_nonneg hfr0 hratio0]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (gInvDiffSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

set_option backward.isDefEq.respectTransparency false in
def gInvDiffRaisedEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => gInvDiffRaisedEndo (I := I) g₀ g₁ x
  contMDiff_toFun := gInvDiffRaisedEndo_contMDiff (I := I) g₀ g₁

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem gInvDiffSlotCoeff_eq_slotInsertEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    gInvDiffSlotCoeff (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem inverseMetricSharpFib_g0FlatY_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (g0FlatCLM (I := I) g₀ b (Y b)))) := by
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricSharp (I := I) g₁ b ((g₀.inner b (Y b)).toLinearMap))) := by
    apply metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x (Y x)]

set_option linter.unusedSectionVars false in
private theorem cotangent_g0FlatY_mdiffAtCotangent
    (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) x := by
  have heq : (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) =
      metricFlat (I := I) g₀ (fun b : M => Y b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro w
    rw [metricFlat_apply]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ b (Y b)) w = _
    exact cotangentToDual_g0FlatCLM (I := I) g₀ b (Y b) w
  rw [heq]
  exact metricFlat_mdiff (I := I) g₀ (Y.contMDiff.mdifferentiableAt (by norm_num))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem endoCov_gInvDiffRaisedField_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) := by
  classical
  set β : Π b : M, Tensor0SSpace 1 I b := fun b : M => g0FlatCLM (I := I) g₀ b (Y b) with hβdef
  set gradY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v with hgradY
  have hYmd := Y.mdifferentiableAt (x := x)
  have hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₁ y) (β y))) x :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hβ₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) x := by
    have hcong : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) := by
      funext y
      rw [hβdef]
      rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hcong]
    exact Y.mdifferentiableAt (x := x)
  have hβcot : MDiffAtCotangent (I := I) (fun b : M => cotangentToCLM (I := I) (β b)) x :=
    cotangent_g0FlatY_mdiffAtCotangent (I := I) g₀ Y x
  have hsharpY_mdiff :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hΛapply : (gInvDiffRaisedEndoField (I := I) g₀ g₁ : Π y : M, _) =
      fun y : M => gInvDiffRaisedEndo (I := I) g₀ g₁ y := rfl
  have hLeibniz := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) Y x v
  rw [hLeibniz]
  have hΛval : ∀ y : M, (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y) =
      (inverseMetricSharpFib (I := I) g₁ y) (β y) - Y y := by
    intro y
    rw [hβdef]
    change gInvDiffRaisedEndo (I := I) g₀ g₁ y (Y y) = _
    rw [gInvDiffRaisedEndo_apply]
  have hΛx : (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) gradY =
      (inverseMetricSharpFib (I := I) g₁ x) (g0FlatCLM (I := I) g₀ x gradY) - gradY := by
    change gInvDiffRaisedEndo (I := I) g₀ g₁ x gradY = _
    rw [gInvDiffRaisedEndo_apply]
  have hsplit : (LeviCivita (I := I) g₀) (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x v
        - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := by
    have hfun : (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) =
        (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) - (fun y : M => Y y) := by
      funext y
      rw [Pi.sub_apply, hΛval y]
    have hop : (LeviCivita (I := I) g₀).toFun
          (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x =
        (LeviCivita (I := I) g₀).toFun
            (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x
          - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x := by
      rw [hfun]
      exact cov_toFun_sub (LeviCivita (I := I) g₀) hsharpY_mdiff hYmd
    have hopv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hop
    simpa using hopv
  rw [hsplit]
  have hcross := covGrad_inverseMetricSharpFib_cross (I := I) g₀ g₁ β hβ hβcot v
  rw [hcross]
  have hT1 : inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x gradY) := by
    have hB := inverseMetricSharpField_covGrad_eq_zero (I := I) g₀ β hβ₀ v
    have hseceq : (fun b : M => (inverseMetricSharpFib (I := I) g₀ b) (β b)) =
        (fun y : M => Y y) := by
      funext y
      rw [hβdef, inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hseceq] at hB
    have hflat : g0FlatCLM (I := I) g₀ x gradY =
        dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v) := by
      rw [hgradY, hB,
        Analysis.Parabolic.TensorSpectral.g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x _]
    rw [hflat]
  rw [hT1, hΛx]
  rw [show (inverseMetricSharpFib (I := I) g₁ x) (β x) =
      gInvRaisedEndo (I := I) g₀ g₁ x (Y x) from by
    rw [hβdef, gInvRaisedEndo_apply]]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem endoCompSection_contMDiff
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        ((A x).comp (B x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => (A x).comp (B x))
  intro Y
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hABY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((A y) (BY y))) :=
    endoApplySection_contMDiff (I := I) (M := M) A BY
  refine hABY.congr (fun x => ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
def endoCompField (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => (A x).comp (B x)
  contMDiff_toFun := endoCompSection_contMDiff (I := I) (M := M) A B

set_option linter.unusedSectionVars false in
@[simp] lemma endoCompField_apply
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) (x : M) :
    (endoCompField (I := I) (M := M) A B x) = (A x).comp (B x) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem endoCovariantDerivative_comp
    (g₀ : SmoothRiemannianMetric I M)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) =
      ((endoCovariantDerivative (I := I) (M := M) g₀) A x v).comp (B x) +
        (A x).comp ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hYmd := Y.mdifferentiableAt (x := x)
  have hABcomp := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (endoCompField (I := I) (M := M) A B) Y x v
  have hAonBY := endoCovariantDerivative_apply (I := I) (M := M) g₀ A BY x v
  have hBonY := endoCovariantDerivative_apply (I := I) (M := M) g₀ B Y x v
  have hfun_eq : (fun y : M => (endoCompField (I := I) (M := M) A B y) (Y y)) =
      (fun y : M => (A y) ((B y) (Y y))) := by
    funext y
    rw [endoCompField_apply, ContinuousLinearMap.comp_apply]
  have hcompval : ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) (Y x) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (endoCompField (I := I) (M := M) A B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [hABcomp, hfun_eq]
  have hgradY : (LeviCivita (I := I) g₀) (fun y => Y y) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := rfl
  have hBgrad : (LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v =
      ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) (Y x) +
        (B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [eq_sub_iff_add_eq] at hBonY
    rw [← hBonY]
  have hAonBY' : ((endoCovariantDerivative (I := I) (M := M) g₀) A x v) ((B x) (Y x)) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (A x) ((LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v) := hAonBY
  rw [← hYx]
  rw [hcompval]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, endoCompField_apply, ContinuousLinearMap.comp_apply]
  rw [hAonBY', hBgrad, map_add]
  abel

set_option linter.unusedSectionVars false in
private lemma sqrt_g0_inner_add_le'
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hsum_nn : 0 ≤ g₀.inner x (a + b) (a + b) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (a + b)
  have hna_nn : 0 ≤ na := Real.sqrt_nonneg _
  have hnb_nn : 0 ≤ nb := Real.sqrt_nonneg _
  have hna_sq : na ^ 2 = g₀.inner x a a := by rw [hna, Real.sq_sqrt haa_nn]
  have hnb_sq : nb ^ 2 = g₀.inner x b b := by rw [hnb, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x a b ≤ na * nb := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x a b
    rw [← hna, ← hnb] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (a + b) (a + b) =
      g₀.inner x a a + 2 * g₀.inner x a b + g₀.inner x b b := by
    have h1 : g₀.inner x (a + b) (a + b)
        = g₀.inner x a (a + b) + g₀.inner x b (a + b) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x a (a + b) = g₀.inner x a a + g₀.inner x a b :=
      map_add (g₀.inner x a) a b
    have h3 : g₀.inner x b (a + b) = g₀.inner x b a + g₀.inner x b b :=
      map_add (g₀.inner x b) a b
    have h4 : g₀.inner x b a = g₀.inner x a b := g₀.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hle_sq : g₀.inner x (a + b) (a + b) ≤ (na + nb) ^ 2 := by
    rw [hexpand]
    have hsq : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [hsq, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem sqrt_inner_endoCov_gInvDiffRaisedField_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x (Y x) (Y x)) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := connDiff_gFibreNorm_le_iteratedCovGrad (I := I) (M := M) g₀
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound Y x v
  have hcoeff : 0 < 1 - δ := by linarith
  set w : TangentSpace I x := Y x with hw_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hinv_le : 1 / (1 - δ) ≤ 2 := by rw [div_le_iff₀ hcoeff]; linarith
  set EC : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) with hEC_def
  set T2 : TangentSpace I x :=
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x w) v
    with hT2_def
  set T3 : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x
      (dualToCotangent (I := I)
        (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)
    with hT3_def
  have hEC_eq : EC = T2 + T3 := by
    rw [hEC_def, hT2_def, hT3_def, hw_def]
    exact endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v
  have hgir := sqrt_inner_gInvRaisedEndo_le (I := I) g₀ g₁
    (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
    (by linarith : δ < 1) hδ0 hbound x w
  rw [← hNw_def] at hgir
  have hT2_bound : Real.sqrt (g₀.inner x T2 T2) ≤ 2 * C₀ * G * Nv * Nw := by
    have hraw := hpw g₁ T h hδ hδ0 hbound x (gInvRaisedEndo (I := I) g₀ g₁ x w) v
    rw [← hNv_def] at hraw
    have hT2_sq : g₀.inner x T2 T2 =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (gInvRaisedEndo (I := I) g₀ g₁ x w) v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (gInvRaisedEndo (I := I) g₀ g₁ x w) v) := by
      simp only [hT2_def, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    rw [hT2_sq]
    refine hraw.trans ?_
    have hgir' : Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x w)
        (gInvRaisedEndo (I := I) g₀ g₁ x w)) ≤ 2 * Nw := by
      refine hgir.trans ?_
      exact mul_le_mul_of_nonneg_right hinv_le hNw_nn
    calc C₀ * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
            Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x w)
              (gInvRaisedEndo (I := I) g₀ g₁ x w)) * Nv
        ≤ C₀ * G * (2 * Nw) * Nv := by
          rw [← hG_def]
          gcongr
      _ = 2 * C₀ * G * Nv * Nw := by ring
  have hT3_bound : Real.sqrt (g₀.inner x T3 T3) ≤ 2 * C₀ * G * Nv * Nw := by
    set Dfun : TangentSpace I x →L[ℝ] ℝ :=
      (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)) with hDfun_def
    set p : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₀ x (dualToCotangent (I := I) Dfun.toLinearMap)
      with hp_def
    have hT3eq : T3 = inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p) := by
      rw [hT3_def]
      congr 1
      exact (g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap)).symm
    set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNpdef
    have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
    have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
    have hNp_sq : Np ^ 2 = g₀.inner x p p := Real.sq_sqrt hpp_nn
    have hDval : ∀ z : TangentSpace I x, Dfun z =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
      intro z
      rw [hDfun_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply]
      change - cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ x w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) = _
      rw [cotangentToDual_g0FlatCLM]
    have hpz : ∀ z : TangentSpace I x, g₀.inner x p z = Dfun z := by
      intro z
      rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap) z]
      rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
      rfl
    have hpp_val : g₀.inner x p p =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v) := by
      rw [hpz p, hDval p]
    have hconn_p := hpw g₁ T h hδ hδ0 hbound x p v
    rw [← hNv_def, ← hNpdef] at hconn_p
    have hconnG : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤ C₀ * G * Np * Nv := hconn_p
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x w
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
    rw [← hNw_def] at hcs
    have hNp_le : Np ≤ C₀ * G * Nv * Nw := by
      have hpp_le : g₀.inner x p p ≤
          Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := by
        rw [hpp_val]
        calc - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            ≤ |g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)| := neg_le_abs _
          _ ≤ Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := hcs
      have hKnn : 0 ≤ C₀ * G * Nv * Nw :=
        mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn
      have hchain : Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤
          Nw * (C₀ * G * Np * Nv) :=
        mul_le_mul_of_nonneg_left hconnG hNw_nn
      have hpp_le2 : g₀.inner x p p ≤ (C₀ * G * Nv * Nw) * Np := by
        refine hpp_le.trans (hchain.trans ?_)
        nlinarith [hNw_nn, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn]
      nlinarith [hNp_sq, hNp_nn, hpp_le2, hKnn]
    have hsharp := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
      (by linarith : δ < 1) hδ0 hbound x p
    rw [← hNpdef] at hsharp
    rw [hT3eq]
    refine hsharp.trans ?_
    have hstep : (1 / (1 - δ)) * Np ≤ 2 * Np :=
      mul_le_mul_of_nonneg_right hinv_le hNp_nn
    refine hstep.trans ?_
    nlinarith [hNp_le, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) (mul_nonneg hNv_nn hNw_nn)]
  have htri : Real.sqrt (g₀.inner x EC EC) ≤
      Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) := by
    rw [hEC_eq]
    exact sqrt_g0_inner_add_le' (I := I) g₀ x T2 T3
  refine htri.trans ?_
  have hsum : Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) ≤
      (2 * C₀ * G * Nv * Nw) + (2 * C₀ * G * Nv * Nw) := add_le_add hT2_bound hT3_bound
  refine hsum.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn]

set_option linter.unusedSectionVars false in
private lemma fiberComponent_slotInsertEndoFib_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x Λ) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [g₀.symm x (e (K 0)) (Λ (e (J 0))), horth (K 1) (J 1)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) e bse hnE hbse horth]
  have hcompsq : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 * (if K 1 = J 1 then (1 : ℝ) else 0) := by
    intro K J
    rw [fiberComponent_slotInsertEndoFib_eq (I := I) g₀ x Λ e horth K J]
    rw [g₀.symm x (Λ (e (J 0))) (e (K 0))]
    by_cases hkj : K 1 = J 1
    · simp only [hkj, if_true, mul_one]
    · simp only [hkj, if_false, mul_zero]; ring
  have hsumeq : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2) =
      ∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [Finset.sum_congr rfl (fun K _ => hcompsq K J)]
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun K : Fin 2 → Fin n => (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 *
        (if K 1 = J 1 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    have hKsum : ∀ k0 : Fin n,
        (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
        (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 := by
      intro k0
      rw [show (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
          ∑ k1 : Fin n, (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 *
            (if k1 = J 1 then (1 : ℝ) else 0) from by
        refine Finset.sum_congr rfl (fun k1 _ => ?_)
        rfl]
      rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (J 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun k0 _ => hKsum k0)]
    exact hpars (Λ (e (J 0)))
  rw [hsumeq]
  have hJbound : ∀ J : Fin 2 → Fin n,
      g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) ≤ B := by
    intro J
    refine hΛ (e (J 0)) ?_
    rw [horth (J 0) (J 0)]; simp
  calc (∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))))
      ≤ ∑ _J : Fin 2 → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option linter.unusedSectionVars false in
private lemma fiberComponent_slotInsertEndoFib_eq_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      g₀.inner x (e (K k)) (Λ (e (J k))) *
        ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x s s
      (show TensorRSSpace s s I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) s k x Λ) (coframeS (I := I) (M := M) g₀ x s e K))
        (fun l => e (J l)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x s e K).toModel
        (Function.update (fun l => e (J l)) k (Λ (e (J k))))
      = coframeS (I := I) (M := M) g₀ x s e K
        (Function.update (fun l => e (J l)) k (Λ (e (J k)))) from rfl]
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun l => g₀.inner x (e (K l))
      (Function.update (fun l => e (J l)) k (Λ (e (J k))) l)) (Finset.mem_univ k)]
  rw [Function.update_self]
  rw [g₀.symm x (e (K k)) (Λ (e (J k)))]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rw [Function.update_of_ne hlk, horth (K l) (J l)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma sum_compSq_slotInsertEndoFib_eq_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (J : Fin s → Fin n) :
    (∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
  classical
  have hcompsq : ∀ K : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
    intro K
    rw [fiberComponent_slotInsertEndoFib_eq_general (I := I) g₀ x s k Λ e horth K J]
    rw [mul_pow]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    by_cases hkj : K l = J l
    · simp [hkj]
    · simp [hkj]
  rw [Finset.sum_congr rfl (fun K _ => hcompsq K)]
  set ee := Equiv.funSplitAt k (Fin n) with hee
  rw [← (Equiv.sum_comp ee.symm
    (fun K : Fin s → Fin n => (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
      ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0)))]
  rw [Fintype.sum_prod_type]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n), (ee.symm (m, ρ)) k = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hinner : ∀ m : Fin n,
      (∑ ρ : {i : Fin s // i ≠ k} → Fin n,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 := by
    intro m
    have hcoe : ∀ (ρ : {i : Fin s // i ≠ k} → Fin n) (l : Fin s) (hl : l ≠ k),
        (ee.symm (m, ρ)) l = ρ ⟨l, hl⟩ := by
      intro ρ l hl
      rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hl]
    have hindic : ∀ ρ : {i : Fin s // i ≠ k} → Fin n,
        (∏ l ∈ Finset.univ.erase k,
          (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0) := by
      intro ρ
      by_cases hρ : ρ = (fun j : {i : Fin s // i ≠ k} => J j)
      · rw [if_pos hρ]
        refine Finset.prod_eq_one (fun l hl => ?_)
        have hlk : l ≠ k := Finset.ne_of_mem_erase hl
        rw [hcoe ρ l hlk, hρ, if_pos rfl]
      · rw [if_neg hρ]
        obtain ⟨j, hj⟩ : ∃ j : {i : Fin s // i ≠ k}, ρ j ≠ J j := by
          by_contra hcon
          exact hρ (funext (fun j => not_not.mp (fun h => hcon ⟨j, h⟩)))
        refine Finset.prod_eq_zero (i := (j : Fin s))
          (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩) ?_
        rw [hcoe ρ (j : Fin s) j.2, if_neg hj]
    rw [Finset.sum_congr rfl (fun ρ _ => by rw [hkval m ρ, hindic ρ] :
      ∀ ρ ∈ Finset.univ,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 *
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0))]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ (fun j : {i : Fin s // i ≠ k} => J j) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  exact hpars (Λ (e (J k)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ s s x
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ s * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ s s x
    (show TensorRSSpace s s I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) e bse hnE hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin s → Fin n, ∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      ∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    exact sum_compSq_slotInsertEndoFib_eq_normSq (I := I) g₀ x s k Λ e horth hpars J
  rw [hsumeq]
  have hJbound : ∀ J : Fin s → Fin n,
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) ≤ B := by
    intro J
    refine hΛ (e (J k)) ?_
    rw [horth (J k) (J k)]; simp
  calc (∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))))
      ≤ ∑ _J : Fin s → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ s * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := sqrt_inner_endoCov_gInvDiffRaisedField_le (I := I) (M := M) g₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀), by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  set Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛ_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁, ← hΛ_def]
  rw [covGrad_toSection_apply (I := I) (M := M) g₀ 2 2
    (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ) x]
  refine le_trans (DifferentialGeometry.Analysis.Sobolev.Tensor.riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs (I := I) (M := M)
    g₀ 2 2 x _ ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) ?_) ?_
  · intro v hv
    have hΦ : tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ).toSection y) x v =
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v))) := by
      rw [← tensorCovDerivAt_def (I := I) (M := M) g₀ 2 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ) x v]
      exact tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 1 Λ x v
    rw [hΦ]
    refine riemannianFiberNormSq_slotInsertEndoFib_le_card_mul (I := I) g₀ x
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) ((4 * C₀ * G) ^ 2) ?_ (by positivity)
    intro a ha
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x a
    have hbd := hpw g₁ T h hδ hδ0 hbound Y x v
    rw [hYx] at hbd
    have hvroot : Real.sqrt (g₀.inner x v v) = 1 := by rw [hv, Real.sqrt_one]
    have haroot : Real.sqrt (g₀.inner x a a) = 1 := by rw [ha, Real.sqrt_one]
    rw [hvroot, haroot, mul_one, mul_one, ← hG_def] at hbd
    have haa_nn : 0 ≤ g₀.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have hsq := Real.sq_sqrt haa_nn
    nlinarith [hbd, Real.sqrt_nonneg (g₀.inner x
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)), hsq,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC₀0) hG_nn]
  · have hsq3 : Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) ^ 2 = (Module.finrank ℝ E : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    have hrhs : (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀)) ^ 2 * G ^ 2 =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by
      rw [mul_pow, hsq3]; ring
    have hlhs : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by ring
    rw [hlhs, hrhs]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (W : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖(W.toSection x : TensorRSSpace r s I x)‖ =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x)]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) (R : ℝ) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
    ‖((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
        TensorRSSpace 2 2 I x)‖ ≤
      (Module.finrank ℝ E : ℝ) * (1 + R) ^ 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
  rw [iteratedCovGrad_zero, pow_zero, mul_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (gInvDiffSlotCoeff (I := I) g₀ g₁)]
  have hb := riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T hδ hδ0 h hbound x
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (Module.finrank ℝ E : ℝ) := Real.sqrt_sq hfr0

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) {R : ℝ}
      (hR0 : 0 ≤ R)
      (hjet : letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
      ‖((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
          TensorRSSpace 2 3 I x)‖ ≤ C * (1 + R) ^ 1 := by
  obtain ⟨C, hC0, hbnd⟩ := riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x R hR0 hjet
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  have hb := hbnd g₁ T hδ hδ0 h hbound x
  have hiter1 : iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [pow_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      (iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)), hiter1]
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hsqrt_le : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt (C ^ 2 * G ^ 2) := Real.sqrt_le_sqrt hb
  refine hsqrt_le.trans ?_
  rw [show C ^ 2 * G ^ 2 = (C * G) ^ 2 from by ring, Real.sqrt_sq (mul_nonneg hC0 hG0)]
  have hGR : G ≤ R := hjet
  calc C * G ≤ C * R := mul_le_mul_of_nonneg_left hGR hC0
    _ ≤ C * (1 + R) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0; linarith

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_toSection_eval
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc (I := I) g₀ g₁]
  exact covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 1
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) x D v

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_endoCov_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) :=
  endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_add_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_smul_comp (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [hca, ha, map_smul]

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_neg_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul_comp (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
def gInvCompPairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add_comp (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul_comp (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hRaised : Continuous (gInvRaisedEndo (I := I) g₀ g₁ x) :=
          (gInvRaisedEndo (I := I) g₀ g₁ x).continuous
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
          have hc : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
          have hcomp : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
              (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0), YZ 1)) :=
            (hRaised.comp (continuous_apply 0)).prodMk (continuous_apply 1)
          exact hc.comp hcomp
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma gInvCompPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (gInvCompPairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := rfl

set_option linter.unusedSectionVars false in
lemma gInvCompPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    gInvCompPairing (I := I) g₀ g₁ x (om + om') =
      gInvCompPairing (I := I) g₀ g₁ x om + gInvCompPairing (I := I) g₀ g₁ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

set_option linter.unusedSectionVars false in
lemma gInvCompPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    gInvCompPairing (I := I) g₀ g₁ x (c • om) =
      c • gInvCompPairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def connDiffGInvCompositeFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => gInvCompPairing (I := I) g₀ g₁ x om
        map_add' := gInvCompPairing_add (I := I) g₀ g₁ x
        map_smul' := gInvCompPairing_smul (I := I) g₀ g₁ x })

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffGInvCompositeFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffGInvCompositeFib (I := I) g₀ g₁ x) om =
      gInvCompPairing (I := I) g₀ g₁ x om := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gInvRaisedEndo_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (gInvRaisedEndo (I := I) g₀ g₁ b (Y b))) := by
  refine (inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y).congr (fun b => ?_)
  rw [gInvRaisedEndo_apply]

set_option backward.isDefEq.respectTransparency false in
theorem connDiffGInvCompositeFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x
        (connDiffGInvCompositeFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffGInvCompositeFib (I := I) g₀ g₁ x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (gInvCompPairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (gInvCompPairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
        (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ (Y (σ 0))) (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
          (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (gInvCompPairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [gInvCompPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
def connDiffGInvComposite (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connDiffGInvCompositeFib (I := I) g₀ g₁ x
      contMDiff_toFun := connDiffGInvCompositeFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma connDiffGInvComposite_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffGInvComposite (I := I) g₀ g₁).toSection x =
      connDiffGInvCompositeFib (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma connDiffGInvComposite_pairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
  rw [connDiffGInvComposite_toSection, connDiffGInvCompositeFib_apply, gInvCompPairing_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_eq_appCcRS_composite
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x)
    (om : Tensor0SSpace 1 I x) :
    om (fun _ : Fin 1 =>
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x)) =
      - ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om)
            (fun j : Fin 2 => if j = 0 then Y x else v)
      + om (fun _ : Fin 1 =>
          inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                  ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)) := by
  rw [covGrad_gInvDiffSlotCoeff_endoCov_apply (I := I) g₀ g₁ Y x v]
  rw [tensor0SOne_apply_add_comp (I := I) x om,
    tensor0SOne_apply_neg_comp (I := I) x om]
  rw [connDiffGInvComposite_pairing_apply (I := I) g₀ g₁ x om
    (fun j : Fin 2 => if j = 0 then Y x else v)]
  simp only [Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]

end Connection
end Integral
end DifferentialGeometry

end
