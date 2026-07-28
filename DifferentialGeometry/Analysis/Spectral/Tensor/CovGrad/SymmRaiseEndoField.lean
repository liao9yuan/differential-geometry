import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCometricRaise
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth

/-!
# Fixed-background raising of a symmetric two-tensor

This file packages the tangent endomorphism obtained by raising one slot of a
smooth symmetric two-tensor with a fixed Riemannian metric.  It is the
linear, fixed-background coefficient used by low-regularity principal
operators.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Raise the second slot of a smooth symmetric two-tensor with the fixed
background metric. -/
noncomputable def symmRaiseEndoFib (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g x
        (ccTensorBilinSymm (I := I) g T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g x
            (ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g x
            (ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [BoundarylessManifold I M] in
@[simp] lemma symmRaiseEndoFib_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v : TangentSpace I x) :
    symmRaiseEndoFib (I := I) (M := M) g T x v =
      metricSharp (I := I) g x
        (ccTensorBilinSymm (I := I) g T x v).toLinearMap := by
  rw [symmRaiseEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [BoundarylessManifold I M] in
/-- The raised endomorphism represents the symmetrized bilinear form. -/
lemma inner_symmRaiseEndo (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    g.inner x (symmRaiseEndoFib (I := I) (M := M) g T x v) w =
      ccTensorBilinSymm (I := I) g T x v w := by
  rw [symmRaiseEndoFib_apply]
  exact inner_metricSharp (I := I) g x
    (ccTensorBilinSymm (I := I) g T x v).toLinearMap w

private theorem symmRaiseEndo_smooth (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (symmRaiseEndoFib (I := I) (M := M) g T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => symmRaiseEndoFib (I := I) (M := M) g T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g T b (Y b)
              (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase :
        (trivializationAt E (TangentSpace I) α).baseSet =
          (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M =>
      (ccTensorBilinSymm (I := I) g T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x
        (ccTensorBilinSymm (I := I) g T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x
      (symmRaiseEndoFib (I := I) (M := M) g T x (Y x))
  rw [symmRaiseEndoFib_apply]

/-- The smooth fixed-background raised endomorphism field. -/
noncomputable def symmRaiseEndo (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => symmRaiseEndoFib (I := I) (M := M) g T x
  contMDiff_toFun := symmRaiseEndo_smooth (I := I) (M := M) g T

@[simp] lemma symmRaiseEndo_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    symmRaiseEndo (I := I) (M := M) g T x =
    symmRaiseEndoFib (I := I) (M := M) g T x := rfl

set_option linter.unusedSectionVars false in
private lemma ccMultilinear_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + U) x : Tensor0SSpace 2 I x) =
      (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) +
        (ccTensorMultilinear (I := I) g U x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

set_option linter.unusedSectionVars false in
private lemma ccModel_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + U) x =
      ccTensorModel (I := I) g T x +
        ccTensorModel (I := I) g U x := by
  unfold ccTensorModel
  rw [ccMultilinear_add, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma ccBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + U) x v w =
      ccTensorBilinSymm (I := I) g T x v w +
        ccTensorBilinSymm (I := I) g U x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccModel_add,
    ContinuousMultilinearMap.add_apply]
  ring

/-- Fixed-background raising is additive in the covariant tensor. -/
lemma symmRaiseEndo_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    symmRaiseEndo (I := I) (M := M) g (T + U) =
      symmRaiseEndo (I := I) (M := M) g T +
        symmRaiseEndo (I := I) (M := M) g U := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [show ((symmRaiseEndo (I := I) (M := M) g T +
      symmRaiseEndo (I := I) (M := M) g U) x) =
      symmRaiseEndo (I := I) (M := M) g T x +
        symmRaiseEndo (I := I) (M := M) g U x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [ContinuousLinearMap.add_apply, map_add]
  simp only [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [ContinuousLinearMap.add_apply, ccBilinSymm_add]
  rw [inner_symmRaiseEndo, inner_symmRaiseEndo]

/-- Fixed-background raising commutes with scalar multiplication. -/
lemma symmRaiseEndo_smul (g : SmoothRiemannianMetric I M) (a : ℝ)
    (T : SmoothCcTensor g 0 2) :
    symmRaiseEndo (I := I) (M := M) g (a • T) =
      a • symmRaiseEndo (I := I) (M := M) g T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [show ((a • symmRaiseEndo (I := I) (M := M) g T) x) =
      a • symmRaiseEndo (I := I) (M := M) g T x from by
    rw [ContMDiffSection.coe_smul]
    rfl]
  rw [ContinuousLinearMap.smul_apply, map_smul]
  simp only [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [ContinuousLinearMap.smul_apply, ccTensorBilinSymm_smul]
  rw [inner_symmRaiseEndo, smul_eq_mul]

private lemma unitModel_eq_bilin (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 S x ![u, w] =
      ccTensorBilin (I := I) g S x u w := by
  rw [ccTensorBilin_apply (I := I) g S x u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g S x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        S.toSection x) (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option linter.unusedSectionVars false in
private lemma interior_product_toModel_eval (s : ℕ) (x : M)
    (v : TangentSpace I x) (D : Tensor0SSpace (s + 1) I x)
    (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  rfl

set_option linter.unusedSectionVars false in
private lemma toModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) =
      (fun _ : Fin 1 => (m 0 : E)) from by
    funext k
    fin_cases k
    rfl]
  rw [cotangentToDual_apply]
  rfl

/-- At rank one, inserting the raised endomorphism is the fixed-background
cometric raise of the symmetrized covariant tensor. -/
lemma insert_symmRaise_eq (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    slotInsertEndoCc (I := I) (M := M) g 0
        (symmRaiseEndo (I := I) (M := M) g T) =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hleft : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g T x (w 0)
        (inverseMetricSharpFib (I := I) g x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (symmRaiseEndo (I := I) (M := M) g T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single (I := I) (M := M) x om
      (Function.update w 0
        (symmRaiseEndo (I := I) (M := M) g T x (w 0)))]
    rw [Function.update_self]
    rw [symmRaiseEndo_apply]
    rw [show cotangentToDual (I := I) (x := x) om
        (symmRaiseEndoFib (I := I) (M := M) g T x (w 0)) =
      cotangentToDualLinear (I := I) (x := x) om
        (symmRaiseEndoFib (I := I) (M := M) g T x (w 0)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (symmRaiseEndoFib (I := I) (M := M) g T x (w 0))]
    rw [g.symm]
    rw [inner_symmRaiseEndo]
  rw [hleft]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 0 x _ om]
  rw [interior_product_toModel_eval (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g
    (Equiv.swap (0 : Fin 2) 1)
    (symmS (I := I) (M := M) g T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g x om)
        (fun k => (show E from w k)) : Fin 2 → E)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E),
        (show E from inverseMetricSharpFib (I := I) g x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_bilin (I := I) (M := M) g
    (symmS (I := I) (M := M) g T) x
    (w 0) (inverseMetricSharpFib (I := I) g x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g T x]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
