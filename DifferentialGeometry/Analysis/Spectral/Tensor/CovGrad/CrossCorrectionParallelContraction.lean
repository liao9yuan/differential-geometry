import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionContractionCalculus
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorFibreCauchySchwarz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound

/-! # The cross-correction contraction realizes `crossCorrectionSection`

For two smooth Riemannian metrics `g₁`, `g₀` on a closed smooth Riemannian manifold `(M, g₀)` modelled
on a real inner-product space `E`, the parallel two-section cometric contraction
`crossCorrParallelContraction` (built frame-free in `CrossCorrectionContractionCalculus`) is here
identified, at the symmetric realized perturbation `h = realizeSymm T₁` (rank `2`) and the slot-cycled
`g₀`-lowered connection difference `D = loweredConnDiff g₁ g₀` (rank `3`), with the nonlinear
cross-correction `(0, 3)`-section `crossCorrectionSection`:

```
crossCorrParallelContraction g₀ (realizeSymmCcTensor g₀ T₁)
    (permuteCcTensor g₀ c[0,1,2] (loweredConnDiffSection g₁ g₀))
  = crossCorrectionSection g₁ g₀ T₁.
```

This concrete identification is the one piece of the contraction development that depends on the
connection-difference jet machinery (`crossCorrectionSection`, `loweredConnDiffSection`,
`sum_inner_dualPair_apply_eq_sum_chartBasis_repr`); it therefore lives here, downstream of both the
frame-free contraction calculus and the connection-difference jet file.  The reusable contraction
calculus itself — the definition, bilinearity, operator-field bridge, slot bookkeeping, and the
`g`-operator-norm fibre envelope — is the first-class byproduct
`CrossCorrectionContractionCalculus`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Measure (chartModelBasis)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The concrete fibre identity: the parallel contraction realizes the cross-correction section

The re-targeted parallel `g₀`-single contraction, evaluated at the symmetric realized perturbation
`h = realizeSymm T₁` and the slot-cycled `g₀`-lowered connection difference, reproduces the nonlinear
cross-correction `(0, 3)`-section `crossCorrectionSection` exactly.  The model contraction reads the
two connection-difference input slots and the perturbation's second argument into the output, raising
the lowered connection-difference output index by the cometric and reconstructing the genuine
connection-difference output vector through the cometric dual-pair (`sum_phi_cometric_inner_basis`, the
rank-`1` specialization of the dual-pair coordinate-trace `sum_inner_dualPair_apply_eq_sum_chartBasis_repr`).
This certifies that the contraction is instantiated at the correct slot (the slot-`2` lowered output
index, matching `crossCorrectionSection`), not the slot-`0` connection-difference input index. -/

set_option linter.unusedSectionVars false in
theorem crossCorrModelFun_eval00 (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + 0) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (3 + 0) ℝ E)
    (p q r : E) :
    crossCorrModelFun (E := E) L 0 0 Sm Tm ![p, q, r] =
      ∑ i : Fin (Module.finrank ℝ E),
        Tm ![(Module.finBasis ℝ E) i, p, q] *
          Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)), r] := by
  classical
  unfold crossCorrModelFun
  rw [modelRankCastCc_apply', ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  have hT : ((Tensor0SBundle.model_interior_product (2 + 0) ((Module.finBasis ℝ E) i))
        ((modelRankCastCc (E := E) (by omega : 3 + 0 = (2 + 0) + 1) Tm)))
        ((fun j => (![p, q, r] : Fin 3 → E) (finCongr (by omega : (2+0)+(1+0)=3+0+0) j)) ∘ Fin.castAdd (1 + 0))
      = Tm ![(Module.finBasis ℝ E) i, p, q] := by
    change (modelRankCastCc (E := E) (by omega : 3 + 0 = (2 + 0) + 1) Tm)
        (Fin.cons ((Module.finBasis ℝ E) i) _) = _
    rw [modelRankCastCc_apply']
    congr 1
    funext j; fin_cases j <;> rfl
  have hS : ((Tensor0SBundle.model_interior_product (1 + 0)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))))
        ((modelRankCastCc (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)))
        ((fun j => (![p, q, r] : Fin 3 → E) (finCongr (by omega : (2+0)+(1+0)=3+0+0) j)) ∘ Fin.natAdd (2 + 0))
      = Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i)), r] := by
    change (modelRankCastCc (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)
        (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))) _) = _
    rw [modelRankCastCc_apply']
    congr 1
    funext j; fin_cases j <;> rfl
  rw [hT, hS]

set_option linter.unusedSectionVars false in
theorem cometricReadingModel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (y : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y) :
    g₀.inner y (cometricReadingModel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricReadingModel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

set_option linter.unusedSectionVars false in
theorem sum_phi_cometric_inner_basis (g₀ : SmoothRiemannianMetric I M) (x : M)
    (P : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hP : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (P k) u = (Module.finBasis ℝ E).repr (u : E) k)
    (φ : TangentSpace I x →L[ℝ] ℝ) (V : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        φ (P i) * g₀.inner x V ((Module.finBasis ℝ E) i) = φ V := by
  classical
  set F : TangentSpace I x →L[ℝ] TangentSpace I x := φ.smulRight V with hF
  have key := sum_inner_dualPair_apply_eq_sum_chartBasis_repr (I := I) (M := M) g₀ x P hP F
  have hLHS : ∑ i : Fin (Module.finrank ℝ E), φ (P i) * g₀.inner x V ((Module.finBasis ℝ E) i)
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (F (P k)) ((Module.finBasis ℝ E) k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hF, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have htr : ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (F ((chartModelBasis E) i)) i
      = LinearMap.trace ℝ (TangentSpace I x) (F : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :=
    (trace_eq_sum_basis_repr (I := I) (M := M) x (chartModelBasis E) F).symm
  rw [hLHS, key, htr, hF]
  rw [show ((ContinuousLinearMap.smulRight φ V : TangentSpace I x →L[ℝ] TangentSpace I x) :
        TangentSpace I x →ₗ[ℝ] TangentSpace I x)
      = LinearMap.smulRight (φ : TangentSpace I x →ₗ[ℝ] ℝ) V from rfl]
  rw [LinearMap.trace_smulRight]
  rfl


set_option linter.unusedSectionVars false in
theorem crossCorrParallelContraction_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0)) (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + 0)) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) 0 0
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x) v := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (crossCorrField (I := I) g₀ S T x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
    (Tensor0SSpace.ofModel
      (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) 0 0
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x))) v = _
  rw [Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
theorem crossCorrParallelContraction_eq_crossCorrectionSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₁)
        (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
          (loweredConnDiffSection (I := I) g₁ g₀))
      = crossCorrectionSection (I := I) g₁ g₀ T₁ := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 3)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hvtuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  have hRHS : Tensor0SSpace.toModel
      ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      ccTensorBilinSymm (I := I) g₀ T₁ x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) (v 2) := by
    rw [hvtuple]
    exact crossCorrectionSection_toModel_apply (I := I) g₁ g₀ T₁ x (v 0) (v 1) (v 2)
  have hLHS : Tensor0SSpace.toModel
      ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
            (loweredConnDiffSection (I := I) g₁ g₀))).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      ccTensorBilinSymm (I := I) g₀ T₁ x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) (v 2) := by
    rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x)
        = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl]
    rw [crossCorrParallelContraction_toModel_apply (I := I) g₀
      (realizeSymmCcTensor (I := I) g₀ T₁)
      (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (loweredConnDiffSection (I := I) g₁ g₀)) x v]
    rw [hvtuple]
    rw [crossCorrModelFun_eval00 (E := E) (cometricReadingModel (I := I) g₀ x)
      (ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x)
      (ccUnitModel (I := I) g₀ (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
        (loweredConnDiffSection (I := I) g₁ g₀)) x) (v 0) (v 1) (v 2)]
    have hA : ∀ i : Fin (Module.finrank ℝ E),
        ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
          ![cometricReadingModel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis i)), v 2]
          = ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis i))) (v 2) := by
      intro i
      rw [← realizeSymmCcTensor_ccTensorBilin_apply, ccTensorBilin_apply]; rfl
    have hB : ∀ i : Fin (Module.finrank ℝ E),
        ccUnitModel (I := I) g₀ (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
            (loweredConnDiffSection (I := I) g₁ g₀)) x
          ![(Module.finBasis ℝ E) i, v 0, v 1]
          = g₀.inner x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) ((Module.finBasis ℝ E) i) := by
      intro i
      change DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (loweredConnDiffSection (I := I) g₁ g₀)) x
          ![(Module.finBasis ℝ E) i, v 0, v 1] = _
      rw [permuteCcTensor_unitModel (I := I) g₀ c[(0 : Fin 3), 1, 2]
        (loweredConnDiffSection (I := I) g₁ g₀) x]
      rw [show (ContinuousMultilinearMap.domDomCongr c[(0 : Fin 3), 1, 2]
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
              (loweredConnDiffSection (I := I) g₁ g₀) x)) ![(Module.finBasis ℝ E) i, v 0, v 1]
          = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
              (loweredConnDiffSection (I := I) g₁ g₀) x ![v 0, v 1, (Module.finBasis ℝ E) i] from by
        rw [ContinuousMultilinearMap.domDomCongr_apply]; congr 1; funext j; fin_cases j <;> rfl]
      change Tensor0SSpace.toModel
        ((loweredConnDiffSection (I := I) g₁ g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            ![v 0, v 1, (Module.finBasis ℝ E) i] = _
      rw [loweredConnDiffSection_toModel_apply (I := I) g₁ g₀ x (v 0) (v 1) ((Module.finBasis ℝ E) i)]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hA i, hB i])]
    have hflip : ∀ w : TangentSpace I x,
        ccTensorBilinSymm (I := I) g₀ T₁ x w (v 2)
          = (ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 2) w := fun w => rfl
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          g₀.inner x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) ((Module.finBasis ℝ E) i)
            * ccTensorBilinSymm (I := I) g₀ T₁ x
                (cometricReadingModel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis i))) (v 2))
        = ∑ i : Fin (Module.finrank ℝ E),
            ((ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 2))
                (cometricReadingModel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis i)))
              * g₀.inner x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) ((Module.finBasis ℝ E) i) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [hflip]; ring]
    rw [sum_phi_cometric_inner_basis (I := I) g₀ x
      (fun i => cometricReadingModel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)))
      (fun k u => cometricReadingModel_dualBasis_inner (I := I) g₀ x k u)
      ((ccTensorBilinSymm (I := I) g₀ T₁ x).flip (v 2))
      (connDiff (I := I) g₁ g₀ x (v 1) (v 0))]
    rfl
  rw [hLHS, hRHS]

end Connection
end Integral
end DifferentialGeometry

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- **Scaling of the intrinsic squared fibre norm.**  `rfns g r s x (c • T) = c² · rfns g r s x T`,
from the bilinear `tensorInnerPointwise` form of `rfns` (`riemannianFiberNormSq_eq_tensorInnerPointwise`)
and its scalar-linearity in each slot. -/
private lemma rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • T) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise, riemannianFiberNormSq_eq_tensorInnerPointwise,
    TensorRSSpace.toModel_smul, Integral.L2.tensorInnerPointwise_smul_left,
    Integral.L2.tensorInnerPointwise_smul_right]
  ring

/-- **(POSIT — the cross-correction order-`p` covariant jet top/rest split, δ-separated.)**  The
genuine *contraction-algebra* content underlying the cross-correction's order-`p` covariant jet: the
section-level value `(∇^p crossCorrectionSection) x` splits, fibrewise at every base point `x`, into a
**top** fibre tensor `Top` and a **rest** fibre tensor `Rest` (the order-`0` term and the strictly
lower-order terms of the binomial covariant Leibniz expansion of the metric/evaluation contraction
`h ⌟ D`, `h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`), with:

* the **top** term `Top = ∇^0 h ⌟ ∇^p D` controlled by the fibre-smallness in *squared* form
  `rfns(Top)(x) ≤ δ² · rfns(∇^p loweredConnDiffSection)(x)` — the `g₀`-fibre operator norm of `h` is
  `≤ δ` (`gFibreOpBound … δ`), and the `g₀`-lowering of the connection difference is a parallel fibre
  isometry (`∇₀ g₀ = 0`), so `‖h ⌟ ∇^p D‖²_{g₀} ≤ δ² · ‖∇^p D‖²_{g₀} = δ² · rfns(∇^p lowered)`; and

* the **rest** term `Rest = ∑_{i ≥ 1, i + q = p} C(p, i) ∇^i h ⌟ ∇^q D` controlled, uniformly over the
  fibre-small `H^{p+3}` ball, by `rfns(Rest)(x) ≤ Crest · (∑_{q < p} rfns(∇^q loweredConnDiffSection)(x)
  + ∑_{l ≤ p+1} rfns(∇^l T₁)(x))` — each lower factor `∇^i h` (`i ≥ 1`) is the jet of the fibrewise
  *linear* realized perturbation `h`, whose `g₀`-fibre operator norm is bounded pointwise and uniformly
  on the compact `M` by the `H^{p+3}` Sobolev ball through the supercritical Sobolev embedding
  `H^{p+3} ↪ C^{p+1}`, leaving the surviving connection-difference jet factor `rfns(∇^q lowered)` (`q <
  p`); the `∑_{l ≤ p+1} rfns(∇^l T₁)` carrier is the perturbation-jet slack absorbing the boundary terms.

This is the genuine **shared bottom** of the cross-correction tower: the δ-separated contraction
Leibniz, carrying the lower covariant gradients of the connection difference *as themselves* on the
right.  It contains no fibre-small `g₁^{-1}` recursion and no strong induction over the order; the full
cross-correction bound `crossCorrectionSection_iteratedCovGrad_rfns_le` folds these lower
`loweredConnDiffSection` jets into the `T₁`-jets by its own route-(a) strong induction.

* **j = 0 collapse litmus.**  At `p = 0` the lower-order Leibniz terms are empty, so `Rest = 0` and the
  split is `(crossCorrectionSection) x = Top` with `rfns(Top)(x) ≤ δ² · rfns(loweredConnDiffSection)(x)`.
* **self-zero litmus.**  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so `crossCorrectionSection = 0` and
  both `Top` and `Rest` vanish (`0 ≤ 0`). -/
theorem crossCorrectionSection_iteratedCovGrad_topRest_split
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ) :
    ∃ Crest : ℝ, 0 ≤ Crest ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3) T₁‖ ≤ B →
        ∀ x : M,
          ∃ Top Rest : Tensor0SBundle.TensorRSSpace 0 (3 + p) I x,
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x = Top + Rest ∧
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x Top ≤
              δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ∧
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x Rest ≤
              Crest * (∑ q ∈ Finset.range p,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
                + ∑ l ∈ Finset.range (p + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) := by
  sorry

/-- **The cross-correction covariant-Leibniz contraction grid, δ-separated.**  The order-`p` covariant
jet of the cross-correction `h ⌟ D` (`h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`) is dominated,
uniformly over the fibre-small `H^{p+3}` ball, by the **δ-separated** grid: the principal term
`δ · rfns(∇^p loweredConnDiffSection)` (the order-`0` contraction absorbed by the fibre-smallness) plus
a constant times the lower covariant gradients of the connection difference `∑_{q < p}
rfns(∇^q loweredConnDiffSection)` and the `≤ (p+1)`-jet of `T₁`.

Proved by the section-level top/rest split `crossCorrectionSection_iteratedCovGrad_topRest_split`
(the genuine contraction-algebra bottom): the `2`-sub-additivity of the squared fibre norm
(`riemannianFiberNormSq_add_le`, factor `2`) over the split `(∇^p crossCorrectionSection) x = Top + Rest`
turns the top bound `rfns(Top) ≤ δ² · rfns(∇^p lowered)` into `2 δ² · rfns(∇^p lowered)`, and the
hypothesis `δ < 1/2` collapses `2 δ² ≤ δ` (`δ(2δ − 1) ≤ 0`), recovering the exact principal coefficient
`δ`; the rest bound `rfns(Rest) ≤ Crest · (…)` contributes the lower-order grid with constant `2 Crest`.

This is the **strictly-smaller** brick of `crossCorrectionSection_iteratedCovGrad_rfns_le`: it is the
*non-inductive* contraction-Leibniz grid (no fibre-small `g₁^{-1}` recursion, no strong induction over
the order), carrying the lower covariant gradients of the connection difference *as themselves* on the
right.  The full cross-correction bound then folds these lower `loweredConnDiffSection` jets into the
`T₁`-jets by the route-(a) strong induction (`crossCorrectionSection_iteratedCovGrad_rfns_le`), which is
*not* part of this brick.

* **j = 0 collapse litmus.**  At `p = 0` the lower-`loweredConnDiff` sum is empty, so this is
  `rfns(crossCorrectionSection)(x) ≤ δ·rfns(loweredConnDiffSection)(x) + Cgrid·∑_{l ≤ 1} rfns(∇^l T₁)(x)`.
* **self-zero litmus.**  At `T₁ = 0`, `crossCorrectionSection = 0` and the bound is `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_grid_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3) T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) ≤
            δ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
            + Cgrid * (∑ q ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                      (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) := by
  classical
  obtain ⟨Crest, hCrest0, hsplit⟩ :=
    crossCorrectionSection_iteratedCovGrad_topRest_split (I := I) g₀ p δ hδ0 hδ1 B
  refine ⟨2 * Crest, by positivity, ?_⟩
  intro T₁ g₁ hr hfib hball x
  obtain ⟨Top, Rest, heq, hTop, hRest⟩ := hsplit T₁ g₁ hr hfib hball x
  -- Abbreviate the principal jet term `L` and the lower-order grid `G`.
  set L := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) with hLdef
  set G := (∑ q ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
      + ∑ l ∈ Finset.range (p + 1 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) with hGdef
  have hLnn : 0 ≤ L := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    exact add_nonneg (Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
      (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
  -- `2`-sub-additivity over the split, then `2 δ² ≤ δ` (from `δ < 1/2`).
  rw [heq]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + p) x Top Rest
  -- `set L` / `set G` have already folded `hTop` to `≤ δ² * L` and `hRest` to `≤ Crest * G`.
  -- `2 δ² · L ≤ δ · L`: `(δ − 2 δ²) · L ≥ 0` since `0 ≤ δ`, `2 δ ≤ 1`, and `0 ≤ L`.
  have hδcoeff : 0 ≤ δ - 2 * δ ^ 2 := by nlinarith [hδ0, hδ1]
  have hδsq : 2 * δ ^ 2 * L ≤ δ * L := by nlinarith [mul_nonneg hδcoeff hLnn]
  have hTop2 : 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x Top ≤ 2 * δ ^ 2 * L := by
    have := mul_le_mul_of_nonneg_left hTop (by norm_num : (0 : ℝ) ≤ 2)
    linarith [this]
  have hRest2 : 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x Rest ≤ 2 * Crest * G := by
    have := mul_le_mul_of_nonneg_left hRest (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [this]
  linarith [hadd, hTop2, hRest2, hδsq]

/-- **(POSIT — the fibre-small-gated cross-correction jet brick.)**  On the fibre-small ball
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ` with `δ < 1/2`) and the Sobolev `H^{p+3}` ball
(`‖T₁.toHs (p+3)‖ ≤ B`), the intrinsic squared fibre norm of the order-`p` covariant gradient of the
cross-correction section `crossCorrectionSection` (the Koszul correction `h ⌟ D`) is dominated by the
**fibre-small-absorbed** principal term `δ · rfns(∇^p loweredConnDiffSection)` plus a perturbation
`≤ (p+1)`-jet term with a constant uniform over the ball.

This is the **binomial covariant-Leibniz grid** of the contraction `h ⌟ D` (the
`ParallelTensorProduct` engine `norm_iteratedCovGrad_prod_le_jetGrid` for the metric/evaluation
contraction of `h = ccTensorBilinSymm g₀ T₁` against the connection difference `D = connDiff g₁ g₀`),
with: the **top term** (`∇^0 h ⌟ ∇^p D`) absorbed via the fibre-smallness `gFibreOpBound … δ` (the
`g₀`-operator norm of `h` is `≤ δ`, so this term is `≤ δ·rfns(∇^p loweredConnDiffSection)` through the
`g₀`-lowering parallel isometry `∇₀ g₀ = 0`); and all **lower terms** (`∇^i h ⌟ ∇^q D`, `q < p`)
folded into the `≤ (p+1)`-jet of `T₁` using the `H^{p+3}` Sobolev ball (bounding the lower-order jet
factors by a ball-uniform constant) and the inductive control of the lower covariant gradients of the
connection difference.  It is strictly smaller than `T1` (it bounds the **cross correction**, carrying
the `δ·loweredConnDiffSection` recursion term) and is **not** `T1` restated.

* **j = 0 collapse litmus.**  At `p = 0` this is
  `rfns(crossCorrectionSection)(x) ≤ δ·rfns(loweredConnDiffSection)(x) + Ccross·∑_{l ≤ 1} rfns(∇^l T₁)(x)`,
  i.e. the correction `h(D, ·)`'s fibre value is bounded by `δ·` the connection difference plus the
  `≤ 1`-jet of `T₁` — exactly the perturbation·connection-difference correction term
  `2·|ccTensorBilinSymm g₀ T₁ x (connDiff …) c|` of `connDiffField_g0_fibre_abs_bound`.
* **self-zero litmus.**  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so `crossCorrectionSection = 0`
  and the bound is `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3) T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) ≤
            δ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
            + Ccross * ∑ l ∈ Finset.range (p + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) := by
  classical
  -- **Strong induction on `p`** establishing the per-order lowered-jet bound
  -- `rfns(∇^q lowered) ≤ Clow q · S` for all `q ≤ p` (the route-(a) differentiated-Koszul recursion,
  -- folding the cross-correction grid's lower covariant gradients of the connection difference into
  -- the perturbation jets), then reading off the cross-correction bound from the grid brick.
  -- The auxiliary lowered-jet bound, with the order-`p` Sobolev ball uniform over `q ≤ p`.
  suffices haux : ∀ q : ℕ, ∃ Clow : ℝ, 0 ≤ Clow ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (q + 3) T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤
            Clow * ∑ l ∈ Finset.range (q + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) by
    -- Read off `crossCorrectionSection_iteratedCovGrad_rfns_le` from the grid brick + the lower-order
    -- lowered-jet bounds folded into the perturbation jets.
    obtain ⟨Cgrid, hCgrid0, hCgrid⟩ :=
      crossCorrectionSection_iteratedCovGrad_grid_le (I := I) g₀ p δ hδ0 hδ1 B
    -- Collect the per-order lowered constants for `q < p`.
    choose Clow hClow0 hClow using haux
    have hClowsum_nn : 0 ≤ ∑ q ∈ Finset.range p, Clow q :=
      Finset.sum_nonneg fun q _ => hClow0 q
    refine ⟨Cgrid + Cgrid * ∑ q ∈ Finset.range p, Clow q, by positivity, ?_⟩
    intro T₁ g₁ hr hfib hball x
    set S := ∑ l ∈ Finset.range (p + 1 + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    have hgrid := hCgrid T₁ g₁ hr hfib hball x
    -- Each lower lowered-jet `rfns(∇^q lowered)` (q < p) ≤ Clow q · (its own jet sum) ≤ Clow q · S.
    have hlow_le : ∀ q ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ Clow q * S := by
      intro q hq
      have hqp : q ≤ p := Nat.le_of_lt (Finset.mem_range.mp hq)
      -- The order-`q` Sobolev ball follows from the order-`p` one by Sobolev-norm monotonicity.
      have hball_q : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (q + 3) T₁‖
          ≤ B := le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : q + 3 ≤ p + 3) T₁) hball
      have h := hClow q T₁ g₁ hr hfib hball_q x
      refine le_trans h ?_
      -- the order-`q` jet sum `∑_{l ≤ q+1}` is ≤ the order-`p` sum `S = ∑_{l ≤ p+1}` (nonneg terms).
      have hsub : (∑ l ∈ Finset.range (q + 1 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ≤ S := by
        rw [hSdef]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega : q + 1 + 1 ≤ p + 1 + 1))
          fun l _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _
      exact mul_le_mul_of_nonneg_left hsub (hClow0 q)
    -- Sum the lower bounds and substitute into the grid brick.
    have hsum_low : (∑ q ∈ Finset.range p,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ q ∈ Finset.range p, Clow q) * S := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hlow_le
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x)
          ≤ δ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
            + Cgrid * (∑ q ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                      (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) + S) := hgrid
      _ ≤ δ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
            + (Cgrid + Cgrid * ∑ q ∈ Finset.range p, Clow q) * S := by
        have := hsum_low
        nlinarith [this, hSnn, hCgrid0,
          Finset.sum_nonneg (fun q (_ : q ∈ Finset.range p) => hClow0 q)]
  -- **The strong induction proving `haux`.**
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_rfns_le (I := I) g₀ q
    obtain ⟨Cg, hCg0, hCg⟩ := crossCorrectionSection_iteratedCovGrad_grid_le (I := I) g₀ q δ hδ0 hδ1 B
    -- Collect the IH constants for the strictly-lower orders `i < q`.
    have hih : ∀ i ∈ Finset.range q, ∃ Ci : ℝ, 0 ≤ Ci ∧
        ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (i + 3) T₁‖ ≤ B →
          ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                    (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤
              Ci * ∑ l ∈ Finset.range (i + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) :=
      fun i hi => ih i (Finset.mem_range.mp hi)
    choose! Ci hCi0 hCi using hih
    have hden : 0 < 4 - 8 * δ := by linarith
    refine ⟨(2 * Ck + 8 * Cg + 8 * Cg * ∑ i ∈ Finset.range q, Ci i) / (4 - 8 * δ), ?_, ?_⟩
    · have : 0 ≤ ∑ i ∈ Finset.range q, Ci i :=
        Finset.sum_nonneg fun i hi => hCi0 i hi
      positivity
    intro T₁ g₁ hr hfib hball x
    set S := ∑ l ∈ Finset.range (q + 1 + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    set L := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) with hLdef
    have hLnn : 0 ≤ L := riemannianFiberNormSq_nonneg _ _ _ _ _
    set Kr := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
        (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x) with hKrdef
    set Cr := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
        (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) with hCrdef
    -- The section-level Koszul identity under ∇^q: 2•lowered = koszulComb − 2•cross ⟹ 4L ≤ 2Kr + 8Cr.
    have hsub : (4 : ℝ) * L ≤ 2 * Kr + 8 * Cr := by
      have hid : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀) =
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (koszulCombSection (I := I) g₁ g₀ T₁) -
            PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁) := by
        rw [← PDE.RicciFlow.iteratedCovGrad_sub]
        congr 1
        rw [koszulCombSection]
        abel
      have h4L : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
            (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) = 4 * L := by
        rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          rfns_smul, hLdef]; norm_num
      have h4Cr : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
            (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) = 4 * Cr := by
        rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          rfns_smul, hCrdef]; norm_num
      have hsmulL : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀) =
          (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (loweredConnDiffSection (I := I) g₁ g₀) := iteratedCovGrad_smul _ _ _ _ _ _
      have hsmulC : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁) =
          (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (crossCorrectionSection (I := I) g₁ g₀ T₁) := iteratedCovGrad_smul _ _ _ _ _ _
      have hle := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + q) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
          (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x)
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
          (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x)
      have hidsec : ((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (loweredConnDiffSection (I := I) g₁ g₀)).toSection x =
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x)
            - (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) := by
        rw [← hsmulC, ← hsmulL, hid, Integral.L2.SmoothCcTensor.toSection_sub,
          ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [← h4L, hidsec]
      have : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
          (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) = 4 * Cr := h4Cr
      nlinarith [hle, this]
    -- POSIT 1 and the grid brick at order `q`.
    have hKr_le : Kr ≤ Ck * S := hCk T₁ g₁ hr x
    have hCr_le : Cr ≤ δ * L + Cg * ((∑ i ∈ Finset.range q,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) + S) := hCg T₁ g₁ hr hfib hball x
    -- Fold the lower `loweredConnDiff` jets (i < q) into `S` by the IH.
    have hlow_le : ∀ i ∈ Finset.range q,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ Ci i * S := by
      intro i hi
      have hball_i : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (i + 3) T₁‖
          ≤ B := le_trans (toHs_norm_mono (I := I) (M := M) g₀
            (by have := Finset.mem_range.mp hi; omega : i + 3 ≤ q + 3) T₁) hball
      have h := hCi i hi T₁ g₁ hr hfib hball_i x
      refine le_trans h ?_
      have hsub2 : (∑ l ∈ Finset.range (i + 1 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ≤ S := by
        rw [hSdef]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by have := Finset.mem_range.mp hi; omega : i + 1 + 1 ≤ q + 1 + 1))
          fun l _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _
      exact mul_le_mul_of_nonneg_left hsub2 (hCi0 i hi)
    have hsum_low : (∑ i ∈ Finset.range q,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ i ∈ Finset.range q, Ci i) * S := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum hlow_le
    have hsumCi_nn : 0 ≤ ∑ i ∈ Finset.range q, Ci i :=
      Finset.sum_nonneg fun i hi => hCi0 i hi
    -- Close: (4 - 16δ)·L ≤ (2Ck + 8Cg + 8Cg·∑Ci)·S, divide.
    have hkey : (4 - 8 * δ) * L ≤
        (2 * Ck + 8 * Cg + 8 * Cg * ∑ i ∈ Finset.range q, Ci i) * S := by
      nlinarith [hsub, hKr_le, hCr_le, hsum_low, hSnn, hLnn, hCg0, hCk0, hsumCi_nn,
        mul_le_mul_of_nonneg_left hsum_low hCg0]
    rw [hLdef] at hkey ⊢
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    rw [← hLdef] at hkey ⊢
    nlinarith [hkey]

/-- **T1 — the iterated-covariant-jet bound for the metrically-lowered connection difference**
(fibre-small ball regime).

For a closed Riemannian manifold `(M, g₀)`, an order `p`, a fibre-smallness parameter `δ < 1/2`, and
a Sobolev ball radius `B`, there is a single nonnegative constant `C` such that for every realized
metric `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` whose perturbation `T₁` is fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`) and `H^{p+3}`-bounded (`‖T₁.toHs (p+3)‖ ≤ B`), the
intrinsic squared fibre norm of the order-`p` covariant gradient of the `g₀`-metrically-lowered
connection difference `loweredConnDiffSection g₁ g₀` is dominated by the `≤ (p+1)`-jet of `T₁`:
```
rfns(∇^p (loweredConnDiffSection g₁ g₀))(x) ≤ C · ∑_{l ≤ p+1} rfns(∇^l T₁)(x).
```

The **fibre-small ball gate is required** (verified): the connection difference is a *nonlinear*
function of `T₁` (the Koszul lowering is `g₁`-inner, pulling in `g₁^{-1}`), so the bound fails
uniformly as `g₁` degenerates over the unconstrained realize family — see the file header.

Proved by the **route-(a) differentiated-Koszul algebra** over the section-level Koszul identity
`2·loweredConnDiffSection = koszulCombSection − 2·crossCorrectionSection` (the clean-linear-part
section minus the cross correction, `koszulCombSection`): the squared-fibre-norm subadditivity
`riemannianFiberNormSq_sub_le` over the identity, the **clean-linear-part jet brick**
`koszulCombSection_iteratedCovGrad_rfns_le` (the linear part is `≤ (p+1)`-jet of `T₁`), and the
**fibre-small-gated cross-correction jet brick** `crossCorrectionSection_iteratedCovGrad_rfns_le`
(the cross correction is `δ·` the lowered connection difference plus the `≤ (p+1)`-jet), the latter's
`δ·rfns(∇^p loweredConnDiffSection)` recursion term moved to the left and divided out (`4 − 16δ > 0`
since `δ < 1/2`). -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3) T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤
            C * ∑ l ∈ Finset.range (p + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) := by
  classical
  obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_rfns_le (I := I) g₀ p
  obtain ⟨Cc, hCc0, hCc⟩ :=
    crossCorrectionSection_iteratedCovGrad_rfns_le (I := I) g₀ p δ hδ0 hδ1 B
  refine ⟨(2 * Ck + 8 * Cc) / (4 - 8 * δ), ?_, ?_⟩
  · have hden : 0 < 4 - 8 * δ := by linarith
    positivity
  intro T₁ g₁ hr hfib hball x
  set L := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) with hLdef
  set Kr := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x) with hKrdef
  set Cr := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) with hCrdef
  set S := ∑ l ∈ Finset.range (p + 1 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _
  have hLnn : 0 ≤ L := riemannianFiberNormSq_nonneg _ _ _ _ _
  -- The section-level Koszul identity, under ∇^p: 2•loweredConnDiff = koszulComb - 2•cross.
  have hid : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀) =
      PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p (koszulCombSection (I := I) g₁ g₀ T₁) -
        PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁) := by
    rw [← PDE.RicciFlow.iteratedCovGrad_sub]
    congr 1
    rw [koszulCombSection]
    abel
  -- rfns(∇^p(2•lowered)) = 4·L ; subadditivity over the identity.
  have hsmulL : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀) =
      (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (loweredConnDiffSection (I := I) g₁ g₀) := iteratedCovGrad_smul _ _ _ _ _ _
  have hsmulC : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁) =
      (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (crossCorrectionSection (I := I) g₁ g₀ T₁) := iteratedCovGrad_smul _ _ _ _ _ _
  have h4L : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) = 4 * L := by
    rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rfns_smul]
    rw [hLdef]; norm_num
  have h4Cr : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) = 4 * Cr := by
    rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rfns_smul]
    rw [hCrdef]; norm_num
  have hsub : (4 : ℝ) * L ≤ 2 * Kr + 2 * (4 * Cr) := by
    have hle := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x)
      (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x)
    rw [← h4Cr]
    have hlhs : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) = 4 * L := h4L
    have hidsec : ((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (loweredConnDiffSection (I := I) g₁ g₀)).toSection x =
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x)
          - (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) := by
      rw [← hsmulC, ← hsmulL, hid, Integral.L2.SmoothCcTensor.toSection_sub,
        ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [← hlhs, hidsec]
    exact hle
  -- Apply the two posits.
  have hKr_le : Kr ≤ Ck * S := hCk T₁ g₁ hr x
  have hCr_le : Cr ≤ δ * L + Cc * S := hCc T₁ g₁ hr hfib hball x
  -- Close: (4 - 8δ)·L ≤ (2 Ck + 8 Cc)·S, divide.
  have hden : 0 < 4 - 8 * δ := by linarith
  have hkey : (4 - 8 * δ) * L ≤ (2 * Ck + 8 * Cc) * S := by nlinarith [hKr_le, hCr_le, hsub, hSnn]
  have hfinal : L ≤ (2 * Ck + 8 * Cc) / (4 - 8 * δ) * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [hkey]
  exact hfinal

end DeTurck
end PDE
end DifferentialGeometry

end
