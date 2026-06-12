import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionContractionCalculus
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotExtendCovariantParallelism
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorFibreCauchySchwarz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SharpOrderRealizedJetEmbedding

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
/-- **The fibrewise model value of the single `g₀`-contraction at `(a, b) = (0, p)`.**  For a
`(0, 2)`-factor `Sm` and a `(0, 3 + p)`-factor `Tm`, the contraction's value at a `(3 + p)`-tuple `m`
sums, over the model-basis index `i`, the product of `Tm` read with `eᵢ` in its leading slot then the
first `2 + p` slots of `m`, against `Sm` read with the cometric-raised dual `♯eⁱ = L(eⁱ)` in its leading
slot then the trailing slot `m (last)`.  The `(0, p)` analogue of `crossCorrModelFun_eval00`. -/
theorem crossCorrModelFun_eval0p (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (p : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + 0) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (3 + p) ℝ E)
    (m : Fin (3 + 0 + p) → E) :
    crossCorrModelFun (E := E) L 0 p Sm Tm m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tm (fun k : Fin (3 + p) => (Fin.cons ((Module.finBasis ℝ E) i)
              (fun j : Fin (2 + p) => m ⟨j.val, by omega⟩) : Fin ((2 + p) + 1) → E)
              (finCongr (by omega : 3 + p = (2 + p) + 1) k)) *
          Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)),
            m ⟨2 + p, by omega⟩] := by
  classical
  unfold crossCorrModelFun
  rw [modelRankCastCc_apply', ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  have hT : ((Tensor0SBundle.model_interior_product (2 + p) ((Module.finBasis ℝ E) i))
        ((modelRankCastCc (E := E) (by omega : 3 + p = (2 + p) + 1) Tm)))
        ((fun j => m (finCongr (by omega : (2+p)+(1+0) = 3+0+p) j)) ∘ Fin.castAdd (1 + 0))
      = Tm (fun k : Fin (3 + p) => (Fin.cons ((Module.finBasis ℝ E) i)
          (fun j : Fin (2 + p) => m ⟨j.val, by omega⟩) : Fin ((2 + p) + 1) → E)
          (finCongr (by omega : 3 + p = (2 + p) + 1) k)) := by
    have hLHS : ((Tensor0SBundle.model_interior_product (2 + p) ((Module.finBasis ℝ E) i))
          ((modelRankCastCc (E := E) (by omega : 3 + p = (2 + p) + 1) Tm)))
          ((fun j => m (finCongr (by omega : (2+p)+(1+0) = 3+0+p) j)) ∘ Fin.castAdd (1 + 0))
        = (modelRankCastCc (E := E) (by omega : 3 + p = (2 + p) + 1) Tm)
            (Fin.cons ((Module.finBasis ℝ E) i)
              ((fun j => m (finCongr (by omega : (2+p)+(1+0) = 3+0+p) j)) ∘ Fin.castAdd (1 + 0))) := rfl
    rw [hLHS, modelRankCastCc_apply']
    have hRHS : Tm (fun k : Fin (3 + p) => (Fin.cons ((Module.finBasis ℝ E) i)
            (fun j : Fin (2 + p) => m ⟨j.val, by omega⟩) : Fin ((2 + p) + 1) → E)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k))
        = (modelRankCastCc (E := E) (by omega : 3 + p = (2 + p) + 1) Tm)
            (Fin.cons ((Module.finBasis ℝ E) i)
              (fun j : Fin (2 + p) => m ⟨j.val, by omega⟩)) := by
      rw [modelRankCastCc_apply']
    rw [hRHS, modelRankCastCc_apply']
    apply congrArg
    funext k
    refine Fin.cases ?_ (fun k' => ?_) (finCongr (by omega : 3 + p = (2 + p) + 1) k)
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ, Function.comp_apply]
      congr 1
  have hS : ((Tensor0SBundle.model_interior_product (1 + 0)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))))
        ((modelRankCastCc (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)))
        ((fun j => m (finCongr (by omega : (2+p)+(1+0) = 3+0+p) j)) ∘ Fin.natAdd (2 + p))
      = Sm ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i)),
          m ⟨2 + p, by omega⟩] := by
    change (modelRankCastCc (E := E) (by omega : 2 + 0 = (1 + 0) + 1) Sm)
        (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis i))) _) = _
    rw [modelRankCastCc_apply']
    congr 1
    funext j
    fin_cases j
    · rfl
    · rfl
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

/-- **The sharp `g₀`-operator dual-frame squared sum.**  For a `g₀`-orthonormal tangent frame `e` at `x`
(with `g₀(e_i, e_j) = δ_{ij}` and Parseval `∑_i g₀(e_i, v)² = g₀(v, v)`), a symmetric bilinear fibre
form `h` with the `g₀`-fibre operator bound `gFibreOpBound g₀ h δ`, and any tangent vector `u`, the
dual-frame squared sum of the covector `h x u` is bounded *sharply* by `δ² · g₀(u, u)`:
`∑_k (h x u (e k))² ≤ δ² · g₀(u, u)`.  This is the operator-norm (not Hilbert–Schmidt) control: the
covector `h x u` is reconstructed as `P = ∑_k h x u (e k) • e k`, whose squared `g₀`-norm equals the
squared sum (frame Parseval), and `‖P‖²_{g₀} = h x u P ≤ δ · √(g₀ u u) · √(‖P‖²_{g₀})`, giving the
sharp `δ²` after dividing out `√(‖P‖²_{g₀})`. -/
private lemma gFibreOpBound_dualFrame_sq_sum_le
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ h δ) (u : TangentSpace I x) :
    ∑ k : Fin n, (h x u (e k)) ^ 2 ≤ δ ^ 2 * g₀.inner x u u := by
  classical
  set Q : ℝ := ∑ k : Fin n, (h x u (e k)) ^ 2 with hQ_def
  -- The frame-reconstructed vector of the covector `h x u`.
  set P : TangentSpace I x := ∑ k : Fin n, (h x u (e k)) • e k with hP_def
  -- `h x u P = Q`: applying `h x u` to `P` reconstructs the squared sum.
  have hhuP : h x u P = Q := by
    rw [hP_def, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [hQ_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [sq]
  -- The frame coordinates of `P` are the values `h x u (e k)`: `g₀(e_k, P) = h x u (e k)`.
  have hcoord : ∀ k : Fin n, g₀.inner x (e k) P = h x u (e k) := by
    intro k
    rw [hP_def, map_sum]
    rw [Finset.sum_eq_single k]
    · rw [ContinuousLinearMap.map_smul, smul_eq_mul, horth k k, if_pos rfl, mul_one]
    · intro l _ hl
      rw [ContinuousLinearMap.map_smul, smul_eq_mul, horth k l, if_neg (fun he => hl he.symm),
        mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  -- `g₀(P, P) = Q`: Parseval in the frame, with the coordinates `g₀(e_k, P) = h x u (e k)`.
  have hPP : g₀.inner x P P = Q := by
    rw [← hpars P, hQ_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoord k]
  -- `Q = h x u P ≤ δ · √(g₀ u u) · √(g₀ P P) = δ · √(g₀ u u) · √Q`.
  have hQnn : 0 ≤ Q := by
    rw [hQ_def]; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have huu_nn : 0 ≤ g₀.inner x u u :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  have hbound : Q ≤ δ * Real.sqrt (g₀.inner x u u) * Real.sqrt Q := by
    have hb := hδ x u P
    rw [hhuP, hPP] at hb
    calc Q = |Q| := (abs_of_nonneg hQnn).symm
      _ ≤ δ * Real.sqrt (g₀.inner x u u) * Real.sqrt Q := hb
  -- Divide out `√Q`: either `Q = 0` (done) or `√Q ≤ δ √(g₀ u u)`, squaring gives the result.
  rcases eq_or_lt_of_le hQnn with hQ0 | hQpos
  · rw [← hQ0]; positivity
  · have hsqQ_pos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
    have hQ_sqrt : Q = Real.sqrt Q * Real.sqrt Q := (Real.mul_self_sqrt hQnn).symm
    have hstep : Real.sqrt Q ≤ δ * Real.sqrt (g₀.inner x u u) := by
      have hb2 : Real.sqrt Q * Real.sqrt Q ≤ (δ * Real.sqrt (g₀.inner x u u)) * Real.sqrt Q := by
        rw [← hQ_sqrt]; linarith [hbound]
      exact le_of_mul_le_mul_right hb2 hsqQ_pos
    have hsqrtuu : Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x u u) = g₀.inner x u u :=
      Real.mul_self_sqrt huu_nn
    have hstep_nn : 0 ≤ δ * Real.sqrt (g₀.inner x u u) :=
      le_trans (Real.sqrt_nonneg Q) hstep
    calc Q = Real.sqrt Q * Real.sqrt Q := hQ_sqrt
      _ ≤ (δ * Real.sqrt (g₀.inner x u u)) * (δ * Real.sqrt (g₀.inner x u u)) :=
          mul_le_mul hstep hstep (Real.sqrt_nonneg _) hstep_nn
      _ = δ ^ 2 * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x u u)) := by ring
      _ = δ ^ 2 * g₀.inner x u u := by rw [hsqrtuu]

/-- **The rank-`0` frame component reads a `(0, s)` operator at the canonical unit.**  For the empty
multi-index `K₀`, `fiberNormSqComponent g₀ x 0 s op n e K₀ J = toModel(op unit) (fun k => e (J k))`
(the rank-`0` cometric weight `coframeS` is the canonical unit `(0, 0)`-tensor). -/
private theorem componentS_zero_eq_unit_local (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n)
    (op : Tensor0SBundle.TensorRSSpace 0 s I x) :
    Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 s op n e K₀ J =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from op)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun k => e (J k)) := by
  classical
  have hcoframe :
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g₀.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
    apply Tensor0SBundle.tensor0SSpace_ext
    intro v
    rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g₀.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        Integral.Connection.coframeS (I := I) (M := M) g₀ x 0 e K₀ from rfl,
      Integral.Connection.coframeS_apply, Finset.prod_of_isEmpty]
    rfl
  unfold Integral.Connection.fiberNormSqComponent
  rw [hcoframe]
  rw [Tensor0SBundle.Tensor0SSpace.toModel, Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  rfl

/-- **The sharp `δ²` order-`0` fibre bound of the cross-correction section.**  Under the `g₀`-fibre
operator bound `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, the intrinsic squared fibre norm of
the cross-correction section `crossCorrectionSection g₁ g₀ T₁` is dominated *sharply* — with the
operator-norm constant `δ²`, no dimension factor — by that of the `g₀`-lowered connection difference:
`rfns(crossCorrectionSection g₁ g₀ T₁)(x) ≤ δ² · rfns(loweredConnDiffSection g₁ g₀)(x)`.

Proved by Parseval in a `g₀`-orthonormal frame: the cross-correction's frame component at `(j₀, j₁, j₂)`
is `h(connDiff (e_{j₁}) (e_{j₀}), e_{j₂})` (`crossCorrectionSection_toModel_apply`), grouped over the
trailing slot `j₂` it is the dual-frame squared sum `∑_{j₂} h(u, e_{j₂})²` (`u := connDiff (e_{j₁})
(e_{j₀})`), bounded sharply by `δ² · g₀(u, u)` (`gFibreOpBound_dualFrame_sq_sum_le`); and `g₀(u, u) =
∑_{j₂} g₀(u, e_{j₂})²` (Parseval) is exactly the `(j₀, j₁)`-slice squared sum of the lowered
connection difference's frame components (`loweredConnDiffSection_toModel_apply`). -/
theorem crossCorrectionSection_rfns_le_sq_loweredConnDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) ≤
      δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ 3 x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- Frame expansion of both sides at rank `3`, with the components read at the canonical unit.
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 3 e
      hreprS ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) K₀,
    Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 3 e
      hreprS ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) K₀]
  -- The cross-correction and lowered frame components at a tuple `J`.
  have hcrossC : ∀ J : Fin 3 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
          ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x
          (connDiff (I := I) g₁ g₀ x (e (J 1)) (e (J 0))) (e (J 2)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ 3 x e K₀ J
      ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x)]
    rw [show (fun k => e (J k)) = ![e (J 0), e (J 1), e (J 2)] from by
      funext k; fin_cases k <;> rfl]
    exact crossCorrectionSection_toModel_apply (I := I) g₁ g₀ T₁ x (e (J 0)) (e (J 1)) (e (J 2))
  have hlowC : ∀ J : Fin 3 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
          ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) n e K₀ J =
        g₀.inner x (connDiff (I := I) g₁ g₀ x (e (J 1)) (e (J 0))) (e (J 2)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ 3 x e K₀ J
      ((loweredConnDiffSection (I := I) g₁ g₀).toSection x)]
    rw [show (fun k => e (J k)) = ![e (J 0), e (J 1), e (J 2)] from by
      funext k; fin_cases k <;> rfl]
    exact loweredConnDiffSection_toModel_apply (I := I) g₁ g₀ x (e (J 0)) (e (J 1)) (e (J 2))
  simp only [hcrossC, hlowC]
  -- Split off the LAST slot (slot 2, `c`) of the `Fin 3 → Fin n` sum via `Fin.snocEquiv`,
  -- leaving slots `0, 1` as a `Fin 2 → Fin n` index `J01`.
  have hsnoc1 : ∀ pr : Fin n × (Fin 2 → Fin n),
      (Fin.snoc pr.2 pr.1 : Fin 3 → Fin n) (1 : Fin 3) = pr.2 1 := by
    intro pr
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc from by apply Fin.ext; rfl, Fin.snoc_castSucc]
  have hsnoc0 : ∀ pr : Fin n × (Fin 2 → Fin n),
      (Fin.snoc pr.2 pr.1 : Fin 3 → Fin n) (0 : Fin 3) = pr.2 0 := by
    intro pr
    rw [show (0 : Fin 3) = (0 : Fin 2).castSucc from by apply Fin.ext; rfl, Fin.snoc_castSucc]
  have hsnoc2 : ∀ pr : Fin n × (Fin 2 → Fin n),
      (Fin.snoc pr.2 pr.1 : Fin 3 → Fin n) (2 : Fin 3) = pr.1 := by
    intro pr
    rw [show (2 : Fin 3) = Fin.last 2 from by apply Fin.ext; rfl, Fin.snoc_last]
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin 3 => Fin n))
        (fun pr : Fin n × (Fin 2 → Fin n) =>
          ccTensorBilinSymm (I := I) g₀ T₁ x
            (connDiff (I := I) g₁ g₀ x (e (pr.2 1)) (e (pr.2 0))) (e pr.1) ^ 2)
        (fun J : Fin 3 → Fin n =>
          ccTensorBilinSymm (I := I) g₀ T₁ x
            (connDiff (I := I) g₁ g₀ x (e (J 1)) (e (J 0))) (e (J 2)) ^ 2)
        (fun pr => by
          simp only [Fin.snocEquiv_apply]
          rw [hsnoc1 pr, hsnoc0 pr, hsnoc2 pr])]
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin 3 => Fin n))
        (fun pr : Fin n × (Fin 2 → Fin n) =>
          g₀.inner x (connDiff (I := I) g₁ g₀ x (e (pr.2 1)) (e (pr.2 0))) (e pr.1) ^ 2)
        (fun J : Fin 3 → Fin n =>
          g₀.inner x (connDiff (I := I) g₁ g₀ x (e (J 1)) (e (J 0))) (e (J 2)) ^ 2)
        (fun pr => by
          simp only [Fin.snocEquiv_apply]
          rw [hsnoc1 pr, hsnoc0 pr, hsnoc2 pr])]
  -- Group by `J01` (slots `0, 1`); the inner sum over `c` is the dual-frame squared sum.
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum (fun J01 _ => ?_)
  set u : TangentSpace I x := connDiff (I := I) g₁ g₀ x (e (J01 1)) (e (J01 0)) with hu_def
  -- The cross inner sum is `∑_c h(u, e c)²`; the lowered inner sum is `∑_c g₀(u, e c)² = g₀(u, u)`.
  have hcross_inner :
      (∑ c : Fin n, ccTensorBilinSymm (I := I) g₀ T₁ x u (e c) ^ 2) ≤
        δ ^ 2 * g₀.inner x u u :=
    gFibreOpBound_dualFrame_sq_sum_le (I := I) g₀ x e horth hpars
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hδ u
  have hlow_inner : (∑ c : Fin n, g₀.inner x u (e c) ^ 2) = g₀.inner x u u := by
    have := hpars u
    rw [← this]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [g₀.symm x u (e c)]
  rw [hlow_inner]
  exact hcross_inner

set_option linter.unusedSectionVars false in
/-- **The unit fibre value of the `(a, b) = (0, p)` cross-correction contraction**, read to the model:
`toModel((crossCorrParallelContraction g₀ (b:=p) S T) unit) = crossCorrModelFun (cometric) 0 p
(ccUnitModel S) (ccUnitModel T)`.  The general-`b` analogue of `crossCorrParallelContraction_toModel_apply`,
through the same `crossCorrField` packaging chain. -/
theorem crossCorrParallelContraction_toModel_apply0p (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0)) (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + p)) (x : M)
    (v : Fin (3 + 0 + p) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p) S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) 0 p
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x) v := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (crossCorrField (I := I) g₀ (a := 0) (b := p) S T x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
    (Tensor0SSpace.ofModel
      (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) 0 p
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x))) v = _
  rw [Tensor0SSpace.toModel_ofModel]

/-- **Last-slot grouping of a `Fin (3 + 0 + p)` index sum.**  A sum of `f` over all index tuples
`J : Fin (3 + 0 + p) → Fin n` regroups as a double sum over the last-slot value `c : Fin n` and the
leading `Fin (2 + p)`-slice `J'`, with the reconstituted tuple inserting `c` at the last slot
(`Fin.snoc` after the rank cast `3 + 0 + p = (2 + p) + 1`).  This is the symbolic-rank replacement for
the concrete-`Fin 3` `Fin.snocEquiv` regrouping (where `(2 + p) + 1` is not defeq `3 + 0 + p`). -/
private lemma sum_index_lastSlot_group {n p : ℕ} (f : (Fin (3 + 0 + p) → Fin n) → ℝ) :
    (∑ J : Fin (3 + 0 + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        f (fun k : Fin (3 + 0 + p) =>
          (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.snocEquiv (fun _ : Fin ((2 + p) + 1) => Fin n)).trans
      (Equiv.arrowCongr (finCongr (by omega : (2 + p) + 1 = 3 + 0 + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp, id_eq, Fin.snocEquiv_apply, finCongr_symm, finCongr_apply]
  congr 1

/-- **Leading-slot grouping of a `Fin (3 + p)` index sum.**  A sum of `f` over all index tuples
`J : Fin (3 + p) → Fin n` regroups as a double sum over the leading-slot value `c : Fin n` and the
trailing `Fin (2 + p)`-slice `J'`, with the reconstituted tuple inserting `c` at the leading slot
(`Fin.cons` after the rank cast `3 + p = (2 + p) + 1`). -/
private lemma sum_index_leadSlot_group {n p : ℕ} (f : (Fin (3 + p) → Fin n) → ℝ) :
    (∑ J : Fin (3 + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        f (fun k : Fin (3 + p) =>
          (Fin.cons c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.consEquiv (fun _ : Fin ((2 + p) + 1) => Fin n)).trans
      (Equiv.arrowCongr (finCongr (by omega : (2 + p) + 1 = 3 + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp, id_eq, Fin.consEquiv_apply, finCongr_symm, finCongr_apply]
  congr 1

/-- **Frame-Riesz reconstruction of a tangent functional.**  For a `g₀`-orthonormal tangent frame `e`
at `x` (with `g₀(e_i, e_j) = δ_{ij}` and the frame expansion `u = ∑_i g₀(e_i, u) • e_i`) and any
continuous tangent functional `ψ`, the frame-reconstructed vector `W = ∑_c ψ(e c) • e c` represents
`ψ` through the metric pairing — `g₀(W, u) = ψ u` for all `u` — and its squared `g₀`-norm is the
squared sum of the frame values, `g₀(W, W) = ∑_c (ψ (e c))²`. -/
private lemma frameRiesz_pair_and_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hexpand : ∀ v : TangentSpace I x, v = ∑ i : Fin n, g₀.inner x (e i) v • e i)
    (ψ : TangentSpace I x →L[ℝ] ℝ) :
    (∀ u : TangentSpace I x,
        g₀.inner x (∑ c : Fin n, ψ (e c) • e c) u = ψ u) ∧
      g₀.inner x (∑ c : Fin n, ψ (e c) • e c) (∑ c : Fin n, ψ (e c) • e c)
        = ∑ c : Fin n, (ψ (e c)) ^ 2 := by
  classical
  set W : TangentSpace I x := ∑ c : Fin n, ψ (e c) • e c with hW_def
  have hpair : ∀ u : TangentSpace I x, g₀.inner x W u = ψ u := by
    intro u
    rw [hW_def]
    rw [map_sum (g₀.inner x) (fun c : Fin n => ψ (e c) • e c) Finset.univ,
      ContinuousLinearMap.sum_apply]
    rw [show (∑ c : Fin n, (g₀.inner x (ψ (e c) • e c)) u) = ∑ c : Fin n, ψ (e c) * g₀.inner x (e c) u
        from by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_smul (g₀.inner x) (ψ (e c)) (e c), ContinuousLinearMap.smul_apply, smul_eq_mul]]
    conv_rhs => rw [hexpand u, map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul, smul_eq_mul, g₀.symm x (e c) u, mul_comm]
  refine ⟨hpair, ?_⟩
  rw [hpair W, hW_def, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul, smul_eq_mul, sq]

/-- **The sharp `δ²` passenger-rank fibre bound of the cross-correction contraction (Lemma B).**
Under the `g₀`-fibre operator bound `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, the intrinsic
squared fibre norm of the order-`(0, p)` cross-correction contraction
`crossCorrParallelContraction g₀ (realizeSymmCcTensor g₀ T₁) Y` (the symmetric realized perturbation
`h = ccTensorBilinSymm g₀ T₁` contracted against the `(0, 3 + p)`-factor `Y` through the `g₀`-cometric)
is dominated *sharply* — with the operator-norm constant `δ²`, no dimension factor — by that of `Y`:
`rfns(crossCorrParallelContraction g₀ (realizeSymm T₁) Y)(x) ≤ δ² · rfns(Y)(x)`.

This is the passenger-rank `p` generalization of `crossCorrectionSection_rfns_le_sq_loweredConnDiff`
(the `p = 0` instance).  Proved by Parseval in a `g₀`-orthonormal frame `e`: the contraction's frame
component at a tuple `J` is, through `crossCorrParallelContraction_toModel_apply0p` and the model eval
`crossCorrModelFun_eval0p`, the cometric-collapsed pairing `h(W_{J'}, e (J last))`, where the
slice-Riesz vector `W_{J'}` (`frameRiesz_pair_and_normSq` of the leading-slot functional of `Y` at the
slice `e ∘ J'`) reconstructs the value of `Y`'s leading-slot functional through frame Parseval and
`sum_phi_cometric_inner_basis`; grouped over the last slot it is the dual-frame squared sum
`∑_c h(W_{J'}, e c)²`, bounded sharply by `δ² · g₀(W_{J'}, W_{J'})`
(`gFibreOpBound_dualFrame_sq_sum_le`); and `g₀(W_{J'}, W_{J'}) = ∑_c (Y-model with `e c` leading)²`
(frame-Riesz) is exactly the `J'`-slice squared sum of `Y`'s frame components, summing to `rfns(Y)`. -/
theorem crossCorrParallelContraction_rfns_le_sq_passenger
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ)
    (Y : Integral.L2.SmoothCcTensor g₀ 0 (3 + p)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + p) x
        ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
            (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x) ≤
      δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x (Y.toSection x) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ (3 + p) x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The leading-slot functional of `Y` at the `Fin (2 + p)` slice-index `J'`, as a CLM.
  set Yunit : Tensor0SBundle.Tensor0SModel (3 + p) ℝ E := Tensor0SBundle.Tensor0SSpace.toModel
      (Y.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) with hYunit_def
  set leadFun : (Fin (2 + p) → Fin n) → (TangentSpace I x →L[ℝ] ℝ) := fun J' =>
    ContinuousMultilinearMap.toContinuousLinearMap Yunit
      (fun k : Fin (3 + p) => (Fin.cons (0 : TangentSpace I x)
          (fun j : Fin (2 + p) => e (J' j)) : Fin ((2 + p) + 1) → E)
          (finCongr (by omega : 3 + p = (2 + p) + 1) k))
      (finCongr (by omega : (2 + p) + 1 = 3 + p) 0) with hleadFun_def
  have hleadFun_apply : ∀ (J' : Fin (2 + p) → Fin n) (u : TangentSpace I x),
      leadFun J' u = Yunit (fun k : Fin (3 + p) => (Fin.cons u
          (fun j : Fin (2 + p) => e (J' j)) : Fin ((2 + p) + 1) → E)
          (finCongr (by omega : 3 + p = (2 + p) + 1) k)) := by
    intro J' u
    rw [hleadFun_def]
    show (ContinuousMultilinearMap.toContinuousLinearMap Yunit
        (fun k : Fin (3 + p) => (Fin.cons (0 : TangentSpace I x)
            (fun j : Fin (2 + p) => e (J' j)) : Fin ((2 + p) + 1) → E)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k))
        (finCongr (by omega : (2 + p) + 1 = 3 + p) 0)) u = _
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext k
    rcases eq_or_ne k (finCongr (by omega : (2 + p) + 1 = 3 + p) 0) with hk | hk
    · subst hk
      rw [Function.update_self]
      rw [show (finCongr (by omega : 3 + p = (2 + p) + 1)
            (finCongr (by omega : (2 + p) + 1 = 3 + p) 0)) = (0 : Fin ((2 + p) + 1)) from by
        apply Fin.ext; simp, Fin.cons_zero]
    · rw [Function.update_of_ne hk]
      -- off the leading slot: both `cons u` and `cons 0` agree.
      have hkne : (finCongr (by omega : 3 + p = (2 + p) + 1) k) ≠ (0 : Fin ((2 + p) + 1)) := by
        intro hc
        apply hk
        apply Fin.ext
        have := congrArg (Fin.val) hc
        simpa using this
      obtain ⟨k', hk'⟩ := Fin.exists_succ_eq.mpr hkne
      rw [← hk', Fin.cons_succ, Fin.cons_succ]
  -- The slice-Riesz vector and its two reconstruction facts.
  set W : (Fin (2 + p) → Fin n) → TangentSpace I x := fun J' =>
    ∑ c : Fin n, leadFun J' (e c) • e c with hW_def
  have hWfacts : ∀ J' : Fin (2 + p) → Fin n,
      (∀ u : TangentSpace I x, g₀.inner x (W J') u = leadFun J' u) ∧
        g₀.inner x (W J') (W J') = ∑ c : Fin n, (leadFun J' (e c)) ^ 2 := by
    intro J'
    rw [hW_def]
    exact frameRiesz_pair_and_normSq (I := I) g₀ x e horth hexpand (leadFun J')
  -- Frame expansion of both sides (the rank `3 + 0 + p` is defeq `3 + p`, same frame `e`).
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x (3 + 0 + p)
      e hreprS ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
          (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x) K₀,
    Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x (3 + p)
      e hreprS (Y.toSection x) K₀]
  -- The contraction's frame component at a tuple `J`.
  have hCcomp : ∀ J : Fin (3 + 0 + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 (3 + 0 + p)
          ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
              (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨2 + p, by omega⟩)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ (3 + 0 + p) x e K₀ J
      ((crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
          (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x)]
    rw [show (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (3 + 0 + p) I x from
          (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
            (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        = (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
            (realizeSymmCcTensor (I := I) g₀ T₁) Y).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        from rfl]
    rw [crossCorrParallelContraction_toModel_apply0p (I := I) g₀ p
      (realizeSymmCcTensor (I := I) g₀ T₁) Y x (fun k => e (J k))]
    rw [crossCorrModelFun_eval0p (E := E) (cometricReadingModel (I := I) g₀ x) p
      (ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x)
      (ccUnitModel (I := I) g₀ Y x) (fun k => e (J k))]
    -- Identify the `S = h` factor.
    have hSfac : ∀ i : Fin (Module.finrank ℝ E),
        ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
          ![cometricReadingModel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis i)),
            (fun k => e (J k)) ⟨2 + p, by omega⟩]
          = ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis i))) (e (J ⟨2 + p, by omega⟩)) := by
      intro i
      rw [← realizeSymmCcTensor_ccTensorBilin_apply, ccTensorBilin_apply]; rfl
    -- Identify the `T = Y` factor as `leadFun J' (finBasis i)`.
    have hTfac : ∀ i : Fin (Module.finrank ℝ E),
        ccUnitModel (I := I) g₀ Y x
            (fun k : Fin (3 + p) => (Fin.cons ((Module.finBasis ℝ E) i)
              (fun j : Fin (2 + p) => (fun k => e (J k)) ⟨j.val, by omega⟩) :
                Fin ((2 + p) + 1) → E)
              (finCongr (by omega : 3 + p = (2 + p) + 1) k))
          = leadFun (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) i) := by
      intro i
      rw [hleadFun_apply (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) i)]
      rfl
    simp only [hSfac, hTfac]
    -- Collapse the cometric sum via `sum_phi_cometric_inner_basis`.
    set φ : TangentSpace I x →L[ℝ] ℝ := (ccTensorBilinSymm (I := I) g₀ T₁ x).flip
      (e (J ⟨2 + p, by omega⟩)) with hφ_def
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          leadFun (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) i)
            * ccTensorBilinSymm (I := I) g₀ T₁ x
                (cometricReadingModel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis i))) (e (J ⟨2 + p, by omega⟩)))
        = ∑ i : Fin (Module.finrank ℝ E),
            φ (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis i)))
              * g₀.inner x (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩))
                  ((Module.finBasis ℝ E) i) from ?_]
    · rw [sum_phi_cometric_inner_basis (I := I) g₀ x
        (fun i => cometricReadingModel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
        (fun k u => cometricReadingModel_dualBasis_inner (I := I) g₀ x k u)
        φ (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩))]
      rfl
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hφ_def, ContinuousLinearMap.flip_apply, mul_comm]
      congr 1
      rw [(hWfacts (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)).1 ((Module.finBasis ℝ E) i)]
  simp only [hCcomp]
  -- Group the LHS by the LAST slot.
  rw [sum_index_lastSlot_group (n := n) (p := p)
    (fun J : Fin (3 + 0 + p) → Fin n =>
      ccTensorBilinSymm (I := I) g₀ T₁ x
        (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨2 + p, by omega⟩)) ^ 2)]
  have hLslice : ∀ (c : Fin n) (J' : Fin (2 + p) → Fin n),
      ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (2 + p) =>
            (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
              (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) ⟨j.val, by omega⟩)))
          (e ((Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) ⟨2 + p, by omega⟩))) ^ 2
        = ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2 := by
    intro c J'
    have hsliceArg : (fun j : Fin (2 + p) =>
          (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) ⟨j.val, by omega⟩)) = J' := by
      funext j
      rw [show (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) (⟨j.val, by omega⟩ : Fin (3 + 0 + p)))
            = Fin.castSucc (n := 2 + p) j from by apply Fin.ext; simp, Fin.snoc_castSucc]
    have hsliceLast : ((Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
          (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) ⟨2 + p, by omega⟩)) = c := by
      rw [show (finCongr (by omega : 3 + 0 + p = (2 + p) + 1) (⟨2 + p, by omega⟩ : Fin (3 + 0 + p)))
            = Fin.last (2 + p) from by apply Fin.ext; simp, Fin.snoc_last]
    rw [hsliceArg, hsliceLast]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun J' _ => hLslice c J'))]
  rw [Finset.sum_comm]
  -- Group the RHS (`Y`'s frame components) by the LEADING slot.
  have hYcomp : ∀ J : Fin (3 + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 (3 + p)
          (Y.toSection x) n e K₀ J = Yunit (fun k => e (J k)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ (3 + p) x e K₀ J (Y.toSection x), hYunit_def]
  simp only [hYcomp]
  rw [sum_index_leadSlot_group (n := n) (p := p)
    (fun J : Fin (3 + p) → Fin n => (Yunit (fun k => e (J k))) ^ 2)]
  have hRslice : ∀ (c : Fin n) (J' : Fin (2 + p) → Fin n),
      (Yunit (fun k => e ((fun k : Fin (3 + p) =>
          (Fin.cons c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k)) k))) ^ 2
        = (leadFun J' (e c)) ^ 2 := by
    intro c J'
    rw [hleadFun_apply J' (e c)]
    have hsliceArg : (fun k : Fin (3 + p) => e ((Fin.cons c J' : Fin ((2 + p) + 1) → Fin n)
          (finCongr (by omega : 3 + p = (2 + p) + 1) k)))
        = (fun k : Fin (3 + p) => (Fin.cons (e c)
            (fun j : Fin (2 + p) => e (J' j)) : Fin ((2 + p) + 1) → E)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k)) := by
      funext k
      refine Fin.cases ?_ (fun k' => ?_) (finCongr (by omega : 3 + p = (2 + p) + 1) k)
      · rw [Fin.cons_zero, Fin.cons_zero]
      · rw [Fin.cons_succ, Fin.cons_succ]
    rw [hsliceArg]
  rw [show (∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        (Yunit (fun k => e ((fun k : Fin (3 + p) =>
          (Fin.cons c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : 3 + p = (2 + p) + 1) k)) k))) ^ 2)
      = ∑ J' : Fin (2 + p) → Fin n, ∑ c : Fin n, (leadFun J' (e c)) ^ 2 from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun J' _ => Finset.sum_congr rfl (fun c _ => hRslice c J'))]
  -- Both sides now grouped by `J'`; sum over `J'`, bound each slice sharply.
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun J' _ => ?_)
  have hcross_inner :
      (∑ c : Fin n, ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2) ≤
        δ ^ 2 * g₀.inner x (W J') (W J') :=
    gFibreOpBound_dualFrame_sq_sum_le (I := I) g₀ x e horth hpars
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hδ (W J')
  rw [(hWfacts J').2] at hcross_inner
  exact hcross_inner

set_option linter.unusedSectionVars false in
/-- **The squared metric `L²` norm of a `(0, s)`-tensor is the integral of its intrinsic squared
fibre norm.**  `‖S‖² = ∫ rfns(S)(x) dμ`, the `SmoothCcTensor`-seminorm read through the model-field
fibre-norm bridge (`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq`) after
`SmoothCcTensor.norm_def`.  The currency converter between the pointwise `rfns` brick layer and the
integrated `L²` two-arm layer. -/
private lemma norm_sq_eq_integral_riemannianFiberNormSq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖S‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
  rw [Integral.L2.SmoothCcTensor.norm_def]
  exact Integral.Connection.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g₀ s S

/-- **The `p`-fold passenger-slot extension of an operator field.**  `slotExtendPow p Φ` extends the
`(r, s)`-operator field `Φ` to the `(r + p, s + p)`-operator field obtained by inserting `p` leading
spectator slots one at a time.  It is the operator tower that the iterated parallel covariant Leibniz of
`appCcRS Φ` produces (each covariant gradient inserts one leading gradient direction as a spectator,
left uncontracted, `slotExtendFib_apply_eval`). -/
noncomputable def slotExtendPow (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ p : ℕ, Integral.L2.SmoothCcTensor g₀ r s → Integral.L2.SmoothCcTensor g₀ (r + p) (s + p)
  | 0 => fun Φ => Φ
  | (p + 1) => fun Φ => slotExtend (I := I) (M := M) g₀ (r + p) (s + p) (slotExtendPow g₀ r s p Φ)

/-- **The `p`-fold leading-slot curry of a `(0, r + p)`-fibre tensor.**  Peels the `p` passenger
directions `q : Fin p → E` off the leading slots one at a time (newest-passenger first, matching the
`slotExtendPow` recursion order), returning the inner `(0, r)`-fibre tensor.  The fibre-level partner of
`slotExtendPow`'s passenger reading. -/
private noncomputable def passengerCurry (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    ∀ (p : ℕ), Tensor0SBundle.Tensor0SSpace (r + p) I x → (Fin p → E) →
      Tensor0SBundle.Tensor0SSpace r I x
  | 0, D, _ => D
  | (p + 1), D, q =>
      passengerCurry g₀ r x p
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
          (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
        (fun j : Fin p => q (Fin.succ j))

set_option linter.unusedSectionVars false in
/-- **The `p`-fold slot extension reads its `p` leading slots as passengers.**  For a `(r, s)`-operator
field `Φ` and a `(0, r + p)`-fibre tensor `D`, the model value of `slotExtendPow p Φ x` applied to `D`
on the tuple `vecAppend q vs` (the `p` passenger directions `q` in the leading slots, the inner `s`-tuple
`vs` in the trailing slots) reads the `p` passenger directions off the leading slots (of both source and
target), leaving `Φ x` to act on the `p`-fold leading-slot curry `passengerCurry p D q`, evaluated on the
trailing `s`-tuple `vs`.  Proved by induction on `p` through `slotExtendFib_apply_eval` (the single-slot
leading-passenger reading) and `tensor0S_curry_apply_eval`. -/
private theorem slotExtendPow_toModel_consSlots (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) :
    ∀ (p : ℕ) (D : Tensor0SBundle.Tensor0SSpace (r + p) I x) (q : Fin p → E) (vs : Fin s → E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (s + p) I x from
              (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x) D)
          (Matrix.vecAppend (by omega : s + p = p + s) q vs) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              Φ.toSection x)
            (passengerCurry (I := I) (M := M) g₀ r x p D q)) vs := by
  intro p
  induction p with
  | zero =>
    intro D q vs
    show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          Φ.toSection x) D) (Matrix.vecAppend (by omega : s + 0 = 0 + s) q vs) = _
    congr 1
    funext k
    rw [Matrix.vecAppend_eq_ite]
    simp only [Nat.not_lt_zero, dif_neg, not_false_iff]
    apply congrArg
    apply Fin.ext
    simp
  | succ p ih =>
    intro D q vs
    -- The input tuple `vecAppend q vs : Fin (s + (p+1)) = Fin ((s+p)+1)` is `Fin.cons (q 0) (rest)`.
    set m : Fin ((s + p) + 1) → E :=
      (Matrix.vecAppend (by omega : s + (p + 1) = (p + 1) + s) q vs :
        Fin (s + (p + 1)) → E) with hm_def
    have hm0 : m 0 = q 0 := by
      rw [hm_def]
      exact Matrix.vecAppend_apply_zero (by omega : s + (p + 1) = (p + 1) + s) q vs
    have hmtail : Matrix.vecTail m
        = Matrix.vecAppend (by omega : s + p = p + s) (fun j : Fin p => q (Fin.succ j)) vs := by
      funext k
      have hL : Matrix.vecTail m k = m k.succ := rfl
      rw [hL, hm_def]
      rw [Matrix.vecAppend_eq_ite (by omega : s + (p + 1) = (p + 1) + s) q vs,
        Matrix.vecAppend_eq_ite (by omega : s + p = p + s) (fun j : Fin p => q (Fin.succ j)) vs]
      simp only []
      by_cases hk : (k : ℕ) < p
      · rw [dif_pos (by simpa [Fin.val_succ] using hk : (k.succ : ℕ) < p + 1), dif_pos hk]
        apply congrArg
        apply Fin.ext
        simp [Fin.val_succ]
      · rw [dif_neg (by simpa [Fin.val_succ] using hk : ¬ (k.succ : ℕ) < p + 1), dif_neg hk]
        apply congrArg
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
    rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
    -- `slotExtendPow (p+1) Φ = slotExtend (slotExtendPow p Φ)`; its toSection is `slotExtendFib …`.
    -- Restate the LHS operator through `slotExtendFib` (all defeq) so `slotExtendFib_apply_eval` fires.
    rw [hm0]
    rw [show Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace (r + (p + 1)) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (s + (p + 1)) I x from
              (slotExtendPow (I := I) (M := M) g₀ r s (p + 1) Φ).toSection x) D)
            (Fin.cons (q 0) (Matrix.vecTail m))
        = Tensor0SBundle.Tensor0SSpace.toModel
            (slotExtendFib (I := I) (M := M) g₀ (r + p) (s + p) x
              (show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (s + p) I x from
                (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x) D)
            (Fin.cons (q 0) (Matrix.vecTail m)) from rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ (r + p) (s + p) x
      (show Tensor0SBundle.Tensor0SSpace (r + p) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + p) I x from
        (slotExtendPow (I := I) (M := M) g₀ r s p Φ).toSection x)
      D (q 0) (Matrix.vecTail m)]
    rw [hmtail]
    rw [show passengerCurry (I := I) (M := M) g₀ r x (p + 1) D q
          = passengerCurry (I := I) (M := M) g₀ r x p
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
                (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
              (fun j : Fin p => q (Fin.succ j)) from rfl]
    exact ih ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
        (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
      (fun j : Fin p => q (Fin.succ j)) vs

set_option linter.unusedSectionVars false in
/-- The `p`-fold passenger-slot extension of a `∇₀`-parallel operator field is `∇₀`-parallel:
`slotExtend` preserves parallelism (`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`). -/
private theorem covGrad_slotExtendPow_eq_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ r s Φ = 0) (p : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (r + p) (s + p)
        (slotExtendPow (I := I) (M := M) g₀ r s p Φ) = 0 := by
  induction p with
  | zero => exact hΦ
  | succ p ih =>
    exact DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.covGrad_slotExtend_eq_zero_of_covGrad_eq_zero
      (I := I) (M := M) g₀ (r + p) (s + p) (slotExtendPow (I := I) (M := M) g₀ r s p Φ) ih

set_option linter.unusedSectionVars false in
/-- **The iterated parallel operator-field covariant Leibniz.**  For a `∇₀`-parallel operator field `Φ`
(`covGrad Φ = 0`), the order-`p` covariant gradient of the operator action `appCcRS Φ W` is the action
of the `p`-fold passenger extension on the order-`p` gradient of the contracted section:
```
∇^p (appCcRS Φ W) = appCcRS (slotExtendPow p Φ) (∇^p W).
```
Each covariant gradient splits by `covGrad_appCcRS_eq` into the differentiated-coefficient action (which
vanishes since `Φ` and its slot extensions are parallel) plus the slot-extended action on the gradient. -/
private theorem iteratedCovGrad_appCcRS_of_parallel (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ b c)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ b c Φ = 0)
    (W : Integral.L2.SmoothCcTensor g₀ a b) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a c p (appCcRS (I := I) (M := M) g₀ a b c Φ W) =
      appCcRS (I := I) (M := M) g₀ a (b + p) (c + p)
        (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W) := by
  induction p with
  | zero =>
    rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero]
    rfl
  | succ p ih =>
    rw [PDE.RicciFlow.iteratedCovGrad_succ, ih]
    rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ a (b + p) (c + p)
      (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W)]
    rw [covGrad_slotExtendPow_eq_zero (I := I) (M := M) g₀ b c Φ hΦ p]
    rw [appCcRS_zero_left (I := I) (M := M) g₀ a (b + p) (c + p + 1)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W), zero_add]
    rw [PDE.RicciFlow.iteratedCovGrad_succ]
    rfl

set_option linter.unusedSectionVars false in
/-- **The order-`p` covariant jet of the cross-correction is the slot-extended cometric action on the
order-`p` jet of the frame-free product section.**  Writing the cross correction as the parallel
cometric contraction `crossCorrParallelContraction g₀ S T` (`S = realizeSymm T₁`,
`T = permute (loweredConnDiff g₁ g₀)`, the section identity
`crossCorrParallelContraction_eq_crossCorrectionSection`), the operator-field factorisation
`crossCorrParallelContraction_eq_appCcRS` exhibits it as `appCcRS (crossCorrCometricOp g₀ 0 0)
(crossCorrProdSection g₀ S T)` of the `∇₀`-parallel cometric double-trace field
(`crossCorrCometricOp_covGrad_eq_zero`); the iterated parallel operator-field Leibniz
`iteratedCovGrad_appCcRS_of_parallel` then carries `∇^p` through as the `p`-fold passenger extension:
```
∇^p (crossCorrectionSection g₁ g₀ T₁)
  = appCcRS (slotExtendPow p (crossCorrCometricOp g₀ 0 0)) (∇^p (crossCorrProdSection g₀ S T)).
```
The cometric pair traces the two ORIGINAL product slots throughout; the `p` gradient directions ride as
leading spectators (`slotExtendPow_toModel_consSlots`). -/
private theorem crossCorrectionSection_iteratedCovGrad_eq_appCcRS_slotExtendPow
    (g₀ g₁ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (crossCorrectionSection (I := I) g₁ g₀ T₁) =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
        (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
          (crossCorrCometricOp (I := I) g₀ 0 0))
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0)
            (realizeSymmCcTensor (I := I) g₀ T₁)
            (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
              (loweredConnDiffSection (I := I) g₁ g₀)))) := by
  rw [← crossCorrParallelContraction_eq_crossCorrectionSection (I := I) g₀ g₁ T₁]
  rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ (a := 0) (b := 0)
    (realizeSymmCcTensor (I := I) g₀ T₁)
    (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (loweredConnDiffSection (I := I) g₁ g₀))]
  exact iteratedCovGrad_appCcRS_of_parallel (I := I) g₀ 0 ((3 + 0) + (2 + 0)) (3 + 0 + 0)
    (crossCorrCometricOp (I := I) g₀ 0 0)
    (crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ 0 0)
    (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0)
      (realizeSymmCcTensor (I := I) g₀ T₁)
      (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (loweredConnDiffSection (I := I) g₁ g₀))) p

/-! ## The δ < 1/2 uniform recursion (the scaled-Young redesign)

The differentiated-Koszul recursion divides by the fibre-small denominator `4 − 8δ`, positive
exactly on `δ < 1/2`.  The Gagliardo–Nirenberg **re-emission** of the top connection-difference jet
(the mixed `i ≥ 1` cells of the cross-correction Leibniz grid, whose GN interpolation re-emits
`‖∇^p loweredConnDiffSection‖²`) is handled by the **`t`-scaled Young split** of the anti-diagonal
engine (`exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le`): the re-emitted top jet
carries the free coefficient `t·δ²`, with the engine constants paying `(1/t)^p` on the lower-order
remainder.  The absorption finale chooses `t := (1 − 2δ)/(1 + 2δ)` from the recursion's own margin,
so `2(1 + t)δ² = 4δ²/(1 + 2δ) ≤ δ` for every `δ < 1/2` — the fibre-smallness hypothesis is `δ < 1/2`
**uniformly in the order `p`** (the former antitone pinned threshold
`crossCorrRecursionThreshold ~ 4^{-p}` is deleted: it was incompatible with every fixed-`δ`
all-order consumer; the sharp binomial constant `4^p` now lives in the per-order constant family on
the lower-order `L²` term, the Hamilton-tame shape).  The product-level top cell (the honest `i = 0`
Leibniz cell, the keystone slot layout) carries the sharp `δ²` passenger bound
`crossCorrKeystoneTop_rfns_le_sq_passenger`; the former crude top-cell envelope reconciliation
(coefficient `4 + 4n²·C_env`) is gone — any fixed additive top coefficient beyond the sharp `2δ²`
would break the `4 − 8δ` terminus at `δ` near `1/2`. -/

/-- **The `appCcRS` fibre-envelope constant of the `p`-fold slot-extended cross-correction cometric
operator** (the `Classical.choose` of `exists_uniform_riemannianFiberNormSq_appCcRS_le` at the
operator `slotExtendPow p (crossCorrCometricOp g₀ 0 0)`). -/
noncomputable def crossCorrEnvelopeConst (g₀ : SmoothRiemannianMetric I M) (p : ℕ) : ℝ :=
  (exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0
    (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (crossCorrCometricOp (I := I) g₀ 0 0))).choose

/-- The envelope constant is nonnegative, and it satisfies its defining fibre envelope. -/
theorem crossCorrEnvelopeConst_spec (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    0 ≤ crossCorrEnvelopeConst (I := I) g₀ p ∧
      ∀ (W : Integral.L2.SmoothCcTensor g₀ 0 (((3 + 0) + (2 + 0)) + p)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + p) x
            ((appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
              (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
                (crossCorrCometricOp (I := I) g₀ 0 0)) W).toSection x) ≤
          crossCorrEnvelopeConst (I := I) g₀ p *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) x
              (W.toSection x) :=
  (exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀ 0
    (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (crossCorrCometricOp (I := I) g₀ 0 0))).choose_spec

/-- **The scaled-Young absorption inequality of the `δ < 1/2` recursion.**  For `0 ≤ δ < 1/2` and
the margin-chosen scale `t := (1 − 2δ)/(1 + 2δ) ∈ (0, 1]`, `2·(1 + t)·δ² = 4δ²/(1 + 2δ) ≤ δ` — the
**fresh** inequality by which the consumer `crossCorrectionSection_iteratedCovGrad_grid_le` relaxes
the `2(1 + t)δ²`-principal of the scaled top/rest split to the load-bearing `δ`-principal, keeping
the downstream `4 − 8δ` recursion denominator positive on all of `δ < 1/2`, uniformly in the order. -/
theorem crossCorrMarginScale_absorb {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    2 * (1 + (1 - 2 * δ) / (1 + 2 * δ)) * δ ^ 2 ≤ δ := by
  have hden : (0 : ℝ) < 1 + 2 * δ := by linarith
  have hcollapse : 1 + (1 - 2 * δ) / (1 + 2 * δ) = 2 / (1 + 2 * δ) := by
    field_simp
    ring
  rw [hcollapse]
  rw [show 2 * (2 / (1 + 2 * δ)) * δ ^ 2 = (4 * δ ^ 2) / (1 + 2 * δ) from by ring]
  rw [div_le_iff₀ hden]
  nlinarith

/-- The margin-chosen scale `t := (1 − 2δ)/(1 + 2δ)` is in `(0, 1]` for `0 ≤ δ < 1/2`. -/
theorem crossCorrMarginScale_mem {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    0 < (1 - 2 * δ) / (1 + 2 * δ) ∧ (1 - 2 * δ) / (1 + 2 * δ) ≤ 1 := by
  have hden : (0 : ℝ) < 1 + 2 * δ := by linarith
  constructor
  · apply div_pos (by linarith) hden
  · rw [div_le_one hden]; linarith

/-! ## Support bricks for the rest-peel proof

Fibre-level `rfns` difference subadditivity, the `L²` difference subadditivity, the order-`0`
`rfns` invariances (slot permutation, rank cast), the section-level commutation of the iterated
covariant gradient with a slot permutation (the gradient direction enters as the new leading slot,
`Equiv.Perm.decomposeFin`), the subtractivity of the slot permutation and of the operator-field
action, the sharp fibre-small `C⁰` sup of the realized perturbation (`n²δ²`), and the
Neumann-absorbed `C⁰` fibre sup of the lowered connection difference. -/

set_option linter.unusedSectionVars false in
/-- **Difference `2`-subadditivity of the intrinsic squared fibre norm.**
`rfns(a − b) ≤ 2·rfns(a) + 2·rfns(b)`, from `riemannianFiberNormSq_add_le` and the `(−1)²`-scaling. -/
private lemma rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  have hneg : riemannianFiberNormSq (I := I) (M := M) g r s x (-b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x b := by
    rw [show (-b) = (-1 : ℝ) • b from by simp, rfns_smul]
    norm_num
  have h := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
  rw [hneg] at h
  rw [sub_eq_add_neg]
  exact h

set_option linter.unusedSectionVars false in
/-- **Difference `2`-subadditivity of the squared metric `L²` norm.**
`‖A − B‖² ≤ 2‖A‖² + 2‖B‖²`, from the real inner-product expansion and Cauchy–Schwarz. -/
private lemma smoothCcTensor_norm_sq_sub_le (g₀ : SmoothRiemannianMetric I M) (m : ℕ)
    (A B : Integral.L2.SmoothCcTensor g₀ 0 m) :
    ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
  have h := norm_sub_sq_real A B
  have hcs2 := abs_real_inner_le_norm A B
  have hcs := neg_le_abs (@inner ℝ _ _ A B)
  nlinarith [h, hcs, hcs2, sq_nonneg (‖A‖ - ‖B‖), norm_nonneg A, norm_nonneg B]

set_option linter.unusedSectionVars false in
/-- **Order-`0` slot-permutation invariance of the intrinsic squared fibre norm.**
`rfns(permuteCcTensor σ W)(x) = rfns(W)(x)` (the `i = 0` instance of
`riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor`). -/
private lemma rfns_permuteCcTensor_zero (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (W.toSection x) :=
  PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M) g₀ σ W 0 x

set_option linter.unusedSectionVars false in
/-- **Order-`0` rank-cast invariance of the intrinsic squared fibre norm.**
`rfns(castRankCc_db h W)(x) = rfns(W)(x)` (the `j = 0` instance of
`rfns_iteratedCovGrad_castRankCc_db`). -/
private lemma rfns_castRankCc_db_zero (g₀ : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W : Integral.L2.SmoothCcTensor g₀ 0 a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 b x
        ((castRankCc_db g₀ 0 h W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 a x (W.toSection x) := by
  have hcast := rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0 h W 0 x
  rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero] at hcast
  exact hcast

set_option linter.unusedSectionVars false in
set_option linter.style.show false in
/-- **The covariant gradient commutes with a slot permutation**: the gradient of a slot-permuted
section is the slot permutation of the gradient, extended by the identity on the new leading
gradient slot (`Equiv.Perm.decomposeFin.symm (0, σ)`).  Local restatement (the library copy is
`private` in the segment-metric curvature tower). -/
private theorem covGrad_permuteCcTensor_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (R : Integral.L2.SmoothCcTensor g₀ 0 s) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s + 1)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) x
    (Integral.Connection.unitZeroSec (I := I) (M := M) x) m]
  have hnat : Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s
              (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R) x (m 0))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s R x (m 0))
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_unit_toModel_domDomCongr_of_section
      (I := I) (M := M) g₀ s σ R (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ R)
      (fun y => PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ R y) x (m 0)
  rw [hnat, ContinuousMultilinearMap.domDomCongr_apply]
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) x
  rw [hR, ContinuousMultilinearMap.domDomCongr_apply]
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    R x (Integral.Connection.unitZeroSec (I := I) (M := M) x)
    (fun k => m ((Equiv.Perm.decomposeFin.symm (0, σ)) k))]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail : Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
      fun j : Fin s => Matrix.vecTail m (σ j) := by
    funext j
    show m ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = m (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [htail]

/-- **The leading-identity extension of a slot permutation by `p` gradient slots**: each covariant
gradient inserts its direction as the new leading slot, so the permutation extends by the identity
on the leading slot at each step (`Equiv.Perm.decomposeFin.symm (0, ·)`). -/
private def leadExtPerm {s : ℕ} (σ : Equiv.Perm (Fin s)) : ∀ p : ℕ, Equiv.Perm (Fin (s + p))
  | 0 => σ
  | (p + 1) => Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)

set_option linter.unusedSectionVars false in
/-- **The iterated covariant gradient commutes with a slot permutation**:
`∇^p (permuteCcTensor σ W) = permuteCcTensor (leadExtPerm σ p) (∇^p W)`. -/
private theorem iteratedCovGrad_permuteCcTensor_eq (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ W) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σ p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p W) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [PDE.RicciFlow.iteratedCovGrad_succ, ih,
      covGrad_permuteCcTensor_local (I := I) g₀ (leadExtPerm σ p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s p W),
      PDE.RicciFlow.iteratedCovGrad_succ]
    rfl

set_option linter.unusedSectionVars false in
/-- **Slot permutation distributes over a section difference.**  Local restatement (the library
copy is `private` in the segment-metric curvature tower). -/
private theorem permuteCcTensor_sub_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A - B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have hsubval : (A - B).toSection x = A.toSection x - B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hsubval' : ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        - (PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          - (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [hsubval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          - Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
            - PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hsubval']; rfl

set_option linter.unusedSectionVars false in
/-- **The operator-field action distributes over a section difference** (from `appCcRS_add_right`
and `appCcRS_smul_right` at `k = −1`). -/
private theorem appCcRS_sub_right_local (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ b c) (W₁ W₂ : Integral.L2.SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g₀ a b c Φ W₁ - appCcRS (I := I) (M := M) g₀ a b c Φ W₂ := by
  rw [sub_eq_add_neg, show -W₂ = (-1 : ℝ) • W₂ from (neg_one_smul ℝ W₂).symm,
    appCcRS_add_right, appCcRS_smul_right, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- **The sharp fibre-small `C⁰` bound of the realized symmetric perturbation.**  Under
`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, the intrinsic squared fibre norm of
`realizeSymmCcTensor g₀ T₁` is everywhere at most `(n·δ)²` (`n = finrank ℝ E`): by frame Parseval
the fibre norm is the squared sum of the `n²` frame components `h(e_i, e_j)`, each of absolute
value at most `δ` on the `g₀`-orthonormal frame. -/
private lemma realizeSymm_rfns_le_of_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hfib : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * δ) ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ 2 x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 2 e
      hreprS ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) K₀]
  -- Each frame component is `h(e_{J0}, e_{J1})`, of absolute value `≤ δ` on the orthonormal frame.
  have hcomp : ∀ J : Fin 2 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ 2 x e K₀ J
      ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x)]
    rw [show (fun k => e (J k)) = ![e (J 0), e (J 1)] from by
      funext k; fin_cases k <;> rfl]
    rw [← realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ T₁ x (e (J 0)) (e (J 1)),
      ccTensorBilin_apply (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x (e (J 0)) (e (J 1)),
      ccTensorModel, ccTensorMultilinear_apply]
  have hterm : ∀ J : Fin 2 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J ^ 2 ≤ δ ^ 2 := by
    intro J
    rw [hcomp J]
    have habs := hfib x (e (J 0)) (e (J 1))
    rw [horth (J 0) (J 0), horth (J 1) (J 1)] at habs
    simp only [if_true, Real.sqrt_one, mul_one] at habs
    calc ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1)) ^ 2
        = |ccTensorBilinSymm (I := I) g₀ T₁ x (e (J 0)) (e (J 1))| ^ 2 := (sq_abs _).symm
      _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc (∑ J : Fin 2 → Fin n,
        Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) n e K₀ J ^ 2)
      ≤ ∑ _J : Fin 2 → Fin n, δ ^ 2 := Finset.sum_le_sum (fun J _ => hterm J)
    _ = (Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = ((Module.finrank ℝ E : ℝ) * δ) ^ 2 := by
        have hfr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hn, hfr]
        push_cast
        ring

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The Neumann-absorbed `C⁰` fibre sup of the lowered connection difference.**  Over the
fibre-small (`δ < 1/2`) supercritically `H^a`-bounded (`2a > finrank + 4`, `‖T₁.toHs a‖ ≤ B`)
realize family, the order-`0` intrinsic squared fibre norm of `loweredConnDiffSection g₁ g₀` is
uniformly bounded: the pointwise differentiated-Koszul absorption
`(4 − 8δ²)·rfns(D) ≤ 2·rfns(koszulCombSection)` (the section identity
`2·D = koszulComb − 2·crossCorrection` with the sharp `δ²` cross bound
`crossCorrectionSection_rfns_le_sq_loweredConnDiff`), the pointwise clean-linear-part jet brick
`koszulCombSection_iteratedCovGrad_rfns_le` at order `0`, and the supercritical jet embedding
`exists_iteratedCovGradJetSum_le_toHs_sharpOrder` for the `≤ 1`-jet of `T₁`. -/
private lemma exists_loweredConnDiff_rfns_fibre_sup (g₀ : SmoothRiemannianMetric I M)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ < 1 / 2) (B : ℝ) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨Ck0, hCk00, hCk0⟩ := koszulCombSection_iteratedCovGrad_rfns_le (I := I) g₀ 0
  obtain ⟨Cemb, hCemb0, hCemb⟩ :=
    exists_iteratedCovGradJetSum_le_toHs_sharpOrder (I := I) g₀ a ha
  refine ⟨Real.sqrt (Ck0 * (2 * (Cemb * max B 0) ^ 2)), Real.sqrt_nonneg _, ?_⟩
  intro T₁ g₁ hr hfib hball x
  rw [Real.sq_sqrt (by positivity)]
  -- The `≤ 1`-jet of `T₁` is uniformly bounded by the supercritical embedding.
  have hjet : iteratedCovGradJetSum (I := I) g₀ T₁ x ≤ Cemb * max B 0 := by
    refine le_trans (hCemb T₁ x) ?_
    exact mul_le_mul_of_nonneg_left (le_trans hball (le_max_left _ _)) hCemb0.le
  have hjet_nn : 0 ≤ iteratedCovGradJetSum (I := I) g₀ T₁ x :=
    iteratedCovGradJetSum_nonneg (I := I) g₀ T₁ x
  have hjet_sq : iteratedCovGradJetSum (I := I) g₀ T₁ x ^ 2 ≤ (Cemb * max B 0) ^ 2 :=
    pow_le_pow_left₀ hjet_nn hjet 2
  -- Each order-`l ≤ 2` jet `rfns` of `T₁` is at most the squared jet sum.
  have hTjet : ∀ l : ℕ, l < 3 →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) ≤
        (Cemb * max B 0) ^ 2 := by
    intro l hl
    refine le_trans ?_ hjet_sq
    have hsqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ≤
        iteratedCovGradJetSum (I := I) g₀ T₁ x := by
      rw [iteratedCovGradJetSum]
      have hhead : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) =
          (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x‖) :=
        (norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g₀ 0 (2 + l)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁) x).symm
      rw [hhead]
      refine Finset.single_le_sum (f := fun j =>
          (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j T₁).toSection x‖))
        (fun j _ => ?_) (Finset.mem_range.mpr hl)
      letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      exact norm_nonneg _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)
        = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ^ 2 :=
          (Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)).symm
      _ ≤ iteratedCovGradJetSum (I := I) g₀ T₁ x ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  -- The order-`0` Koszul clean-linear-part bound.
  set rD := riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
    ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) with hrD
  set rK := riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
    ((koszulCombSection (I := I) g₁ g₀ T₁).toSection x) with hrK
  set rC := riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
    ((crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) with hrC
  have hrD_nn : 0 ≤ rD := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hkoszul : rK ≤ Ck0 * (2 * (Cemb * max B 0) ^ 2) := by
    have h := hCk0 T₁ g₁ hr x
    rw [show PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 0
        (koszulCombSection (I := I) g₁ g₀ T₁) = koszulCombSection (I := I) g₁ g₀ T₁ from rfl] at h
    rw [← hrK] at h
    refine le_trans h ?_
    have hsum : (∑ l ∈ Finset.range (0 + 1 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ≤
        2 * (Cemb * max B 0) ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have h0 := hTjet 0 (by omega)
      have h1 := hTjet 1 (by omega)
      linarith
    exact mul_le_mul_of_nonneg_left hsum hCk00
  -- The section identity `2•D = koszulComb − 2•crossCorrection`, read pointwise.
  have hsec : (2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀ =
      koszulCombSection (I := I) g₁ g₀ T₁
        - (2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁ := by
    rw [koszulCombSection]
    abel
  have hpt : (((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀).toSection x :
        TensorRSSpace 0 3 I x) =
      (koszulCombSection (I := I) g₁ g₀ T₁).toSection x
        - (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) := by
    rw [hsec, Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have h4D : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀).toSection x) = 4 * rD := by
    rw [show (((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀).toSection x :
          TensorRSSpace 0 3 I x) = (2 : ℝ) • (loweredConnDiffSection (I := I) g₁ g₀).toSection x
        from by rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
      rfns_smul, ← hrD]
    norm_num
  have h2C : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x) = 4 * rC := by
    rw [show (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x :
          TensorRSSpace 0 3 I x) =
        (2 : ℝ) • (crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x
        from by rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
      rfns_smul, ← hrC]
    norm_num
  have hsub : 4 * rD ≤ 2 * rK + 8 * rC := by
    have hle := rfns_sub_le (I := I) (M := M) g₀ 0 3 x
      ((koszulCombSection (I := I) g₁ g₀ T₁).toSection x)
      (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x)
    rw [h2C, ← hrK] at hle
    have heq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((koszulCombSection (I := I) g₁ g₀ T₁).toSection x
          - (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁).toSection x)) = 4 * rD := by
      rw [← hpt]
      exact h4D
    rw [heq] at hle
    linarith
  have hcross : rC ≤ δ ^ 2 * rD := by
    rw [hrC, hrD]
    exact crossCorrectionSection_rfns_le_sq_loweredConnDiff (I := I) g₀ g₁ T₁ hfib x
  -- Neumann absorption: `(4 − 8δ²) ≥ 2` since `δ < 1/2`, so `rD ≤ rK`.
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith [hsub, hcross, hkoszul, hrD_nn, mul_le_mul_of_nonneg_right hδsq hrD_nn]

/-- **The keystone product-level top cell of the order-`p` cross-correction covariant jet.**  The
`i = 0` binomial cell of the operator-reduced covariant Leibniz of the parallel cometric contraction
`h ⌟ D`: the `p`-fold slot-extended cometric operator (`slotExtendPow p (crossCorrCometricOp g₀ 0 0)`)
applied to the slot-permuted bare product of the order-`p` jet factor `Z` (in the contraction's
original `D`-slot layout, the `p` gradient directions riding as spectators) with the realized
symmetric perturbation `realizeSymm T₁`.  This is the **honest Leibniz top cell** of
`∇^p (crossCorrectionSection g₁ g₀ T₁)` at `Z := ∇^p (permute c[0,1,2] (loweredConnDiffSection))` —
the cometric pair traces the two ORIGINAL product slots throughout (`slotExtendPow_toModel_consSlots`),
NOT the gradient slot that the section-level `(a := 0, b := p)` contraction
`crossCorrParallelContraction` would trace (the two layouts genuinely differ: the keystone contracts
the original slot, the `b := p` form contracts slot `0`; the model certificate at `p = 1, 2, 3`
refutes their equality). -/
noncomputable def crossCorrKeystoneTop (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 ((3 + 0) + p)) :
    Integral.L2.SmoothCcTensor g₀ 0 ((3 + 0 + 0) + p) :=
  appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (crossCorrCometricOp (I := I) g₀ 0 0))
    (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p)
      (castRankCc_db g₀ 0 (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
        ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
          (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
          (realizeSymmCcTensor (I := I) g₀ T₁))))

set_option linter.unusedSectionVars false in
private lemma leadExtPerm_apply_of_lt {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    ∀ (p : ℕ) (k : Fin (s + p)), k.val < p → leadExtPerm σ p k = k := by
  intro p
  induction p with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ p ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · have hk' : k = (0 : Fin ((s + p) + 1)) := Fin.ext hk0
      rw [hk']
      change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)) (0 : Fin ((s + p) + 1)) = _
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    · have hk' : k = Fin.succ (⟨k.val - 1, by omega⟩ : Fin (s + p)) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [hk']
      change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p))
          (Fin.succ (⟨k.val - 1, by omega⟩ : Fin (s + p))) = _
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
      rw [ih ⟨k.val - 1, by omega⟩ (by change k.val - 1 < p; omega)]

set_option linter.unusedSectionVars false in
private lemma leadExtPerm_apply_natAdd {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    ∀ (p : ℕ) (j : Fin s),
      leadExtPerm σ p (Fin.cast (by omega : p + s = s + p) (Fin.natAdd p j)) =
        Fin.cast (by omega : p + s = s + p) (Fin.natAdd p (σ j)) := by
  intro p
  induction p with
  | zero =>
    intro j
    rw [show (Fin.cast (by omega : 0 + s = s + 0) (Fin.natAdd 0 j)) = (j : Fin (s + 0)) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
    change σ j = _
    exact Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)
  | succ p ih =>
    intro j
    rw [show (Fin.cast (by omega : (p + 1) + s = s + (p + 1)) (Fin.natAdd (p + 1) j))
        = Fin.succ (Fin.cast (by omega : p + s = s + p) (Fin.natAdd p j)) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)]
    change (Equiv.Perm.decomposeFin.symm (0, leadExtPerm σ p)) (Fin.succ _) = _
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, ih j]
    exact Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)

set_option linter.unusedSectionVars false in
private lemma passengerCurry_toModel (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    ∀ (p : ℕ) (D : Tensor0SBundle.Tensor0SSpace (r + p) I x) (q : Fin p → E) (w : Fin r → E),
      Tensor0SBundle.Tensor0SSpace.toModel (passengerCurry (I := I) (M := M) g₀ r x p D q) w =
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Matrix.vecAppend (by omega : r + p = p + r) q w) := by
  intro p
  induction p with
  | zero =>
    intro D q w
    change Tensor0SBundle.Tensor0SSpace.toModel D w = _
    congr 1
    funext k
    rw [Matrix.vecAppend_eq_ite]
    simp only [Nat.not_lt_zero, dif_neg, not_false_iff]
    apply congrArg
    apply Fin.ext
    simp
  | succ p ih =>
    intro D q w
    rw [show passengerCurry (I := I) (M := M) g₀ r x (p + 1) D q
        = passengerCurry (I := I) (M := M) g₀ r x p
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
              (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
            (fun j : Fin p => q (Fin.succ j)) from rfl]
    rw [ih ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (r + p) x)
        (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0))
      (fun j : Fin p => q (Fin.succ j)) w]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (show Tensor0SBundle.Tensor0SSpace ((r + p) + 1) I x from D) (q 0)
      (Matrix.vecAppend (by omega : r + p = p + r) (fun j : Fin p => q (Fin.succ j)) w)]
    congr 1
    funext k
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [Fin.cons_zero]
      exact (Matrix.vecAppend_apply_zero (by omega : r + (p + 1) = (p + 1) + r) q w).symm
    · rw [Fin.cons_succ]
      rw [Matrix.vecAppend_eq_ite, Matrix.vecAppend_eq_ite]
      simp only [Fin.val_succ]
      by_cases hk : (k' : ℕ) < p
      · rw [dif_pos hk, dif_pos (by omega)]
        apply congrArg
        apply Fin.ext
        simp
      · rw [dif_neg hk, dif_neg (by omega)]
        apply congrArg
        simp only [Fin.mk.injEq]
        omega

set_option linter.unusedSectionVars false in
/-- Defining evaluation of the `IntrinsicSpectral.DeTurck.modelRankCast` model rank cast. -/
private lemma modelRankCast_apply_local {m n : ℕ} (h : m = n)
    (T : Tensor0SBundle.Tensor0SModel m ℝ E) (v : Fin n → E) :
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E) h T v =
      T (fun i => v (finCongr h i)) := by
  change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T v = _
  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T
      = ContinuousMultilinearMap.domDomCongr (finCongr h) T from rfl,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- The unit-model value of a rank-cast section reads the original on the cast tuple. -/
private lemma unitModel_castRankCc_db_local (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ 0 a) (x : M) (v : Fin b → TangentSpace I x) :
    Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ b
        (castRankCc_db g₀ 0 h W) x v =
      Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ a W x
        (fun i => v (Fin.cast h i)) := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
/-- The model image of the cometric double-trace operator section value. -/
private lemma crossCorrCometricOp_toSection_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ)
    (x : M) (P : Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
          (crossCorrCometricOp (I := I) g₀ a b).toSection x) P) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E)
          (3 + a + b)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel P)) := rfl

set_option linter.unusedSectionVars false in
/-- Concrete values of the `(a, b) = (0, 0)` cross-correction slot permutation on `Fin 5`. -/
private lemma crossCorrPerm00_val (j : Fin ((3 + 0) + (2 + 0))) :
    ((crossCorrPerm 0 0) j).val =
      if j.val < 3 then 1 + j.val else if j.val = 3 then 0 else 4 := by
  by_cases h3 : j.val < 3
  · rw [show j = Fin.castAdd (2 + 0) (⟨j.val, h3⟩ : Fin (3 + 0)) from Fin.ext rfl,
      crossCorrPerm_castAdd 0 0]
    simp only [Fin.val_castAdd]
    rw [if_pos h3]
  · have hjlt : j.val < 5 := j.isLt
    rw [show j = Fin.natAdd (3 + 0) (⟨j.val - 3, by omega⟩ : Fin (2 + 0)) from
      Fin.ext (by simp only [Fin.val_natAdd]; omega),
      crossCorrPerm_natAdd 0 0]
    simp only [Fin.val_natAdd]
    by_cases h4 : j.val - 3 = 0
    · rw [if_pos h4, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h4, if_neg (by omega), if_neg (by omega)]
      omega

set_option linter.unusedSectionVars false in
/-- Last-slot grouping of a `Fin ((3 + 0 + 0) + p)` index sum. -/
private lemma sum_index_lastSlot_group' {n p : ℕ} (f : (Fin ((3 + 0 + 0) + p) → Fin n) → ℝ) :
    (∑ J : Fin ((3 + 0 + 0) + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        f (fun k : Fin ((3 + 0 + 0) + p) =>
          (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.snocEquiv (fun _ : Fin ((2 + p) + 1) => Fin n)).trans
      (Equiv.arrowCongr (finCongr (by omega : (2 + p) + 1 = (3 + 0 + 0) + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, finCongr_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- Middle-slot (position `p`) grouping of a `Fin ((3 + 0) + p)` index sum. -/
private lemma sum_index_midSlot_group {n p : ℕ} (f : (Fin ((3 + 0) + p) → Fin n) → ℝ) :
    (∑ J : Fin ((3 + 0) + p) → Fin n, f J) =
      ∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        f (fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((Fin.insertNthEquiv (fun _ : Fin ((2 + p) + 1) => Fin n) ⟨p, by omega⟩).trans
      (Equiv.arrowCongr (finCongr (by omega : (2 + p) + 1 = (3 + 0) + p)) (Equiv.refl (Fin n))))
    _ _ ?_).symm
  intro pr
  simp only [Equiv.trans_apply, finCongr_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- The unit-model value of the keystone's slot-permuted bare-product argument: the `Z`-factor
reads the (val-identity) leading `3 + p` product slots through the keystone permutation, the
realized-perturbation factor the trailing `2`. -/
private lemma keystoneArg_unit_toModel (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₁ : SmoothCcTensor g₀ 0 2) (Z : SmoothCcTensor g₀ 0 ((3 + 0) + p)) (x : M)
    (u : Fin (((3 + 0) + (2 + 0)) + p) → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (((3 + 0) + (2 + 0)) + p) I x from
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        u =
      ccUnitModel (I := I) g₀ Z x
          (fun t : Fin ((3 + 0) + p) =>
            u (leadExtPerm (crossCorrPerm 0 0) p
              (⟨t.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p)))) *
        ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
          (fun l : Fin (2 + 0) =>
            u (leadExtPerm (crossCorrPerm 0 0) p
              (⟨((3 + 0) + p) + l.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p)))) := by
  classical
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (((3 + 0) + (2 + 0)) + p) I x from
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      = Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ (((3 + 0) + (2 + 0)) + p)
          (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p)
            (castRankCc_db g₀ 0 (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
              ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
                (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
                (realizeSymmCcTensor (I := I) g₀ T₁)))) x from rfl]
  rw [permuteCcTensor_unitModel (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p) _ x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_castRankCc_db_local (I := I) g₀
    (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p) _ x]
  rw [show (bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
        (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
        (realizeSymmCcTensor (I := I) g₀ T₁)
      = castRankCc_db g₀ 0 (by omega : (3 + (0 + p)) + (2 + 0) = (3 + 2) + (0 + p) + 0)
          (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) g₀
            (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
            (realizeSymmCcTensor (I := I) g₀ T₁)) from rfl]
  rw [unitModel_castRankCc_db_local (I := I) g₀
    (by omega : (3 + (0 + p)) + (2 + 0) = (3 + 2) + (0 + p) + 0) _ x]
  rw [Analysis.Parabolic.TensorSpectral.unitModelProdSection_unitModel (I := I) g₀
    (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
    (realizeSymmCcTensor (I := I) g₀ T₁) x]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [unitModel_castRankCc_db_local (I := I) g₀ (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z x]
  rw [show Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ ((3 + 0) + p) Z x
      = ccUnitModel (I := I) g₀ Z x from rfl]
  rw [show Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ (2 + 0)
        (realizeSymmCcTensor (I := I) g₀ T₁) x
      = ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x from rfl]
  congr 1
  congr 1
  funext t
  refine congrArg u (congrArg (leadExtPerm (crossCorrPerm 0 0) p) (Fin.ext ?_))
  simp only [Fin.val_cast, Fin.val_natAdd]
  omega

set_option linter.unusedSectionVars false in
/-- Evaluation of `vecAppend q w` below the passenger threshold. -/
private lemma vecAppend_lt_eval {α : Type*} {r p : ℕ} (q : Fin p → α) (w : Fin r → α)
    (k : Fin (r + p)) (hk : k.val < p) :
    Matrix.vecAppend (by omega : r + p = p + r) q w k = q ⟨k.val, hk⟩ := by
  simp only [Matrix.vecAppend_eq_ite]
  rw [dif_pos hk]

set_option linter.unusedSectionVars false in
/-- Evaluation of `vecAppend q w` on the `w`-block. -/
private lemma vecAppend_natAdd_eval {α : Type*} {r p : ℕ} (q : Fin p → α) (w : Fin r → α)
    (j : Fin r) :
    Matrix.vecAppend (by omega : r + p = p + r) q w
        (Fin.cast (by omega : p + r = r + p) (Fin.natAdd p j)) = w j := by
  simp only [Matrix.vecAppend_eq_ite]
  rw [dif_neg (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
  apply congrArg
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd]
  omega

set_option linter.unusedSectionVars false in
/-- Leading-slot evaluation of the double-`cons` model tuple. -/
private lemma consPair_eval_zero {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (hi : i.val = 0) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = A := by
  rw [show i = (0 : Fin (s2 + 2)) from Fin.ext (by rw [Fin.val_zero]; exact hi)]
  rw [show (0 : Fin (s2 + 2)) = (0 : Fin ((s2 + 1) + 1)) from rfl, Fin.cons_zero]

set_option linter.unusedSectionVars false in
/-- Second-slot evaluation of the double-`cons` model tuple. -/
private lemma consPair_eval_one {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (hi : i.val = 1) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = B := by
  rw [show i = Fin.succ (0 : Fin (s2 + 1)) from Fin.ext (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
  rw [Fin.cons_succ, Fin.cons_zero]

set_option linter.unusedSectionVars false in
/-- Tail evaluation of the double-`cons` model tuple. -/
private lemma consPair_eval_tail {s2 : ℕ} (A B : E) (m : Fin s2 → E) (i : Fin (s2 + 2))
    (l : Fin s2) (hi : i.val = 2 + l.val) :
    (Fin.cons A (Fin.cons B m) : Fin (s2 + 2) → E) i = m l := by
  rw [show i = Fin.succ (Fin.succ l) from Fin.ext (by simp only [Fin.val_succ]; omega)]
  rw [Fin.cons_succ, Fin.cons_succ]


set_option linter.unusedSectionVars false in
/-- The keystone `Z`-factor tuple identity: through the lead-extended cross-correction
permutation, the bare-product `Z`-block reads the passenger slots, the model-basis vector in the
contracted (position-`p`) slot, and the two following frame slots — the `insertNth` slice tuple. -/
private lemma keystone_tupleZ_eval (x : M) {nn p : ℕ} (e : Fin nn → TangentSpace I x)
    (J : Fin ((3 + 0 + 0) + p) → Fin nn) (A B : E) :
    (fun t : Fin ((3 + 0) + p) =>
      Matrix.vecAppend (by omega : ((3 + 0) + (2 + 0)) + p = p + ((3 + 0) + (2 + 0)))
          (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
          (fun i : Fin ((3 + 0) + (2 + 0)) =>
            (Fin.cons A (Fin.cons B
                (fun l : Fin (3 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E))) :
              Fin ((3 + 0 + 0) + 2) → E)
              (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2) i))
        (leadExtPerm (crossCorrPerm 0 0) p
          (⟨t.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p))))
    = fun t : Fin ((3 + 0) + p) =>
        (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) B
          (fun j : Fin (2 + p) => (e (J ⟨j.val, by omega⟩) : E)) : Fin ((2 + p) + 1) → E)
          (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t) := by
  funext t
  by_cases ht : t.val < p
  · rw [leadExtPerm_apply_of_lt (crossCorrPerm 0 0) p
      (⟨t.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p)) ht]
    rw [vecAppend_lt_eval _ _ (⟨t.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p)) ht]
    have hsa : (⟨p, by omega⟩ : Fin ((2 + p) + 1)).succAbove (⟨t.val, by omega⟩ : Fin (2 + p))
        = finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        exact ht)]
      exact Fin.ext (by simp only [Fin.val_castSucc, finCongr_apply, Fin.val_cast])
    rw [← hsa, Fin.insertNth_apply_succAbove]
  · rw [show (⟨t.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((3 + 0) + (2 + 0)) = ((3 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨t.val - p, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)]
    rw [leadExtPerm_apply_natAdd (crossCorrPerm 0 0) p
      (⟨t.val - p, by omega⟩ : Fin ((3 + 0) + (2 + 0)))]
    rcases (by omega : t.val - p = 0 ∨ t.val - p = 1 ∨ t.val - p = 2) with h0 | h1 | h2
    · rw [show (⟨t.val - p, by omega⟩ : Fin ((3 + 0) + (2 + 0))) = ⟨0, by omega⟩ from Fin.ext h0]
      rw [show (crossCorrPerm 0 0) (⟨0, by omega⟩ : Fin ((3 + 0) + (2 + 0)))
          = (⟨1, by omega⟩ : Fin ((3 + 0) + (2 + 0))) from
        Fin.ext (by rw [crossCorrPerm00_val]; rfl)]
      rw [vecAppend_natAdd_eval]
      rw [consPair_eval_one A B _
        (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2)
          (⟨1, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) rfl]
      rw [show finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t
          = (⟨p, by omega⟩ : Fin ((2 + p) + 1)) from
        Fin.ext (by simp only [finCongr_apply, Fin.val_cast]; omega)]
      rw [Fin.insertNth_apply_same]
    · rw [show (⟨t.val - p, by omega⟩ : Fin ((3 + 0) + (2 + 0))) = ⟨1, by omega⟩ from Fin.ext h1]
      rw [show (crossCorrPerm 0 0) (⟨1, by omega⟩ : Fin ((3 + 0) + (2 + 0)))
          = (⟨2, by omega⟩ : Fin ((3 + 0) + (2 + 0))) from
        Fin.ext (by rw [crossCorrPerm00_val]; rfl)]
      rw [vecAppend_natAdd_eval]
      rw [consPair_eval_tail A B _
        (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2)
          (⟨2, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) (⟨0, by omega⟩ : Fin (3 + 0 + 0)) rfl]
      have hsa : (⟨p, by omega⟩ : Fin ((2 + p) + 1)).succAbove (⟨p, by omega⟩ : Fin (2 + p))
          = finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.val_castSucc]; omega)]
        exact Fin.ext (by simp only [Fin.val_succ, finCongr_apply, Fin.val_cast]; omega)
      rw [← hsa, Fin.insertNth_apply_succAbove]
      exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change p + 0 = p; omega))
    · rw [show (⟨t.val - p, by omega⟩ : Fin ((3 + 0) + (2 + 0))) = ⟨2, by omega⟩ from Fin.ext h2]
      rw [show (crossCorrPerm 0 0) (⟨2, by omega⟩ : Fin ((3 + 0) + (2 + 0)))
          = (⟨3, by omega⟩ : Fin ((3 + 0) + (2 + 0))) from
        Fin.ext (by rw [crossCorrPerm00_val]; rfl)]
      rw [vecAppend_natAdd_eval]
      rw [consPair_eval_tail A B _
        (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2)
          (⟨3, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) (⟨1, by omega⟩ : Fin (3 + 0 + 0)) rfl]
      have hsa : (⟨p, by omega⟩ : Fin ((2 + p) + 1)).succAbove
            (⟨p + 1, by omega⟩ : Fin (2 + p))
          = finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.val_castSucc]; omega)]
        exact Fin.ext (by simp only [Fin.val_succ, finCongr_apply, Fin.val_cast]; omega)
      rw [← hsa, Fin.insertNth_apply_succAbove]

set_option linter.unusedSectionVars false in
/-- The keystone realized-perturbation tuple identity: through the lead-extended cross-correction
permutation, the perturbation block reads the cometric-raised covector and the last frame slot. -/
private lemma keystone_tupleS_eval (x : M) {nn p : ℕ} (e : Fin nn → TangentSpace I x)
    (J : Fin ((3 + 0 + 0) + p) → Fin nn) (A B : E) :
    (fun l : Fin (2 + 0) =>
      Matrix.vecAppend (by omega : ((3 + 0) + (2 + 0)) + p = p + ((3 + 0) + (2 + 0)))
          (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
          (fun i : Fin ((3 + 0) + (2 + 0)) =>
            (Fin.cons A (Fin.cons B
                (fun l2 : Fin (3 + 0 + 0) => (e (J ⟨p + l2.val, by omega⟩) : E))) :
              Fin ((3 + 0 + 0) + 2) → E)
              (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2) i))
        (leadExtPerm (crossCorrPerm 0 0) p
          (⟨((3 + 0) + p) + l.val, by omega⟩ : Fin (((3 + 0) + (2 + 0)) + p))))
    = ![A, (e (J ⟨2 + p, by omega⟩) : E)] := by
  funext l
  rcases (by omega : l.val = 0 ∨ l.val = 1) with hl | hl
  · rw [show l = (0 : Fin (2 + 0)) from Fin.ext (by rw [Fin.val_zero]; exact hl)]
    rw [show (⟨((3 + 0) + p) + (0 : Fin (2 + 0)).val, by omega⟩ :
          Fin (((3 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((3 + 0) + (2 + 0)) = ((3 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨3, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega)]
    rw [leadExtPerm_apply_natAdd (crossCorrPerm 0 0) p (⟨3, by omega⟩ : Fin ((3 + 0) + (2 + 0)))]
    rw [show (crossCorrPerm 0 0) (⟨3, by omega⟩ : Fin ((3 + 0) + (2 + 0)))
        = (⟨0, by omega⟩ : Fin ((3 + 0) + (2 + 0))) from
      Fin.ext (by rw [crossCorrPerm00_val]; rfl)]
    rw [vecAppend_natAdd_eval]
    rw [consPair_eval_zero A B _
      (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2)
        (⟨0, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) rfl]
    rw [Matrix.cons_val_zero]
  · rw [show l = (1 : Fin (2 + 0)) from Fin.ext (by rw [Fin.val_one]; exact hl)]
    rw [show (⟨((3 + 0) + p) + (1 : Fin (2 + 0)).val, by omega⟩ :
          Fin (((3 + 0) + (2 + 0)) + p))
        = Fin.cast (by omega : p + ((3 + 0) + (2 + 0)) = ((3 + 0) + (2 + 0)) + p)
            (Fin.natAdd p (⟨4, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_one]; omega)]
    rw [leadExtPerm_apply_natAdd (crossCorrPerm 0 0) p (⟨4, by omega⟩ : Fin ((3 + 0) + (2 + 0)))]
    rw [show (crossCorrPerm 0 0) (⟨4, by omega⟩ : Fin ((3 + 0) + (2 + 0)))
        = (⟨4, by omega⟩ : Fin ((3 + 0) + (2 + 0))) from
      Fin.ext (by rw [crossCorrPerm00_val]; rfl)]
    rw [vecAppend_natAdd_eval]
    rw [consPair_eval_tail A B _
      (finCongr (by omega : (3 + 0) + (2 + 0) = (3 + 0 + 0) + 2)
        (⟨4, by omega⟩ : Fin ((3 + 0) + (2 + 0)))) (⟨2, by omega⟩ : Fin (3 + 0 + 0)) rfl]
    rw [show ((![A, (e (J ⟨2 + p, by omega⟩) : E)] : Fin 2 → E) (1 : Fin (2 + 0)))
        = (e (J ⟨2 + p, by omega⟩) : E) from rfl]
    beta_reduce
    exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change p + 2 = 2 + p; omega))

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The sharp `δ²` passenger fibre bound of the keystone product-level top cell.**
Under the `g₀`-fibre operator bound `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, the intrinsic
squared fibre norm of the keystone top cell `crossCorrKeystoneTop g₀ p T₁ Z` is dominated *sharply*
— with the operator-norm constant `δ²`, NO dimension factor, NO envelope constant, uniformly in the
passenger order `p` — by that of the jet factor `Z`:
`rfns(crossCorrKeystoneTop g₀ p T₁ Z)(x) ≤ δ² · rfns(Z)(x)`.

This is the keystone-layout sibling of the proven section-level passenger bound
`crossCorrParallelContraction_rfns_le_sq_passenger`: the keystone traces the realized perturbation
`h = ccTensorBilinSymm g₀ T₁` (fibre operator norm `≤ δ`) through the `g₀`-cometric against the
factor's ORIGINAL contraction slot (sitting after the `p` spectator gradient slots), instead of the
leading slot.  The same frame-Riesz Parseval argument applies with the slice-Riesz vector built on
the keystone's contracted slot: the contraction's frame component at a tuple is the pairing
`h(W, e c)` of the slot-Riesz reconstruction `W` of the corresponding slice functional of `Z`
(`slotExtendPow_toModel_consSlots` reads the `p` spectators off; `passengerCurry` exposes the inner
contraction), bounded by `gFibreOpBound_dualFrame_sq_sum_le` and frame Parseval exactly as in the
proven sibling.

**Why this sharp bound is load-bearing.**  The `δ < 1/2`-uniform differentiated-Koszul recursion
(`4 − 8δ > 0` exactly on `δ < 1/2`) has NO slack for any constant `> 1` on the top cell: a top arm
`c·δ²·‖∇^p D‖²` with `c > 1` forces `δ < 1/(2√c)`, and the former envelope route
(`c = n²·C_env(p)`, `p`-dependent) is precisely the deleted antitone-threshold disease.  Proved by
the frame-Riesz mirror at the keystone slot layout: `slotExtendPow_toModel_consSlots` reads the `p`
spectator slots off, `passengerCurry_toModel` and `keystoneArg_unit_toModel` expose the inner
contraction's frame component at a tuple as the pairing `h(W, e c)` of the slot-Riesz
reconstruction `W` of the position-`p` slice functional of `Z` (`keystone_tupleZ_eval`,
`keystone_tupleS_eval`), and the middle-slot regrouping (`sum_index_midSlot_group`) closes the
Parseval argument through `gFibreOpBound_dualFrame_sq_sum_le` exactly as in the proven sibling.

**Non-vacuity.**  At `T₁ = 0` both sides are `0`; for `T₁` with `h ≠ 0` the keystone cell is
genuinely nonzero on generic `Z` (the cometric trace is the genuine single contraction
`crossCorrModelFun`), so the bound carries genuine content and a smaller-than-`δ²` constant is
falsified by a rank-one `h` aligned with `Z`'s contracted slot. -/
theorem crossCorrKeystoneTop_rfns_le_sq_passenger
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 ((3 + 0) + p)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + p) x
        ((crossCorrKeystoneTop (I := I) g₀ p T₁ Z).toSection x) ≤
      δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0) + p) x (Z.toSection x) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hreprS⟩ :=
    Integral.Connection.tangent_orthonormalBasisS_witness (I := I) (M := M) g₀ (3 + p) x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The slice functional of `Z` at the contracted (position-`p`) slot, as a CLM.
  set leadFun : (Fin (2 + p) → Fin n) → (TangentSpace I x →L[ℝ] ℝ) := fun J' =>
    ContinuousMultilinearMap.toContinuousLinearMap (ccUnitModel (I := I) g₀ Z x)
      (fun k : Fin ((3 + 0) + p) =>
        (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) (0 : E)
          (fun j : Fin (2 + p) => (e (J' j) : E)) : Fin ((2 + p) + 1) → E)
          (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k))
      (finCongr (by omega : (2 + p) + 1 = (3 + 0) + p) (⟨p, by omega⟩ : Fin ((2 + p) + 1)))
    with hleadFun_def
  have hleadFun_apply : ∀ (J' : Fin (2 + p) → Fin n) (u : TangentSpace I x),
      leadFun J' u = ccUnitModel (I := I) g₀ Z x
        (fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) (u : E)
            (fun j : Fin (2 + p) => (e (J' j) : E)) : Fin ((2 + p) + 1) → E)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) := by
    intro J' u
    rw [hleadFun_def]
    change (ContinuousMultilinearMap.toContinuousLinearMap (ccUnitModel (I := I) g₀ Z x)
        (fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) (0 : E)
            (fun j : Fin (2 + p) => (e (J' j) : E)) : Fin ((2 + p) + 1) → E)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k))
        (finCongr (by omega : (2 + p) + 1 = (3 + 0) + p)
          (⟨p, by omega⟩ : Fin ((2 + p) + 1)))) u = _
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext k
    rcases eq_or_ne k (finCongr (by omega : (2 + p) + 1 = (3 + 0) + p)
        (⟨p, by omega⟩ : Fin ((2 + p) + 1))) with hk | hk
    · rw [hk, Function.update_self]
      rw [show (finCongr (by omega : (3 + 0) + p = (2 + p) + 1)
            (finCongr (by omega : (2 + p) + 1 = (3 + 0) + p)
              (⟨p, by omega⟩ : Fin ((2 + p) + 1)))) = (⟨p, by omega⟩ : Fin ((2 + p) + 1)) from
        Fin.ext (by simp)]
      rw [Fin.insertNth_apply_same]
    · rw [Function.update_of_ne hk]
      have hne : (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)
          ≠ (⟨p, by omega⟩ : Fin ((2 + p) + 1)) := by
        intro hc
        apply hk
        apply Fin.ext
        have := congrArg Fin.val hc
        simpa [Fin.val_cast] using this
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hne
      rw [← hj', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  -- The slice-Riesz vector and its two reconstruction facts.
  set W : (Fin (2 + p) → Fin n) → TangentSpace I x := fun J' =>
    ∑ c : Fin n, leadFun J' (e c) • e c with hW_def
  have hWfacts : ∀ J' : Fin (2 + p) → Fin n,
      (∀ u : TangentSpace I x, g₀.inner x (W J') u = leadFun J' u) ∧
        g₀.inner x (W J') (W J') = ∑ c : Fin n, (leadFun J' (e c)) ^ 2 := by
    intro J'
    rw [hW_def]
    exact frameRiesz_pair_and_normSq (I := I) g₀ x e horth hexpand (leadFun J')
  -- Frame expansion of both sides.
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x
      ((3 + 0 + 0) + p) e hreprS ((crossCorrKeystoneTop (I := I) g₀ p T₁ Z).toSection x) K₀,
    Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x
      ((3 + 0) + p) e hreprS (Z.toSection x) K₀]
  -- The keystone frame component at a tuple `J`.
  have hCcomp : ∀ J : Fin ((3 + 0 + 0) + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 ((3 + 0 + 0) + p)
          ((crossCorrKeystoneTop (I := I) g₀ p T₁ Z).toSection x) n e K₀ J =
        ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨2 + p, by omega⟩)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ ((3 + 0 + 0) + p) x e K₀ J
      ((crossCorrKeystoneTop (I := I) g₀ p T₁ Z).toSection x)]
    rw [show crossCorrKeystoneTop (I := I) g₀ p T₁ Z
        = appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
            (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
              (crossCorrCometricOp (I := I) g₀ 0 0))
            (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm (crossCorrPerm 0 0) p)
              (castRankCc_db g₀ 0
                  (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
                ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0 + p) (b := 0)
                  (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p)) Z)
                  (realizeSymmCcTensor (I := I) g₀ T₁)))) from rfl]
    rw [appCcRS_toSection (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)]
    rw [ContinuousLinearMap.comp_apply]
    rw [show (fun k : Fin ((3 + 0 + 0) + p) => (e (J k) : E))
        = Matrix.vecAppend (by omega : (3 + 0 + 0) + p = p + (3 + 0 + 0))
            (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
            (fun l : Fin (3 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E)) from by
      funext k
      simp only [Matrix.vecAppend_eq_ite]
      by_cases hk : k.val < p
      · rw [dif_pos hk]
      · rw [dif_neg hk]
        exact congrArg (fun z => (e (J z) : E)) (Fin.ext (by change k.val = p + (k.val - p); omega))]
    rw [slotExtendPow_toModel_consSlots (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) x
      (crossCorrCometricOp (I := I) g₀ 0 0) p _
      (fun j : Fin p => (e (J ⟨j.val, by omega⟩) : E))
      (fun l : Fin (3 + 0 + 0) => (e (J ⟨p + l.val, by omega⟩) : E))]
    rw [crossCorrCometricOp_toSection_toModel (I := I) g₀ 0 0 x _]
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply
      (3 + 0 + 0) (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel
        (I := I) g₀ x) _ _]
    rw [show DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel
          (I := I) g₀ x = cometricReadingModel (I := I) g₀ x from rfl]
    simp only [modelRankCast_apply_local, passengerCurry_toModel]
    simp only [keystoneArg_unit_toModel (I := I) g₀ p T₁ Z x]
    simp only [keystone_tupleZ_eval (I := I) x e J, keystone_tupleS_eval (I := I) x e J]
    have hSfac : ∀ w₁ w₂ : TangentSpace I x,
        ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ![(w₁ : E), (w₂ : E)]
          = ccTensorBilinSymm (I := I) g₀ T₁ x w₁ w₂ := by
      intro w₁ w₂
      rw [← realizeSymmCcTensor_ccTensorBilin_apply, ccTensorBilin_apply]
      rfl
    have hper : ∀ kk : Fin (Module.finrank ℝ E),
        ccUnitModel (I := I) g₀ Z x
            (fun t : Fin ((3 + 0) + p) =>
              (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1))
                ((Module.finBasis ℝ E) kk : E)
                (fun j : Fin (2 + p) => (e (J ⟨j.val, by omega⟩) : E)) :
                  Fin ((2 + p) + 1) → E)
                (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) t)) *
          ccUnitModel (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
            ![(cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)) : E),
              (e (J ⟨2 + p, by omega⟩) : E)]
        = leadFun (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) kk) *
            ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              (e (J ⟨2 + p, by omega⟩)) := by
      intro kk
      rw [hleadFun_apply (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)
        ((Module.finBasis ℝ E) kk)]
      rw [hSfac]
    rw [Finset.sum_congr rfl (fun kk _ => hper kk)]
    set φ : TangentSpace I x →L[ℝ] ℝ := (ccTensorBilinSymm (I := I) g₀ T₁ x).flip
      (e (J ⟨2 + p, by omega⟩)) with hφ_def
    rw [show (∑ kk : Fin (Module.finrank ℝ E),
          leadFun (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩) ((Module.finBasis ℝ E) kk) *
            ccTensorBilinSymm (I := I) g₀ T₁ x
              (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              (e (J ⟨2 + p, by omega⟩)))
        = ∑ kk : Fin (Module.finrank ℝ E),
            φ (cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis kk)))
              * g₀.inner x (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩))
                  ((Module.finBasis ℝ E) kk) from by
      refine Finset.sum_congr rfl (fun kk _ => ?_)
      rw [hφ_def, ContinuousLinearMap.flip_apply, mul_comm]
      congr 1
      rw [(hWfacts (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)).1 ((Module.finBasis ℝ E) kk)]]
    rw [sum_phi_cometric_inner_basis (I := I) g₀ x
      (fun i => cometricReadingModel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis i)))
      (fun k u => cometricReadingModel_dualBasis_inner (I := I) g₀ x k u)
      φ (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩))]
    rfl
  -- The `Z` frame component at a tuple `J`.
  have hZcomp : ∀ J : Fin ((3 + 0) + p) → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 ((3 + 0) + p)
          (Z.toSection x) n e K₀ J = ccUnitModel (I := I) g₀ Z x (fun k => e (J k)) := by
    intro J
    rw [componentS_zero_eq_unit_local (I := I) g₀ ((3 + 0) + p) x e K₀ J (Z.toSection x)]
    rfl
  simp only [hCcomp, hZcomp]
  -- Group the LHS by the LAST slot.
  rw [sum_index_lastSlot_group' (n := n) (p := p)
    (fun J : Fin ((3 + 0 + 0) + p) → Fin n =>
      ccTensorBilinSymm (I := I) g₀ T₁ x
        (W (fun j : Fin (2 + p) => J ⟨j.val, by omega⟩)) (e (J ⟨2 + p, by omega⟩)) ^ 2)]
  have hLslice : ∀ (c : Fin n) (J' : Fin (2 + p) → Fin n),
      ccTensorBilinSymm (I := I) g₀ T₁ x
          (W (fun j : Fin (2 + p) =>
            (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
              (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1) ⟨j.val, by omega⟩)))
          (e ((Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1) ⟨2 + p, by omega⟩))) ^ 2
        = ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2 := by
    intro c J'
    have hsliceArg : (fun j : Fin (2 + p) =>
          (Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1) ⟨j.val, by omega⟩)) = J' := by
      funext j
      rw [show (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1)
            (⟨j.val, by omega⟩ : Fin ((3 + 0 + 0) + p)))
            = Fin.castSucc (n := 2 + p) j from by apply Fin.ext; simp, Fin.snoc_castSucc]
    have hsliceLast : ((Fin.snoc J' c : Fin ((2 + p) + 1) → Fin n)
          (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1) ⟨2 + p, by omega⟩)) = c := by
      rw [show (finCongr (by omega : (3 + 0 + 0) + p = (2 + p) + 1)
            (⟨2 + p, by omega⟩ : Fin ((3 + 0 + 0) + p)))
            = Fin.last (2 + p) from by apply Fin.ext; simp, Fin.snoc_last]
    rw [hsliceArg, hsliceLast]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun J' _ => hLslice c J'))]
  rw [Finset.sum_comm]
  -- Group the RHS (`Z`'s frame components) by the MIDDLE (position-`p`) slot.
  rw [sum_index_midSlot_group (n := n) (p := p)
    (fun J : Fin ((3 + 0) + p) → Fin n =>
      (ccUnitModel (I := I) g₀ Z x (fun k => e (J k))) ^ 2)]
  have hRslice : ∀ (c : Fin n) (J' : Fin (2 + p) → Fin n),
      (ccUnitModel (I := I) g₀ Z x (fun k => e ((fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) k))) ^ 2
        = (leadFun J' (e c)) ^ 2 := by
    intro c J'
    rw [hleadFun_apply J' (e c)]
    have hsliceArg : (fun k : Fin ((3 + 0) + p) => (e ((fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) k) : E))
        = (fun k : Fin ((3 + 0) + p) =>
            (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) ((e c : TangentSpace I x) : E)
              (fun j : Fin (2 + p) => (e (J' j) : E)) : Fin ((2 + p) + 1) → E)
              (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) := by
      funext k
      beta_reduce
      rcases eq_or_ne (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)
          (⟨p, by omega⟩ : Fin ((2 + p) + 1)) with hk | hk
      · rw [hk, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hk
        rw [← hj', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    rw [hsliceArg]
  rw [show (∑ c : Fin n, ∑ J' : Fin (2 + p) → Fin n,
        (ccUnitModel (I := I) g₀ Z x (fun k => e ((fun k : Fin ((3 + 0) + p) =>
          (Fin.insertNth (⟨p, by omega⟩ : Fin ((2 + p) + 1)) c J' : Fin ((2 + p) + 1) → Fin n)
            (finCongr (by omega : (3 + 0) + p = (2 + p) + 1) k)) k))) ^ 2)
      = ∑ J' : Fin (2 + p) → Fin n, ∑ c : Fin n, (leadFun J' (e c)) ^ 2 from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun J' _ => Finset.sum_congr rfl (fun c _ => hRslice c J'))]
  -- Both sides grouped by `J'`; bound each slice sharply.
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun J' _ => ?_)
  have hcross_inner :
      (∑ c : Fin n, ccTensorBilinSymm (I := I) g₀ T₁ x (W J') (e c) ^ 2) ≤
        δ ^ 2 * g₀.inner x (W J') (W J') :=
    gFibreOpBound_dualFrame_sq_sum_le (I := I) g₀ x e horth hpars
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hδ (W J')
  rw [(hWfacts J').2] at hcross_inner
  exact hcross_inner

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The `t`-scaled Gagliardo–Nirenberg integrated *peeled* bound on the cross-correction
`Rest` arm, in the realized-perturbation factor.**  The squared metric `L²` mass of the
**rest** cell of the order-`p` cross-correction jet — the difference
`∇^p (crossCorrectionSection g₁ g₀ T₁) − crossCorrKeystoneTop g₀ p T₁ (∇^p (permute c[0,1,2] D))`,
with the keystone top the honest `i = 0` binomial cell (all `p` derivatives on the
connection-difference factor, in the contraction's own slot layout) — is dominated, for every free
scale `t ∈ (0, 1]`, by
```
‖∇^p cc − KeystoneTop_p‖²
  ≤ t · δ² · ‖∇^p loweredConnDiffSection‖²
    + Cpk · (1/t)^p · (∑_{q < p} ‖∇^q loweredConnDiffSection‖² + ∑_{i ≤ p+1} ‖∇^i (realizeSymm T₁)‖²),
```
uniformly over the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{p+3+a}`-bounded (`2a > finrank + 4`) perturbation family.

**Why the top re-emission carries the free scale `t`.**  The strict-window form (no `‖∇^p D‖²` term
at all) is **FALSE for `p ≥ 4`**: the mixed binomial cells `∇^i h ⊛ ∇^{p−i} D` (`i ≥ 1`)
Gagliardo–Nirenberg-interpolate at the cell diagonal and **re-emit** the top jet `‖∇^p D‖²` — but
only with the **fractional power `2(p−i)/p < 2`**, so the scaled Young split
(`exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le`) prices the re-emission at the
free `t·δ²`, the engine constants paying `(1/t)^p` on the lower-order remainder.  The former named
fixed-coefficient emission `K(p)·δ²·‖∇^p D‖²` (and the antitone threshold `δ < δ₀(p) ~ 4^{-p}`
pinned to absorb it) is DELETED: it was incompatible with every fixed-`δ` all-order consumer.

It assembles from: (1) the operator-reduced iterated covariant Leibniz
`crossCorrectionSection_iteratedCovGrad_eq_appCcRS_slotExtendPow` — `∇^p cc` is the slot-extended
parallel cometric operator applied to `∇^p` of the bare product; the keystone top is the same
operator on the product-level top cell, so the REST is a single operator action on the peeled
product difference; (2) the pointwise peeled binomial-Leibniz `rfns` grid
`RfnsBilinearProduct.rfns_iteratedCovGrad_prod_topRest_le_peeledDiagGrid` (constant `4^p`), pushed
through the `appCcRS` fibre envelope (`crossCorrEnvelopeConst`); (3) the grid split into the
strictly-sub-diagonal window (the symmetric two-arm engine
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` at window `p − 1`, all arms
lower-order) plus the anti-diagonal `i + l = p` cells (the `t`-scaled top-arm engine), with the
fibre-small `C⁰` sup of `w = realizeSymm T₁` (`rfns(w)(x) ≤ n²δ²`, sharp from `gFibreOpBound`) and
the Neumann-absorbed `C⁰` sup of `D` (`exists_loweredConnDiff_rfns_fibre_sup`, gated by the
supercritical jet embedding, `2a > finrank + 4`, `δ < 1/2`).

**Non-vacuity.**  The bound carries genuine content on the strictly-lower connection-difference
jets, the realized-perturbation jets, and the `t`-scaled re-emitted top jet.  At `T₁ = 0` the
difference is `0` and the bound is `0 ≤ 0`; at `p = 0` the rest cell vanishes identically (the
peeled grid is empty) and the bound is trivial. -/
theorem crossCorrectionSection_iteratedCovGrad_rest_peel_realizeSymm_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (crossCorrectionSection (I := I) g₁ g₀ T₁)
              - crossCorrKeystoneTop (I := I) g₀ p T₁
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p
                    (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                      (loweredConnDiffSection (I := I) g₁ g₀)))‖ ^ 2 ≤
          t * δ ^ 2 *
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
            + Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := by
  classical
  have hδhalf : δ < 1 / 2 := hδ1
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  obtain ⟨hCenv0, hCenvB⟩ := crossCorrEnvelopeConst_spec (I := I) g₀ p
  -- The strictly-sub-diagonal symmetric engine (window `p − 1`) and the anti-diagonal scaled engine.
  obtain ⟨cGlow, hcGlow0, hGNlow⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
      (I := I) (M := M) g₀ 3 2 (p - 1)
  obtain ⟨cAnti, hcAnti0, hAnti⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le
      (I := I) (M := M) g₀ 3 2 p
  obtain ⟨ΛD, hΛD0, hΛD⟩ :=
    exists_loweredConnDiff_rfns_fibre_sup (I := I) g₀ hδ0 hδhalf B a ha
  set nE : ℝ := (Module.finrank ℝ E : ℝ) with hnE
  have hnE0 : 0 ≤ nE := by rw [hnE]; positivity
  set cE := crossCorrEnvelopeConst (I := I) g₀ p with hcE
  -- The internal rescale denominator of the anti-diagonal top arm.
  set Ar : ℝ := cE * 4 ^ p * nE ^ 2 + 1 with hAr
  have hAr1 : (1 : ℝ) ≤ Ar := by
    rw [hAr]
    have : (0 : ℝ) ≤ cE * 4 ^ p * nE ^ 2 := by positivity
    linarith
  have hAr0 : (0 : ℝ) < Ar := lt_of_lt_of_le zero_lt_one hAr1
  refine ⟨cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) + cAnti * Ar ^ p * ΛD ^ 2),
    by positivity, ?_⟩
  intro t ht0 ht1 T₁ g₁ hr hfib hball
  have hball_a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖ ≤ B :=
    le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ p + 3 + a) T₁) hball
  -- Abbreviations (set-folded into the goal).
  set D := loweredConnDiffSection (I := I) g₁ g₀ with hDd
  set wS := realizeSymmCcTensor (I := I) g₀ T₁ with hwS
  set Tt := PDE.DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D with hTtd
  set Xp := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (crossCorrectionSection (I := I) g₁ g₀ T₁) with hXpd
  set Φb := bareTensorRfnsBilinearProduct (I := I) g₀ 3 2 with hΦbd
  set Φp := slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (crossCorrCometricOp (I := I) g₀ 0 0) with hΦpd
  set U := Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
      (p := 3 + 0) (q := 2 + 0) g₀ Tt wS with hUd
  set TopU := castRankCc_db g₀ 0
      (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
      (Φb.prod (a := 0 + p) (b := 0)
        (castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p))
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Tt)) wS) with hTopUd
  set σcc := crossCorrPerm 0 0 with hσccd
  set Ztop := PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p) TopU with hZtopd
  set Ap := crossCorrKeystoneTop (I := I) g₀ p T₁
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Tt) with hApd
  -- The keystone top is the slot-extended operator on the permuted product-level top cell.
  have hApeq : Ap =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p) Φp Ztop := rfl
  -- (1) The operator-reduced iterated Leibniz: `∇^p cc = appCcRS Φp (∇^p P)`.
  have hXeq : Xp =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p) Φp
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Tt)) :=
    crossCorrectionSection_iteratedCovGrad_eq_appCcRS_slotExtendPow (I := I) g₀ g₁ T₁ p
  -- (2) The product section is the slot-permuted bare product.
  have hPU : crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Tt =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ σcc U :=
    crossCorrProdSection_eq_permute_unitModelProdSection (I := I) (a := 0) (b := 0) g₀ wS Tt
  -- The bare-product realization of `U` (the `RfnsBilinearProduct` instance's `prod` field).
  have hUb : U = Φb.prod (a := 0) (b := 0) Tt wS := rfl
  -- (3) The iterated gradient commutes with the slot permutation.
  have hPp : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
        (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Tt) =
      PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p U) := by
    rw [hPU]
    exact iteratedCovGrad_permuteCcTensor_eq (I := I) g₀ σcc U p
  -- (4) `Xp − Ap` as a single operator action on the permuted product-level difference.
  have hXAeq : Xp - Ap =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p) Φp
        (PDE.DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p U - TopU)) := by
    rw [hApeq, permuteCcTensor_sub_local, appCcRS_sub_right_local, ← hPp, ← hXeq]
  -- (5) The pointwise peeled binomial-Leibniz grid of the bare product (constant `mu·4^p = 4^p`).
  have hpeel : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 2) + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (Φb.prod (a := 0) (b := 0) Tt wS) - TopU).toSection x) ≤
    (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    have hgrid := Φb.rfns_iteratedCovGrad_prod_topRest_le_peeledDiagGrid p (a := 0) (b := 0) Tt wS x
    have hmu : Φb.mu = 1 := rfl
    rw [hmu, one_mul] at hgrid
    exact hgrid
  -- (6) The fibre-small `C⁰` sups of the two factors.
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (wS.toSection x) ≤
      (nE * δ) ^ 2 := by
    intro x
    rw [hwS, hnE]
    exact realizeSymm_rfns_le_of_gFibreOpBound (I := I) g₀ T₁ hfib x
  have hSsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Tt.toSection x) ≤
      ΛD ^ 2 := by
    intro x
    rw [hTtd, rfns_permuteCcTensor_zero, hDd]
    exact hΛD T₁ g₁ hr hfib hball_a x
  -- The per-order `‖∇^i Tt‖² = ‖∇^i D‖²` slot-permutation norm invariance.
  have hTtD : ∀ i : ℕ, ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt‖ ^ 2 =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D‖ ^ 2 := by
    intro i
    rw [norm_sq_eq_integral_riemannianFiberNormSq, norm_sq_eq_integral_riemannianFiberNormSq]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hTtd]
    exact PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M)
      g₀ c[(0 : Fin 3), 1, 2] D i x
  -- (7) The pointwise envelope bound on `rfns(Xp − Ap)` against the PEELED grid (window `i < p`).
  have hXApt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + p) x
      ((Xp - Ap).toSection x) ≤
    cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    rw [hXAeq]
    refine le_trans (hCenvB _ x) ?_
    rw [rfns_permuteCcTensor_zero, hUb]
    calc cE * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
              (Φb.prod (a := 0) (b := 0) Tt wS)
            - TopU).toSection x)
        ≤ cE * ((4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) :=
          mul_le_mul_of_nonneg_left (hpeel x) hCenv0
      _ = cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
          ring
  -- (8) The two engine instances (the strictly-sub-diagonal window `p − 1`, the anti-diagonal `p`).
  obtain ⟨hint_low, hlow⟩ := hGNlow Tt wS ΛD (nE * δ) hΛD0 (by positivity) hSsup hTsup
  set tt : ℝ := t / Ar with htt
  have htt0 : 0 < tt := by rw [htt]; positivity
  have htt1 : tt ≤ 1 := by
    rw [htt, div_le_one hAr0]
    linarith
  obtain ⟨hint_anti, hanti⟩ := hAnti Tt wS ΛD (nE * δ) hΛD0 (by positivity) hSsup hTsup tt htt0 htt1
  -- (9) The named jet sums.
  set Lp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D‖ ^ 2 with hLpd
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q D‖ ^ 2 with hSlowd
  set Sw := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i wS‖ ^ 2 with hSwd
  have hLp_nn : 0 ≤ Lp := by rw [hLpd]; positivity
  have hSlow_nn : 0 ≤ Slow := by rw [hSlowd]; positivity
  have hSw_nn : 0 ≤ Sw := by rw [hSwd]; positivity
  have hSwfold : ∀ N : ℕ, N ≤ p + 1 + 1 → (∑ l ∈ Finset.range N,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw := by
    intro N hN
    rw [hSwd]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hN) (fun l _ _ => by positivity)
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- Degenerate order `p = 0`: the peeled grid is empty, so `‖Xp − Ap‖² ≤ 0`.
    subst hp0
    have hzero : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + 0) x
        ((Xp - Ap).toSection x) ≤ 0 := by
      intro x
      refine le_trans (hXApt x) (le_of_eq ?_)
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    have hXA0 : ‖Xp - Ap‖ ^ 2 ≤ 0 := by
      rw [norm_sq_eq_integral_riemannianFiberNormSq]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (0 : ℝ) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
              (MeasureTheory.integrable_zero _ _ _) (Eventually.of_forall (fun x => hzero x))
            exact riemannianFiberNormSq_nonneg _ _ _ _ _
        _ = 0 := by simp
    have hrhs_nn : 0 ≤ t * δ ^ 2 * Lp
        + cE * 4 ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) + cAnti * Ar ^ 0 * ΛD ^ 2)
          * (1 / t) ^ 0 * (Slow + Sw) := by
      have h1 : 0 ≤ t * δ ^ 2 * Lp := by positivity
      have h2 : 0 ≤ cE * (4:ℝ) ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) + cAnti * Ar ^ 0 * ΛD ^ 2)
          * (1 / t) ^ 0 * (Slow + Sw) := by positivity
      linarith
    linarith [hXA0, hrhs_nn]
  · -- Genuine order `p ≥ 1`: rewrite the window-(p−1) ranges to `p` and assemble.
    have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hppos
    rw [hp1] at hlow hint_low
    -- The peeled grid splits pointwise as the sub-diagonal window grid plus the anti-diagonal.
    have hgrid_split : ∀ x : M, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
          ∑ l ∈ Finset.range (p + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) =
        (∑ i ∈ Finset.range p,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
            ∑ l ∈ Finset.range (p - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
        + ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hip : i < p := Finset.mem_range.mp hi
      rw [show p + 1 - i = (p - i) + 1 from by omega, Finset.sum_range_succ, mul_add]
    -- Integrate the pointwise envelope bound through the grid split.
    have hXAint : ‖Xp - Ap‖ ^ 2 ≤ cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
      rw [norm_sq_eq_integral_riemannianFiberNormSq]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (cE * (4 : ℝ) ^ p * ((∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
            + ∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x))) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
              ((hint_low.add hint_anti).const_mul _) (Eventually.of_forall (fun x => ?_))
            · exact riemannianFiberNormSq_nonneg _ _ _ _ _
            · refine le_trans (hXApt x) (le_of_eq ?_)
              rw [hgrid_split x]
        _ = cE * (4 : ℝ) ^ p * ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add hint_low hint_anti]
    -- Fold the engine S-arms into the `D`-jet sums.
    have hSlow_eq : (∑ i ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt‖ ^ 2) = Slow := by
      rw [hSlowd]
      exact Finset.sum_congr rfl (fun i _ => hTtD i)
    have hLp_eq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Tt‖ ^ 2 = Lp := by
      rw [hLpd]; exact hTtD p
    rw [hSlow_eq] at hlow
    rw [hLp_eq] at hanti
    -- The two w-arms fold into `Sw`.
    have hSw_low : (∑ l ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold p (by omega)
    have hSw_anti : (∑ l ∈ Finset.range (p + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold (p + 1) (by omega)
    -- The low-window integral bound, folded.
    have hlow' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
          ∑ l ∈ Finset.range (p - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ) ≤
        cGlow * ((nE * δ) ^ 2 * Slow + ΛD ^ 2 * Sw) := by
      refine le_trans hlow ?_
      have h2 : ΛD ^ 2 * (∑ l ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛD ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_low (by positivity)
      nlinarith [hcGlow0, h2]
    -- The anti-diagonal integral bound, with the internal rescale `tt = t / Ar`.
    have hanti' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        tt * ((nE * δ) ^ 2 * Lp) + cAnti * (1 / tt) ^ p * (ΛD ^ 2 * Sw) := by
      refine le_trans hanti ?_
      have h2 : ΛD ^ 2 * (∑ l ∈ Finset.range (p + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛD ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_anti (by positivity)
      have hc : 0 ≤ cAnti * (1 / tt) ^ p := by positivity
      nlinarith [hc, h2]
    -- The rescale algebra: `cE·4^p·tt·nE²·δ² ≤ t·δ²` and `(1/tt)^p = Ar^p·(1/t)^p`.
    have htopscale : cE * (4 : ℝ) ^ p * (tt * ((nE * δ) ^ 2 * Lp)) ≤ t * δ ^ 2 * Lp := by
      rw [htt]
      rw [show cE * (4 : ℝ) ^ p * (t / Ar * ((nE * δ) ^ 2 * Lp))
          = (cE * 4 ^ p * nE ^ 2) / Ar * (t * δ ^ 2 * Lp) from by ring]
      have hfrac : (cE * 4 ^ p * nE ^ 2) / Ar ≤ 1 := by
        rw [div_le_one hAr0, hAr]
        linarith
      have hmass : 0 ≤ t * δ ^ 2 * Lp := by positivity
      nlinarith [hfrac, hmass]
    have hinv_tt : (1 / tt) ^ p = Ar ^ p * (1 / t) ^ p := by
      rw [htt, one_div_div, show Ar / t = Ar * (1 / t) from by ring, mul_pow]
    have h1t1 : (1 : ℝ) ≤ (1 / t) ^ p := one_le_pow₀ (by rw [le_div_iff₀ ht0]; linarith)
    -- Assemble.
    have hfinal : cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        t * δ ^ 2 * Lp
          + cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) + cAnti * Ar ^ p * ΛD ^ 2)
            * (1 / t) ^ p * (Slow + Sw) := by
      have hcE4 : (0 : ℝ) ≤ cE * 4 ^ p := by positivity
      have hsum_le := add_le_add hlow' hanti'
      have hstep : cE * (4 : ℝ) ^ p *
          ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Tt).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
          cE * 4 ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛD ^ 2 * Sw))
            + cE * 4 ^ p * (tt * ((nE * δ) ^ 2 * Lp))
            + cE * 4 ^ p * (cAnti * (1 / tt) ^ p * (ΛD ^ 2 * Sw)) := by
        nlinarith [hsum_le, hcE4]
      refine le_trans hstep ?_
      rw [hinv_tt]
      have hlow_piece : cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛD ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) * (1 / t) ^ p * (Slow + Sw) := by
        have hbase : cGlow * ((nE * δ) ^ 2 * Slow + ΛD ^ 2 * Sw) ≤
            cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) * (Slow + Sw) := by
          nlinarith [hcGlow0, hSlow_nn, hSw_nn, sq_nonneg (nE * δ), sq_nonneg ΛD,
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg (nE * δ)) hSw_nn),
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg ΛD) hSlow_nn)]
        calc cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛD ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) * (Slow + Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) * (1 : ℝ) * (Slow + Sw) := by ring
          _ ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) * (1 / t) ^ p * (Slow + Sw) := by
              have hmono : cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) * (1 : ℝ) ≤
                  cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) * (1 / t) ^ p := by
                have hc : (0 : ℝ) ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2)) := by
                  positivity
                nlinarith [h1t1, hc]
              exact mul_le_mul_of_nonneg_right hmono (by linarith [hSlow_nn, hSw_nn])
      have hanti_piece : cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛD ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cAnti * Ar ^ p * ΛD ^ 2) * (1 / t) ^ p * (Slow + Sw) := by
        have hc : (0 : ℝ) ≤ cAnti * Ar ^ p * ΛD ^ 2 * (1 / t) ^ p := by positivity
        have hbase : cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛD ^ 2 * Sw) ≤
            cAnti * Ar ^ p * ΛD ^ 2 * (1 / t) ^ p * (Slow + Sw) := by
          nlinarith [hSlow_nn, hc]
        calc cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛD ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cAnti * Ar ^ p * ΛD ^ 2 * (1 / t) ^ p * (Slow + Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cAnti * Ar ^ p * ΛD ^ 2) * (1 / t) ^ p * (Slow + Sw) := by ring
      have hdistr : cE * (4 : ℝ) ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2))
            * (1 / t) ^ p * (Slow + Sw)
          + cE * 4 ^ p * (cAnti * Ar ^ p * ΛD ^ 2) * (1 / t) ^ p * (Slow + Sw)
          = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + ΛD ^ 2) + cAnti * Ar ^ p * ΛD ^ 2)
            * (1 / t) ^ p * (Slow + Sw) := by ring
      linarith [hlow_piece, hanti_piece, htopscale, hdistr.le, hdistr.ge]
    exact le_trans hXAint hfinal


set_option linter.unusedSectionVars false in
/-- **The `t`-scaled Gagliardo–Nirenberg `L²` bound on the cross-correction `Rest` arm, in the
`T₁`-jet currency** (proven glue over the peeled child and the realize-jet `L²` conversion).
The squared metric `L²` mass of the **rest** cell of the order-`p` cross-correction jet — the
difference `∇^p (crossCorrectionSection g₁ g₀ T₁) − crossCorrKeystoneTop g₀ p T₁ (∇^p (permute
c[0,1,2] loweredConnDiffSection))`, the keystone top being the honest `i = 0` binomial cell — is
dominated, for every free scale `t ∈ (0, 1]`, uniformly over the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{p+3+a}`-bounded
(`2a > finrank + 4`) perturbation family, by the `t`-scaled top re-emission `t·δ²·‖∇^p
loweredConnDiffSection‖²` plus `Crest·(1/t)^p` times the **lower** covariant gradients of the
connection difference `∑_{q < p} ‖∇^q loweredConnDiffSection‖²` (kept as themselves) plus the
`≤ (p+1)`-jet of `T₁` `∑_{l ≤ p+1} ‖∇^l T₁‖²`.

This is the genuine **deep frontier content** of the decomposition: the `i ≥ 1` binomial cells
`∇^i h ⊛ ∇^l D` of the operator-reduced covariant Leibniz of the parallel cometric contraction
`h ⌟ D`, each a genuine *product* of two independently varying factors, integrable only after
Gagliardo–Nirenberg interpolation — the strictly-sub-diagonal cells by the symmetric two-arm engine
(all arms lower-order), the anti-diagonal cells by the `t`-scaled top-arm engine (the re-emitted
top jet at the free `t·δ²`).  The keystone top cell, carrying the sharp `δ²` passenger bound
(`crossCorrKeystoneTop_rfns_le_sq_passenger`), is NOT part of this `Rest` bound — it is carried by
the decomposition's `Top` arm.

**Non-vacuity.**  The bound carries genuine content on both the lower connection-difference jets and
the `T₁`-jets (a zero coefficient falsifies it whenever a lower cell is genuinely present).  At
`T₁ = 0` the difference is `0` and the bound is `0 ≤ 0`.

Proven by folding the peeled child's realized-factor jet sum into the `T₁`-jets through the
per-order realize-jet `rfns` conversion, the `t`-scaled re-emission term riding unchanged. -/
theorem crossCorrectionSection_iteratedCovGrad_rest_grid_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Crest : ℝ, 0 ≤ Crest ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (crossCorrectionSection (I := I) g₁ g₀ T₁)
              - crossCorrKeystoneTop (I := I) g₀ p T₁
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p
                    (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                      (loweredConnDiffSection (I := I) g₁ g₀)))‖ ^ 2 ≤
          t * δ ^ 2 *
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
            + Crest * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  -- The peeled `t`-scaled GN bound supplies the rest bound in the realized-factor currency;
  -- the per-order realize-jet `rfns` conversion folds the realized arm into the `T₁`-jets.
  obtain ⟨Cpk, hCpk0, hCpk⟩ :=
    crossCorrectionSection_iteratedCovGrad_rest_peel_realizeSymm_le (I := I) g₀ p δ hδ0 hδ1 B a ha
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  -- The order-`i` realize-jet `L²` conversion (one constant per `i`), integrated from the pointwise rfns.
  have hconv : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 ≤
          Ci * ∑ l ∈ Finset.range (i + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
    intro i
    obtain ⟨C, hC0, hC⟩ :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum
        (I := I) g₀ i
    refine ⟨C, hC0, fun T₁ => ?_⟩
    rw [norm_sq_eq_integral_riemannianFiberNormSq]
    have hpt := hC T₁
    have hintRl : ∀ l, MeasureTheory.Integrable (fun x =>
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) μ :=
      fun l => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + l) _
    have hintRsum : MeasureTheory.Integrable (fun x => C * ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) μ :=
      (MeasureTheory.integrable_finset_sum (Finset.range (i + 1)) (fun l _ => hintRl l)).const_mul C
    calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) ∂μ
        ≤ ∫ x, (C * ∑ l ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
              hintRsum (Eventually.of_forall (fun x => ?_))
            · exact riemannianFiberNormSq_nonneg _ _ _ _ _
            · exact hpt x
      _ = C * ∑ l ∈ Finset.range (i + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_finset_sum _ (fun l _ => hintRl l)]
            congr 1
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [norm_sq_eq_integral_riemannianFiberNormSq]
  choose Ci hCi0 hCi using hconv
  set Cmax := (∑ i ∈ Finset.range (p + 1 + 1), Ci i) with hCmax
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun i _ => hCi0 i
  refine ⟨Cpk * (1 + Cmax), by positivity, ?_⟩
  intro t ht0 ht1 T₁ g₁ hr hfib hball
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
          (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hSlow
  set ST := ∑ l ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hST
  have hSlow_nn : 0 ≤ Slow := Finset.sum_nonneg fun q _ => by positivity
  have hST_nn : 0 ≤ ST := Finset.sum_nonneg fun l _ => by positivity
  have hpk := hCpk t ht0 ht1 T₁ g₁ hr hfib hball
  rw [← hSlow] at hpk
  have hwconv : (∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤ Cmax * ST := by
    rw [hCmax, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine le_trans (hCi i T₁) ?_
    have hsub : (∑ l ∈ Finset.range (i + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) ≤ ST := by
      rw [hST]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by have := Finset.mem_range.mp hi; omega : i + 1 ≤ p + 1 + 1))
        fun l _ _ => by positivity
    exact mul_le_mul_of_nonneg_left hsub (hCi0 i)
  set Sw := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 with hSw
  have hSw_nn : 0 ≤ Sw := Finset.sum_nonneg fun i _ => by positivity
  have htp : (0 : ℝ) ≤ (1 / t) ^ p := by positivity
  -- `Cpk·(1/t)^p·(Slow + Sw) ≤ Cpk·(1+Cmax)·(1/t)^p·(Slow + ST)`; the scaled emission term rides.
  have hgrid_le : Cpk * (1 / t) ^ p * (Slow + Sw) ≤
      Cpk * (1 + Cmax) * (1 / t) ^ p * (Slow + ST) := by
    have hbase : Cpk * (Slow + Sw) ≤ Cpk * (1 + Cmax) * (Slow + ST) := by
      have h1 : Cpk * (Slow + Sw) ≤ Cpk * (Slow + Cmax * ST) := by
        gcongr
      refine h1.trans ?_
      nlinarith [mul_nonneg (mul_nonneg hCpk0 hCmax0) hSlow_nn, mul_nonneg hCpk0 hST_nn,
        hSlow_nn, hST_nn, hCpk0, hCmax0]
    calc Cpk * (1 / t) ^ p * (Slow + Sw)
        = (1 / t) ^ p * (Cpk * (Slow + Sw)) := by ring
      _ ≤ (1 / t) ^ p * (Cpk * (1 + Cmax) * (Slow + ST)) :=
          mul_le_mul_of_nonneg_left hbase htp
      _ = Cpk * (1 + Cmax) * (1 / t) ^ p * (Slow + ST) := by ring
  linarith [hpk, hgrid_le]

set_option linter.unusedSectionVars false in
/-- **The top/rest decomposition of the cross-correction order-`p` covariant jet, with its two
sharp arm bounds** (proven glue over the keystone passenger bound and the `t`-scaled GN rest
child).  The order-`p` covariant jet of the cross-correction splits as
`∇^p (crossCorrectionSection g₁ g₀ T₁) = Top + Rest`, where:

* the **top** section `Top` is the keystone product-level `i = 0` binomial cell
  `crossCorrKeystoneTop g₀ p T₁ (∇^p (permute c[0,1,2] loweredConnDiffSection))` (all `p`
  derivatives on the connection-difference factor, the cometric tracing the factor's ORIGINAL
  slot), whose squared metric `L²` mass is **sharply** `‖Top‖² ≤ δ² · ‖∇^p
  loweredConnDiffSection‖²` — the genuine δ²-spectator content
  (`crossCorrKeystoneTop_rfns_le_sq_passenger`, NO dimension factor, NO envelope, uniformly in
  `p`);

* the **rest** section `Rest` (the `i ≥ 1` binomial cells) carries, for the free scale
  `t ∈ (0, 1]`, the `t`-scaled Gagliardo–Nirenberg bound
  `‖Rest‖² ≤ t·δ²·‖∇^p loweredConnDiffSection‖² + Crest·(1/t)^p·(∑_{q < p} ‖∇^q
  loweredConnDiffSection‖² + ∑_{l ≤ p+1} ‖∇^l T₁‖²)`
  (`crossCorrectionSection_iteratedCovGrad_rest_grid_le`) — the re-emitted top jet at the free
  `t·δ²`, the engine constants on the lower-order remainder.

The two arms are then combined by the `2`-subadditivity `‖Top + Rest‖² ≤ 2‖Top‖² + 2‖Rest‖²` in
the split below, giving the `2(1 + t)δ²` principal that the margin-chosen scale
`t = (1 − 2δ)/(1 + 2δ)` absorbs to `δ` on all of `δ < 1/2` (`crossCorrMarginScale_absorb`).

**Non-vacuity.**  Both bounds carry genuine content: the top bound carries the single high
derivative `‖∇^p lowered‖`, the rest bound the lower connection-difference jets and the `T₁`-jets.
At `T₁ = 0` everything vanishes and both bounds are `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_topRest_decomp
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Crest : ℝ, 0 ≤ Crest ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ∃ Top Rest : Integral.L2.SmoothCcTensor g₀ 0 (3 + p),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁) = Top + Rest ∧
          ‖Top‖ ^ 2 ≤ δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ∧
          ‖Rest‖ ^ 2 ≤ t * δ ^ 2 *
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + Crest * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  -- The `Rest` arm constant from the `t`-scaled Gagliardo–Nirenberg child.
  obtain ⟨Crest, hCrest0, hRest⟩ :=
    crossCorrectionSection_iteratedCovGrad_rest_grid_le (I := I) g₀ p δ hδ0 hδ1 B a ha
  refine ⟨Crest, hCrest0, ?_⟩
  intro t ht0 ht1 T₁ g₁ hr hfib hball
  -- The keystone product-level **top** cell: the honest `i = 0` binomial cell, in the
  -- contraction's own slot layout, so the sharp `δ²` keystone passenger bound applies directly.
  set Top : Integral.L2.SmoothCcTensor g₀ 0 (3 + p) :=
    crossCorrKeystoneTop (I := I) g₀ p T₁
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p
        (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
          (loweredConnDiffSection (I := I) g₁ g₀))) with hTop_def
  refine ⟨Top, PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (crossCorrectionSection (I := I) g₁ g₀ T₁) - Top, ?_, ?_, ?_⟩
  · -- The decomposition arm: `∇^p cc = Top + (∇^p cc − Top)`.
    rw [add_sub_cancel]
  · -- The **top** arm: `‖Top‖² ≤ δ² · ‖∇^p loweredConnDiffSection‖²`.
    -- `‖Top‖² = ∫ rfns(Top)` and `‖∇^p lowered‖² = ∫ rfns(∇^p lowered)`; the pointwise keystone
    -- passenger bound `rfns(Top)(x) ≤ δ²·rfns(∇^p permute lowered)(x) = δ²·rfns(∇^p lowered)(x)`
    -- integrates.
    set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
    rw [hTop_def, norm_sq_eq_integral_riemannianFiberNormSq, norm_sq_eq_integral_riemannianFiberNormSq]
    -- Pointwise keystone bound at `Z = ∇^p (permute c[0,1,2] lowered)`.
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
            ((crossCorrKeystoneTop (I := I) g₀ p T₁
                (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p
                  (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                    (loweredConnDiffSection (I := I) g₁ g₀)))).toSection x) ≤
          δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) := by
      intro x
      refine le_trans (crossCorrKeystoneTop_rfns_le_sq_passenger (I := I) g₀ p T₁ hfib
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
            (loweredConnDiffSection (I := I) g₁ g₀))) x) ?_
      -- `rfns(∇^p permute lowered)(x) = rfns(∇^p lowered)(x)` (slot-reindex invariance).
      exact mul_le_mul_of_nonneg_left (le_of_eq
        (PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor
          (I := I) (M := M) g₀ c[(0 : Fin 3), 1, 2]
          (loweredConnDiffSection (I := I) g₁ g₀) p x)) (sq_nonneg δ)
    -- Integrate the pointwise bound.
    have hintLow : MeasureTheory.Integrable (fun x =>
        δ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) μ :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + p) _).const_mul (δ ^ 2)
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
      hintLow (Eventually.of_forall hpt)
    exact riemannianFiberNormSq_nonneg _ _ _ _ _
  · -- The **rest** arm: the `t`-scaled Gagliardo–Nirenberg bound, verbatim.
    exact hRest t ht0 ht1 T₁ g₁ hr hfib hball

set_option linter.unusedSectionVars false in
/-- **The cross-correction order-`p` covariant jet top/rest split, `t`-scaled, integrated `L²`
two-arm form.**  The squared metric `L²` norm of the order-`p` covariant gradient of the
cross-correction `h ⌟ D` (`h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`) is dominated, for
every free scale `t ∈ (0, 1]`, by a **`2(1 + t)δ²`-arm** carrying the single high derivative on the
`g₀`-lowered connection difference, plus `Crest·(1/t)^p` times the lower covariant gradients of the
connection difference and the `≤ (p+1)`-jet of `T₁`:
```
‖∇^p crossCorrectionSection g₁ g₀ T₁‖²
  ≤ 2 (1 + t) δ² · ‖∇^p loweredConnDiffSection g₁ g₀‖²
    + Crest · (1/t)^p · (∑_{q < p} ‖∇^q loweredConnDiffSection g₁ g₀‖² + ∑_{l ≤ p+1} ‖∇^l T₁‖²),
```
with `Crest ≥ 0` uniform over the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`,
`δ < 1/2`) supercritically-`H^{p+3+a}`-bounded perturbation family.

**Why the principal coefficient is `2(1 + t)δ²`.**  The jet splits as `∇^p cc = Top + Rest`
(`crossCorrectionSection_iteratedCovGrad_topRest_decomp`): the keystone top carries the sharp `δ²`
(`crossCorrKeystoneTop_rfns_le_sq_passenger`), the rest carries the `t`-scaled re-emission `t·δ²`;
the `2`-subadditivity `‖Top + Rest‖² ≤ 2‖Top‖² + 2‖Rest‖²` absorbs the cross term (an exactly-`δ²`
principal is false for `p ≥ 1`: the `L²` cross term `2⟪Top, Rest⟫` carries the top order).  The
single consumer `crossCorrectionSection_iteratedCovGrad_grid_le` instantiates `t` at the recursion
margin `(1 − 2δ)/(1 + 2δ)` and relaxes the principal to the load-bearing `δ` by the fresh scaled
absorption `crossCorrMarginScale_absorb`, so the downstream `4 − 8δ` terminus holds on all of
`δ < 1/2`, uniformly in the order.

**Why INTEGRATED, not pointwise (the former pointwise statement was false for `p ≥ 3`).**  The
order-`p` binomial covariant Leibniz of `h ⌟ D` carries a middle term `∇^i h ⊛ ∇^{p−i} D`, a genuine
*product* of two independently varying factors; the supercritical `H^{p+3}` ball funds only the
order-`≤ 2` jet of `h` pointwise, and `D` has no unconditional `C⁰` sup bound, so the product cannot
be dominated *pointwise* by a sum of `rfns`-jets.  This is Gagliardo–Nirenberg interpolation
content, true only after integration.

* **`p = 0` collapse litmus.**  At `p = 0` the lower-`loweredConnDiff` sum is empty and the bound is
  `‖cc‖² ≤ 2(1 + t)δ²·‖loweredConnDiffSection‖² + Crest·∑_{l ≤ 1} ‖∇^l T₁‖²`.
* **self-zero litmus.**  At `T₁ = 0`, `crossCorrectionSection = 0` and the bound is `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_topRest_split
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Crest : ℝ, 0 ≤ Crest ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          2 * (1 + t) * δ ^ 2 *
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Crest * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  -- Obtain the top/rest decomposition with its two sharp arm bounds.
  obtain ⟨Crest, hCrest0, hdecomp⟩ :=
    crossCorrectionSection_iteratedCovGrad_topRest_decomp (I := I) g₀ p δ hδ0 hδ1 B a ha
  refine ⟨2 * Crest, by positivity, ?_⟩
  intro t ht0 ht1 T₁ g₁ hr hfib hball
  obtain ⟨Top, Rest, hsum, hTop, hRest⟩ := hdecomp t ht0 ht1 T₁ g₁ hr hfib hball
  -- `2`-subadditivity of the squared norm on the sum `∇^p cc = Top + Rest`.
  have h2sub : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤ 2 * ‖Top‖ ^ 2 + 2 * ‖Rest‖ ^ 2 := by
    rw [hsum]
    have hns := norm_add_sq_real Top Rest
    have hcs := abs_real_inner_le_norm Top Rest
    have hcs' := le_abs_self (@inner ℝ _ _ Top Rest)
    nlinarith [hns, hcs, hcs', sq_nonneg (‖Top‖ - ‖Rest‖), norm_nonneg Top, norm_nonneg Rest]
  -- Combine: `2 ‖Top‖² ≤ 2 δ² ‖∇^p lowered‖²` and
  -- `2 ‖Rest‖² ≤ 2 t δ² ‖∇^p lowered‖² + 2 Crest · (1/t)^p · grid`.
  set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
  set G := (∑ q ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
      + ∑ l ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) with hGdef
  nlinarith [h2sub, hTop, hRest]

set_option linter.unusedSectionVars false in
/-- **The cross-correction covariant-Leibniz contraction grid, δ-separated, integrated `L²` form.**
The squared metric `L²` norm of the order-`p` covariant gradient of the cross-correction `h ⌟ D`
(`h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`) is dominated, uniformly over the fibre-small
(`δ < 1/2`) `H^{p+3+a}` ball, by the **δ-separated** grid: the principal term
`δ · ‖∇^p loweredConnDiffSection‖²` plus a constant times the lower covariant gradients of the
connection difference `∑_{q < p} ‖∇^q loweredConnDiffSection‖²` and the `≤ (p+1)`-jet of `T₁`.

Proved directly from the `t`-scaled top/rest split
`crossCorrectionSection_iteratedCovGrad_topRest_split` (the genuine contraction-algebra bottom): its
`2(1 + t)δ²`-arm, instantiated at the margin-chosen scale `t := (1 − 2δ)/(1 + 2δ)`, is relaxed to
the principal `δ · ‖∇^p lowered‖²` by the **fresh scaled-Young absorption**
`crossCorrMarginScale_absorb` (`2(1 + t)δ² = 4δ²/(1 + 2δ) ≤ δ` on all of `δ < 1/2`); the rest arm
`Crest·(1/t)^p·(…)` carries the lower-order grid with the `δ`-dependent (but order-uniform in the
hypothesis) constant `Crest·((1 + 2δ)/(1 − 2δ))^p`.

This is the **strictly-smaller** brick of `crossCorrectionSection_iteratedCovGrad_rfns_le`: it is the
*non-inductive* contraction-Leibniz grid (no fibre-small `g₁^{-1}` recursion, no strong induction over
the order), carrying the lower covariant gradients of the connection difference *as themselves* on the
right.  The full cross-correction bound then folds these lower `loweredConnDiffSection` jets into the
`T₁`-jets by the route-(a) strong induction (`crossCorrectionSection_iteratedCovGrad_rfns_le`), which is
*not* part of this brick.

* **j = 0 collapse litmus.**  At `p = 0` the lower-`loweredConnDiff` sum is empty, so this is
  `‖crossCorrectionSection‖² ≤ δ·‖loweredConnDiffSection‖² + Cgrid·∑_{l ≤ 1} ‖∇^l T₁‖²`.
* **self-zero litmus.**  At `T₁ = 0`, `crossCorrectionSection = 0` and the bound is `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_grid_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Cgrid * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  obtain ⟨Crest, hCrest0, hsplit⟩ :=
    crossCorrectionSection_iteratedCovGrad_topRest_split (I := I) g₀ p δ hδ0 hδ1 B a ha
  -- The margin-chosen scale.
  obtain ⟨htm0, htm1⟩ := crossCorrMarginScale_mem hδ0 hδ1
  refine ⟨Crest * (1 / ((1 - 2 * δ) / (1 + 2 * δ))) ^ p, by positivity, ?_⟩
  intro T₁ g₁ hr hfib hball
  -- Abbreviate the principal jet term `L` and the lower-order grid `G`.
  set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
  set G := (∑ q ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
      + ∑ l ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) with hGdef
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  -- The `t`-scaled split at the margin scale, then the fresh scaled-Young absorption
  -- `2(1 + t)δ² ≤ δ`.
  have hsp := hsplit ((1 - 2 * δ) / (1 + 2 * δ)) htm0 htm1 T₁ g₁ hr hfib hball
  rw [← hLdef, ← hGdef] at hsp
  have habs : 2 * (1 + (1 - 2 * δ) / (1 + 2 * δ)) * δ ^ 2 ≤ δ :=
    crossCorrMarginScale_absorb hδ0 hδ1
  have hδsq : 2 * (1 + (1 - 2 * δ) / (1 + 2 * δ)) * δ ^ 2 * L ≤ δ * L :=
    mul_le_mul_of_nonneg_right habs hLnn
  linarith [hsp, hδsq]

set_option linter.unusedSectionVars false in
/-- **Squared `L²`-norm scaling of an iterated covariant jet.**  `‖∇^j (c • S)‖² = c² · ‖∇^j S‖²`,
from `iteratedCovGrad_smul` and the inner-product-space norm scaling `‖c • ·‖ = |c| · ‖·‖`. -/
private lemma iteratedCovGrad_norm_sq_smul (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) (c : ℝ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (c • S)‖ ^ 2 =
      c ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2 := by
  rw [iteratedCovGrad_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

set_option linter.unusedSectionVars false in
/-- **`2`-subadditivity of the squared `L²` norm on a difference of iterated covariant jets.**
`‖∇^j (S - T)‖² ≤ 2 ‖∇^j S‖² + 2 ‖∇^j T‖²`, from `iteratedCovGrad_sub`, the inner-product expansion
`‖A - B‖² = ‖A‖² - 2⟪A, B⟫ + ‖B‖²`, and Cauchy–Schwarz. -/
private lemma iteratedCovGrad_norm_sq_sub_le (g₀ : SmoothRiemannianMetric I M) (s j : ℕ)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (S - T)‖ ^ 2 ≤
      2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2
        + 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 := by
  rw [PDE.RicciFlow.iteratedCovGrad_sub]
  set A := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S with hA
  set Bb := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T with hBb
  have h := norm_sub_sq_real A Bb
  have hcs2 := abs_real_inner_le_norm A Bb
  have hcs := neg_le_abs (@inner ℝ _ _ A Bb)
  nlinarith [h, hcs, hcs2, sq_nonneg (‖A‖ - ‖Bb‖), norm_nonneg A, norm_nonneg Bb]

set_option linter.unusedSectionVars false in
/-- **The clean-linear-part jet brick, integrated `L²` form.**  The squared metric `L²` norm of the
order-`p` covariant gradient of the section-level clean linear part `koszulCombSection g₁ g₀ T₁` is
dominated by the `≤ (p+1)`-jet of `T₁`: `‖∇^p koszulCombSection‖² ≤ C · ∑_{l ≤ p+1} ‖∇^l T₁‖²`.

This is the pointwise `koszulCombSection_iteratedCovGrad_rfns_le` brick (sorry-free, the linear part is a
linear combination of slot readings of `covGrad (realizeSymm T₁)` — no `D`-product, so it is genuinely
bounded pointwise by the `T₁`-jets, no Gagliardo–Nirenberg obstruction) integrated by `∫`-monotonicity
(`integral_mono_of_nonneg`) through the squared-`L²`/fibre-norm bridge
`norm_sq_eq_integral_riemannianFiberNormSq`. -/
private lemma koszulCombSection_iteratedCovGrad_norm_sq_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (koszulCombSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          C * ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := koszulCombSection_iteratedCovGrad_rfns_le (I := I) g₀ p
  refine ⟨C, hC0, ?_⟩
  intro T₁ g₁ hr
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  rw [norm_sq_eq_integral_riemannianFiberNormSq]
  have hpt := hC T₁ g₁ hr
  have hintRl : ∀ l, MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) μ :=
    fun l => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + l) _
  have hintRsum : MeasureTheory.Integrable (fun x => C * ∑ l ∈ Finset.range (p + 1 + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) μ :=
    (MeasureTheory.integrable_finset_sum (Finset.range (p + 1 + 1))
      (fun l _ => hintRl l)).const_mul C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x) ∂μ
      ≤ ∫ x, (C * ∑ l ∈ Finset.range (p + 1 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ∂μ := by
          refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
            hintRsum (Eventually.of_forall (fun x => ?_))
          · exact riemannianFiberNormSq_nonneg _ _ _ _ _
          · exact hpt x
    _ = C * ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _
            (fun l _ => hintRl l)]
          congr 1
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [norm_sq_eq_integral_riemannianFiberNormSq]

set_option linter.unusedSectionVars false in
/-- **(The fibre-small-gated cross-correction jet brick, integrated `L²` form.)**  On the fibre-small ball
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ` with `δ < 1/2`) and the Sobolev `H^{p+3+a}` ball
(`‖T₁.toHs (p+3)‖ ≤ B`), the intrinsic squared fibre norm of the order-`p` covariant gradient of the
cross-correction section `crossCorrectionSection` (the Koszul correction `h ⌟ D`) is dominated by the
**fibre-small-absorbed** principal term `δ · rfns(∇^p loweredConnDiffSection)` plus a perturbation
`≤ (p+1)`-jet term with a constant uniform over the ball.

This is the **binomial covariant-Leibniz grid** of the contraction `h ⌟ D` (the
`ParallelTensorProduct`-style operator-reduced Leibniz of the contraction `h ⌟ D`
(`h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`), with: the **top term** (`∇^0 h ⌟ ∇^p D`)
absorbed via the fibre-smallness `gFibreOpBound … δ` (the `g₀`-operator norm of `h` is `≤ δ`, so this
term is `≤ δ·‖∇^p loweredConnDiffSection‖²` through the `g₀`-lowering parallel isometry `∇₀ g₀ = 0`);
and all **lower terms** (`∇^i h ⌟ ∇^q D`, `q < p`) folded into the `≤ (p+1)`-jet of `T₁` using the
`H^{p+3}` Sobolev ball and the inductive control of the lower covariant gradients of the connection
difference.  It is strictly smaller than `T1` (it bounds the **cross correction**, carrying the
`δ·loweredConnDiffSection` recursion term) and is **not** `T1` restated.

* **j = 0 collapse litmus.**  At `p = 0` this is
  `‖crossCorrectionSection‖² ≤ δ·‖loweredConnDiffSection‖² + Ccross·∑_{l ≤ 1} ‖∇^l T₁‖²`.
* **self-zero litmus.**  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so `crossCorrectionSection = 0`
  and the bound is `0 ≤ 0`. -/
theorem crossCorrectionSection_iteratedCovGrad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Ccross * ∑ l ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
  classical
  -- **Strong induction on `p`** establishing the per-order lowered-jet bound
  -- `‖∇^q lowered‖² ≤ Clow q · S` for all `q ≤ p` (the route-(a) differentiated-Koszul recursion,
  -- folding the cross-correction grid's lower covariant gradients of the connection difference into
  -- the perturbation jets), then reading off the cross-correction bound from the grid brick.  The
  -- single `δ < 1/2` hypothesis is order-uniform, so it discharges the recursion at every order.
  suffices haux : ∀ q : ℕ, ∃ Clow : ℝ, 0 ≤ Clow ∧ (q ≤ p →
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (q + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          Clow * ∑ l ∈ Finset.range (q + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) by
    obtain ⟨Cgrid, hCgrid0, hCgrid⟩ :=
      crossCorrectionSection_iteratedCovGrad_grid_le (I := I) g₀ p δ hδ0 hδ1 B a ha
    choose Clow hClow0 hClow using haux
    have hClowsum_nn : 0 ≤ ∑ q ∈ Finset.range p, Clow q :=
      Finset.sum_nonneg fun q _ => hClow0 q
    refine ⟨Cgrid + Cgrid * ∑ q ∈ Finset.range p, Clow q, by positivity, ?_⟩
    intro T₁ g₁ hr hfib hball
    set S := ∑ l ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
    have hgrid := hCgrid T₁ g₁ hr hfib hball
    have hlow_le : ∀ q ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ Clow q * S := by
      intro q hq
      have hqp : q ≤ p := Nat.le_of_lt (Finset.mem_range.mp hq)
      have hball_q : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (q + 3 + a) T₁‖
          ≤ B := le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : q + 3 + a ≤ p + 3 + a) T₁) hball
      have h := hClow q hqp T₁ g₁ hr hfib hball_q
      refine le_trans h ?_
      have hsub : (∑ l ∈ Finset.range (q + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) ≤ S := by
        rw [hSdef]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega : q + 1 + 1 ≤ p + 1 + 1))
          fun l _ _ => by positivity
      exact mul_le_mul_of_nonneg_left hsub (hClow0 q)
    have hsum_low : (∑ q ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤
        (∑ q ∈ Finset.range p, Clow q) * S := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hlow_le
    calc
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2
          ≤ δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
            + Cgrid * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 + S) := hgrid
      _ ≤ δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
            + (Cgrid + Cgrid * ∑ q ∈ Finset.range p, Clow q) * S := by
        nlinarith [hsum_low, hSnn, hCgrid0, hClowsum_nn]
  -- **The strong induction proving `haux`.**
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    by_cases hqp : q ≤ p
    swap
    · exact ⟨0, le_rfl, fun hqp' => absurd hqp' hqp⟩
    have hδ1q : δ < 1 / 2 := hδ1
    have hδhalf : δ < 1 / 2 := hδ1
    obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_norm_sq_le (I := I) g₀ q
    obtain ⟨Cg, hCg0, hCg⟩ :=
      crossCorrectionSection_iteratedCovGrad_grid_le (I := I) g₀ q δ hδ0 hδ1q B a ha
    -- Collect the IH constants for the strictly-lower orders `i < q`.
    have hih : ∀ i ∈ Finset.range q, ∃ Ci : ℝ, 0 ≤ Ci ∧
        ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (i + 3 + a) T₁‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Ci * ∑ l ∈ Finset.range (i + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
      intro i hi
      obtain ⟨Ci, hCi0, hCi⟩ := ih i (Finset.mem_range.mp hi)
      exact ⟨Ci, hCi0, hCi (le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hqp)⟩
    choose! Ci hCi0 hCi using hih
    have hden : 0 < 4 - 8 * δ := by linarith
    refine ⟨(2 * Ck + 8 * Cg + 8 * Cg * ∑ i ∈ Finset.range q, Ci i) / (4 - 8 * δ), ?_, ?_⟩
    · have : 0 ≤ ∑ i ∈ Finset.range q, Ci i :=
        Finset.sum_nonneg fun i hi => hCi0 i hi
      positivity
    intro _ T₁ g₁ hr hfib hball
    set S := ∑ l ∈ Finset.range (q + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
    set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
      (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
    have hLnn : 0 ≤ L := by rw [hLdef]; positivity
    set Kr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
      (koszulCombSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hKrdef
    set Cr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
      (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hCrdef
    -- The section-level Koszul identity under ∇^q: 2•lowered = koszulComb − 2•cross ⟹ 4L ≤ 2Kr + 8Cr.
    have hsub : (4 : ℝ) * L ≤ 2 * Kr + 8 * Cr := by
      -- The section-level identity `2•lowered = koszulComb − 2•cross`, applied to `∇^q`.
      have hid : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀) =
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (koszulCombSection (I := I) g₁ g₀ T₁) -
            PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁) := by
        rw [← PDE.RicciFlow.iteratedCovGrad_sub]
        congr 1
        rw [koszulCombSection]
        abel
      -- `‖∇^q(2•lowered)‖² = 4 L` and `‖∇^q(2•cross)‖² = 4 Cr`.
      have h4L : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 = 4 * L := by
        rw [iteratedCovGrad_norm_sq_smul, hLdef]; norm_num
      have h4Cr : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 = 4 * Cr := by
        rw [iteratedCovGrad_norm_sq_smul, hCrdef]; norm_num
      -- `‖∇^q(koszul − 2•cross)‖² ≤ 2‖∇^q koszul‖² + 2‖∇^q(2•cross)‖²` (sub-subadditivity).
      have hle := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 q
        (koszulCombSection (I := I) g₁ g₀ T₁) ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁)
      rw [PDE.RicciFlow.iteratedCovGrad_sub] at hle
      -- Rewrite `‖∇^q(2•lowered)‖²` through the identity to `‖∇^q koszul − ∇^q(2•cross)‖²`.
      rw [hid] at h4L
      rw [← hKrdef] at hle
      rw [h4Cr] at hle
      linarith [hle, h4L]
    -- POSIT 1 (the integrated clean-linear-part brick) and the grid brick at order `q`.
    have hKr_le : Kr ≤ Ck * S := hCk T₁ g₁ hr
    have hCr_le : Cr ≤ δ * L + Cg * ((∑ i ∈ Finset.range q,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2) + S) := hCg T₁ g₁ hr hfib hball
    -- Fold the lower `loweredConnDiff` jets (i < q) into `S` by the IH.
    have hlow_le : ∀ i ∈ Finset.range q,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
            (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ Ci i * S := by
      intro i hi
      have hball_i : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (i + 3 + a) T₁‖
          ≤ B := le_trans (toHs_norm_mono (I := I) (M := M) g₀
            (by have := Finset.mem_range.mp hi; omega : i + 3 + a ≤ q + 3 + a) T₁) hball
      have h := hCi i hi T₁ g₁ hr hfib hball_i
      refine le_trans h ?_
      have hsub2 : (∑ l ∈ Finset.range (i + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) ≤ S := by
        rw [hSdef]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by have := Finset.mem_range.mp hi; omega : i + 1 + 1 ≤ q + 1 + 1))
          fun l _ _ => by positivity
      exact mul_le_mul_of_nonneg_left hsub2 (hCi0 i hi)
    have hsum_low : (∑ i ∈ Finset.range q,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤
        (∑ i ∈ Finset.range q, Ci i) * S := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum hlow_le
    have hsumCi_nn : 0 ≤ ∑ i ∈ Finset.range q, Ci i :=
      Finset.sum_nonneg fun i hi => hCi0 i hi
    -- Close: (4 − 8δ)·L ≤ (2Ck + 8Cg + 8Cg·∑Ci)·S, divide.
    have hkey : (4 - 8 * δ) * L ≤
        (2 * Ck + 8 * Cg + 8 * Cg * ∑ i ∈ Finset.range q, Ci i) * S := by
      nlinarith [hsub, hKr_le, hCr_le, hsum_low, hSnn, hLnn, hCg0, hCk0, hsumCi_nn,
        mul_le_mul_of_nonneg_left hsum_low hCg0]
    rw [hLdef] at hkey ⊢
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    rw [← hLdef] at hkey ⊢
    nlinarith [hkey]

set_option linter.unusedSectionVars false in
/-- **T1 — the iterated-covariant-jet bound for the metrically-lowered connection difference**
(fibre-small ball regime).

For a closed Riemannian manifold `(M, g₀)`, an order `p`, a fibre-smallness parameter
`δ < 1/2` (the order-uniform fibre-smallness gate of the scaled-Young redesign), and
a Sobolev ball radius `B`, there is a single nonnegative constant `C` such that for every realized
metric `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` whose perturbation `T₁` is fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`) and `H^{p+3}`-bounded (`‖T₁.toHs (p+3)‖ ≤ B`), the
intrinsic squared metric `L²` norm of the order-`p` covariant gradient of the `g₀`-metrically-lowered
connection difference `loweredConnDiffSection g₁ g₀` is dominated by the `≤ (p+1)`-jet of `T₁`:
```
‖∇^p (loweredConnDiffSection g₁ g₀)‖² ≤ C · ∑_{l ≤ p+1} ‖∇^l T₁‖².
```

This is the **chain terminus** (no `sorry` of its own): the single-arm integrated `L²` jet bound that
the difference-arm consumer `crossCorrectionDiff_iteratedCovGrad_topRest_split`
(`ConnectionDifferenceQuadraticTraceProduct.lean`) reads to fold the *fixed* connection-difference
factors `D₁, D₂` into the `T₁, T₂` jets.

The **fibre-small ball gate is required** (verified): the connection difference is a *nonlinear*
function of `T₁` (the Koszul lowering is `g₁`-inner, pulling in `g₁^{-1}`), so the bound fails
uniformly as `g₁` degenerates over the unconstrained realize family — see the file header.

Proved by the **route-(a) differentiated-Koszul algebra** over the section-level Koszul identity
`2·loweredConnDiffSection = koszulCombSection − 2·crossCorrectionSection` (the clean-linear-part
section minus the cross correction, `koszulCombSection`): the squared-`L²`-norm subadditivity
`iteratedCovGrad_norm_sq_sub_le` over the identity, the **integrated clean-linear-part jet brick**
`koszulCombSection_iteratedCovGrad_norm_sq_le` (the linear part is `≤ (p+1)`-jet of `T₁`), and the
**fibre-small-gated cross-correction jet brick** `crossCorrectionSection_iteratedCovGrad_rfns_le`
(the cross correction is `δ·` the lowered connection difference plus the `≤ (p+1)`-jet), the latter's
`δ·‖∇^p loweredConnDiffSection‖²` recursion term moved to the left and divided out (`4 − 8δ > 0`
since `δ < 1/2`). -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          C * ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
  classical
  have hδhalf : δ < 1 / 2 := hδ1
  obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_norm_sq_le (I := I) g₀ p
  obtain ⟨Cc, hCc0, hCc⟩ :=
    crossCorrectionSection_iteratedCovGrad_rfns_le (I := I) g₀ p δ hδ0 hδ1 B a ha
  refine ⟨(2 * Ck + 8 * Cc) / (4 - 8 * δ), ?_, ?_⟩
  · have hden : 0 < 4 - 8 * δ := by linarith
    positivity
  intro T₁ g₁ hr hfib hball
  set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
  set Kr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
    (koszulCombSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hKrdef
  set Cr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
    (crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hCrdef
  set S := ∑ l ∈ Finset.range (p + 1 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
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
  -- `‖∇^p(2•lowered)‖² = 4 L` and `‖∇^p(2•cross)‖² = 4 Cr`.
  have h4L : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 = 4 * L := by
    rw [iteratedCovGrad_norm_sq_smul, hLdef]; norm_num
  have h4Cr : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 = 4 * Cr := by
    rw [iteratedCovGrad_norm_sq_smul, hCrdef]; norm_num
  -- `4L = ‖∇^p koszul − ∇^p(2•cross)‖² ≤ 2 Kr + 2·(4 Cr)`.
  have hsub : (4 : ℝ) * L ≤ 2 * Kr + 2 * (4 * Cr) := by
    have hle := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 p
      (koszulCombSection (I := I) g₁ g₀ T₁) ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁)
    rw [PDE.RicciFlow.iteratedCovGrad_sub] at hle
    rw [hid] at h4L
    rw [← hKrdef, h4Cr] at hle
    linarith [hle, h4L]
  -- Apply the two posits.
  have hKr_le : Kr ≤ Ck * S := hCk T₁ g₁ hr
  have hCr_le : Cr ≤ δ * L + Cc * S := hCc T₁ g₁ hr hfib hball
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
