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

/-- **(POSIT — the cross-correction order-`p` covariant jet top/rest split, δ-separated.)**  The
section-level value `(∇^p crossCorrectionSection) x` splits, fibrewise at every base point `x`, into a
**top** fibre tensor `Top` and a **rest** fibre tensor `Rest` (the order-`0` term and the strictly
lower-order terms of the binomial covariant Leibniz expansion of the metric/evaluation contraction
`h ⌟ D`, `h = ccTensorBilinSymm g₀ T₁`, `D = connDiff g₁ g₀`), with the **top** term controlled by the
fibre-smallness in *squared* form (`δ²`) and the **rest** term by the lower covariant gradients of the
connection difference plus the `≤ (p+1)`-jet of `T₁`. -/
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
