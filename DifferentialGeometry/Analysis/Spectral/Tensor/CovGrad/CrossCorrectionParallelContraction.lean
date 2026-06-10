import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative

/-! # The cross-correction parallel two-section contraction `h ⌟ D`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, the file `QuadraticProductRfnsGrid` packages the **diagonal `rfns` jet grid**
of an abstract parallel fibrewise bilinear product `Φ : RfnsBilinearProduct g₀ s₁ s₂ s₀`
(`exists_rfns_iteratedCovGrad_prod_diagGrid_le`).  The cross-correction-difference and quadratic-Cross
covariant-Faà-di-Bruno arms of the segment-metric Ricci difference consume that grid at the **specific**
two-section parallel contraction

```
prod (realizeSymmCcTensor g₀ Tₖ) (loweredConnDiffSection gₖ g₀)   :   (0, 2) ⌟ (0, 3) → (0, 3),
```

the `g₀`-metric single contraction `h ⌟ D` of the symmetric realized perturbation `h = realizeSymm Tₖ`
(rank `2`) against the `g₀`-lowered connection difference `D = loweredConnDiff gₖ g₀` (rank `3`),
pairing one slot of each factor through the cometric `g₀⁻¹` (parallel, `∇₀ g₀⁻¹ = 0`), so the result
carries the remaining `(2 − 1) + (3 − 1) = 3` covariant slots.  This is exactly the fibre shape of the
nonlinear cross-correction `crossCorrectionSection`
(`ccTensorBilinSymm g₀ Tₖ x (connDiff gₖ g₀ x b a) c`).

This file supplies the missing instance for that contraction.

## What this file provides

* `crossCorrParallelContraction` — the section-level **parallel fibrewise bilinear `g₀`-single
  contraction** `(0, 2 + a) ⊗ (0, 3 + b) → (0, 3 + a + b)`, fibrewise `ℝ`-bilinear, built from the
  model tensor product `Bundle.continuousMultilinearMap.modelProduct` followed by the cometric
  `g₀⁻¹` single trace of the two contracted leading slots (frame-free, depending on `g₀` only through
  the smooth cometric Hom-section `inverseMetricSharpField`, NO chart-selected ambient frame).
* `crossCorrParallelContraction_covGrad_prod` — the **exact two-section parallel covariant Leibniz**
  `∇₀(prod S T) = (rank-cast) prod (∇₀S) T + prod S (∇₀T)`: the cross term differentiating the bilinear
  contraction itself vanishes because the cometric is parallel.
* `crossCorrParallelContraction_rfns_prod_le` — the fibrewise **`rfns` operator bound**
  `rfns(prod S T)(x) ≤ μ · rfns(S)(x) · rfns(T)(x)` with a base-point-uniform constant.
* `crossCorrRfnsBilinearProduct` — the assembled `RfnsBilinearProduct g₀ 2 3 3`, on which the diagonal
  `rfns` jet grid `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` is instantiated
  for the cross-correction product.

A reusable covariant-calculus byproduct (R1 — its own first-class home in the covariant-gradient API),
decoupled from the specific factor sections `realizeSymm Tₖ` / `loweredConnDiff gₖ g₀`: the instance is
generic over the two factors; the consumer (the difference-arm covariant-jet bound) instantiates it at
the realized perturbation and the lowered connection difference. -/

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
open DifferentialGeometry.Integral.Measure (chartModelBasis)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The fibrewise model single cometric contraction

The contraction `h ⌟ D` of a rank-`(2 + a)` factor `S` against a rank-`(3 + b)` factor `T` is the
fibrewise single `g₀`-contraction pairing one slot of `S` with one slot of `T` through the cometric
`g₀⁻¹` (frame-free).  Because the cometric is `∇₀`-parallel (`∇₀ g₀⁻¹ = 0`), the contraction is a
parallel fibrewise bilinear bundle map, so its covariant gradient obeys the exact two-section Leibniz
with no differentiated-map cross term, and it is fibrewise operator-bounded in the intrinsic `rfns`
currency.  These two genuine `∇`-compatibility facts are the parallel-contraction analogues, for a
**two-section** bilinear `g₀`-contraction, of the single-section trace facts `ricciModelTrace42Op_covGrad`
and `riemannianFiberNormSq_compRS_le_mul`; they are the genuine deep covariant-calculus content of the
cross-correction product, supplied here as the two `RfnsBilinearProduct` fields. -/

/-- **Model-fibre rank reindex `Tensor0SModel m → Tensor0SModel n` along `h : m = n`** (local
re-statement, via the isometric `domDomCongrₗᵢ (finCongr h)`; kept in this file so the construction
sits in the generic covariant-gradient layer with no dependence on the segment-metric DeTurck file). -/
noncomputable def modelRankCastCc {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap

/-- **The fibrewise model value of the single `g₀`-contraction `(0, 2 + a) ⊗ (0, 3 + b) →
(0, 3 + a + b)`.**  For each model-basis index `i`, raise the dual covector `eⁱ` by the cometric
reading `L` to a vector `♯eⁱ`, read `♯eⁱ` into the leading slot of `Sm` (`model_interior_product`) and
`eᵢ` into the leading slot of `Tm`, and tensor-multiply the two resulting reduced tensors
(`modelProduct`), summing over `i` — the single cometric trace of `Sm ⊗ Tm` pairing the leading slot of
each factor.  The reduced `Tm`-factor (the lowered connection-difference output side) leads the
product, so the result slots read `[Tm-reduced (2 + b), Sm-reduced (1 + a)]`; this is the output slot
order matched by the concrete cross-correction section `crossCorrectionSection` (connection-difference
input slots first, perturbation argument last).  Transported across the `Nat`-rank cast
`(3 + b − 1) + (2 + a − 1) = 3 + a + b` (here `(2 + b) + (1 + a) = 3 + a + b`).

Reads `g₀` only through the cometric reading `L : Tensor0SModel 1 ℝ E →L[ℝ] E`; frame-free.  Genuinely
fibrewise `ℝ`-bilinear (`model_interior_product` is linear in the tensor, `modelProduct` bilinear, the
finite sum linear), so it kills the zero tensor in either argument — non-vacuous. -/
noncomputable def crossCorrModelFun (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (a b : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (3 + b) ℝ E) :
    Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E :=
  modelRankCastCc (E := E) (by omega : (2 + b) + (1 + a) = 3 + a + b)
    (∑ i : Fin (Module.finrank ℝ E),
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (2 + b) (1 + a)
        (Tensor0SBundle.model_interior_product (2 + b) ((Module.finBasis ℝ E) i)
          (modelRankCastCc (E := E) (by omega : 3 + b = (2 + b) + 1) Tm))
        (Tensor0SBundle.model_interior_product (1 + a)
          (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
          (modelRankCastCc (E := E) (by omega : 2 + a = (1 + a) + 1) Sm)))

/-- **The model cometric reading at `x`** `Tensor0SModel 1 ℝ E →L[ℝ] E`: the fibrewise cometric
(inverse-metric sharp) `inverseMetricSharpFib g₀ x` read through the model identification
`tensor0SSpace_continuousLinearEquiv 1 x` (a model covector `α ↦ ♯α`).  The model reading of the
globally smooth cometric Hom-section `inverseMetricSharpField`; frame-free. -/
noncomputable def cometricReadingModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  (inverseMetricSharpFib (I := I) g₀ x).comp
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm.toContinuousLinearMap

/-- **The unit fibre value of a `(0, s)`-section as a model `Tensor0SModel s`.**  The `(0, s)`-tensor
fibre `S.toSection x : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` evaluated at the canonical unit
`(0, 0)`-tensor, read to the model.  This is the standard `(0, s)`-as-`Hom(scalar, ·)` unit extraction. -/
noncomputable def ccUnitModel {s : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 s) (x : M) : Tensor0SBundle.Tensor0SModel s ℝ E :=
  Tensor0SBundle.Tensor0SSpace.toModel
    ((S.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) 1))

/-- **Base-point smoothness of the cross-correction model fibre field** (POSITED deep construction
child).  The `Tensor0SModel (3 + a + b)`-valued total-space map `x ↦ ofModel (crossCorrModelFun
(cometricReadingModel g₀ x) a b (ccUnitModel S x) (ccUnitModel T x))` is smooth: the model contraction is
a finite sum over the model basis of continuous-bilinear `modelProduct`s of `model_interior_product`s of
the (trivialised, smooth) unit fibres of `S`, `T` against the globally smooth cometric Hom-section
`inverseMetricSharpField`, so the value is a smooth section — the same `clm_apply` model-bilinear
smoothness argument as `interiorProductField_contMDiff`, valid at the C^∞ level.  The fibre value is the
genuine non-vacuous single cometric trace `crossCorrModelFun`, not a packaged conclusion. -/
theorem crossCorrField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (3 + a + b) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) a b
            (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x)))) := by
  sorry

/-- **The cross-correction model fibre field** of the single `g₀`-contraction of two factor sections
`S`, `T`: the `Tensor0SSpace (3 + a + b)`-valued fibre `x ↦ ofModel (crossCorrModelFun
(cometricReadingModel g₀ x) a b (ccUnitModel S x) (ccUnitModel T x))`, the genuine non-vacuous single
cometric trace `crossCorrModelFun`.  Packaged as a `Tensor0SField` (a smooth `(3 + a + b)`-multilinear
section), smoothness by `crossCorrField_contMDiff`. -/
noncomputable def crossCorrField (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (3 + a + b) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (3 + a + b)
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) a b
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x)),
    crossCorrField_contMDiff (I := I) g₀ S T⟩

/-- **The section-level cross-correction parallel `g₀`-single contraction** `(0, 2 + a) ⊗ (0, 3 + b) →
(0, 3 + a + b)`: the smooth compactly-supported `(0, 3 + a + b)`-tensor packaging the model contraction
`crossCorrField` through `MixedSection.fromMultilinearSection` (the same packaging chain as
`crossCorrectionSection`); compact support automatic on the closed manifold `M`.  The fibre value is the
genuine non-vacuous single cometric trace (`crossCorrModelFun`), NOT a packaged conclusion. -/
noncomputable def crossCorrParallelContraction (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    SmoothCcTensor g₀ 0 (3 + a + b) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (crossCorrField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-! ## The concrete fibre identity: the parallel contraction realizes the cross-correction section

The re-targeted parallel `g₀`-single contraction, evaluated at the symmetric realized perturbation
`h = realizeSymm T₁` and the slot-cycled `g₀`-lowered connection difference, reproduces the nonlinear
cross-correction `(0, 3)`-section `crossCorrectionSection` exactly.  The model contraction reads the
two connection-difference input slots and the perturbation's second argument into the output, raising
the lowered connection-difference output index by the cometric and reconstructing the genuine
connection-difference output vector through the cometric dual-pair (`sum_phi_cometric_inner_basis`, the
rank-`1` specialization of the dual-pair coordinate-trace `sum_inner_dualPair_apply_eq_sum_chartBasis_repr`).
This certifies that `crossCorrRfnsBilinearProduct` is instantiated at the correct contraction (the
slot-`2` lowered output index, matching `crossCorrectionSection`), not the slot-`0` connection-difference
input index. -/

set_option linter.unusedSectionVars false in
theorem modelRankCastCc_apply' {m n : ℕ} (h : m = n) (T : Tensor0SBundle.Tensor0SModel m ℝ E)
    (v : Fin n → E) :
    modelRankCastCc (E := E) h T v = T (fun i => v (finCongr h i)) := by
  change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T v = _
  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T
      = ContinuousMultilinearMap.domDomCongr (finCongr h) T from rfl,
    ContinuousMultilinearMap.domDomCongr_apply]

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

/-! ## The two genuine `∇`-compatibility fields, and the assembled `RfnsBilinearProduct`

The two `RfnsBilinearProduct g₀ 2 3 3` fields below are the genuine deep covariant-calculus content of
the cross-correction product (the dispatch's "two fields, both genuine new covariant calculus").  They
are posited here as the deep children and discharged in dedicated builds; the parent — the assembled
instance `crossCorrRfnsBilinearProduct` and its diagonal `rfns` jet grid — is real composition on top. -/

/-- **The exact two-section parallel covariant Leibniz of the cross-correction `g₀`-single contraction**
(POSITED deep covariant-calculus child).  `∇₀(prod S T) = (rank-cast) prod (∇₀S) T + prod S (∇₀T)`: the
cross term differentiating the contraction itself vanishes because the cometric is `∇₀`-parallel
(`∇₀ g₀⁻¹ = 0`).  This is the **two-section** bilinear analogue of the single-section trace Leibniz
`ricciModelTrace42Op_covGrad`; the left summand carries covariant rank `(3 + (a + 1)) + b`, rank-cast to
`(3 + a + b) + 1` by `castRankCc_db`. -/
theorem crossCorrParallelContraction_covGrad_prod (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    covGrad g₀ 0 (3 + a + b) (crossCorrParallelContraction (I := I) g₀ S T) =
      castRankCc_db g₀ 0 (by omega : 3 + (a + 1) + b = 3 + a + b + 1)
          (crossCorrParallelContraction (I := I) g₀ (a := a + 1) (b := b)
            (covGrad g₀ 0 (2 + a) S) T) +
        crossCorrParallelContraction (I := I) g₀ (a := a) (b := b + 1) S
          (covGrad g₀ 0 (3 + b) T) := by
  sorry

/-- **The base-point-uniform `rfns` operator bound of the cross-correction `g₀`-single contraction**
(POSITED deep covariant-calculus child).  There is a nonnegative constant `μ`, uniform over the two
factors `S`, `T`, the shifts `a`, `b`, and the base point `x`, with `rfns(prod S T)(x) ≤ μ · rfns(S)(x) ·
rfns(T)(x)` — the fibrewise continuity/boundedness of the parallel bilinear `g₀`-contraction in the
intrinsic squared fibre-norm currency.  This is the **two-section** bilinear analogue of the
single-section partial-trace Cauchy–Schwarz `riemannianFiberNormSq_compRS_le_mul` (the contraction is
fibrewise bounded by the operator norm of the cometric pairing).  The existence form yields the constant
`mu` and the bound together for the assembled instance. -/
theorem exists_uniform_crossCorrParallelContraction_rfns_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∀ {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a))
      (T : SmoothCcTensor g₀ 0 (3 + b)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + a + b) x
          ((crossCorrParallelContraction (I := I) g₀ S T).toSection x) ≤
        μ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by
  sorry

/-- **The assembled `RfnsBilinearProduct g₀ 2 3 3` for the cross-correction `g₀`-single contraction
`h ⌟ D`.**  The parallel fibrewise bilinear product `prod (realizeSymm Tₖ) (loweredConnDiff gₖ g₀)`
packaged as a `RfnsBilinearProduct`, assembled from the concrete contraction `crossCorrParallelContraction`
and its two genuine `∇`-compatibility fields (the exact two-section parallel covariant Leibniz
`crossCorrParallelContraction_covGrad_prod` and the uniform `rfns` operator bound
`exists_uniform_crossCorrParallelContraction_rfns_le`).

On this instance the cross-correction-difference and quadratic-Cross covariant-Faà-di-Bruno arms cite the
diagonal `rfns` jet grid `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` (the exact
pointwise shape the integrated Gagliardo–Nirenberg two-arm engine consumes).  Decoupled from the specific
factor sections; the consumer instantiates `prod` at `realizeSymmCcTensor g₀ Tₖ` and
`loweredConnDiffSection gₖ g₀`. -/
noncomputable def crossCorrRfnsBilinearProduct (g₀ : SmoothRiemannianMetric I M) :
    RfnsBilinearProduct g₀ 2 3 3 where
  prod := fun S T => crossCorrParallelContraction (I := I) g₀ S T
  covGrad_prod := fun S T => crossCorrParallelContraction_covGrad_prod (I := I) g₀ S T
  mu := (exists_uniform_crossCorrParallelContraction_rfns_le (I := I) g₀).choose
  mu_nonneg := (exists_uniform_crossCorrParallelContraction_rfns_le (I := I) g₀).choose_spec.1
  rfns_prod_le := fun S T x =>
    (exists_uniform_crossCorrParallelContraction_rfns_le (I := I) g₀).choose_spec.2 S T x

/-- **The diagonal `rfns` jet grid for the cross-correction `g₀`-single contraction `h ⌟ D`.**  The
consumer-facing specialisation of `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` at
the assembled cross-correction instance `crossCorrRfnsBilinearProduct`: for the two factors `h`, `D`
(here a rank-`2` factor `S` and a rank-`3` factor `T`), there is a nonnegative order-dependent constant
`C`, uniform over the factors and the base point, with the diagonal (convolution) product grid
```
rfns(∇^j (h ⌟ D))(x) ≤ C j · ∑_{i ≤ j} rfns(∇^i h)(x) · (∑_{l ≤ j − i} rfns(∇^l D)(x)).
```
This is exactly the pointwise shape the integrated Gagliardo–Nirenberg two-arm engine consumes; P1/LEAF2
instantiate `S := realizeSymmCcTensor g₀ Tₖ`, `T := loweredConnDiffSection gₖ g₀`. -/
theorem exists_rfns_iteratedCovGrad_crossCorrProd_diagGrid_le (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (T : SmoothCcTensor g₀ 0 3) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (x : M) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
          ((iteratedCovGrad g₀ 0 3 j
            ((crossCorrRfnsBilinearProduct (I := I) g₀).prod (a := 0) (b := 0) S T)).toSection x) ≤
        C j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad g₀ 0 2 i S).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad g₀ 0 3 l T).toSection x) :=
  (crossCorrRfnsBilinearProduct (I := I) g₀).exists_rfns_iteratedCovGrad_prod_diagGrid_le S T

end Connection
end Integral
end DifferentialGeometry

end
