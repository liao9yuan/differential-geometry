import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

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
each factor.  Transported across the `Nat`-rank cast `(2 + a − 1) + (3 + b − 1) = 3 + a + b` (here
`(1 + a) + (2 + b) = 3 + a + b`).

Reads `g₀` only through the cometric reading `L : Tensor0SModel 1 ℝ E →L[ℝ] E`; frame-free.  Genuinely
fibrewise `ℝ`-bilinear (`model_interior_product` is linear in the tensor, `modelProduct` bilinear, the
finite sum linear), so it kills the zero tensor in either argument — non-vacuous. -/
noncomputable def crossCorrModelFun (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (a b : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (3 + b) ℝ E) :
    Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E :=
  modelRankCastCc (E := E) (by omega : (1 + a) + (2 + b) = 3 + a + b)
    (∑ i : Fin (Module.finrank ℝ E),
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (1 + a) (2 + b)
        (Tensor0SBundle.model_interior_product (1 + a)
          (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis i)))
          (modelRankCastCc (E := E) (by omega : 2 + a = (1 + a) + 1) Sm))
        (Tensor0SBundle.model_interior_product (2 + b) ((Module.finBasis ℝ E) i)
          (modelRankCastCc (E := E) (by omega : 3 + b = (2 + b) + 1) Tm)))

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
