import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
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

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the model-fibre rank reindex.**  `modelRankCastCc h T` evaluated on a
`Fin n`-tuple `v` reads `T` on the rank-`m` reindexed tuple `i ↦ v (finCongr h i)`. -/
theorem modelRankCastCc_apply' {m n : ℕ} (h : m = n) (T : Tensor0SBundle.Tensor0SModel m ℝ E)
    (v : Fin n → E) :
    modelRankCastCc (E := E) h T v = T (fun i => v (finCongr h i)) := by
  change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T v = _
  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ (finCongr h)) T
      = ContinuousMultilinearMap.domDomCongr (finCongr h) T from rfl,
    ContinuousMultilinearMap.domDomCongr_apply]

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

/-- **The cross-correction slot permutation** `Fin ((3 + b) + (2 + a)) ≃ Fin ((3 + b) + (2 + a))`.
On the model product `Tm ⊗ Sm` (the `Tm`-block leading) it rotates the leading `4 + b` slots
cyclically — sending the `Sm`-leading slot (model-product index `3 + b`) to position `0`, the
`Tm`-leading slot (index `0`) to position `1`, the remaining `Tm` slots to positions `2 … 3 + b`,
and fixing the trailing `Sm` slots — so that after `domDomCongr` the two slots to be contracted
through the cometric (`Sm`-slot-`0`, `Tm`-slot-`0`) become the leading adjacent pair, matching the
slot convention of the model double trace `modelDoubleTrace`/`cometricRaiseSlot0Fib`.  Built as
`finRotate ((3 + b) + 1)` on the leading block and the identity on the trailing `1 + a` block. -/
noncomputable def crossCorrPerm (a b : ℕ) : Equiv.Perm (Fin ((3 + b) + (2 + a))) :=
  (finCongr (by omega : ((3 + b) + 1) + (1 + a) = (3 + b) + (2 + a))).permCongr
    (finSumFinEquiv.permCongr (Equiv.sumCongr (finRotate ((3 + b) + 1)) (Equiv.refl (Fin (1 + a)))))

set_option linter.unusedSectionVars false in
/-- The cross-correction permutation reads a `Tm`-block slot `castAdd (2 + a) j` to model-product
position `1 + j` (the `Tm`-leading slot moves to position `1`, the remaining `Tm` slots shift up by one). -/
theorem crossCorrPerm_castAdd (a b : ℕ) (j : Fin (3 + b)) :
    ((crossCorrPerm a b) (Fin.castAdd (2 + a) j)).val = 1 + j.val := by
  unfold crossCorrPerm
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Equiv.sumCongr_apply]
  rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = ((3 + b) + 1) + (1 + a)) (Fin.castAdd (2 + a) j))
      = Fin.castAdd (1 + a) (Fin.castSucc j) from by
    apply Fin.ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]]
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp only [Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd,
    finRotate_succ_apply, Fin.val_add_one_of_lt (Fin.castSucc_lt_last j), Fin.val_castSucc]
  omega

set_option linter.unusedSectionVars false in
/-- The cross-correction permutation reads an `Sm`-block slot `natAdd (3 + b) k` to model-product
position `0` when `k = 0` (the `Sm`-leading slot moves to position `0`) and to position `(3 + b) + k`
otherwise (the remaining `Sm` slots are fixed). -/
theorem crossCorrPerm_natAdd (a b : ℕ) (k : Fin (2 + a)) :
    ((crossCorrPerm a b) (Fin.natAdd (3 + b) k)).val
      = if k.val = 0 then 0 else (3 + b) + k.val := by
  unfold crossCorrPerm
  simp only [Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Equiv.sumCongr_apply]
  rcases Nat.eq_zero_or_pos k.val with hk | hk
  · rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = ((3 + b) + 1) + (1 + a)) (Fin.natAdd (3 + b) k))
        = Fin.castAdd (1 + a) (Fin.last (3 + b)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega]
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Sum.map_inl, finSumFinEquiv_apply_left, finRotate_last, Fin.val_cast, Fin.val_castAdd]
    simp [hk]
  · rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = ((3 + b) + 1) + (1 + a)) (Fin.natAdd (3 + b) k))
        = Fin.natAdd ((3 + b) + 1) (⟨k.val - 1, by omega⟩ : Fin (1 + a)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd]; omega]
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp only [Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
    rw [if_neg (by omega)]; omega

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **`domDomCongr` of a smooth `(0, n)`-tensor field is smooth.**  Permuting the slots of a smooth
`(0, n)`-tensor field by a fixed index permutation `σ` reindexes only the trivialised basis coordinate
(the trivialisation commutes with `domDomCongr`, both acting through the fibre `symmL`); so the permuted
field is smooth by the basis-coordinate criterion `contMDiff_multilinearSection_iff_coord` (its coordinate
at `τ` is the original field's coordinate at `τ ∘ σ`).  A generic covariant-calculus byproduct. -/
theorem tensor0SField_domDomCongr_contMDiff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace n I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
        Tensor0SBundle.Tensor0SSpace n I x))).mpr ?_
  have hY' := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Y x : Tensor0SBundle.Tensor0SSpace n I x))).mp hY
  intro τ x₀
  refine (hY' (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
    (Bundle.continuousMultilinearMap ℝ n E (TangentSpace I)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  rfl

/-- **The frame-free (unpermuted) model product field** `x ↦ ofModel (modelProduct (ccUnitModel T x)
(ccUnitModel S x))`, a smooth `(0, (3 + b) + (2 + a))`-tensor field.  The model product of the smooth
unit fibres of `T`, `S` is smooth: its trivialised coordinate factors, by `modelProduct_apply`, into a
product of a `T`-coordinate and an `S`-coordinate (the basis-coordinate criterion
`contMDiff_multilinearSection_iff_coord`).  Frame-free; carries NO cometric. -/
theorem crossCorrProdUnpermField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I z) x
        ((Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
              (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)) :
            Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((3 + b) + (2 + a))
  classical
  have hTfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (3 + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (3 + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (3 + b) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (ccUnitModel (I := I) g₀ T x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) g₀ (3 + b) T)
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (ccUnitModel (I := I) g₀ S x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) g₀ (2 + a) S)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
          (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)) :
          Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))).mpr ?_
  have hT := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (ccUnitModel (I := I) g₀ T x) :
      Tensor0SBundle.Tensor0SSpace (3 + b) I x))).mp hTfield
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (ccUnitModel (I := I) g₀ S x) :
      Tensor0SBundle.Tensor0SSpace (2 + a) I x))).mp hSfield
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := ∞)
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hT (τ ∘ Fin.castAdd (2 + a)) x₀)).clm_apply
        (hS (τ ∘ Fin.natAdd (3 + b)) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
      (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

/-- **The cross-correction permuted model product field** `x ↦ ofModel (domDomCongr (crossCorrPerm)
(modelProduct (ccUnitModel T x) (ccUnitModel S x)))`, a smooth `(0, (3 + b) + (2 + a))`-tensor field.
The model product of the smooth unit fibres of `T`, `S` is a smooth field
(`crossCorrProdUnpermField_contMDiff`), and the slot permutation preserves smoothness
(`tensor0SField_domDomCongr_contMDiff`).  Frame-free: the field carries NO cometric — the cometric
enters only later through the parallel raise. -/
theorem crossCorrProdField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
              (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((3 + b) + (2 + a))
  classical
  -- the permuted product field smoothness; the target's model product matches `toModel (ofModel _)`.
  refine (tensor0SField_domDomCongr_contMDiff (crossCorrPerm a b)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
          (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)) :
          Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))
    (crossCorrProdUnpermField_contMDiff (I := I) g₀ S T)).congr (fun x => ?_)
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
/-- The `Tm`-factor tuple identity: the leading `Tm`-block of the cometric-raised slot-permuted product,
read off the double-trace cons-tuple, coincides with the `Tm` interior-product argument tuple of
`crossCorrModelFun`. -/
private theorem crossCorrTm_tuple (a b : ℕ) (p q : E) (m : Fin (3 + a + b) → E) :
    (fun j : Fin (3 + b) => (Fin.cons p (Fin.cons q m) : Fin ((3 + a + b) + 2) → E)
        (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          ((crossCorrPerm a b) (Fin.castAdd (2 + a) j))))
      = (Fin.cons q (fun i : Fin (2 + b) => m (Fin.cast (by omega : (2 + b) + (1 + a) = 3 + a + b)
            (Fin.castAdd (1 + a) i))) : Fin ((2 + b) + 1) → E)
          ∘ Fin.cast (by omega : 3 + b = (2 + b) + 1) := by
  funext j
  rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
        ((crossCorrPerm a b) (Fin.castAdd (2 + a) j)))
      = (⟨1 + j.val, by omega⟩ : Fin ((3 + a + b) + 2)) from by
    apply Fin.ext; rw [Fin.val_cast, crossCorrPerm_castAdd]]
  rw [show (⟨1 + j.val, by omega⟩ : Fin ((3 + a + b) + 2)) = Fin.succ ⟨j.val, by omega⟩ from by
    apply Fin.ext; simp only [Fin.val_succ]; omega]
  rw [Fin.cons_succ]
  simp only [Function.comp_apply]
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · rw [show (⟨j.val, by omega⟩ : Fin ((3 + a + b) + 1)) = (0 : Fin ((3 + a + b) + 1)) from
      Fin.ext (by rw [Fin.val_zero]; exact hj)]
    rw [Fin.cons_zero]
    rw [show (Fin.cast (by omega : 3 + b = (2 + b) + 1) j) = (0 : Fin ((2 + b) + 1)) from
      Fin.ext (by rw [Fin.val_cast, Fin.val_zero]; exact hj)]
    rw [Fin.cons_zero]
  · rw [show (⟨j.val, by omega⟩ : Fin ((3 + a + b) + 1)) = Fin.succ ⟨j.val - 1, by omega⟩ from by
      apply Fin.ext; simp only [Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    rw [show (Fin.cast (by omega : 3 + b = (2 + b) + 1) j) = Fin.succ (⟨j.val - 1, by omega⟩ : Fin (2 + b)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    rfl

set_option linter.unusedSectionVars false in
/-- The `Sm`-factor tuple identity: the trailing `Sm`-block of the cometric-raised slot-permuted product,
read off the double-trace cons-tuple, coincides with the `Sm` interior-product argument tuple of
`crossCorrModelFun`. -/
private theorem crossCorrSm_tuple (a b : ℕ) (Lc q : E) (m : Fin (3 + a + b) → E) :
    (fun l : Fin (2 + a) => (Fin.cons Lc (Fin.cons q m) : Fin ((3 + a + b) + 2) → E)
        (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          ((crossCorrPerm a b) (Fin.natAdd (3 + b) l))))
      = (Fin.cons Lc (fun i : Fin (1 + a) => m (Fin.cast (by omega : (2 + b) + (1 + a) = 3 + a + b)
            (Fin.natAdd (2 + b) i))) : Fin ((1 + a) + 1) → E)
          ∘ Fin.cast (by omega : 2 + a = (1 + a) + 1) := by
  funext l
  simp only [Function.comp_apply]
  rcases Nat.eq_zero_or_pos l.val with hl | hl
  · rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          ((crossCorrPerm a b) (Fin.natAdd (3 + b) l)))
        = (0 : Fin ((3 + a + b) + 2)) from by
      apply Fin.ext; rw [Fin.val_cast, crossCorrPerm_natAdd, Fin.val_zero, if_pos hl]]
    rw [Fin.cons_zero]
    rw [show (Fin.cast (by omega : 2 + a = (1 + a) + 1) l) = (0 : Fin ((1 + a) + 1)) from
      Fin.ext (by rw [Fin.val_cast, Fin.val_zero]; exact hl)]
    rw [Fin.cons_zero]
  · rw [show (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          ((crossCorrPerm a b) (Fin.natAdd (3 + b) l)))
        = Fin.succ (Fin.succ (⟨(1 + b) + l.val, by omega⟩ : Fin (3 + a + b))) from by
      apply Fin.ext; rw [Fin.val_cast, crossCorrPerm_natAdd, if_neg (by omega)]
      simp only [Fin.val_succ]; omega]
    rw [Fin.cons_succ, Fin.cons_succ]
    rw [show (Fin.cast (by omega : 2 + a = (1 + a) + 1) l) = Fin.succ (⟨l.val - 1, by omega⟩ : Fin (1 + a)) from by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
    exact congrArg m (Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega))

set_option linter.unusedSectionVars false in
/-- **The cross-correction single cometric trace is the model double trace of the permuted product.**
The genuine single `g₀⁻¹` contraction `crossCorrModelFun L a b Sm Tm` equals the FRAME-FREE model double
trace `modelDoubleTrace (3 + a + b) L` (raise the leading slot by `L`, natural-trace it against the next)
of the rank-cast slot-permuted model product `Tm ⊗ Sm` (`crossCorrPerm` brings the two slots to be
contracted to the leading adjacent pair).  This re-presents the two-factor cometric contraction as a
single-tensor leading-slot raise-and-trace, the form whose smoothness is the parallel-raise/natural-trace
field calculus. -/
theorem crossCorrModelFun_eq_modelDoubleTrace_perm
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) (a b : ℕ)
    (Sm : Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (Tm : Tensor0SBundle.Tensor0SModel (3 + b) ℝ E) :
    crossCorrModelFun (E := E) L a b Sm Tm =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b) L
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
            (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a) Tm Sm))) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply]
  unfold crossCorrModelFun
  rw [modelRankCastCc_apply', ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  -- reduce the double-trace summand `D (cons (L cᵏ) (cons eₖ m))` to `Tm(tupleT) * Sm(tupleS)`.
  have hDsummand : (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
        (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a) Tm Sm)))
        (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) m))
      = Tm ((fun j : Fin (3 + b) => (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin ((3 + a + b) + 2) → E)
            (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
              ((crossCorrPerm a b) (Fin.castAdd (2 + a) j)))))
          * Sm ((fun l : Fin (2 + a) => (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin ((3 + a + b) + 2) → E)
            (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
              ((crossCorrPerm a b) (Fin.natAdd (3 + b) l))))) := by
    change (ContinuousMultilinearMap.domDomCongr
          (finCongr (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2))
          (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a) Tm Sm))) _ = _
    rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  rw [hDsummand]
  -- the `crossCorrModelFun` summand is `Tm(tupleT) * Sm(tupleS)` for the SAME tuples (interior products
  -- reduce to the rank-cast cons-tuples, matched by the tuple identities `crossCorrTm/Sm_tuple`).
  rw [crossCorrTm_tuple a b _ ((Module.finBasis ℝ E) k) m,
    crossCorrSm_tuple a b (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k) m]
  rfl


/-- **Base-point smoothness of the cross-correction model fibre field**.  The `Tensor0SModel (3 + a + b)`-
valued total-space map `x ↦ ofModel (crossCorrModelFun (cometricReadingModel g₀ x) a b (ccUnitModel S x)
(ccUnitModel T x))` is smooth.  Frame-free route: by `crossCorrModelFun_eq_modelDoubleTrace_perm` the
fibre value is the model double trace `modelDoubleTrace (3 + a + b) (cometricLmodel g₀ x)` of the smooth
rank-cast slot-permuted product field `crossCorrProdField`; that double trace is realized as the
leading-slot cometric raise (`cometricRaiseSlot0Fib`, smooth through the globally-smooth cometric
Hom-section `inverseMetricSharpField` on the *variable* covector) followed by the FRAME-FREE natural trace
(`contractTraceField`) at the unit — the SAME raise-then-trace calculus as `ricciModelTrace42Fib_contMDiff`,
with NO chart-selected ambient frame.  Non-vacuous: the genuine single cometric trace `crossCorrModelFun`. -/
theorem crossCorrField_contMDiff (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (3 + a + b) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) a b
            (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x)))) := by
  -- the rank-cast slot-permuted product field `D`, a smooth `(0, (3 + a + b) + 2)`-tensor field.
  set D : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
        (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
        (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)))) with hD
  have hDsmooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((3 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((3 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I z) x (D x)) := by
    refine (tensor0SField_castRank_contMDiff (I := I) (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))) :
              Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))
      (crossCorrProdField_contMDiff (I := I) g₀ S T)).congr (fun x => ?_)
    rw [hD]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  -- the smooth cometric raise of `D`'s leading slot.
  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (3 + a + b) D hDsmooth
  -- the FRAME-FREE natural trace of the raise, then evaluate at the unit `(0, 0)`-tensor.
  have htrace := contractTraceField_contMDiff (I := I) 0 (3 + a + b)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (D x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (3 + a + b) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (3 + a + b) x
            (cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (D x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    crossCorrModelFun_eq_modelDoubleTrace_perm (cometricReadingModel (I := I) g₀ x) a b
      (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x)]
  rw [show cometricReadingModel (I := I) g₀ x
      = DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x from rfl]
  rw [← DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.model_contract_trace_raiseSlot0ModelL
    (E := E) (3 + a + b) (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
    (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
      (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
      (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
          (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))))]
  rw [contract_trace_unitZero_toModel (I := I) (3 + a + b) x
    (cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (D x))]
  congr 1

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

/-! ## The operator-field bridge: the parallel contraction as a fixed-cometric post-composition

The cross-correction `g₀`-single contraction `crossCorrParallelContraction g₀ S T` factors, fibrewise,
as the post-composition of a **fixed** smooth cometric double-trace operator field
`crossCorrCometricOp g₀ a b` (a `((3 + b) + (2 + a), 3 + a + b)`-operator field, reading `g₀` only
through the `∇₀`-parallel cometric `g₀⁻¹`) after the **frame-free** slot-permuted model tensor-product
section `crossCorrProdSection g₀ S T` (a `(0, (3 + b) + (2 + a))`-tensor, carrying NO cometric).  This is
the bilinear analogue of the operator-field action route used by `ricciModelTrace42Op`: it reduces both
`∇`-compatibility facts to the operator-field B-rule `covGrad_appCcRS_eq` (the cometric being parallel,
the differentiated-field cross term vanishes) and the partial-contraction Cauchy–Schwarz
`riemannianFiberNormSq_compRS_le_mul`, with the genuine two-section content carried by the product
section `crossCorrProdSection` (its own two-section covariant Leibniz and operator bound) and the
slot-permuted reconciliation of the operator field. -/

/-- **The frame-free slot-permuted model tensor-product section** `(0, (3 + b) + (2 + a))` of the unit
fibres of `T`, `S`: `x ↦ ofModel (domDomCongr (crossCorrPerm a b) (modelProduct (ccUnitModel T x)
(ccUnitModel S x)))`, the pure tensor product carrying NO cometric (the cometric enters only through the
post-composed operator field).  Smooth by `crossCorrProdField_contMDiff`; compact support automatic. -/
noncomputable def crossCorrProdField (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ ((3 + b) + (2 + a)) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((3 + b) + (2 + a))
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
          (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))),
    crossCorrProdField_contMDiff (I := I) g₀ S T⟩

noncomputable def crossCorrProdSection (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    SmoothCcTensor g₀ 0 ((3 + b) + (2 + a)) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (crossCorrProdField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The frame-free UNPERMUTED model tensor-product field** `x ↦ ofModel (modelProduct (ccUnitModel T x)
(ccUnitModel S x))`, the slot-permuted product section's pre-image under `crossCorrPerm` (`Tm`-block
leading, then `Sm`-block).  Smooth by `crossCorrProdUnpermField_contMDiff`. -/
noncomputable def crossCorrProdUnpermField (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ ((3 + b) + (2 + a)) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ((3 + b) + (2 + a))
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)),
    crossCorrProdUnpermField_contMDiff (I := I) g₀ S T⟩

/-- **The frame-free UNPERMUTED model tensor-product section** packaging `crossCorrProdUnpermField`. -/
noncomputable def crossCorrProdUnpermSection (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    SmoothCcTensor g₀ 0 ((3 + b) + (2 + a)) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (crossCorrProdUnpermField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The fibre value of the cometric double-trace operator field at `x`: the model-level cometric double
trace `D ↦ ofModel (modelDoubleTrace (3 + a + b) (cometricLmodel g₀ x) (modelRankCast (toModel D)))`,
mapping a `(0, (3 + b) + (2 + a))`-tensor to a `(0, 3 + a + b)`-tensor.  Built — exactly as the
operator-field sibling `ricciModelTrace42Fib` — as the single model continuous-linear map
`modelDoubleTrace (3 + a + b) (cometricLmodel g₀ x) ∘ modelRankCast` sandwiched by the identity
`tensor0SSpace_continuousLinearEquiv` fibre/model bridge (which carries the canonical multilinear-map
topology to the `Tensor0SSpace` operator topology, the standard `tensor0SSpace_topology_eq` plumbing).
The frame-free cometric raise of slot `0` then the natural trace against the original slot are folded into
`modelDoubleTrace`; `g₀` enters only through the SMOOTH cometric reading `cometricLmodel`.  Non-vacuous:
the genuine single cometric trace. -/
private noncomputable def crossCorrCometricOpFib (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace ((3 + b) + (2 + a)) (3 + a + b) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (3 + a + b) x).symm.toContinuousLinearMap.comp
    ((DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)).comp
      ((DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((3 + b) + (2 + a)) x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- The model image of the cometric double-trace fibre operator is the model `modelDoubleTrace` against
the cometric reading on the rank-cast model input.  Definitional, since `Tensor0SSpace.toModel =
tensor0SSpace_continuousLinearEquiv` is the identity. -/
private theorem crossCorrCometricOpFib_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from crossCorrCometricOpFib (I := I) g₀ a b x) P) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel P)) := rfl

/-- **Base-point smoothness of the cometric double-trace operator field.**  Mirrors
`crossCorrField_contMDiff`: the field is the fibre rank-cast followed by the cometric raise
(`cometricRaiseSlot0Fib_section_contMDiff`, smooth through the globally smooth cometric Hom-section
`inverseMetricSharpField`) and the frame-free natural trace (`contractTraceField_contMDiff`), lifted
from per-vector to operator smoothness by `contMDiff_clm_section_of_pointwise`.  POSITED child paired
with the fibre value `crossCorrCometricOpFib`. -/
private theorem crossCorrCometricOpFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel ((3 + b) + (2 + a)) (3 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel ((3 + b) + (2 + a)) (3 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace ((3 + b) + (2 + a)) (3 + a + b) I z) x
        (crossCorrCometricOpFib (I := I) g₀ a b x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (3 + a + b) I x)
    (φ := fun x => crossCorrCometricOpFib (I := I) g₀ a b x)
  intro Y
  -- The rank-cast of `Y` to a `(0, (3 + a + b) + 2)`-field (a fixed model CLM, smoothness-preserving).
  let Y' : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
        (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
  have hY' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((3 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((3 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I z) x (Y' x)) :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensor0SField_castRank_contMDiff
      (I := I) (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) (fun x => Y x) Y.contMDiff
  -- The smooth cometric raise of `Y'`'s leading slot.
  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (3 + a + b) Y' hY'
  -- The frame-free natural trace of the raise (smooth `(0, 3 + a + b)`-field).
  have htrace := contractTraceField_contMDiff (I := I) 0 (3 + a + b)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (Y' x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (3 + a + b) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (3 + a + b) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (3 + a + b) x
            (cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  refine htraceUnit.congr (fun x => ?_)
  -- the matching fibre identity: crossCorrCometricOpFib g₀ a b x (Y x) = trace(raise Y')(unit)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrCometricOpFib_toModel]
  -- modelDoubleTrace (3+a+b) (cometricLmodel g₀ x) (modelRankCast (toModel (Y x)))
  --   = toModel ((contract_trace 0 (3+a+b) x (raise (Y' x))) (unit0))
  rw [← DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.model_contract_trace_raiseSlot0ModelL
    (E := E) (3 + a + b) (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
    (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
      (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))]
  rw [contract_trace_unitZero_toModel (I := I) (3 + a + b) x
    (cometricRaiseSlot0Fib (I := I) g₀ (3 + a + b) x (Y' x))]
  congr 1

/-- **The fixed smooth cometric double-trace operator field** as a `SmoothCcTensor`, packaging the
fibre value `crossCorrCometricOpFib` (smooth by `crossCorrCometricOpFib_contMDiff`); compact support
automatic on the closed manifold. -/
private noncomputable def crossCorrCometricOp (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    SmoothCcTensor g₀ ((3 + b) + (2 + a)) (3 + a + b) where
  toSection :=
    { toFun := fun x : M => crossCorrCometricOpFib (I := I) g₀ a b x
      contMDiff_toFun := crossCorrCometricOpFib_contMDiff (I := I) g₀ a b }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The parallel contraction is the operator-field action of the fixed cometric double-trace field
on the frame-free product section** (POSITED bridge child).  `crossCorrParallelContraction g₀ S T =
appCcRS g₀ 0 ((3 + b) + (2 + a)) (3 + a + b) (crossCorrCometricOp g₀ a b) (crossCorrProdSection g₀ S T)`:
the fibre value of the contraction (`crossCorrModelFun = modelDoubleTrace ∘ modelRankCast ∘ perm ∘
modelProduct`, `crossCorrModelFun_eq_modelDoubleTrace_perm`) is the post-composition of the fixed
cometric trace operator after the slot-permuted model product, fibrewise. -/
private theorem crossCorrParallelContraction_eq_appCcRS (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ S T =
      appCcRS (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
        (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 3 + a + b)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  -- LHS at the unit: the model value `crossCorrModelFun (cometricReadingModel g₀ x) a b (ccUnit S)(ccUnit T)`.
  have hLHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((crossCorrParallelContraction (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) a b
        (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x) := by
    change Tensor0SBundle.Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
            (crossCorrField (I := I) g₀ S T x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.Tensor0SSpace.ofModel
        (crossCorrModelFun (E := E) (cometricReadingModel (I := I) g₀ x) a b
          (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x))) = _
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  -- RHS at the unit: the post-composition of the fixed cometric trace operator on the product fibre.
  have hRHS : Tensor0SBundle.Tensor0SSpace.toModel
      ((appCcRS (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
          (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T)).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
          (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
              (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)))) := by
    rw [appCcRS_toSection (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
      (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T) x]
    rw [ContinuousLinearMap.comp_apply]
    rw [show (crossCorrCometricOp (I := I) g₀ a b).toSection x
        = crossCorrCometricOpFib (I := I) g₀ a b x from rfl]
    rw [crossCorrCometricOpFib_toModel]
    -- the product section's fibre value at the unit, read to the model.
    have hP : Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from
          (crossCorrProdSection (I := I) g₀ S T).toSection x)
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
        ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)) := by
      change Tensor0SBundle.Tensor0SSpace.toModel
          ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
              (crossCorrProdField (I := I) g₀ S T x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) = _
      rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
        ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
      change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
              (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)))) = _
      rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [hP]
  rw [hLHS, hRHS,
    crossCorrModelFun_eq_modelDoubleTrace_perm (cometricReadingModel (I := I) g₀ x) a b
      (ccUnitModel (I := I) g₀ S x) (ccUnitModel (I := I) g₀ T x),
    show cometricReadingModel (I := I) g₀ x
        = DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x from rfl]

set_option linter.unusedVariables false in
/-- **The fixed source-rank reindex operator field** `(0, (3 + b) + (2 + a)) → (0, (3 + a + b) + 2)`,
the pure `Nat`-rank reindex of the source covariant slots along `(3 + b) + (2 + a) = (3 + a + b) + 2`
(both `= 5 + a + b`), built fibrewise as `equiv((3 + a + b) + 2).symm ∘ modelRankCast H ∘
equiv((3 + b) + (2 + a))`, frame-free (carries NO cometric, depends on `g₀` only as the bundle's base
metric).  Smoothness routes through `tensor0SField_castRank_contMDiff` (the fixed model `modelRankCast`
preserves section smoothness), lifted to operator smoothness by `contMDiff_clm_section_of_pointwise`.
The metric `g₀` is a phantom parameter (the reindex is frame-free); it is retained so the packaged
`crossCorrSourceReindex` lands in `SmoothCcTensor g₀`. -/
private noncomputable def crossCorrSourceReindexFib (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace ((3 + b) + (2 + a)) ((3 + a + b) + 2) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((3 + a + b) + 2) x).symm.toContinuousLinearMap.comp
    ((DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
        (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) ((3 + b) + (2 + a)) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- `toModel` of the source reindex is the model rank cast. -/
private theorem crossCorrSourceReindexFib_toModel (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (crossCorrSourceReindexFib (I := I) g₀ a b x P) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel P) := rfl

private theorem crossCorrSourceReindexFib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel ((3 + b) + (2 + a)) ((3 + a + b) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel ((3 + b) + (2 + a)) ((3 + a + b) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace ((3 + b) + (2 + a)) ((3 + a + b) + 2) I z) x
        (crossCorrSourceReindexFib (I := I) g₀ a b x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel ((3 + a + b) + 2) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x)
    (φ := fun x => crossCorrSourceReindexFib (I := I) g₀ a b x)
  intro Y
  exact (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensor0SField_castRank_contMDiff
    (I := I) (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) (fun x => Y x) Y.contMDiff).congr
    (fun x => rfl)

/-- **The fixed source-rank reindex operator field** as a `SmoothCcTensor`. -/
private noncomputable def crossCorrSourceReindex (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    SmoothCcTensor g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) where
  toSection :=
    { toFun := fun x : M => crossCorrSourceReindexFib (I := I) g₀ a b x
      contMDiff_toFun := crossCorrSourceReindexFib_contMDiff (I := I) g₀ a b }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The cometric double-trace operator field factors as the rank-generic double-trace field after
the source reindex.**  `crossCorrCometricOp g₀ a b = appCcRS g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2)
(3 + a + b) (cometricDoubleTraceField g₀ (3 + a + b)) (crossCorrSourceReindex g₀ a b)`: fibrewise the
single cometric trace `crossCorrCometricOpFib` is `cometricDoubleTraceFib g₀ (3 + a + b)` post-composed
after the source reindex (both `toModel`-equal `modelDoubleTrace (3 + a + b) (cometricLmodel) ∘
modelRankCast H`, the rank-generic field's reflexive `modelRankCast` collapsing to the identity). -/
private theorem crossCorrCometricOp_eq_appCcRS_cometricDoubleTraceField (g₀ : SmoothRiemannianMetric I M)
    (a b : ℕ) :
    crossCorrCometricOp (I := I) g₀ a b =
      appCcRS (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) (3 + a + b)
        (cometricDoubleTraceField (I := I) g₀ (3 + a + b)) (crossCorrSourceReindex (I := I) g₀ a b) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro P
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
      ((crossCorrCometricOp (I := I) g₀ a b).toSection x P) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) (Tensor0SBundle.Tensor0SSpace.toModel P)) :=
    crossCorrCometricOpFib_toModel (I := I) g₀ a b x P
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
      ((appCcRS (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) (3 + a + b)
          (cometricDoubleTraceField (I := I) g₀ (3 + a + b)) (crossCorrSourceReindex (I := I) g₀ a b)).toSection x P) =
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace (E := E) (3 + a + b)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel (I := I) g₀ x)
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
          (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) (Tensor0SBundle.Tensor0SSpace.toModel P)) := by
    rw [appCcRS_toSection (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) (3 + a + b)
      (cometricDoubleTraceField (I := I) g₀ (3 + a + b)) (crossCorrSourceReindex (I := I) g₀ a b) x,
      ContinuousLinearMap.comp_apply]
    change Tensor0SBundle.Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g₀ (3 + a + b) x
          (crossCorrSourceReindexFib (I := I) g₀ a b x P)) = _
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ (3 + a + b) x
        (crossCorrSourceReindexFib (I := I) g₀ a b x P),
      crossCorrSourceReindexFib_toModel (I := I) g₀ a b x P]
  exact hL.trans hR.symm

/-- **The fixed source-rank reindex operator field is `∇₀`-parallel** (POSITED NAMED general-infra
child — to be homed in `Geometry/Connection/TensorNabla` as the generic "fixed `Nat`-rank source-slot
reindex is parallel" fact).  `covGrad g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2)
(crossCorrSourceReindex g₀ a b) = 0`: the reindex is a fixed slot relabelling of the operator's source
covariant slots (the model `modelRankCast` along a `Nat`-rank equality), carrying NO cometric and
independent of the metric jets, so its covariant gradient vanishes (the slot reindex commutes with the
Levi-Civita connection — a `domDomCongr`-by-`finCongr` reindex is `∇₀`-parallel). -/
private theorem crossCorrSourceReindex_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    covGrad (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2)
        (crossCorrSourceReindex (I := I) g₀ a b) = 0 := by
  classical
  -- The directional covariant derivative of the fixed-`modelRankCast` operator field vanishes:
  -- the `(0, S)`-covariant derivative of the rank-reindexed contracted section equals the rank
  -- reindex of the `(0, R)`-covariant derivative (the reindex is a constant fibre relabelling,
  -- `∇₀`-parallel), so the Hom-connection product rule's two terms cancel.
  have hnat : ∀ {m n : ℕ} (h : m = n) (w : ∀ y : M, Tensor0SBundle.Tensor0SSpace m I y) (x : M) (v : E),
      (Tensor0SNabla.tensor0SCovariantDerivative I M n (LeviCivita (I := I) g₀))
          (fun y : M => Tensor0SBundle.Tensor0SSpace.ofModel
            (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E) h
              (Tensor0SBundle.Tensor0SSpace.toModel (w y)))) x v =
        Tensor0SBundle.Tensor0SSpace.ofModel
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E) h
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g₀)) w x v))) := by
    intro m n h w x v
    subst h
    simp only [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast_refl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  -- the operator field's value on any source tensor is the rank reindex of that tensor.
  have hΦval : ∀ (y : M) (P : Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I y),
      (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I y →L[ℝ]
          Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I y from
        (crossCorrSourceReindex (I := I) g₀ a b).toSection y) P =
        Tensor0SBundle.Tensor0SSpace.ofModel
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
            (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
            (Tensor0SBundle.Tensor0SSpace.toModel P)) := by
    intro y P
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    exact crossCorrSourceReindexFib_toModel (I := I) g₀ a b y P
  -- It suffices that the directional covariant derivative vanishes at every base point/direction.
  have hdir : ∀ (x : M) (v : E),
      tensorCovDerivAt (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2)
        (crossCorrSourceReindex (I := I) g₀ a b) x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.Tensor0SModel ((3 + b) + (2 + a)) ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I y) (n := (⊤ : ℕ∞)) x D
    rw [tensorCovDerivAt_def (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2)
        (crossCorrSourceReindex (I := I) g₀ a b) x v, ContinuousLinearMap.zero_apply, ← hw]
    rw [TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) ((3 + b) + (2 + a))
      ((3 + a + b) + 2) (LeviCivita (I := I) g₀) (crossCorrSourceReindex (I := I) g₀ a b).toSection
      w x v]
    rw [show (fun y : M =>
          (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I y →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I y from
            (crossCorrSourceReindex (I := I) g₀ a b).toSection y) (w y)) =
        (fun y : M => Tensor0SBundle.Tensor0SSpace.ofModel
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
            (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
            (Tensor0SBundle.Tensor0SSpace.toModel (w y)))) from funext (fun y => hΦval y (w y))]
    rw [hnat (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) (fun y => w y) x v]
    rw [hΦval x ((Tensor0SNabla.tensor0SCovariantDerivative I M ((3 + b) + (2 + a))
      (LeviCivita (I := I) g₀)) (fun y => w y) x v)]
    rw [sub_self]
  -- Assemble: the section-level covariant gradient is determined by the directional derivative.
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀
      ((3 + b) + (2 + a)) ((3 + a + b) + 2) (crossCorrSourceReindex (I := I) g₀ a b) x D m,
    hdir x (m 0), ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

set_option linter.unusedSectionVars false in
/-- **`appCcRS` is zero on a zero contracted section** (fibrewise the operator post-composes with the
zero fibre map).  The right-zero companion of `appCcRS_zero_left`. -/
private theorem appCcRS_zero_right (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    appCcRS (I := I) (M := M) g₀ a b c Φ 0 = 0 := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection (I := I) (M := M) g₀ a b c Φ 0 x]
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
  ext D
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero]

/-- **The fixed cometric double-trace operator field is `∇₀`-parallel.**
`covGrad g₀ ((3 + b) + (2 + a)) (3 + a + b) (crossCorrCometricOp g₀ a b) = 0`.  Through the operator-field
factorisation `crossCorrCometricOp = appCcRS (cometricDoubleTraceField g₀ (3 + a + b)) (sourceReindex)`,
the operator-field B-rule `covGrad_appCcRS_eq` splits the gradient into the rank-generic field's gradient
(zero by `cometricDoubleTraceField_covGrad_eq_zero`, the cometric `∇₀ g₀⁻¹ = 0`) post-composed after the
reindex, plus the slot-extended field post-composed after the reindex's gradient (zero by
`crossCorrSourceReindex_covGrad_eq_zero`, the fixed slot reindex being parallel). -/
private theorem crossCorrCometricOp_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
    covGrad (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b)
        (crossCorrCometricOp (I := I) g₀ a b) = 0 := by
  rw [crossCorrCometricOp_eq_appCcRS_cometricDoubleTraceField (I := I) g₀ a b]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) (3 + a + b)
    (cometricDoubleTraceField (I := I) g₀ (3 + a + b)) (crossCorrSourceReindex (I := I) g₀ a b),
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ (3 + a + b),
    appCcRS_zero_left (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) ((3 + a + b) + 1)
      (crossCorrSourceReindex (I := I) g₀ a b), zero_add,
    crossCorrSourceReindex_covGrad_eq_zero (I := I) g₀ a b,
    appCcRS_zero_right (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (((3 + a + b) + 2) + 1) ((3 + a + b) + 1)
      (slotExtend (I := I) (M := M) g₀ ((3 + a + b) + 2) (3 + a + b)
        (cometricDoubleTraceField (I := I) g₀ (3 + a + b)))]

/-- **The two-section covariant Leibniz of the frame-free product section** (POSITED product-Leibniz
child).  The operator-field slot-extension of the parallel cometric field, applied to the covariant
gradient of the slot-permuted model product, reconciles with the two shifted-order contractions:
```
appCcRS (slotExtend (crossCorrCometricOp g₀ a b)) (covGrad (crossCorrProdSection g₀ S T)) =
  castRankCc_db ... (crossCorrParallelContraction g₀ (a := a + 1) (b := b) (covGrad S) T)
  + crossCorrParallelContraction g₀ (a := a) (b := b + 1) S (covGrad T).
```
The covariant gradient of the model tensor product `modelProduct` splits by the slot-correction Leibniz
`covariantSlotCorrection_modelProduct` (`∇ g = 0` killing the cross term) into the `S`-gradient and the
`T`-gradient pieces, each re-wrapped by the slot-extended cometric field into the corresponding
shifted-rank cross-correction contraction. -/
private theorem appCcRS_slotExtend_crossCorrProd_covGrad_eq (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    appCcRS (I := I) (M := M) g₀ 0 (((3 + b) + (2 + a)) + 1) ((3 + a + b) + 1)
        (slotExtend (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b)
          (crossCorrCometricOp (I := I) g₀ a b))
        (covGrad (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a))
          (crossCorrProdSection (I := I) g₀ S T)) =
      castRankCc_db g₀ 0 (by omega : 3 + (a + 1) + b = 3 + a + b + 1)
          (crossCorrParallelContraction (I := I) g₀ (a := a + 1) (b := b)
            (covGrad g₀ 0 (2 + a) S) T) +
        crossCorrParallelContraction (I := I) g₀ (a := a) (b := b + 1) S
          (covGrad g₀ 0 (3 + b) T) := by
  sorry

/-- **An all-ranks `g₀(x)`-orthonormal frame Parseval witness.**  At `x` there is a single tangent
frame `e : Fin n → T_xM` (`n = finrank ℝ E`) representing the intrinsic `(0, s)` fibre norm as the
frame double sum at *every* rank `s` simultaneously — the standard `g₀(x)`-orthonormal basis, for which
the frame Parseval representation is definitional (`rfl`).  (The cross-rank local re-statement of
`tangent_orthonormalBasisS_witness`, which fixes a single rank.) -/
private theorem ccAllRanksFrameWitness (g₀ : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ E ∧
      ∀ (s : ℕ) (S : Tensor0SBundle.TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g₀ x 0 s S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g₀.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g₀.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g₀.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with heob_def
  refine ⟨n, fun i => eob i, ?_, fun s S => rfl⟩
  rfl

/-- **The rank-`0` frame component reads the operator at the canonical unit.**  For a `(0, s)`-fibre
operator `op` and the empty multi-index, the frame component `fiberNormSqComponent g₀ x 0 s op n e ∅ J`
is the model value of the unit-evaluated `(0, s)`-form `toModel(op unit)` on the frame tuple
`fun k => e (J k)` (the rank-`0` cometric weight `coframeS` is the canonical unit `(0, 0)`-tensor). -/
private theorem ccFiberNormSqComponent_zero_eq_unit (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n)
    (op : Tensor0SBundle.TensorRSSpace 0 s I x) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 s op n e K₀ J =
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
        coframeS (I := I) (M := M) g₀ x 0 e K₀ from rfl,
      coframeS_apply, Finset.prod_of_isEmpty]
    rfl
  unfold fiberNormSqComponent
  rw [hcoframe]
  rw [Tensor0SBundle.Tensor0SSpace.toModel, Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  rfl

/-- **The rank-`0` intrinsic fibre norm as the frame sum of squared unit values.**  In any all-ranks
`g₀(x)`-orthonormal Parseval frame `e`, the intrinsic `(0, s)` fibre norm of a fibre operator `op` is
the frame sum, over the slot multi-index `J`, of the squared model value of the unit-evaluated
`(0, s)`-form `toModel(op unit)` on the frame tuple `fun k => e (J k)`. -/
private theorem ccRfns_zero_eq_sum_unit (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : Tensor0SBundle.TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 0 s S n e K J)
    (op : Tensor0SBundle.TensorRSSpace 0 s I x) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x op =
      ∑ J : Fin s → Fin n,
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from op)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J k))) ^ 2 := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x s e hrepr op (fun k => k.elim0)]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [ccFiberNormSqComponent_zero_eq_unit (I := I) g₀ s x e (fun k => k.elim0) J op]

/-- **The frame-free UNPERMUTED model tensor-product section's fibre norm is the product of the factor
fibre norms** (POSITED NAMED general-infra child — to be homed in `Geometry/Curvature/FiberNormParseval`
as the generic "`rfns` of a model tensor product is the product of the factor `rfns`" fact).
`rfns(crossCorrProdUnpermSection g₀ S T)(x) = rfns(T)(x) · rfns(S)(x)` (in particular `≤`): in a
`g₀(x)`-orthonormal Parseval frame `e`, the unit value of the product section is the model product
`modelProduct (ccUnitModel T x) (ccUnitModel S x)`, whose value on a frame tuple `e ∘ J` splits — by
`modelProduct_apply` along `J = (J_T, J_S)` — into `αT(e ∘ J_T) · αS(e ∘ J_S)` (the `T`-block tuple
times the `S`-block tuple).  Squaring and reindexing the slot sum over `Fin ((3 + b) + (2 + a)) → Fin n`
as a product over `(Fin (3 + b) → Fin n) × (Fin (2 + a) → Fin n)` (`Fin.appendEquiv`) factors the double
sum into the `T`-block sum times the `S`-block sum, i.e. `rfns(T) · rfns(S)`. -/
private theorem crossCorrProdUnpermSection_rfns_le (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x
        ((crossCorrProdUnpermSection (I := I) g₀ S T).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) := by
  classical
  obtain ⟨n, e, _hn, hrepr⟩ := ccAllRanksFrameWitness (I := I) g₀ x
  -- the unit value of the product section, read to the model, is the model product of the two factor
  -- units (the unit-evaluation of the packaged `fromMultilinearSection` field).
  have hunit : Tensor0SBundle.Tensor0SSpace.toModel
        ((crossCorrProdUnpermSection (I := I) g₀ S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x) := by
    rw [show (crossCorrProdUnpermSection (I := I) g₀ S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
            (crossCorrProdUnpermField (I := I) g₀ S T x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        from rfl]
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
    change Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x))) = _
    rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  -- model value of the product unit on a frame tuple splits into the two block evaluations.
  have hsplit : ∀ J : Fin ((3 + b) + (2 + a)) → Fin n,
      Tensor0SBundle.Tensor0SSpace.toModel
          ((crossCorrProdUnpermSection (I := I) g₀ S T).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun k => e (J k)) =
        (ccUnitModel (I := I) g₀ T x) (fun k => e (J (Fin.castAdd (2 + a) k))) *
          (ccUnitModel (I := I) g₀ S x) (fun k => e (J (Fin.natAdd (3 + b) k))) := by
    intro J
    rw [hunit, Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  rw [ccRfns_zero_eq_sum_unit (I := I) g₀ ((3 + b) + (2 + a)) x e (hrepr ((3 + b) + (2 + a)))
      ((crossCorrProdUnpermSection (I := I) g₀ S T).toSection x),
    ccRfns_zero_eq_sum_unit (I := I) g₀ (3 + b) x e (hrepr (3 + b)) (T.toSection x),
    ccRfns_zero_eq_sum_unit (I := I) g₀ (2 + a) x e (hrepr (2 + a)) (S.toSection x)]
  -- reindex the slot sum by `Fin.appendEquiv`, then split into a product of block sums.
  rw [← Fintype.sum_equiv (Fin.appendEquiv (3 + b) (2 + a))
      (fun pr : (Fin (3 + b) → Fin n) × (Fin (2 + a) → Fin n) =>
        ((ccUnitModel (I := I) g₀ T x) (fun k => e (pr.1 k)) *
          (ccUnitModel (I := I) g₀ S x) (fun k => e (pr.2 k))) ^ 2)
      (fun J : Fin ((3 + b) + (2 + a)) → Fin n =>
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((crossCorrProdUnpermSection (I := I) g₀ S T).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J k))) ^ 2) ?_]
  · refine le_of_eq ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun JT _ => Finset.sum_congr rfl (fun JS _ => ?_))
    rw [mul_pow]
    rfl
  · intro pr
    simp only
    rw [hsplit ((Fin.appendEquiv (3 + b) (2 + a)) pr)]
    have hT : (fun k => e (((Fin.appendEquiv (3 + b) (2 + a)) pr) (Fin.castAdd (2 + a) k))) =
        (fun k => e (pr.1 k)) := by
      funext k
      simp only [Fin.appendEquiv_apply, Fin.append_left]
    have hS : (fun k => e (((Fin.appendEquiv (3 + b) (2 + a)) pr) (Fin.natAdd (3 + b) k))) =
        (fun k => e (pr.2 k)) := by
      funext k
      simp only [Fin.appendEquiv_apply, Fin.append_right]
    rw [hT, hS]

/-- **The unit-evaluated model form of the (un)permuted product section.**  At `x`, the
unit-evaluated model `(0, (3 + b) + (2 + a))`-form of the slot-permuted product section
`crossCorrProdSection` is `domDomCongr (crossCorrPerm a b)` of the unpermuted product section's
(`crossCorrProdUnpermSection`), since the permuted field value is `ofModel (domDomCongr crossCorrPerm
(modelProduct ...))` and the unpermuted field value is `ofModel (modelProduct ...)`. -/
private theorem crossCorrProdSection_unitModel_eq_domDomCongr (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) (y : M) :
    unitModel (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (crossCorrProdSection (I := I) g₀ S T) y =
      ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
        (unitModel (I := I) (M := M) g₀ ((3 + b) + (2 + a))
          (crossCorrProdUnpermSection (I := I) g₀ S T) y) := by
  have hP : ∀ (W : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞
        ((3 + b) + (2 + a))),
      unitModel (I := I) (M := M) g₀ ((3 + b) + (2 + a))
          ⟨MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
            (E := (TangentSpace I : M → Type _)) ∞ W, HasCompactSupport.of_compactSpace _⟩ y =
        Tensor0SBundle.Tensor0SSpace.toModel (W y) := by
    intro W
    change Tensor0SBundle.Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) y).smulRight (W y)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I y) (1 : ℝ))) = _
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [show crossCorrProdSection (I := I) g₀ S T =
      ⟨MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
        (E := (TangentSpace I : M → Type _)) ∞ (crossCorrProdField (I := I) g₀ S T),
        HasCompactSupport.of_compactSpace _⟩ from rfl,
    show crossCorrProdUnpermSection (I := I) g₀ S T =
      ⟨MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
        (E := (TangentSpace I : M → Type _)) ∞ (crossCorrProdUnpermField (I := I) g₀ S T),
        HasCompactSupport.of_compactSpace _⟩ from rfl,
    hP (crossCorrProdField (I := I) g₀ S T), hP (crossCorrProdUnpermField (I := I) g₀ S T)]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T y) (ccUnitModel (I := I) g₀ S y)))) =
    ContinuousMultilinearMap.domDomCongr (crossCorrPerm a b)
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T y) (ccUnitModel (I := I) g₀ S y))))
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

/-- **The frame-free product section's fibre norm is bounded by the product of the factor fibre norms.**
`rfns(crossCorrProdSection g₀ S T)(x) ≤ rfns(S)(x) · rfns(T)(x)`: the slot permutation `crossCorrPerm` is
an `rfns`-isometry (`riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` at order `0`, the
permutation being a parallel fibre isometry), so the permuted product section's fibre norm equals the
unpermuted product section's, which is bounded by the product of the factor fibre norms
(`crossCorrProdUnpermSection_rfns_le`). -/
private theorem crossCorrProdSection_rfns_le (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x
        ((crossCorrProdSection (I := I) g₀ S T).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by
  -- the permutation is an `rfns`-isometry: the permuted product section's fibre norm equals the
  -- unpermuted one's.
  have hperm := riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
    (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (crossCorrPerm a b)
    (crossCorrProdUnpermSection (I := I) g₀ S T) (crossCorrProdSection (I := I) g₀ S T)
    (fun y => crossCorrProdSection_unitModel_eq_domDomCongr (I := I) g₀ S T y) 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero] at hperm
  rw [hperm]
  -- the unpermuted product section's fibre norm is bounded by the product of the factor fibre norms.
  rw [mul_comm (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x))]
  exact crossCorrProdUnpermSection_rfns_le (I := I) g₀ S T x

/-- **The pointwise `rfns` bilinear bound of the cross-correction contraction at a single base point.**
`rfns(prod S T)(x) ≤ μx · rfns(S)(x) · rfns(T)(x)`, where `μx` is any bound on the fibre norm of the
cometric trace operator field at `x`.  Through the operator-field factorisation
`crossCorrParallelContraction = appCcRS (crossCorrCometricOp g₀ a b) (crossCorrProdSection g₀ S T)`, the
fibre value is the fixed cometric trace operator post-composed after the product section, so the intrinsic
partial-contraction Cauchy–Schwarz `riemannianFiberNormSq_compRS_le_mul` bounds it by
`rfns(crossCorrCometricOp g₀ a b)(x) · rfns(crossCorrProdSection)(x) ≤ μx · rfns(S)(x) · rfns(T)(x)`
(`crossCorrProdSection_rfns_le` for the second factor). -/
private theorem crossCorrParallelContraction_rfns_le_pointwise (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) (x : M)
    (μx : ℝ) (hμx : riemannianFiberNormSq (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b) x
        ((crossCorrCometricOp (I := I) g₀ a b).toSection x) ≤ μx) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + a + b) x
        ((crossCorrParallelContraction (I := I) g₀ S T).toSection x) ≤
      μx * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by
  -- The fibre value of the contraction is `(crossCorrCometricOpFib x).comp (crossCorrProdSection x)`.
  have hfib : (crossCorrParallelContraction (I := I) g₀ S T).toSection x =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
        (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from (crossCorrCometricOp (I := I) g₀ a b).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from
            (crossCorrProdSection (I := I) g₀ S T).toSection x)) := by
    rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ S T,
      appCcRS_toSection (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
        (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T) x]
  rw [hfib]
  -- Cauchy–Schwarz: rfns(Φ ∘ W) ≤ rfns(Φ) · rfns(W).
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b) x
    (show Tensor0SBundle.TensorRSSpace ((3 + b) + (2 + a)) (3 + a + b) I x from
      (crossCorrCometricOp (I := I) g₀ a b).toSection x)
    (show Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x from
      (crossCorrProdSection (I := I) g₀ S T).toSection x)) ?_
  -- Bound each factor: rfns(Φ) ≤ μx, rfns(W) ≤ rfns(S)·rfns(T).
  calc riemannianFiberNormSq (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b) x
          ((crossCorrCometricOp (I := I) g₀ a b).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x
          ((crossCorrProdSection (I := I) g₀ S T).toSection x)
      ≤ μx * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x)) := by
        apply mul_le_mul hμx (crossCorrProdSection_rfns_le (I := I) g₀ S T x)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x _)
          (le_trans (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b) x _) hμx)
    _ = μx * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by ring

/-- **The post-composition operator of the rank-generic cometric double-trace fibre operator**, as a
continuous-linear map on the `(0, p + 2)`-tensor fibre: `w ↦ (cometricDoubleTraceField g₀ p).toSection x
∘ w` (post-composition is `ℝ`-linear; closed to a continuous-linear map on the finite-dimensional
fibre).  The `p`-passenger analogue of the sibling `fieldRecPostcompCLM`. -/
private noncomputable def cometricDoubleTracePostcompCLM (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (x : M) :
    Tensor0SBundle.TensorRSSpace 0 (p + 2) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 0 p I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 (p + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 2) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 (p + 2) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 2) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace p I x from
          (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (p + 2) I x from w)
      map_add' := fun _ _ => ContinuousLinearMap.comp_add _ _ _
      map_smul' := fun _ _ => ContinuousLinearMap.comp_smul _ _ _ }

set_option linter.unusedSectionVars false in
/-- Defining evaluation of `cometricDoubleTracePostcompCLM`: post-composition by the cometric
double-trace fibre operator. -/
private theorem cometricDoubleTracePostcompCLM_apply (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (w : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x) :
    cometricDoubleTracePostcompCLM (I := I) g₀ p x w =
      (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + 2) I x from w) := by
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 (p + 2) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 2) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 (p + 2) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (p + 2) I x))
  exact congrFun (LinearMap.coe_toContinuousLinearMap' _) w

set_option linter.unusedSectionVars false in
/-- **(POSIT — the order-uniform passenger ampliation of the rank-generic cometric double-trace fibre
envelope; NAMED general-infra child, to be homed in `Geometry/Curvature/FiberNormParseval`.)**  From the
base passenger-count (`p = 0`) uniform fibre envelope `hbase`, the SAME constant `κ` bounds the
post-composition action of the cometric double-trace fibre operator at *every* passenger count `p`:
```
rfns_{(0,p)}((cometricDoubleTraceField g₀ p).toSection x ∘ w) ≤ κ · rfns_{(0,p+2)}(w).
```

This is the genuine deep **`g`-operator-norm** content (NOT the HS route, which is *not* `p`-uniform: the
cometric double trace acts as the identity on the `p` passed-through covariant slots, so its HS fibre
norm grows by a `dim`-factor per passenger slot).  The leading passenger covariant slot is an isometric
ampliation for the intrinsic fibre envelope: slicing it with the all-ranks frame Parseval split
(`riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame`) and passing each slot-`0` slice of the action
through the passenger-passing slice identity for the cometric double trace reduces the passenger-`(p+1)`
bound to the passenger-`p` bound (the `p`-analogue of `ricciModelTrace42_postcomp_rfns_le_aux`).  It is
**non-vacuous** (a degenerate `κ = 0` is rejected whenever the cometric trace is nonzero); its body is
the posited per-`p` ampliation core. -/
private theorem cometricDoubleTrace_postcomp_rfns_le_aux (g₀ : SmoothRiemannianMetric I M) (κ : ℝ)
    (hbase : ∀ (x : M) (w : Tensor0SBundle.TensorRSSpace 0 2 I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 0 x
          ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 0 I x from
            (cometricDoubleTraceField (I := I) g₀ 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from w)) ≤
        κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x w) :
    ∀ (p : ℕ) (x : M) (w : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from w)) ≤
        κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x w := by
  sorry

/-- **The rank-generic order-uniform `g₀`-operator-norm-route post-composition fibre envelope of the
intrinsic `g₀⁻¹` double-trace field** (POSITED NAMED general-infra child — to be homed in
`Geometry/Curvature/FiberNormParseval`, the rank-generic foundation of the cometric trace's `g`-operator
bound).  There is a single nonnegative `κ`, **uniform over the passenger count `p`** and the base point
`x`, with a post-composition fibre operator `A` (`A w = (cometricDoubleTraceField g₀ p).toSection x ∘ w`)
bounding the intrinsic squared fibre norm of the cometric-trace operator-field action through the
**`g`-operator norm**: `rfns_{(0, p)}(A w) ≤ κ · rfns_{(0, p + 2)}(w)`.

This is the genuine `g`-operator-norm core (NOT the Hilbert–Schmidt route, which is *not* `p`-uniform:
the double trace acts as the identity on the `p` passed-through covariant slots, so its HS fibre norm
grows like `dim^p`).  Assembled from the base passenger-count (`p = 0`) section envelope
`exists_uniform_riemannianFiberNormSq_appCcRS_le` (lifted to a fibre-value envelope through a smooth
section realizing an arbitrary fibre value, `ContMDiffSection.exists_eq_at`) and the order-uniform
passenger ampliation `cometricDoubleTrace_postcomp_rfns_le_aux` (the leading passenger slot is an
isometric ampliation for the intrinsic fibre envelope).  Non-vacuous (`κ = 0` is rejected whenever the
cometric trace is nonzero). -/
private theorem exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (p : ℕ) (x : M),
      ∃ A : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x →L[ℝ]
          Tensor0SBundle.TensorRSSpace 0 p I x,
        (∀ w : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x,
          A w = (show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from w)) ∧
        ∀ w : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x (A w) ≤
            κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x w := by
  classical
  -- The uniform constant is the base passenger-count (`p = 0`) section envelope of the fixed cometric
  -- double-trace field `cometricDoubleTraceField g₀ 0 : SmoothCcTensor g₀ 2 0`.
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M)
      g₀ 0 2 0 (cometricDoubleTraceField (I := I) g₀ 0)
  -- Lift the section envelope to a fibre-value envelope through a smooth section realizing any fibre
  -- value at `x` (`ContMDiffSection.exists_eq_at`).
  have hbase : ∀ (x : M) (w : Tensor0SBundle.TensorRSSpace 0 2 I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 0 x
          ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 0 I x from
            (cometricDoubleTraceField (I := I) g₀ 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from w)) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x w := by
    intro x w
    obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (V := fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) (n := (⊤ : ℕ∞)) x w
    have hW := hC ⟨σ, HasCompactSupport.of_compactSpace _⟩ x
    rw [appCcRS_toSection (I := I) (M := M) g₀ 0 2 0
      (cometricDoubleTraceField (I := I) g₀ 0)
      ⟨σ, HasCompactSupport.of_compactSpace _⟩ x] at hW
    rw [hσ] at hW
    exact hW
  refine ⟨C, hC0, fun p x => ?_⟩
  refine ⟨cometricDoubleTracePostcompCLM (I := I) g₀ p x,
    fun w => cometricDoubleTracePostcompCLM_apply (I := I) g₀ p x w, fun w => ?_⟩
  rw [cometricDoubleTracePostcompCLM_apply (I := I) g₀ p x w]
  exact cometricDoubleTrace_postcomp_rfns_le_aux (I := I) g₀ C hbase p x w

/-- **The fixed source-rank reindex is an `rfns`-isometric ampliation** (POSITED NAMED general-infra
child — to be homed in `Geometry/Curvature/FiberNormParseval` as the generic "a fixed `Nat`-rank
covariant-slot reindex `modelRankCast` preserves the intrinsic fibre norm" fact).  Post-composing a
`(0, (3 + b) + (2 + a))`-tensor with the fixed source reindex `crossCorrSourceReindexFib` (the model
`modelRankCast` slot relabelling along `(3 + b) + (2 + a) = (3 + a + b) + 2`) does not increase its
intrinsic squared fibre norm: the reindex is the `domDomCongrₗᵢ`-by-`finCongr` model isometry, a parallel
fibre isometry that relabels the orthonormal-frame tensor components, so it preserves `rfns`. -/
private theorem crossCorrSourceReindex_postcomp_rfns_le (g₀ : SmoothRiemannianMetric I M) (a b : ℕ)
    (x : M) (v : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + a + b) + 2) x
        ((show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x from
          (crossCorrSourceReindex (I := I) g₀ a b).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x v := by
  classical
  obtain ⟨n, e, _hn, hrepr⟩ := ccAllRanksFrameWitness (I := I) g₀ x
  set H : (3 + b) + (2 + a) = (3 + a + b) + 2 := by omega with hH_def
  -- the unit value of `reindex ∘ v` is `reindexFib (v unit)`; its model value on a frame tuple is
  -- the model value of `v unit` on the `finCongr H`-reindexed tuple (a parallel fibre isometry).
  have hmodel : ∀ J : Fin ((3 + a + b) + 2) → Fin n,
      Tensor0SBundle.Tensor0SSpace.toModel
          (((show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x from
              (crossCorrSourceReindex (I := I) g₀ a b).toSection x).comp
              (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v))
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun k => e (J k)) =
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J (Fin.cast (by omega) k))) := by
    intro J
    rw [ContinuousLinearMap.comp_apply]
    rw [show (crossCorrSourceReindex (I := I) g₀ a b).toSection x =
        crossCorrSourceReindexFib (I := I) g₀ a b x from rfl]
    rw [crossCorrSourceReindexFib_toModel (I := I) g₀ a b x]
    -- `modelRankCast H D` evaluated on a tuple `m` reads `D` on the `finCongr H`-reindexed tuple.
    rw [show (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelRankCast (E := E)
            (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
                (ContinuousMultilinearMap.constOfIsEmpty ℝ
                  (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))))
          (fun k => e (J k)) =
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
          (fun i => (fun k => e (J k)) (finCongr (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) i)) from by
        change (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            (finCongr (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)))
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
                (ContinuousMultilinearMap.constOfIsEmpty ℝ
                  (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
            (fun k => e (J k)) = _
        rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
              (finCongr (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2)))
              (Tensor0SBundle.Tensor0SSpace.toModel
                ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
                  (ContinuousMultilinearMap.constOfIsEmpty ℝ
                    (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) =
            ContinuousMultilinearMap.domDomCongr
              (finCongr (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2))
              (Tensor0SBundle.Tensor0SSpace.toModel
                ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
                  (ContinuousMultilinearMap.constOfIsEmpty ℝ
                    (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) from rfl,
          ContinuousMultilinearMap.domDomCongr_apply]]
    rfl
  rw [ccRfns_zero_eq_sum_unit (I := I) g₀ ((3 + a + b) + 2) x e (hrepr ((3 + a + b) + 2))
      ((show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x from
        (crossCorrSourceReindex (I := I) g₀ a b).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)),
    ccRfns_zero_eq_sum_unit (I := I) g₀ ((3 + b) + (2 + a)) x e (hrepr ((3 + b) + (2 + a))) v]
  refine le_of_eq ?_
  rw [Finset.sum_congr rfl (fun J _ => by rw [hmodel J])]
  -- reindex the slot sum over `Fin ((3 + a + b) + 2) → Fin n` by `finCongr H` to the source rank.
  rw [← Fintype.sum_equiv
      (Equiv.arrowCongr (finCongr (by omega : (3 + a + b) + 2 = (3 + b) + (2 + a))) (Equiv.refl (Fin n)))
      (fun J : Fin ((3 + a + b) + 2) → Fin n =>
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J (Fin.cast (by omega) k)))) ^ 2)
      (fun J' : Fin ((3 + b) + (2 + a)) → Fin n =>
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J' k))) ^ 2) ?_]
  intro J
  beta_reduce
  have htuple : (fun k => e (J (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) k))) =
      (fun k => e (((Equiv.arrowCongr
          (finCongr (by omega : (3 + a + b) + 2 = (3 + b) + (2 + a))) (Equiv.refl (Fin n))) J) k)) := by
    funext k
    rw [show ((Equiv.arrowCongr
          (finCongr (by omega : (3 + a + b) + 2 = (3 + b) + (2 + a))) (Equiv.refl (Fin n))) J) k =
        J (Fin.cast (by omega : (3 + b) + (2 + a) = (3 + a + b) + 2) k) from by
      simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq, finCongr_symm,
        finCongr_apply]]
  rw [htuple]

/-- **The order-uniform `g₀`-operator-norm-route post-composition fibre envelope of the cometric
trace operator field** (the `(a, b)`-uniform `g`-operator-norm route, the bilinear twin of
`exists_uniform_ricciModelTrace42_postcomp_gOpNorm_rfns_le`).  There is a single nonnegative `κ`,
**uniform over the rank shifts `(a, b)`** and the base point `x`, with a post-composition fibre operator
`A` (`A v = (crossCorrCometricOp g₀ a b).toSection x ∘ v`) bounding the intrinsic squared fibre norm of
the operator-field action through the **`g`-operator norm**:
`rfns_{(0, 3 + a + b)}(A v) ≤ κ · rfns_{(0, (3 + b) + (2 + a))}(v)`.

Discharged through the operator-field factorisation `crossCorrCometricOp g₀ a b =
appCcRS (cometricDoubleTraceField g₀ (3 + a + b)) (crossCorrSourceReindex g₀ a b)`: the rank-generic
`g`-operator-norm envelope `exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le` (uniform
over the passenger count `p`, here `p = 3 + a + b`) bounds the cometric-trace post-composition, and the
fixed source reindex is an `rfns`-isometric ampliation (`crossCorrSourceReindex_postcomp_rfns_le`).  This
is the `g`-OPERATOR-norm route, NOT the HS route, which is *not* `(a, b)`-uniform (the cometric double
trace acts as the identity on the `3 + a + b` passed-through slots, so its HS fibre norm grows like
`dim^{3 + a + b}`).  Non-vacuous (`κ = 0` is rejected whenever the cometric trace is nonzero). -/
private theorem exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (a b : ℕ) (x : M),
      ∃ A : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x →L[ℝ]
          Tensor0SBundle.TensorRSSpace 0 (3 + a + b) I x,
        (∀ v : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x,
          A v = (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
            (crossCorrCometricOp (I := I) g₀ a b).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)) ∧
        ∀ v : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + a + b) x (A v) ≤
            κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x v := by
  classical
  -- The uniform constant is the rank-generic envelope `κ` of the intrinsic cometric double-trace field
  -- (uniform in the passenger count `p`); the cross-correction cometric operator factors as that field
  -- at `p = 3 + a + b` post-composed after the fixed (isometric) source reindex.
  obtain ⟨κ, hκ0, hκ⟩ := exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le (I := I) g₀
  refine ⟨κ, hκ0, fun a b x => ?_⟩
  obtain ⟨A₀, hA₀def, hA₀bound⟩ := hκ (3 + a + b) x
  -- The fixed source-reindex post-composition CLM `v ↦ (sourceReindexFib x).comp v`.
  letI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))
  letI : T2Space (Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x))
  set Pre : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace 0 ((3 + a + b) + 2) I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x from
            (crossCorrSourceReindex (I := I) g₀ a b).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v)
        map_add' := fun _ _ => ContinuousLinearMap.comp_add _ _ _
        map_smul' := fun _ _ => ContinuousLinearMap.comp_smul _ _ _ } with hPre_def
  have hPre_apply : ∀ v : Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x,
      Pre v = (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace ((3 + a + b) + 2) I x from
        (crossCorrSourceReindex (I := I) g₀ a b).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x from v) := by
    intro v; rw [hPre_def]; exact congrFun (LinearMap.coe_toContinuousLinearMap' _) v
  -- The cross-correction cometric operator `A := A₀ ∘ Pre`.
  -- the fibre of the operator-field factorisation `crossCorrCometricOp = appCcRS doubleTrace reindex`.
  have hfib : (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
        (crossCorrCometricOp (I := I) g₀ a b).toSection x) =
      (show Tensor0SBundle.Tensor0SSpace (3 + a + b + 2) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (3 + a + b) I x from
        (cometricDoubleTraceField (I := I) g₀ (3 + a + b)).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace ((3 + b) + (2 + a)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (3 + a + b + 2) I x from
          (crossCorrSourceReindex (I := I) g₀ a b).toSection x) := by
    rw [crossCorrCometricOp_eq_appCcRS_cometricDoubleTraceField (I := I) g₀ a b]
    exact appCcRS_toSection (I := I) (M := M) g₀ ((3 + b) + (2 + a)) ((3 + a + b) + 2) (3 + a + b)
      (cometricDoubleTraceField (I := I) g₀ (3 + a + b)) (crossCorrSourceReindex (I := I) g₀ a b) x
  refine ⟨A₀.comp Pre, fun v => ?_, fun v => ?_⟩
  · -- `A v = crossCorrCometricOpFib ∘ v`, via the factorisation through `cometricDoubleTraceField`.
    rw [ContinuousLinearMap.comp_apply, hA₀def (Pre v), hPre_apply v, hfib,
      ContinuousLinearMap.comp_assoc]
  · -- The fibre-norm bound: `rfns(A₀ (Pre v)) ≤ κ · rfns(Pre v) ≤ κ · rfns(v)`.
    rw [ContinuousLinearMap.comp_apply]
    refine le_trans (hA₀bound (Pre v)) ?_
    rw [hPre_apply v]
    exact mul_le_mul_of_nonneg_left (crossCorrSourceReindex_postcomp_rfns_le (I := I) g₀ a b x v) hκ0

/-! ## The two genuine `∇`-compatibility fields, and the assembled `RfnsBilinearProduct`

The two `RfnsBilinearProduct g₀ 2 3 3` fields below are the genuine deep covariant-calculus content of
the cross-correction product (the dispatch's "two fields, both genuine new covariant calculus").  They
are discharged here through the operator-field bridge above; the parent — the assembled instance
`crossCorrRfnsBilinearProduct` and its diagonal `rfns` jet grid — is real composition on top. -/

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
  -- Bridge: the parallel contraction is the operator-field action of the fixed parallel cometric
  -- double-trace field on the frame-free product section.
  rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ S T]
  -- B-rule: ∇₀(appCcRS Ψ P) = appCcRS (∇₀Ψ) P + appCcRS (slotExtend Ψ) (∇₀P); the first term
  -- vanishes because the cometric field Ψ is ∇₀-parallel (∇₀ g₀⁻¹ = 0).
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
    (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T),
    crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ a b,
    appCcRS_zero_left (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) ((3 + a + b) + 1)
      (crossCorrProdSection (I := I) g₀ S T), zero_add]
  -- The surviving slot-extended term reconciles, through the product Leibniz, with the two
  -- shifted-order cross-correction contractions.
  exact appCcRS_slotExtend_crossCorrProd_covGrad_eq (I := I) g₀ S T

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
  -- The uniform constant is the single `(a, b)`-uniform `g`-operator-norm-route envelope `κ` of the
  -- cometric trace operator field (the passenger slots are isometric ampliations for the operator
  -- norm, unlike the HS norm which grows by a `dim`-factor per passenger slot).  The contraction's
  -- fibre value is the operator's post-composition action on the product section
  -- (`crossCorrParallelContraction = appCcRS (crossCorrCometricOp) (crossCorrProdSection)`), so the
  -- envelope bounds it by `κ · rfns(crossCorrProdSection) ≤ κ · rfns(S) · rfns(T)`.
  obtain ⟨κ, hκ_nn, hκ⟩ := exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le (I := I) g₀
  refine ⟨κ, hκ_nn, fun {a b} S T x => ?_⟩
  obtain ⟨A, hAdef, hAbound⟩ := hκ a b x
  -- The contraction's fibre value is `A (crossCorrProdSection.toSection x)`.
  have hfib : (crossCorrParallelContraction (I := I) g₀ S T).toSection x =
      A (show Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x from
        (crossCorrProdSection (I := I) g₀ S T).toSection x) := by
    rw [hAdef (show Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x from
      (crossCorrProdSection (I := I) g₀ S T).toSection x)]
    rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ S T,
      appCcRS_toSection (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
        (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T) x]
  rw [hfib]
  -- `g`-operator-norm action bound, then the product-section fibre-norm bound.
  refine le_trans (hAbound (show Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x from
    (crossCorrProdSection (I := I) g₀ S T).toSection x)) ?_
  calc κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) x
          ((crossCorrProdSection (I := I) g₀ S T).toSection x)
      ≤ κ * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x)) :=
        mul_le_mul_of_nonneg_left (crossCorrProdSection_rfns_le (I := I) g₀ S T x) hκ_nn
    _ = κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by ring

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
