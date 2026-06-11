import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0SliceFiberNormDomination
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz

/-! # The cross-correction parallel two-section cometric contraction `h ⌟ D`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file builds the **section-level parallel fibrewise bilinear `g₀`-single
contraction**

```
crossCorrParallelContraction g₀ S T   :   (0, 2 + a) ⊗ (0, 3 + b) → (0, 3 + a + b),
```

the `g₀`-metric single contraction `h ⌟ D` of a rank-`(2 + a)` factor `S` against a rank-`(3 + b)`
factor `T`, pairing one slot of each factor through the cometric `g₀⁻¹` (parallel, `∇₀ g₀⁻¹ = 0`), so
the result carries the remaining `(2 + a − 1) + (3 + b − 1) = 3 + a + b` covariant slots.  Built from
the model tensor product `Bundle.continuousMultilinearMap.modelProduct` followed by the cometric
`g₀⁻¹` single trace of the two contracted leading slots (frame-free, depending on `g₀` only through the
smooth cometric Hom-section `inverseMetricSharpField`, NO chart-selected ambient frame).

## What this file provides

* `crossCorrParallelContraction` — the section-level parallel fibrewise bilinear `g₀`-single
  contraction, fibrewise `ℝ`-bilinear.
* `crossCorrParallelContraction_toModel_apply` — its unit fibre value as the model contraction
  `crossCorrModelFun`.
* the cross-correction bilinearity primitives (`crossCorrParallelContraction_add/sub/smul_left/_right`),
  the operator-field bridge (`crossCorrParallelContraction_eq_appCcRS`), the slot bookkeeping
  (`crossCorrCovGradPerm` and its value lemmas), and the frame/Parseval witnesses serving the
  cross-correction jet analysis.
* `exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le` — the **order-`(a, b)`-uniform
  `g`-operator-norm post-composition fibre envelope** of the cometric trace operator field (the genuine
  deep `g`-operator-norm content, NOT the `dim`-growing Hilbert–Schmidt route).

A reusable covariant-calculus byproduct (R1 — its own first-class home in the covariant-gradient API),
decoupled from the specific factor sections `realizeSymm Tₖ` / `loweredConnDiff gₖ g₀`; the concrete
identification of this contraction with the nonlinear cross-correction `crossCorrectionSection` lives
downstream in `CrossCorrectionParallelContraction` (which imports this file and the
connection-difference jet file).

(A previously-assembled `RfnsBilinearProduct` instance, its two-section slot-extension Leibniz, and its
diagonal jet grid were Lean-refuted as stated and removed — see the removal note before the retained
slot-bookkeeping section below.) -/

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
noncomputable def crossCorrCometricOp (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
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
theorem crossCorrParallelContraction_eq_appCcRS (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
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

/-! ## Bilinearity of the cross-correction parallel contraction

The cross-correction parallel `g₀`-single contraction `crossCorrParallelContraction g₀ S T` is the
operator-field action `appCcRS (crossCorrCometricOp g₀ a b)` of a **fixed** (`S, T`-independent)
cometric double-trace field on the model tensor-product section `crossCorrProdSection g₀ S T`
(`crossCorrParallelContraction_eq_appCcRS`).  The action is `ℝ`-linear in the contracted section
(`appCcRS_add_right`, `appCcRS_smul_right`), and the product section is fibrewise `ℝ`-bilinear in the
two factors (`crossCorrProdSection` reads to `domDomCongr (modelProduct (ccUnit T) (ccUnit S))`, and
`modelProduct` is bilinear, `ccUnitModel` additive in its section).  Hence the contraction is
fibrewise `ℝ`-bilinear in `(S, T)` — the bilinearity the bilinear-difference factorization
`Φ(h₁, D₁) − Φ(h₂, D₂) = Φ(h₁ − h₂, D₁) + Φ(h₂, D₁ − D₂)` of the cross-correction section
difference consumes. -/

set_option linter.unusedSectionVars false in
/-- **The unit-model value of the cross-correction product section** is the slot-permuted model tensor
product of the unit fibres of `T`, `S`. -/
private theorem crossCorrProdSection_unitModel (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a)) (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b))
    (x : M) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((crossCorrProdSection (I := I) g₀ S T).toSection x
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

set_option linter.unusedSectionVars false in
/-- **`ccUnitModel` is additive in the section.**  `ccUnitModel g₀ (S₁ + S₂) x = ccUnitModel g₀ S₁ x +
ccUnitModel g₀ S₂ x` — the unit fibre value is additive, since `toSection` and `toModel` are. -/
private theorem ccUnitModel_add {s : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (S₁ S₂ : Integral.L2.SmoothCcTensor g₀ 0 s) (x : M) :
    ccUnitModel (I := I) g₀ (S₁ + S₂) x = ccUnitModel (I := I) g₀ S₁ x + ccUnitModel (I := I) g₀ S₂ x := by
  unfold ccUnitModel
  rw [show (S₁ + S₂).toSection x = S₁.toSection x + S₂.toSection x from by
    rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
/-- **The cross-correction product section is additive in the second factor `T`.** -/
private theorem crossCorrProdSection_add_right (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrProdSection (I := I) g₀ S (T₁ + T₂) =
      crossCorrProdSection (I := I) g₀ S T₁ + crossCorrProdSection (I := I) g₀ S T₂ := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := (3 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrProdSection_unitModel (I := I) g₀ S (T₁ + T₂) x]
  rw [show ((crossCorrProdSection (I := I) g₀ S T₁ + crossCorrProdSection (I := I) g₀ S T₂).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      (crossCorrProdSection (I := I) g₀ S T₁).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x) +
        (crossCorrProdSection (I := I) g₀ S T₂).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x) from by
    rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add,
    crossCorrProdSection_unitModel (I := I) g₀ S T₁ x,
    crossCorrProdSection_unitModel (I := I) g₀ S T₂ x, ccUnitModel_add]
  apply ContinuousMultilinearMap.ext; intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    show (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (ccUnitModel (I := I) g₀ T₁ x + ccUnitModel (I := I) g₀ T₂ x)
        (ccUnitModel (I := I) g₀ S x)) =
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T₁ x) (ccUnitModel (I := I) g₀ S x)
          + Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T₂ x) (ccUnitModel (I := I) g₀ S x) from by
      apply ContinuousMultilinearMap.ext; intro w
      rw [ContinuousMultilinearMap.add_apply, Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        ContinuousMultilinearMap.add_apply, add_mul],
    ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in
/-- **The cross-correction product section is additive in the first factor `S`.** -/
private theorem crossCorrProdSection_add_left (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S₁ S₂ : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrProdSection (I := I) g₀ (S₁ + S₂) T =
      crossCorrProdSection (I := I) g₀ S₁ T + crossCorrProdSection (I := I) g₀ S₂ T := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := (3 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrProdSection_unitModel (I := I) g₀ (S₁ + S₂) T x]
  rw [show ((crossCorrProdSection (I := I) g₀ S₁ T + crossCorrProdSection (I := I) g₀ S₂ T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      (crossCorrProdSection (I := I) g₀ S₁ T).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x) +
        (crossCorrProdSection (I := I) g₀ S₂ T).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x) from by
    rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add,
    crossCorrProdSection_unitModel (I := I) g₀ S₁ T x,
    crossCorrProdSection_unitModel (I := I) g₀ S₂ T x, ccUnitModel_add]
  apply ContinuousMultilinearMap.ext; intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    show (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (ccUnitModel (I := I) g₀ T x)
        (ccUnitModel (I := I) g₀ S₁ x + ccUnitModel (I := I) g₀ S₂ x)) =
        Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S₁ x)
          + Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S₂ x) from by
      apply ContinuousMultilinearMap.ext; intro w
      rw [ContinuousMultilinearMap.add_apply, Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        ContinuousMultilinearMap.add_apply, mul_add],
    ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is additive in the second factor `T`.**  Via the
operator-field bridge `crossCorrParallelContraction_eq_appCcRS` and the additivity of the action in
the contracted section (`appCcRS_add_right`) over the additive product section. -/
theorem crossCorrParallelContraction_add_right (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ S (T₁ + T₂) =
      crossCorrParallelContraction (I := I) g₀ S T₁ + crossCorrParallelContraction (I := I) g₀ S T₂ := by
  rw [crossCorrParallelContraction_eq_appCcRS, crossCorrParallelContraction_eq_appCcRS,
    crossCorrParallelContraction_eq_appCcRS, crossCorrProdSection_add_right,
    appCcRS_add_right]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is additive in the first factor `S`.** -/
theorem crossCorrParallelContraction_add_left (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S₁ S₂ : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ (S₁ + S₂) T =
      crossCorrParallelContraction (I := I) g₀ S₁ T + crossCorrParallelContraction (I := I) g₀ S₂ T := by
  rw [crossCorrParallelContraction_eq_appCcRS, crossCorrParallelContraction_eq_appCcRS,
    crossCorrParallelContraction_eq_appCcRS, crossCorrProdSection_add_left,
    appCcRS_add_right]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is `ℝ`-homogeneous in the second factor `T`.** -/
theorem crossCorrParallelContraction_smul_right (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (k : ℝ) (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ S (k • T) =
      k • crossCorrParallelContraction (I := I) g₀ S T := by
  classical
  rw [crossCorrParallelContraction_eq_appCcRS, crossCorrParallelContraction_eq_appCcRS]
  rw [show crossCorrProdSection (I := I) g₀ S (k • T) = k • crossCorrProdSection (I := I) g₀ S T from ?_,
    appCcRS_smul_right]
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := (3 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrProdSection_unitModel (I := I) g₀ S (k • T) x]
  rw [show ((k • crossCorrProdSection (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      k • ((crossCorrProdSection (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) from by
    rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_smul,
    crossCorrProdSection_unitModel (I := I) g₀ S T x,
    show ccUnitModel (I := I) g₀ (k • T) x = k • ccUnitModel (I := I) g₀ T x from by
      unfold ccUnitModel
      rw [show (k • T).toSection x = k • T.toSection x from by
          rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
        ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]]
  apply ContinuousMultilinearMap.ext; intro v
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    show (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (k • ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x)) =
        k • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x) from by
      apply ContinuousMultilinearMap.ext; intro w
      rw [ContinuousMultilinearMap.smul_apply, Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc],
    ContinuousMultilinearMap.smul_apply]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is subtractive in the second factor `T`.** -/
theorem crossCorrParallelContraction_sub_right (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ S (T₁ - T₂) =
      crossCorrParallelContraction (I := I) g₀ S T₁ - crossCorrParallelContraction (I := I) g₀ S T₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ T₂, crossCorrParallelContraction_add_right,
    crossCorrParallelContraction_smul_right, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is `ℝ`-homogeneous in the first factor `S`.** -/
theorem crossCorrParallelContraction_smul_left (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (k : ℝ) (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ (k • S) T =
      k • crossCorrParallelContraction (I := I) g₀ S T := by
  classical
  rw [crossCorrParallelContraction_eq_appCcRS, crossCorrParallelContraction_eq_appCcRS]
  rw [show crossCorrProdSection (I := I) g₀ (k • S) T = k • crossCorrProdSection (I := I) g₀ S T from ?_,
    appCcRS_smul_right]
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := (3 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrProdSection_unitModel (I := I) g₀ (k • S) T x]
  rw [show ((k • crossCorrProdSection (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      k • ((crossCorrProdSection (I := I) g₀ S T).toSection x
        (Integral.Connection.unitZeroSec (I := I) (M := M) x)) from by
    rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_smul,
    crossCorrProdSection_unitModel (I := I) g₀ S T x,
    show ccUnitModel (I := I) g₀ (k • S) x = k • ccUnitModel (I := I) g₀ S x from by
      unfold ccUnitModel
      rw [show (k • S).toSection x = k • S.toSection x from by
          rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
        ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]]
  apply ContinuousMultilinearMap.ext; intro v
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    show (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
        (ccUnitModel (I := I) g₀ T x) (k • ccUnitModel (I := I) g₀ S x)) =
        k • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) (3 + b) (2 + a)
            (ccUnitModel (I := I) g₀ T x) (ccUnitModel (I := I) g₀ S x) from by
      apply ContinuousMultilinearMap.ext; intro w
      rw [ContinuousMultilinearMap.smul_apply, Bundle.continuousMultilinearMap.modelProduct_apply,
        Bundle.continuousMultilinearMap.modelProduct_apply,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm],
    ContinuousMultilinearMap.smul_apply]

set_option linter.unusedSectionVars false in
/-- **The cross-correction parallel contraction is subtractive in the first factor `S`.** -/
theorem crossCorrParallelContraction_sub_left (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S₁ S₂ : Integral.L2.SmoothCcTensor g₀ 0 (2 + a))
    (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrParallelContraction (I := I) g₀ (S₁ - S₂) T =
      crossCorrParallelContraction (I := I) g₀ S₁ T - crossCorrParallelContraction (I := I) g₀ S₂ T := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ S₂, crossCorrParallelContraction_add_left,
    crossCorrParallelContraction_smul_left, neg_one_smul, ← sub_eq_add_neg]

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
theorem crossCorrCometricOp_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a b : ℕ) :
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

/-- **The cross-correction second-summand slot reindexing** `Fin (3 + a + b + 1) ≃ itself`.  In the
second Leibniz summand `prod S (∇T)` of the `g₀`-single contraction `h ⌟ D`, the high covariant
derivative of the second factor `T` enters the contraction output at the interior slot where the second
factor's surviving block begins, NOT at the leading slot the LHS `∇(prod S T)` carries it at (`covGrad`
inserts its new slot at index `0`).  This constant slot reindexing relocates that interior gradient slot
to the leading slot, so that the exact two-section Leibniz holds; being a constant (point-independent)
reindex it is a parallel fibre isometry, leaving every iterated-gradient `rfns` of the second summand
invariant (`riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor`), so the grid engine strips it freely.
Built as `finRotate ((2 + a) + 1)` on the leading block and the identity on the trailing `1 + b` block
(the `crossCorrPerm` idiom); the precise prefix length is the surviving-output relocation of the
contracted product's gradient slot, verified together with the cometric Leibniz discharge below. -/
noncomputable def crossCorrCovGradPerm {a b : ℕ} : Equiv.Perm (Fin (3 + a + b + 1)) :=
  (finCongr (by omega : (((2 + a) + 1) + (1 + b)) = 3 + a + b + 1)).permCongr
    (finSumFinEquiv.permCongr
      (Equiv.sumCongr (finRotate ((2 + a) + 1)) (Equiv.refl (Fin (1 + b)))))

/-- Value of `crossCorrCovGradPerm` on the leading block interior `j < 2 + a`: `j ↦ j + 1`. -/
private lemma crossCorrCovGradPerm_val_lt {a b : ℕ} (i : Fin (3 + a + b + 1)) (hi : (i : ℕ) < 2 + a) :
    ((crossCorrCovGradPerm (a := a) (b := b)) i : ℕ) = (i : ℕ) + 1 := by
  simp only [crossCorrCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : 3 + a + b + 1 = ((2 + a) + 1) + (1 + b)) i) =
      Fin.castAdd (1 + b) ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, finRotate_succ_apply,
    finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd]
  rw [Fin.val_add_one_of_lt (by exact Fin.mk_lt_mk.mpr (by omega : (i:ℕ) < 2 + a))]

/-- Value of `crossCorrCovGradPerm` at the gradient slot `i = 2 + a`: `2 + a ↦ 0`. -/
private lemma crossCorrCovGradPerm_val_eq {a b : ℕ} (i : Fin (3 + a + b + 1)) (hi : (i : ℕ) = 2 + a) :
    ((crossCorrCovGradPerm (a := a) (b := b)) i : ℕ) = 0 := by
  simp only [crossCorrCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : 3 + a + b + 1 = ((2 + a) + 1) + (1 + b)) i) =
      Fin.castAdd (1 + b) ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl]
  rw [show (⟨(i : ℕ), by omega⟩ : Fin ((2 + a) + 1)) = Fin.last (2 + a) from by
    apply Fin.ext; simp [hi]]
  rw [finRotate_last, finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd, Fin.val_zero]

/-- Value of `crossCorrCovGradPerm` on the trailing passenger block `i > 2 + a`: fixed. -/
private lemma crossCorrCovGradPerm_val_gt {a b : ℕ} (i : Fin (3 + a + b + 1)) (hi : 2 + a < (i : ℕ)) :
    ((crossCorrCovGradPerm (a := a) (b := b)) i : ℕ) = (i : ℕ) := by
  simp only [crossCorrCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : 3 + a + b + 1 = ((2 + a) + 1) + (1 + b)) i) =
      Fin.natAdd ((2 + a) + 1) ⟨(i : ℕ) - ((2 + a) + 1), by omega⟩ from by
    apply Fin.ext; simp; omega]
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd, Fin.val_mk]
  omega

/-! ### The cometric slot-extension Leibniz (REMOVED — Lean-refuted as previously stated)

A previously-posited two-section covariant Leibniz for the slot-extended cometric contraction —
asserting `appCcRS (slotExtend (crossCorrCometricOp)) (covGrad (crossCorrProdSection S T))` equals
the two SHIFTED contractions `crossCorrParallelContraction (a+1) b (covGrad S) T` +
`permuteCcTensor crossCorrCovGradPerm (crossCorrParallelContraction a (b+1) S (covGrad T))` — was
Lean-certified FALSE and deleted together with its dependent field proof, instance, and jet grid:
the left side keeps the new gradient direction a FREE SPECTATOR (the slot-extended cometric pair
traces the two ORIGINAL product slots), while the shifted right side traces the GRADIENT slot of
the differentiated factor; the cometric completeness closure identifying the two holds only when
the undifferentiated factor is itself an inner-product form (the `a = b = 0` instance), not at
general ranks (numeric model-fibre witness).  The TRUE identity keeps both arms at ranks `(a, b)`
with the gradient direction a spectator passenger on the differentiated factor; it should be
re-posited in that form only when a consumer materialises (none exists today: the deleted jet grid
had no consumers library-wide).  The slot bookkeeping (`crossCorrCovGradPerm` and its value lemmas)
is retained for that future form. -/

/-! ### The two-section parallel covariant Leibniz (operator-reduced TRUE form)

The cross-correction `g₀`-single contraction `crossCorrParallelContraction g₀ S T` factors as the
operator-field action `appCcRS (crossCorrCometricOp g₀ a b) (crossCorrProdSection g₀ S T)` of the
**fixed** `∇₀`-parallel cometric double-trace field after the frame-free product section
(`crossCorrParallelContraction_eq_appCcRS`).  The operator-field B-rule `covGrad_appCcRS_eq` therefore
splits its covariant gradient into the differentiated-field action (which **vanishes** because the
cometric is `∇₀`-parallel, `crossCorrCometricOp_covGrad_eq_zero`) plus the **slot-extended** field
acting on the gradient of the frame-free product section:

```
∇₀(h ⌟ D) = appCcRS (slotExtend (crossCorrCometricOp g₀ a b)) (∇₀ (crossCorrProdSection g₀ S T)).
```

This is the exact two-section parallel covariant Leibniz of the contraction, the bilinear lift of the
single-section trace fact `ricciModelTrace42Op_covGrad`.  Crucially, `slotExtend` inserts the new
gradient direction as a **leading passenger** read first and passed UNCONTRACTED
(`slotExtendFib_apply_eval`), while the cometric pair `crossCorrCometricOp` continues to trace the two
ORIGINAL product slots (`modelDoubleTrace` traces the two LEADING slots, which `crossCorrPerm` placed
at the slots-to-be-contracted) — so the gradient direction is a **free spectator** over the original
traced slots.

This is the TRUE form named in the removal note above; it is NOT (and does not reduce to) the
Lean-refuted shifted-rank shape `crossCorrParallelContraction (a+1) b (covGrad S) T + …`, whose first
arm feeds `covGrad S` (gradient slot leading) into the contraction at rank `a+1`, where
`crossCorrModelFun L (a+1) b` raises that gradient slot through the cometric `L = g₀⁻¹` and traces it —
contracting the gradient direction OUT, not leaving it a spectator.  No slot reindexing of the output
can reconcile the two (a slot summed through `g₀⁻¹` is rank-reduced away and cannot become a spectator
slot), so the `RfnsBilinearProduct.covGrad_prod` structure field — which demands exactly that
shifted-rank shape — is NOT realizable for this contraction; the Leibniz lands here as a first-class
standalone theorem (the diagonal `rfns` jet grid, when a consumer materialises, derives directly from
this operator-reduced form via `slotExtend`'s `rfns`-isometry, not through the structure). -/
theorem crossCorrParallelContraction_covGrad (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    covGrad (I := I) (M := M) g₀ 0 (3 + a + b)
        (crossCorrParallelContraction (I := I) g₀ S T) =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + b) + (2 + a)) + 1) ((3 + a + b) + 1)
        (slotExtend (I := I) (M := M) g₀ ((3 + b) + (2 + a)) (3 + a + b)
          (crossCorrCometricOp (I := I) g₀ a b))
        (covGrad (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a))
          (crossCorrProdSection (I := I) g₀ S T)) := by
  rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ S T,
    covGrad_appCcRS_eq (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
      (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T),
    crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ a b,
    appCcRS_zero_left (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) ((3 + a + b) + 1)
      (crossCorrProdSection (I := I) g₀ S T), zero_add]

set_option linter.unusedSectionVars false in
/-- **The frame-free product section is a slot-permuted bare tensor product** of the unit fibres of `T`,
`S`.  `crossCorrProdSection g₀ S T = permuteCcTensor (crossCorrPerm a b) (unitModelProdSection g₀ T S)`:
both are the `(0, (3 + b) + (2 + a))`-section whose unit fibre is the slot-permuted model product
`domDomCongr (crossCorrPerm a b) (modelProduct (ccUnit T) (ccUnit S))` (`crossCorrProdSection_unitModel`
for the left, `permuteCcTensor_unitModel` ∘ `unitModelProdSection_unitModel` for the right, with
`ccUnitModel = unitModel` definitionally).  This exposes the product section — whose covariant gradient
the operator-reduced Leibniz `crossCorrParallelContraction_covGrad` carries — as the bare two-section
tensor product (`unitModelProdSection`, whose own two-section covariant Leibniz is
`unitModelProdSection_covGrad_unitModel_pub`), pre-composed with the constant slot reindexing
`crossCorrPerm` (a parallel fibre isometry). -/
theorem crossCorrProdSection_eq_permute_unitModelProdSection (g₀ : SmoothRiemannianMetric I M)
    {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b)) :
    crossCorrProdSection (I := I) g₀ S T =
      permuteCcTensor g₀ (crossCorrPerm a b)
        (unitModelProdSection (I := I) g₀ T S) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := (3 + b) + (2 + a))
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [crossCorrProdSection_unitModel (I := I) g₀ S T x]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        ((permuteCcTensor g₀ (crossCorrPerm a b) (unitModelProdSection (I := I) g₀ T S)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))
      = unitModel (I := I) (M := M) g₀ ((3 + b) + (2 + a))
          (permuteCcTensor g₀ (crossCorrPerm a b) (unitModelProdSection (I := I) g₀ T S)) x from rfl]
  rw [permuteCcTensor_unitModel (I := I) g₀ (crossCorrPerm a b) (unitModelProdSection (I := I) g₀ T S) x,
    unitModelProdSection_unitModel (I := I) g₀ T S x]
  rfl

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
theorem crossCorrParallelContraction_rfns_le_pointwise (g₀ : SmoothRiemannianMetric I M)
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

/-- **The trailing-slot curried `(0, 0) → (0, s)` fibre operator.**  Reads the trailing covariant slot
of a `(0, s + 1)` fibre operator `w` (i.e. of its unit value `w(⋆)`) at a tangent direction `v`,
producing a `(0, 0) → (0, s)` fibre operator whose unit value, on a model tuple `m : Fin s → E`, is
`toModel(w ⋆) (Fin.snoc m v)`.  Packaged through `ofModel`/`smulRight` exactly as `slot0Curry`, so it is
a genuine fibre tensor consumable by the passenger ampliation induction; metric-free (the trailing slot
insertion uses no frame). -/
private noncomputable def tailCurryUnitFib {s : ℕ} {x : M}
    (w : Tensor0SBundle.TensorRSSpace 0 (s + 1) I x) (v : E) :
    Tensor0SBundle.TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (Tensor0SBundle.Tensor0SSpace.ofModel
      ((ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (s + 1) I x from w)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
                (1 : ℝ)))).curryRight))

set_option linter.unusedSectionVars false in
/-- **The defining unit-tuple value of the trailing-slot curry.**  The model value of the unit of
`tailCurryUnitFib w v`, on a tuple `m : Fin s → E`, reads `w`'s unit on the tuple `m` with `v` appended
as the trailing covariant slot (`Fin.snoc m v`). -/
private theorem tailCurryUnitFib_unit_toModel {s : ℕ} {x : M}
    (w : Tensor0SBundle.TensorRSSpace 0 (s + 1) I x) (v : E) (m : Fin s → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          tailCurryUnitFib (I := I) (M := M) w v)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        m =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x
              from w)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.snoc m v) := by
  classical
  rw [tailCurryUnitFib, ContinuousLinearMap.smulRight_apply]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
      (1 : ℝ) := by
    rw [tensor00Scalar_apply (I := I) (M := M) x
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      (fun k : Fin 0 => k.elim0)]
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hscalar, one_smul, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousMultilinearMap.curryRight_apply]

set_option linter.unusedSectionVars false in
/-- **The cometric double-trace passenger passthrough (the genuine cometric-specific ingredient).**  The
unit value of the one-passenger-lower cometric post-composition `cometric(p) ∘ wⱼ`, where
`wⱼ = tailCurryUnitFib w (vlast)` is the trailing-curried input, read on a model tuple `m : Fin p → E`,
equals the unit value of the full cometric post-composition `cometric(p+1) ∘ w` read on `Fin.snoc m
vlast` (the same passenger appended as the trailing covariant slot).  The cometric contracts the two
leading slots `{0, 1}` and passes the trailing passenger unchanged; concretely this is the model-tuple
identity `modelDoubleTrace_apply` together with two applications of `Fin.cons_snoc_eq_snoc_cons` (the
trailing append commutes past the two leading cometric-trace insertions). -/
private theorem cometric_postcomp_tailCurry_unit_eq (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (w : Tensor0SBundle.TensorRSSpace 0 (p + 1 + 2) I x) (vlast : E) (m : Fin p → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace p I x from
          (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (p + 2) I x from
            tailCurryUnitFib (I := I) (M := M) w vlast))
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        m =
      Tensor0SBundle.Tensor0SSpace.toModel
          (((show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (p + 1) I x from
            (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.snoc m vlast) := by
  classical
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceField_toSection]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ p x _,
    cometricDoubleTraceFib_toModel (I := I) g₀ (p + 1) x _]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply
      (E := E) p (cometricLmodel (I := I) g₀ x) _ m,
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply
      (E := E) (p + 1) (cometricLmodel (I := I) g₀ x) _ (Fin.snoc m vlast)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tailCurryUnitFib_unit_toModel (I := I) (M := M) w vlast]
  congr 1
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons]

set_option linter.unusedSectionVars false in
/-- **The per-trailing-direction slice bound powering the passenger ampliation.**  In an all-ranks
`g₀(x)`-orthonormal Parseval frame `e`, the trailing-slot slice (the passenger covariant slot the
cometric double trace passes through unchanged) of the post-composition's output frame sum is the
one-passenger-lower cometric post-composition's fibre norm acting on the trailing-curried input
`tailCurryUnitFib w (e j)`, bounded — by the inductive hypothesis `ih` at passenger count `p` — by `κ`
times the trailing-curried input's frame sum, i.e. the `j`-slice of `κ · rfns_{(0,p+3)}(w)`.  The
cometric passthrough (slot-`p+2` passenger commutes with the leading `{0,1}` cometric trace) is the
model-tuple identity `Fin.cons_snoc_eq_snoc_cons`. -/
private theorem cometricDoubleTrace_postcomp_rfns_slice_le (g₀ : SmoothRiemannianMetric I M) (κ : ℝ)
    (p : ℕ)
    (ih : ∀ (x : M) (w : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from w)) ≤
        κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x w)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (w : Tensor0SBundle.TensorRSSpace 0 (p + 1 + 2) I x)
    (unit0 : Tensor0SBundle.Tensor0SSpace 0 I x)
    (hunit0 : unit0 =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    (j : Fin n)
    (hrepr : ∀ (s : ℕ) (S : Tensor0SBundle.TensorRSSpace 0 s I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 0 s S n e K J) :
    ∑ J : Fin p → Fin n,
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 1) I x from
              (show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
                (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))
              unit0)
            (fun k => e ((Fin.snoc J j : Fin (p + 1) → Fin n) k))) ^ 2 ≤
      ∑ J : Fin (p + 2) → Fin n,
        κ * (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w) unit0)
            (fun k => e ((Fin.snoc J j : Fin (p + 1 + 2) → Fin n) k))) ^ 2 := by
  classical
  subst hunit0
  -- The trailing-curried input fibre tensor `wⱼ := tailCurryUnitFib w (e j)`.
  set wj : Tensor0SBundle.TensorRSSpace 0 (p + 2) I x :=
    tailCurryUnitFib (I := I) (M := M) w ((e j : TangentSpace I x) : E) with hwj_def
  -- LHS slice frame sum = `rfns_{(0,p)}(cometric(p) ∘ wⱼ)`, RHS slice frame sum = `κ · rfns_{(0,p+2)}(wⱼ)`.
  have hLHS : ∑ J : Fin p → Fin n,
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 1) I x from
              (show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
                (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
                (1 : ℝ)))
            (fun k => e ((Fin.snoc J j : Fin (p + 1) → Fin n) k))) ^ 2 =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 p x
          ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace p I x from
            (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 2) I x from wj)) := by
    rw [ccRfns_zero_eq_sum_unit (I := I) g₀ p x e (hrepr p)
      ((show Tensor0SBundle.Tensor0SSpace (p + 2) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace p I x from
        (cometricDoubleTraceField (I := I) g₀ p).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + 2) I x from wj))]
    refine Finset.sum_congr rfl fun J _ => ?_
    have htuple : (fun k => e ((Fin.snoc J j : Fin (p + 1) → Fin n) k)) =
        Fin.snoc (fun k => e (J k)) ((e j : TangentSpace I x)) := by
      have := Fin.comp_snoc (fun a : Fin n => e a) J j
      simpa [Function.comp] using this
    rw [htuple]
    congr 1
    exact (cometric_postcomp_tailCurry_unit_eq (I := I) g₀ p x w ((e j : TangentSpace I x) : E)
      (fun k => e (J k))).symm
  have hRHS : ∑ J : Fin (p + 2) → Fin n,
        κ * (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
                (1 : ℝ)))
            (fun k => e ((Fin.snoc J j : Fin (p + 1 + 2) → Fin n) k))) ^ 2 =
      κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (p + 2) x wj := by
    rw [ccRfns_zero_eq_sum_unit (I := I) g₀ (p + 2) x e (hrepr (p + 2)) wj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    have htuple : (fun k => e ((Fin.snoc J j : Fin (p + 1 + 2) → Fin n) k)) =
        Fin.snoc (fun k => e (J k)) ((e j : TangentSpace I x)) := by
      have := Fin.comp_snoc (fun a : Fin n => e a) J j
      simpa [Function.comp] using this
    rw [htuple]
    congr 2
    rw [hwj_def, tailCurryUnitFib_unit_toModel (I := I) (M := M) w ((e j : TangentSpace I x) : E)
      (fun k => e (J k))]
  rw [hLHS, hRHS]
  exact ih x wj

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
  intro p
  induction p with
  | zero => exact hbase
  | succ p ih =>
    intro x w
    classical
    obtain ⟨n, e, _hn, hrepr⟩ := ccAllRanksFrameWitness (I := I) g₀ x
    -- Abbreviations for the two model-unit values (`w unit` and the postcomposed `cometric(p+1) ∘ w`
    -- unit), as plain `(0, ·)` model multilinear forms.
    set unit0 : Tensor0SBundle.Tensor0SSpace 0 I x :=
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)
      with hunit0
    set Dw : Tensor0SBundle.Tensor0SModel (p + 1 + 2) ℝ E :=
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w) unit0) with hDw_def
    -- The trailing-slot Parseval split of the *output* fibre norm, peeling the trailing passenger
    -- covariant slot via `Fin.snocEquiv`.  Per trailing direction `j`, the slice fibre norm is the
    -- one-passenger-lower cometric postcomposition acting on the trailing-curried input.
    -- LHS (output) frame sum.
    rw [ccRfns_zero_eq_sum_unit (I := I) g₀ (p + 1) x e (hrepr (p + 1))
      ((show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (p + 1) I x from
        (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))]
    -- RHS (input) frame sum, split off the leading-passenger nothing — we rewrite the whole `rfns w`
    -- as the frame sum and peel its trailing index too.
    rw [ccRfns_zero_eq_sum_unit (I := I) g₀ (p + 1 + 2) x e (hrepr (p + 1 + 2)) w]
    -- Peel the trailing index `Fin.snocEquiv` on the output frame sum.
    rw [← Fintype.sum_equiv
        (Fin.snocEquiv (fun _ : Fin (p + 1) => Fin n))
        (fun jJ : Fin n × (Fin p → Fin n) =>
          (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                (show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                  (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
                  (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                      Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))
                unit0)
              (fun k => e ((Fin.snoc jJ.2 jJ.1 : Fin (p + 1) → Fin n) k))) ^ 2)
        (fun J : Fin (p + 1) → Fin n =>
          (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                (show Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace (p + 1) I x from
                  (cometricDoubleTraceField (I := I) g₀ (p + 1)).toSection x).comp
                  (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                      Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w))
                unit0)
              (fun k => e (J k))) ^ 2)
        (fun jJ => by rfl)]
    -- Distribute `κ` through the input frame sum, then peel its trailing index.
    rw [Finset.mul_sum]
    rw [← Fintype.sum_equiv
        (Fin.snocEquiv (fun _ : Fin (p + 1 + 2) => Fin n))
        (fun jJ : Fin n × (Fin (p + 2) → Fin n) =>
          κ * (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w) unit0)
              (fun k => e ((Fin.snoc jJ.2 jJ.1 : Fin (p + 1 + 2) → Fin n) k))) ^ 2)
        (fun J : Fin (p + 1 + 2) → Fin n =>
          κ * (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (p + 1 + 2) I x from w) unit0)
              (fun k => e (J k))) ^ 2)
        (fun jJ => by rfl)]
    -- Now both sides are `∑_{(j, J)}`; reduce `(j, J)` to `j` and `J` via `Fintype.sum_prod_type`,
    -- and bound termwise.  Per trailing direction `j`, the output slice frame sum is the one-lower
    -- cometric postcomposition's fibre norm, bounded by `κ ·` the input slice frame sum by `ih`.
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    -- the per-`j` trailing slice: this is `rfns_{(0,p)}(cometric(p) ∘ wⱼ) ≤ κ · rfns_{(0,p+2)}(wⱼ)`
    -- with `wⱼ` the trailing-curried (slot `p+2` fixed to `e j`) input, supplied by `ih`.
    exact cometricDoubleTrace_postcomp_rfns_slice_le (I := I) g₀ κ p ih x e w unit0 hunit0 j hrepr

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
theorem exists_uniform_cometricDoubleTraceField_postcomp_gOpNorm_rfns_le
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
theorem exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le
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

/-! ## The cross-correction parallel contraction as an `RfnsBilinearProduct`

The cross-correction `g₀`-single contraction `crossCorrParallelContraction g₀` is a *parallel*
fibrewise bilinear bundle map `(0, 2 + a) ⊗ (0, 3 + b) → (0, 3 + a + b)` (parallel because the cometric
`g₀⁻¹` it contracts through is `∇₀`-parallel, `crossCorrCometricOp_covGrad_eq_zero`).  It therefore
realizes the `rfns`-currency two-section bilinear-product abstraction `RfnsBilinearProduct g₀ 2 3 3` of
`QuadraticProductRfnsGrid`, whose binomial covariant-Leibniz `rfns` diagonal grid
`exists_rfns_iteratedCovGrad_prod_diagGrid_le` is the order-`p` jet control the cross-correction
top/rest split consumes.

The two genuine `∇`-compatibility fields:

* `rfns_prod_le` — the `g`-fibre-norm operator bound `rfns(prod S T)(x) ≤ κ · rfns(S)(x) · rfns(T)(x)`,
  with `κ` the order-`(a, b)`-uniform `g`-operator-norm envelope of the cometric trace operator field
  (`exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le`) and `crossCorrProdSection_rfns_le` for
  the product-section factor;
* `covGrad_prod` — the exact two-section covariant Leibniz `∇(prod S T) = (rank-cast) prod (∇S) T +
  (slot-reindex) prod S (∇T)`, the differentiated-operator cross term vanishing by the cometric
  parallelism (`crossCorrCometricOp_covGrad_eq_zero`), the second summand's interior gradient slot
  relocated to the leading slot by the constant reindexing `crossCorrCovGradPerm` (a parallel fibre
  isometry the grid engine strips freely). -/

/-- **The uniform `rfns` bilinear bound of the cross-correction contraction.**  There is a single
order-`(a, b)`-uniform nonnegative constant `κ` with `rfns(prod S T)(x) ≤ κ · rfns(S)(x) · rfns(T)(x)`
for every gradient shift `(a, b)`, factor pair `S, T` and point `x`.  Through the operator-field
factorisation `crossCorrParallelContraction = appCcRS (crossCorrCometricOp) (crossCorrProdSection)`, the
fibre value is the cometric trace operator post-composed after the product section's fibre; the uniform
post-composition `g`-operator-norm envelope `exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le`
bounds it by `κ · rfns(crossCorrProdSection)(x) ≤ κ · rfns(S)(x) · rfns(T)(x)`
(`crossCorrProdSection_rfns_le`). -/
theorem exists_uniform_crossCorrParallelContraction_rfns_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {a b : ℕ} (S : SmoothCcTensor g₀ 0 (2 + a)) (T : SmoothCcTensor g₀ 0 (3 + b))
      (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + a + b) x
          ((crossCorrParallelContraction (I := I) g₀ S T).toSection x) ≤
        κ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (S.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + b) x (T.toSection x) := by
  classical
  obtain ⟨κ, hκ0, hκ⟩ := exists_uniform_crossCorrCometricOp_postcomp_gOpNorm_rfns_le (I := I) g₀
  refine ⟨κ, hκ0, fun {a b} S T x => ?_⟩
  obtain ⟨A, hAdef, hAbound⟩ := hκ a b x
  -- The contraction's fibre value is `A (crossCorrProdSection.toSection x)` (the operator-field action).
  have hfib : (crossCorrParallelContraction (I := I) g₀ S T).toSection x =
      A (show Tensor0SBundle.TensorRSSpace 0 ((3 + b) + (2 + a)) I x from
        (crossCorrProdSection (I := I) g₀ S T).toSection x) := by
    rw [hAdef ((crossCorrProdSection (I := I) g₀ S T).toSection x),
      crossCorrParallelContraction_eq_appCcRS (I := I) g₀ S T,
      appCcRS_toSection (I := I) (M := M) g₀ 0 ((3 + b) + (2 + a)) (3 + a + b)
        (crossCorrCometricOp (I := I) g₀ a b) (crossCorrProdSection (I := I) g₀ S T) x]
  rw [hfib]
  refine le_trans (hAbound ((crossCorrProdSection (I := I) g₀ S T).toSection x)) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (crossCorrProdSection_rfns_le (I := I) g₀ S T x) hκ0

end Connection
end Integral
end DifferentialGeometry

end
