import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Tensor.Multilinear.Tensor

/-! # The DeTurck-Cartan quadratic-arm `RfnsBilinearProduct` instance — the bare tensor product

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file builds the witness for the **quadratic Rest arm** (the `D∘D` arm)
of the covariant Faà-di-Bruno split of the Lie half of the Ricci–DeTurck linearization:
`deTurckCartanRfnsBilinearProduct : RfnsBilinearProduct g₀ 3 3 6`, the genuine **bare fibrewise model
tensor product** of two `(0, 3)`-connection-difference-type sections.

## What the quadratic arm consumes, and why the bare tensor product is the right witness

`symLoweredDeTurckVF g g_bg` is the symmetrised `g`-lowering of `∇W`, where `W = deTurckVF g g_bg` is
the `g`-trace of `connDiff (g, g_bg)` (`cartanRHSBilin`, `deTurckVF_apply_eq`); it is a
covariant-Faà-di-Bruno contraction of the metric jet, order-`≤ 2` in the metric.  Beside the value jet
(the linear arm `deTurckCartanDiffBilinOp`, `DiffBilinOp`) the difference of two such contractions
carries a genuine **quadratic-in-difference `D∘D`** part — the bilinear product of two independently
varying connection-difference gauge fields, the high derivative landing on either factor.  Its
covariant jet is controlled, through the diagonal two-product `rfns` grid
`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le`
(`QuadraticProductRfnsGrid.lean`, sorry-free), by the convolution `≤ j`-jet of both factors.

The **bare fibrewise model tensor product** `S ⊗ T` (no contraction, no cometric) is exactly the
right `RfnsBilinearProduct`:

* it is a genuine, *nonzero* parallel fibrewise bilinear bundle map (`mu = 1`), not a degenerate
  `mu ≡ 0` witness;
* its squared fibre norm is **exactly multiplicative**, `rfns(S ⊗ T)(x) = rfns(S)(x) · rfns(T)(x)`
  (`bareTensorProdSection_rfns_le`, the genuine continuity/boundedness in the intrinsic currency,
  proved frame-by-frame through the all-ranks `g₀(x)`-orthonormal Parseval frame and the slot-block
  factorisation `Fin.appendEquiv`);
* its covariant gradient obeys the **exact two-section covariant Leibniz** with no cross term
  (`bareTensorProdSection_covGrad`), because the tensor-product bundle map is parallel — it carries no
  metric at all.

The single high covariant derivative may land on **either** factor (the binomial covariant Leibniz of
the two-section product), so the diagonal grid carries the full `≤ j`-jet of both connection-difference
factors — exactly the structure of the `connDiff ∧ connDiff` quadratic cross term.

## Why a generic bare-product engine (R1)

The bare tensor product is decoupled from the specific factor sections; the consumer instantiates it at
the two connection-difference fields and folds in the metric-built coefficient sups.  We therefore build
the reusable generic engine `bareTensorRfnsBilinearProduct g₀ s₁ s₂ : RfnsBilinearProduct g₀ s₁ s₂
(s₁ + s₂)` (the canonical "the bare fibrewise model tensor product is a parallel bilinear product with
operator constant `1`"), and name the DeTurck-Cartan quadratic-arm witness as its `(3, 3, 6)`
specialisation.

## Non-vacuity

`bareTensorProdSection_rfns_le` is the genuine multiplicativity, so for `S`, `T` with `rfns(S)(x) > 0`,
`rfns(T)(x) > 0` (a generic fibre) one has `rfns(prod S T)(x) = rfns(S)(x) · rfns(T)(x) > 0`, while a
degenerate `mu ≡ 0` right side `0 · rfns(S)(x) · rfns(T)(x)` vanishes — the `mu ≡ 0` witness is
rejected.  The chosen `mu = 1` genuinely uses the sections. -/

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

/-! ## The fibrewise model tensor-product value and field -/

/-- **The unit fibre value of a `(0, s)`-section as a model `Tensor0SModel s`.**  The `(0, s)`-tensor
fibre `S.toSection x : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` evaluated at the canonical unit
`(0, 0)`-tensor, read to the model.  The standard `(0, s)`-as-`Hom(scalar, ·)` unit extraction. -/
noncomputable def bareUnitModel {s : ℕ} (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 s) (x : M) : Tensor0SBundle.Tensor0SModel s ℝ E :=
  Tensor0SBundle.Tensor0SSpace.toModel
    ((S.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) 1))

/-- **The frame-free model tensor-product field** `x ↦ ofModel (modelProduct (bareUnitModel S x)
(bareUnitModel T x))`, a smooth `(0, s₁ + s₂)`-tensor field.  The model product of the smooth unit
fibres of `S`, `T` is smooth: its trivialised coordinate factors, by `modelProduct_apply`, into a
product of an `S`-coordinate and a `T`-coordinate (the basis-coordinate criterion
`contMDiff_multilinearSection_iff_coord`).  Frame-free; carries NO metric. -/
theorem bareTensorProdField_contMDiff (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s₁ + s₂) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s₁ + s₂) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s₁ + s₂) I z) x
        ((Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
              (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x)) :
            Tensor0SBundle.Tensor0SSpace (s₁ + s₂) I x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s₁ + s₂)
  classical
  have hSfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s₁ ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s₁ ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s₁ I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (bareUnitModel (I := I) g₀ S x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g₀ s₁ S)
  have hTfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s₂ ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s₂ ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s₂ I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (bareUnitModel (I := I) g₀ T x))) := by
    simpa only [Tensor0SBundle.Tensor0SSpace.ofModel_toModel] using
      (contMDiff_unitEvalSection (I := I) (M := M) g₀ s₂ T)
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
          (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x)) :
          Tensor0SBundle.Tensor0SSpace (s₁ + s₂) I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (bareUnitModel (I := I) g₀ S x) :
      Tensor0SBundle.Tensor0SSpace s₁ I x))).mp hSfield
  have hT := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (bareUnitModel (I := I) g₀ T x) :
      Tensor0SBundle.Tensor0SSpace s₂ I x))).mp hTfield
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := ∞)
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hS (τ ∘ Fin.castAdd s₂) x₀)).clm_apply
        (hT (τ ∘ Fin.natAdd s₁) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
      (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

/-- **The frame-free model tensor-product field** as a `Tensor0SField`, packaging
`bareTensorProdField_contMDiff`. -/
noncomputable def bareTensorProdField (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (s₁ + s₂) :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s₁ + s₂)
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
        (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x)),
    bareTensorProdField_contMDiff (I := I) g₀ S T⟩

/-- **The bare model tensor-product section** `S ⊗ T : (0, s₁) ⊗ (0, s₂) → (0, s₁ + s₂)`, packaging
`bareTensorProdField`.  The genuine non-vacuous fibrewise `ℝ`-bilinear tensor product, frame-free
(carries no metric). -/
noncomputable def bareTensorProdSection (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) :
    SmoothCcTensor g₀ 0 (s₁ + s₂) where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (bareTensorProdField (I := I) g₀ S T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The unit-evaluated model value of the bare tensor-product section is the model product of the two
factor units.  Definitional unfolding of `bareTensorProdSection` through the `fromMultilinearSection`
unit evaluation. -/
theorem bareTensorProdSection_unitModel (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) (x : M) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((bareTensorProdSection (I := I) g₀ S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
        (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x) := by
  rw [show (bareTensorProdSection (I := I) g₀ S T).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (bareTensorProdField (I := I) g₀ S T x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (Tensor0SBundle.Tensor0SSpace.ofModel
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) s₁ s₂
          (bareUnitModel (I := I) g₀ S x) (bareUnitModel (I := I) g₀ T x))) = _
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

/-! ## The intrinsic `rfns` multiplicativity (the `mu = 1` operator bound) -/

/-- **The rank-`0` frame component reads the operator at the canonical unit.**  For a `(0, s)`-fibre
operator `op` and the empty multi-index, the frame component `fiberNormSqComponent g₀ x 0 s op n e ∅ J`
is the model value of the unit-evaluated `(0, s)`-form `toModel(op unit)` on the frame tuple
`fun k => e (J k)` (the rank-`0` cometric weight is the canonical unit `(0, 0)`-tensor, the empty
product `1`). -/
private theorem bareFiberNormSqComponent_zero_eq_unit (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n)
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
private theorem bareCcRfns_zero_eq_sum_unit (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
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
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x s e hrepr op
    (fun k => k.elim0)]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [bareFiberNormSqComponent_zero_eq_unit (I := I) g₀ s x e (fun k => k.elim0) J op]

/-- **An all-ranks `g₀(x)`-orthonormal frame Parseval witness.**  At `x` there is a single tangent
frame `e : Fin n → T_xM` (`n = finrank ℝ E`) representing the intrinsic `(0, s)` fibre norm as the
frame double sum at *every* rank `s` simultaneously — the standard `g₀(x)`-orthonormal basis built
exactly as in the definition of `riemannianFiberNormSq`, for which the frame Parseval representation is
definitional (`rfl`).  (The cross-rank local re-statement; the precedent's `ccAllRanksFrameWitness`.) -/
private theorem bareAllRanksFrameWitness (g₀ : SmoothRiemannianMetric I M) (x : M) :
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

/-- **The bare model tensor-product section's fibre norm is the product of the factor fibre norms**
(the genuine `rfns` operator bound, with operator constant `mu = 1`).
`rfns(bareTensorProdSection g₀ S T)(x) = rfns(S)(x) · rfns(T)(x)` (here stated as `≤`): in a
`g₀(x)`-orthonormal Parseval frame `e`, the unit value of the product section is the model product
`modelProduct (bareUnitModel S x) (bareUnitModel T x)`, whose value on a frame tuple `e ∘ J` splits —
by `modelProduct_apply` along `J = (J_S, J_T)` — into `αS(e ∘ J_S) · αT(e ∘ J_T)`.  Squaring and
reindexing the slot sum over `Fin (s₁ + s₂) → Fin n` as a product over `(Fin s₁ → Fin n) ×
(Fin s₂ → Fin n)` (`Fin.appendEquiv`) factors the double sum into the `S`-block sum times the `T`-block
sum, i.e. `rfns(S) · rfns(T)`.

This is the **two-section** intrinsic-currency analogue of the model-norm boundedness `modelProduct`
carries, and it forces `prod 0 T = 0`, `prod S 0 = 0`; a degenerate `mu ≡ 0` witness is rejected. -/
theorem bareTensorProdSection_rfns_le (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂) x
        ((bareTensorProdSection (I := I) g₀ S T).toSection x) ≤
      (1 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 s₁ x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s₂ x (T.toSection x) := by
  classical
  rw [one_mul]
  obtain ⟨n, e, _hn, hrepr⟩ := bareAllRanksFrameWitness (I := I) g₀ x
  -- model value of the product unit on a frame tuple splits into the two block evaluations.
  have hsplit : ∀ J : Fin (s₁ + s₂) → Fin n,
      Tensor0SBundle.Tensor0SSpace.toModel
          ((bareTensorProdSection (I := I) g₀ S T).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun k => e (J k)) =
        (bareUnitModel (I := I) g₀ S x) (fun k => e (J (Fin.castAdd s₂ k))) *
          (bareUnitModel (I := I) g₀ T x) (fun k => e (J (Fin.natAdd s₁ k))) := by
    intro J
    rw [bareTensorProdSection_unitModel, Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  rw [bareCcRfns_zero_eq_sum_unit (I := I) g₀ (s₁ + s₂) x e (hrepr (s₁ + s₂))
      ((bareTensorProdSection (I := I) g₀ S T).toSection x),
    bareCcRfns_zero_eq_sum_unit (I := I) g₀ s₁ x e (hrepr s₁) (S.toSection x),
    bareCcRfns_zero_eq_sum_unit (I := I) g₀ s₂ x e (hrepr s₂) (T.toSection x)]
  refine le_of_eq ?_
  rw [← Fintype.sum_equiv (Fin.appendEquiv s₁ s₂)
      (fun pr : (Fin s₁ → Fin n) × (Fin s₂ → Fin n) =>
        ((bareUnitModel (I := I) g₀ S x) (fun k => e (pr.1 k)) *
          (bareUnitModel (I := I) g₀ T x) (fun k => e (pr.2 k))) ^ 2)
      (fun J : Fin (s₁ + s₂) → Fin n =>
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((bareTensorProdSection (I := I) g₀ S T).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J k))) ^ 2) ?_]
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun JS _ => Finset.sum_congr rfl (fun JT _ => ?_))
    rw [mul_pow]
    rfl
  · intro pr
    simp only
    rw [hsplit ((Fin.appendEquiv s₁ s₂) pr)]
    have hS : (fun k => e (((Fin.appendEquiv s₁ s₂) pr) (Fin.castAdd s₂ k))) =
        (fun k => e (pr.1 k)) := by
      funext k
      simp only [Fin.appendEquiv_apply, Fin.append_left]
    have hT : (fun k => e (((Fin.appendEquiv s₁ s₂) pr) (Fin.natAdd s₁ k))) =
        (fun k => e (pr.2 k)) := by
      funext k
      simp only [Fin.appendEquiv_apply, Fin.append_right]
    rw [hS, hT]

/-! ## The rank-normalised bare product and its covariant Leibniz -/

/-- **The rank-normalised bare tensor product** `S ⊗ T : (0, s₁ + a) ⊗ (0, s₂ + b) → (0, s₀ + a + b)`
(with `s₀ = s₁ + s₂`).  The natural model tensor product `bareTensorProdSection` produces covariant rank
`(s₁ + a) + (s₂ + b)`; this is its rank-cast to the field-required rank `(s₁ + s₂) + a + b` (equal as
naturals).  The genuine non-vacuous fibrewise `ℝ`-bilinear tensor product, in the slot/rank shape the
`RfnsBilinearProduct` field consumes. -/
noncomputable def bareProd (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (s₁ + a)) (T : SmoothCcTensor g₀ 0 (s₂ + b)) :
    SmoothCcTensor g₀ 0 ((s₁ + s₂) + a + b) :=
  castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + b) = (s₁ + s₂) + a + b)
    (bareTensorProdSection (I := I) g₀ S T)

set_option linter.unusedSectionVars false in
/-- The rank-normalised bare product strips its rank-cast under `rfns`: at every base point its fibre
norm equals that of the natural model tensor product (the rank-cast `castRankCc_db` is `rfns`-invariant,
`rfns_iteratedCovGrad_castRankCc_db` at gradient order `0`). -/
theorem bareProd_rfns_eq (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (s₁ + a)) (T : SmoothCcTensor g₀ 0 (s₂ + b)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s₁ + s₂) + a + b) x
        ((bareProd (I := I) g₀ s₁ s₂ S T).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s₁ + a) + (s₂ + b)) x
        ((bareTensorProdSection (I := I) g₀ S T).toSection x) := by
  have h := rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
    (by omega : (s₁ + a) + (s₂ + b) = (s₁ + s₂) + a + b)
    (bareTensorProdSection (I := I) g₀ S T) 0 x
  rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g₀ 0 ((s₁ + s₂) + a + b),
    PDE.RicciFlow.iteratedCovGrad_zero (I := I) g₀ 0 ((s₁ + a) + (s₂ + b))] at h
  exact h

/-- **The `rfns` operator bound of the rank-normalised bare product** (operator constant `mu = 1`).
`rfns(bareProd S T)(x) ≤ 1 · rfns(S)(x) · rfns(T)(x)`: the rank-cast is `rfns`-invariant
(`bareProd_rfns_eq`), and the underlying model tensor product is exactly multiplicative
(`bareTensorProdSection_rfns_le`).  The genuine fibrewise continuity in the intrinsic currency; it forces
`bareProd 0 T = 0`, `bareProd S 0 = 0`, so a degenerate `mu ≡ 0` witness is rejected. -/
theorem bareProd_rfns_le (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (s₁ + a)) (T : SmoothCcTensor g₀ 0 (s₂ + b)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s₁ + s₂) + a + b) x
        ((bareProd (I := I) g₀ s₁ s₂ S T).toSection x) ≤
      (1 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + b) x (T.toSection x) := by
  rw [bareProd_rfns_eq (I := I) g₀ s₁ s₂ S T x]
  exact bareTensorProdSection_rfns_le (I := I) g₀ S T x

/-- **The bare-product second-summand slot reindexing** `Fin ((s₁ + s₂) + a + b + 1) ≃ itself`.  On
the bare product `S ⊗ (∇T)` (the `S`-block leading, then the `∇T`-block whose own leading slot is the
new gradient direction) it rotates the leading `(s₁ + a) + 1` slots cyclically — sending the `∇T`-block
leading slot (model-product index `s₁ + a`, the gradient direction) to position `0`, and shifting the
`S`-block slots `0 … (s₁ + a) − 1` up to positions `1 … s₁ + a` — and fixes the trailing `∇T`-passenger
slots, so that after `domDomCongr` the gradient direction the second Leibniz summand reads at the
interior slot `s₁ + a` becomes the leading slot `0`, matching the slot convention of the LHS
`∇(S ⊗ T)`.  Built as `finRotate ((s₁ + a) + 1)` on the leading block and the identity on the trailing
`s₂ + b` block (the `crossCorrPerm` idiom). -/
noncomputable def bareProdCovGradPerm (s₁ s₂ : ℕ) {a b : ℕ} :
    Equiv.Perm (Fin ((s₁ + s₂) + a + b + 1)) :=
  (finCongr (by omega : (((s₁ + a) + 1) + (s₂ + b)) = (s₁ + s₂) + a + b + 1)).permCongr
    (finSumFinEquiv.permCongr
      (Equiv.sumCongr (finRotate ((s₁ + a) + 1)) (Equiv.refl (Fin (s₂ + b)))))

/-- Value of `bareProdCovGradPerm` on the leading `S`-block interior `j < s₁ + a`: `j ↦ j + 1`. -/
private lemma bareProdCovGradPerm_val_lt (s₁ s₂ : ℕ) {a b : ℕ}
    (i : Fin ((s₁ + s₂) + a + b + 1)) (hi : (i : ℕ) < s₁ + a) :
    ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b)) i : ℕ) = (i : ℕ) + 1 := by
  simp only [bareProdCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (s₁ + s₂) + a + b + 1 = ((s₁ + a) + 1) + (s₂ + b)) i) =
      Fin.castAdd (s₂ + b) ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, finRotate_succ_apply,
    finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd]
  rw [Fin.val_add_one_of_lt (by exact Fin.mk_lt_mk.mpr (by omega : (i:ℕ) < s₁ + a))]

/-- Value of `bareProdCovGradPerm` at the gradient slot `i = s₁ + a`: `s₁ + a ↦ 0`. -/
private lemma bareProdCovGradPerm_val_eq (s₁ s₂ : ℕ) {a b : ℕ}
    (i : Fin ((s₁ + s₂) + a + b + 1)) (hi : (i : ℕ) = s₁ + a) :
    ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b)) i : ℕ) = 0 := by
  simp only [bareProdCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (s₁ + s₂) + a + b + 1 = ((s₁ + a) + 1) + (s₂ + b)) i) =
      Fin.castAdd (s₂ + b) ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl]
  rw [show (⟨(i : ℕ), by omega⟩ : Fin ((s₁ + a) + 1)) = Fin.last (s₁ + a) from by
    apply Fin.ext; simp [hi]]
  rw [finRotate_last, finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd, Fin.val_zero]

/-- Value of `bareProdCovGradPerm` on the trailing passenger block `i > s₁ + a`: fixed. -/
private lemma bareProdCovGradPerm_val_gt (s₁ s₂ : ℕ) {a b : ℕ}
    (i : Fin ((s₁ + s₂) + a + b + 1)) (hi : s₁ + a < (i : ℕ)) :
    ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b)) i : ℕ) = (i : ℕ) := by
  simp only [bareProdCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (s₁ + s₂) + a + b + 1 = ((s₁ + a) + 1) + (s₂ + b)) i) =
      Fin.natAdd ((s₁ + a) + 1) ⟨(i : ℕ) - ((s₁ + a) + 1), by omega⟩ from by
    apply Fin.ext; simp; omega]
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd, Fin.val_mk]
  omega

/-- The bare unit-model value coincides with the canonical unit-model value (the rank-`0` input slot
`constOfIsEmpty 1` is the model image of `unitTensor`). -/
private theorem bareUnitModel_eq_unitModel (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g₀ 0 s) (x : M) :
    bareUnitModel (I := I) g₀ S x = unitModel (I := I) (M := M) g₀ s S x := by
  rfl

/-- The bare model tensor-product section coincides with the unit-model product section
(`unitModelProdSection`), so its proven unit-fibre covariant Leibniz transfers. -/
private theorem bareTensorProdSection_eq_unitModelProdSection (g₀ : SmoothRiemannianMetric I M)
    {s₁ s₂ : ℕ} (S : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) :
    bareTensorProdSection (I := I) g₀ S T = unitModelProdSection (I := I) g₀ S T := by
  rfl

/-- The `s + (k + 1)`-rank shape of `unitModel_covGrad_unitForm` (the gradient of an `(0, s + k)`
section).  Defeq-equal to the `((s + k) + 1)`-rank statement, restated so the rank is `s + (k + 1)` —
the shape the rank-normalised bare product carries (`bareProd (a := a + 1)`). -/
private theorem unitModel_covGrad_unitForm_addAssoc (g₀ : SmoothRiemannianMetric I M) {s k : ℕ}
    (W : SmoothCcTensor g₀ 0 (s + k)) (x : M) (v : Fin (s + (k + 1)) → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (s + (k + 1)) (covGrad g₀ 0 (s + k) W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + k) (LeviCivita (I := I) g₀)
          (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + k) I y from
            W.toSection y) (unitTensor (I := I) (M := M) y)) x (v 0))
        (Matrix.vecTail v) :=
  unitModel_covGrad_unitForm (I := I) (s := s + k) g₀ W x v

/-- Two successive rank-casts collapse to one (transport composition). -/
private theorem castRankCc_db_castRankCc_db (g₀ : SmoothRiemannianMetric I M) {a b c : ℕ}
    (h1 : a = b) (h2 : b = c) (W : SmoothCcTensor g₀ 0 a) :
    castRankCc_db g₀ 0 h2 (castRankCc_db g₀ 0 h1 W) =
      castRankCc_db g₀ 0 (h1.trans h2) W := by
  subst h1; subst h2; rfl

/-- The rank-normalised bare product is the rank-cast of the unit-model product section. -/
private theorem bareProd_eq_castRankCc_unitModelProdSection (g₀ : SmoothRiemannianMetric I M)
    (s₁ s₂ : ℕ) {a b : ℕ} (S : SmoothCcTensor g₀ 0 (s₁ + a)) (T : SmoothCcTensor g₀ 0 (s₂ + b)) :
    bareProd (I := I) g₀ s₁ s₂ S T =
      castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + b) = (s₁ + s₂) + a + b)
        (unitModelProdSection (I := I) g₀ S T) := by
  rfl

/-- The unit-model value of a rank-cast section reads `W`'s unit-model value on the `finCongr`-cast
tuple (the cast `h ▸ W` collapses by `subst`). -/
private theorem unitModel_castRankCc_db (g₀ : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g₀ 0 a) (x : M) (v : Fin b → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ b (castRankCc_db g₀ 0 h W) x v =
      unitModel (I := I) (M := M) g₀ a W x (fun i => v (Fin.cast h i)) := by
  subst h
  rfl

/-- The unit-model value of the covariant gradient of a rank-cast section reads `covGrad W`'s
unit-model value on the `finCongr`-cast tuple (the cast collapses by `subst`). -/
private theorem unitModel_covGrad_castRankCc_db (g₀ : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ 0 a) (x : M) (v : Fin (b + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (b + 1) (covGrad g₀ 0 b (castRankCc_db g₀ 0 h W)) x v =
      unitModel (I := I) (M := M) g₀ (a + 1) (covGrad g₀ 0 a W) x
        (fun i => v (Fin.cast (by omega) i)) := by
  subst h
  rfl

/-- Reading the unit-model value of a section at the unit recovers `unitModel`. -/
private theorem toModel_toSection_unitZero_eq_unitModel (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g₀ 0 s) (x : M) (v : Fin s → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          W.toSection x) (unitZeroSec (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ s W x v := by
  rfl

/-- **The product covariant-Leibniz second-summand slot reindexing** `Fin ((p + q) + 1) ≃ itself`:
`finRotate (p + 1)` on the leading `p + 1` slots, identity on the trailing `q` slots.  Relocates the
interior gradient slot (model-product index `p`) of the second summand `S ⊗ (∇T)` to the leading slot,
matching `∇(S ⊗ T)`. -/
def prodCovGradPerm (p q : ℕ) : Equiv.Perm (Fin ((p + q) + 1)) :=
  (finCongr (by omega : ((p + 1) + q) = (p + q) + 1)).permCongr
    (finSumFinEquiv.permCongr
      (Equiv.sumCongr (finRotate (p + 1)) (Equiv.refl (Fin q))))

/-- **Value of `prodCovGradPerm` on the leading-block interior** `j < p`: `j ↦ j + 1`
(`finRotate (p + 1)` shifts the `S`-block slots up). -/
private lemma prodCovGradPerm_val_lt (p q : ℕ) (i : Fin ((p + q) + 1)) (hi : (i : ℕ) < p) :
    ((prodCovGradPerm p q) i : ℕ) = (i : ℕ) + 1 := by
  simp only [prodCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (p + q) + 1 = (p + 1) + q) i) =
      Fin.castAdd q ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, finRotate_succ_apply,
    finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd]
  rw [Fin.val_add_one_of_lt (by exact Fin.mk_lt_mk.mpr (by omega : (i:ℕ) < p))]

/-- **Value of `prodCovGradPerm` at the gradient slot** `i = p`: `p ↦ 0`
(`finRotate (p + 1)` wraps the last `S`-block slot to the front). -/
private lemma prodCovGradPerm_val_eq (p q : ℕ) (i : Fin ((p + q) + 1)) (hi : (i : ℕ) = p) :
    ((prodCovGradPerm p q) i : ℕ) = 0 := by
  simp only [prodCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (p + q) + 1 = (p + 1) + q) i) =
      Fin.castAdd q ⟨(i : ℕ), by omega⟩ from by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl]
  rw [show (⟨(i : ℕ), by omega⟩ : Fin (p + 1)) = Fin.last p from by apply Fin.ext; simp [hi]]
  rw [finRotate_last, finSumFinEquiv_apply_left, Fin.val_cast, Fin.val_castAdd, Fin.val_zero]

/-- **Value of `prodCovGradPerm` on the trailing passenger block** `i > p`: fixed
(the identity on the `∇T`-passenger `Fin q` block). -/
private lemma prodCovGradPerm_val_gt (p q : ℕ) (i : Fin ((p + q) + 1)) (hi : p < (i : ℕ)) :
    ((prodCovGradPerm p q) i : ℕ) = (i : ℕ) := by
  simp only [prodCovGradPerm, Equiv.permCongr_apply, finCongr_symm, finCongr_apply]
  rw [show (Fin.cast (by omega : (p + q) + 1 = (p + 1) + q) i) =
      Fin.natAdd (p + 1) ⟨(i : ℕ) - (p + 1), by omega⟩ from by apply Fin.ext; simp; omega]
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd, Fin.val_mk]
  omega

/-- **The exact two-section covariant Leibniz of the bare model tensor-product section** at every rank
`p`, `q` (the section-level form).  The cross term differentiating the parallel tensor-product map
vanishes; the left summand is rank-cast from `(p + 1) + q`; the second summand's interior gradient slot
(index `p`) is relocated to the leading slot by `prodCovGradPerm`.  Proved at the unit fibre through
`unitModelProdSection_covGrad_unitModel_pub` (LHS) and `unitModelProdSection_unitModel` +
`permuteCcTensor_unitModel` + `unitModel_covGrad_unitForm` (the two RHS summands), matched by the
`modelProduct` slot-block structure. -/
theorem unitModelProdSection_covGrad (g₀ : SmoothRiemannianMetric I M) {p q : ℕ}
    (S : SmoothCcTensor g₀ 0 p) (T : SmoothCcTensor g₀ 0 q) :
    covGrad g₀ 0 (p + q) (unitModelProdSection (I := I) g₀ S T) =
      castRankCc_db g₀ 0 (by omega : (p + 1) + q = (p + q) + 1)
          (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 p S) T) +
        PDE.DeTurck.permuteCcTensor g₀ (prodCovGradPerm p q)
          (castRankCc_db g₀ 0 (by omega : p + (q + 1) = (p + q) + 1)
            (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T))) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  -- RHS: split the section sum, distribute the unit evaluation and `toModel`.
  rw [show ((castRankCc_db g₀ 0 (by omega : (p + 1) + q = (p + q) + 1)
            (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 p S) T) +
          PDE.DeTurck.permuteCcTensor g₀ (prodCovGradPerm p q)
            (castRankCc_db g₀ 0 (by omega : p + (q + 1) = (p + q) + 1)
              (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T)))).toSection x) =
        (castRankCc_db g₀ 0 (by omega : (p + 1) + q = (p + q) + 1)
            (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 p S) T)).toSection x +
          (PDE.DeTurck.permuteCcTensor g₀ (prodCovGradPerm p q)
            (castRankCc_db g₀ 0 (by omega : p + (q + 1) = (p + q) + 1)
              (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T)))).toSection x from rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (covGrad g₀ 0 (p + q) (unitModelProdSection (I := I) g₀ S T)) x v]
  -- Summand 1: strip cast, read unit-model product.
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (castRankCc_db g₀ 0 (by omega : (p + 1) + q = (p + q) + 1)
      (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 p S) T)) x v]
  rw [unitModel_castRankCc_db (I := I) g₀ (by omega : (p + 1) + q = (p + q) + 1)
    (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 p S) T) x]
  rw [unitModelProdSection_unitModel (I := I) g₀ (covGrad g₀ 0 p S) T x]
  -- Summand 2: read permuteCcTensor (domDomCongr), strip cast, read unit-model product.
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (PDE.DeTurck.permuteCcTensor g₀ (prodCovGradPerm p q)
      (castRankCc_db g₀ 0 (by omega : p + (q + 1) = (p + q) + 1)
        (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T)))) x v]
  rw [PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ (prodCovGradPerm p q)
    (castRankCc_db g₀ 0 (by omega : p + (q + 1) = (p + q) + 1)
      (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T))) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_castRankCc_db (I := I) g₀ (by omega : p + (q + 1) = (p + q) + 1)
    (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 q T)) x]
  rw [unitModelProdSection_unitModel (I := I) g₀ S (covGrad g₀ 0 q T) x]
  -- LHS via the public unit-fibre Leibniz; then split every model product to scalars and
  -- convert every covariant-gradient unit-model to the directional form, leaving pure slot arithmetic.
  rw [unitModelProdSection_covGrad_unitModel_pub (I := I) g₀ S T x v]
  simp only [Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [unitModel_covGrad_unitForm (I := I) g₀ S x, unitModel_covGrad_unitForm (I := I) g₀ T x]
  -- Rewrite each of the six RHS slot-tuples / directions to its LHS counterpart, via the value
  -- characterisation of `prodCovGradPerm` (and the plain casts for the first summand).
  have hS1dir : ((fun i : Fin ((p + 1) + q) =>
        v (Fin.cast (by omega : (p + 1) + q = (p + q) + 1) i)) ∘ Fin.castAdd q) 0 = v 0 := by
    simp only [Function.comp_apply]; apply congrArg; apply Fin.ext; simp
  have hS1tup : Matrix.vecTail ((fun i : Fin ((p + 1) + q) =>
        v (Fin.cast (by omega : (p + 1) + q = (p + q) + 1) i)) ∘ Fin.castAdd q) =
      Matrix.vecTail v ∘ Fin.castAdd q := by
    funext j; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_castAdd]
  have hS1pass : ((fun i : Fin ((p + 1) + q) =>
        v (Fin.cast (by omega : (p + 1) + q = (p + q) + 1) i)) ∘ Fin.natAdd (p + 1)) =
      Matrix.vecTail v ∘ Fin.natAdd p := by
    funext k; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_natAdd]; omega
  have hS2pass : ((fun i : Fin (p + (q + 1)) =>
        v ((prodCovGradPerm p q) (Fin.cast (by omega : p + (q + 1) = (p + q) + 1) i))) ∘
        Fin.castAdd (q + 1)) = Matrix.vecTail v ∘ Fin.castAdd q := by
    funext j; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    rw [prodCovGradPerm_val_lt p q _ (by simp only [Fin.val_cast, Fin.val_castAdd]; omega)]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_castAdd]
  have hS2dir : ((fun i : Fin (p + (q + 1)) =>
        v ((prodCovGradPerm p q) (Fin.cast (by omega : p + (q + 1) = (p + q) + 1) i))) ∘
        Fin.natAdd p) 0 = v 0 := by
    simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    rw [prodCovGradPerm_val_eq p q _ (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega)]
    simp
  have hS2tup : Matrix.vecTail ((fun i : Fin (p + (q + 1)) =>
        v ((prodCovGradPerm p q) (Fin.cast (by omega : p + (q + 1) = (p + q) + 1) i))) ∘
        Fin.natAdd p) = Matrix.vecTail v ∘ Fin.natAdd p := by
    funext k; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    rw [prodCovGradPerm_val_gt p q _ (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_natAdd]; omega
  rw [hS1dir, hS1tup, hS1pass, hS2pass, hS2dir, hS2tup]

/-- **The exact two-section covariant Leibniz of the bare model tensor product** (POSITED deep
covariant-calculus child — to be homed in `Geometry/Connection/TensorNabla` as the generic "covariant
gradient of a bare model tensor product obeys the exact two-section Leibniz" fact, the parallel-bundle-
map analogue of the metric-contraction single-step Leibniz).

`∇₀(bareProd S T) = (rank-cast) bareProd (∇₀S) T + (slot-reindex) bareProd S (∇₀T)`: the cross term
differentiating the bilinear tensor-product map itself **vanishes**, because the model tensor-product
bundle map is parallel (it carries no metric — `∇₀` of the constant tensor-product structure is `0`).
This is the genuine deep covariant-calculus content of the quadratic arm: the binomial covariant Leibniz
of the two-section product, the high derivative landing on either factor.  The left summand carries
covariant rank `(s₁ + s₂) + (a + 1) + b`, rank-cast to `((s₁ + s₂) + a + b) + 1` by `castRankCc_db`; the
second summand's gradient slot is interior (the bare product reads the second factor's new gradient
direction at the start of the second factor block, index `s₁ + a`, NOT at the leading slot
`∇(S ⊗ T)` carries it at — `unitModel_unitModelProdSection_covGrad_right`), so it is relocated to the
leading slot by the constant slot reindexing `bareProdCovGradPerm` (a parallel fibre isometry leaving
every iterated-gradient `rfns` invariant).  The slot-0 two-section Leibniz at the unit fibre is
`unitModelProdSection_covGrad_unitModel`.

Non-vacuity: at a parallel pair the identity is the genuine product Leibniz (both summands present), not
a tautology; at `S = 0` (or `T = 0`) both sides vanish through `bareProd`'s `ℝ`-bilinearity. -/
theorem bareProd_covGrad (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) {a b : ℕ}
    (S : SmoothCcTensor g₀ 0 (s₁ + a)) (T : SmoothCcTensor g₀ 0 (s₂ + b)) :
    covGrad g₀ 0 ((s₁ + s₂) + a + b) (bareProd (I := I) g₀ s₁ s₂ S T) =
      castRankCc_db g₀ 0 (by omega : (s₁ + s₂) + (a + 1) + b = (s₁ + s₂) + a + b + 1)
          (bareProd (I := I) g₀ s₁ s₂ (a := a + 1) (b := b)
            (covGrad g₀ 0 (s₁ + a) S) T) +
        PDE.DeTurck.permuteCcTensor g₀ (bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
          (castRankCc_db g₀ 0 (by omega : (s₁ + s₂) + a + (b + 1) = (s₁ + s₂) + a + b + 1)
            (bareProd (I := I) g₀ s₁ s₂ (a := a) (b := b + 1) S (covGrad g₀ 0 (s₂ + b) T))) := by
  classical
  -- Reduce to the rank-`p,q` section-level Leibniz `unitModelProdSection_covGrad` (with
  -- `p = s₁ + a`, `q = s₂ + b`); `bareProd` is the rank-cast of `unitModelProdSection`, the summands'
  -- casts compose, and `bareProdCovGradPerm` is `prodCovGradPerm` transported along the equal rank.
  rw [bareProd_eq_castRankCc_unitModelProdSection (I := I) g₀ s₁ s₂ S T,
    bareProd_eq_castRankCc_unitModelProdSection (I := I) g₀ s₁ s₂ (a := a + 1)
      (covGrad g₀ 0 (s₁ + a) S) T,
    bareProd_eq_castRankCc_unitModelProdSection (I := I) g₀ s₁ s₂ (b := b + 1) S
      (covGrad g₀ 0 (s₂ + b) T)]
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  -- Collapse the two nested rank-casts in each summand to a single cast.
  rw [castRankCc_db_castRankCc_db (I := I) g₀
      (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + (a + 1) + b)
      (by omega : (s₁ + s₂) + (a + 1) + b = (s₁ + s₂) + a + b + 1)
      (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 (s₁ + a) S) T),
    castRankCc_db_castRankCc_db (I := I) g₀
      (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + (b + 1))
      (by omega : (s₁ + s₂) + a + (b + 1) = (s₁ + s₂) + a + b + 1)
      (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T))]
  -- RHS: split the section sum, distribute the unit evaluation and `toModel`.
  rw [show ((castRankCc_db g₀ 0 (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1)
            (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 (s₁ + a) S) T) +
          PDE.DeTurck.permuteCcTensor g₀ (bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
            (castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1)
              (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T)))).toSection x) =
        (castRankCc_db g₀ 0 (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1)
            (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 (s₁ + a) S) T)).toSection x +
          (PDE.DeTurck.permuteCcTensor g₀ (bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
            (castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1)
              (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T)))).toSection x
      from rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  -- LHS: strip the outer cast, then the public unit-fibre Leibniz.
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (covGrad g₀ 0 ((s₁ + s₂) + a + b)
      (castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + b) = (s₁ + s₂) + a + b)
        (unitModelProdSection (I := I) g₀ S T))) x v]
  rw [unitModel_covGrad_castRankCc_db (I := I) g₀ (by omega : (s₁ + a) + (s₂ + b) = (s₁ + s₂) + a + b)
    (unitModelProdSection (I := I) g₀ S T) x v]
  -- Summand 1: strip the cast, read unit-model product.
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (castRankCc_db g₀ 0 (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1)
      (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 (s₁ + a) S) T)) x v]
  rw [unitModel_castRankCc_db (I := I) g₀ (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1)
    (unitModelProdSection (I := I) g₀ (covGrad g₀ 0 (s₁ + a) S) T) x]
  rw [unitModelProdSection_unitModel (I := I) (p := s₁ + (a + 1)) g₀
    (covGrad g₀ 0 (s₁ + a) S) T x]
  -- Summand 2: permuteCcTensor (domDomCongr), strip the cast, read unit-model product.
  rw [toModel_toSection_unitZero_eq_unitModel (I := I) g₀
    (PDE.DeTurck.permuteCcTensor g₀ (bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
      (castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1)
        (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T)))) x v]
  rw [PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ (bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
    (castRankCc_db g₀ 0 (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1)
      (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T))) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_castRankCc_db (I := I) g₀ (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1)
    (unitModelProdSection (I := I) g₀ S (covGrad g₀ 0 (s₂ + b) T)) x]
  rw [unitModelProdSection_unitModel (I := I) (q := s₂ + (b + 1)) g₀ S
    (covGrad g₀ 0 (s₂ + b) T) x]
  -- LHS via the public unit-fibre Leibniz; then split all model products to scalars.
  rw [unitModelProdSection_covGrad_unitModel_pub (I := I) g₀ S T x
    (fun i => v (Fin.cast (by omega) i))]
  simp only [Bundle.continuousMultilinearMap.modelProduct_apply]
  -- Convert each gradient unit-model (`s₁ + (a+1)` / `s₂ + (b+1)` shape) to the directional form.
  rw [unitModel_covGrad_unitForm_addAssoc (I := I) (s := s₁) (k := a) g₀ S x,
    unitModel_covGrad_unitForm_addAssoc (I := I) (s := s₂) (k := b) g₀ T x]
  -- Match the six RHS slot-tuples / directions to their LHS counterparts (all casts are
  -- value-preserving; the perm is value-characterised by `bareProdCovGradPerm_val_*`).
  have hS1dir : ((fun i : Fin ((s₁ + (a + 1)) + (s₂ + b)) =>
        v (Fin.cast (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.castAdd (s₂ + b)) 0 =
      (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) 0 := by
    simp only [Function.comp_apply]; apply congrArg; apply Fin.ext; simp
  have hS1tup : Matrix.vecTail ((fun i : Fin ((s₁ + (a + 1)) + (s₂ + b)) =>
        v (Fin.cast (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.castAdd (s₂ + b)) =
      Matrix.vecTail (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.castAdd (s₂ + b) := by
    funext j; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext; simp [Fin.val_succ]
  have hS1pass : ((fun i : Fin ((s₁ + (a + 1)) + (s₂ + b)) =>
        v (Fin.cast (by omega : (s₁ + (a + 1)) + (s₂ + b) = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.natAdd (s₁ + (a + 1))) =
      Matrix.vecTail (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.natAdd (s₁ + a) := by
    funext k; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext; simp [Fin.val_succ]; omega
  have hS2pass : ((fun i : Fin ((s₁ + a) + (s₂ + (b + 1))) =>
        v ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
          (Fin.cast (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1) i))) ∘
        Fin.castAdd (s₂ + (b + 1))) =
      Matrix.vecTail (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.castAdd (s₂ + b) := by
    funext j; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    rw [bareProdCovGradPerm_val_lt s₁ s₂ _ (by simp only [Fin.val_cast, Fin.val_castAdd]; omega)]
    simp [Fin.val_succ]
  have hS2dir : ((fun i : Fin ((s₁ + a) + (s₂ + (b + 1))) =>
        v ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
          (Fin.cast (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1) i))) ∘
        Fin.natAdd (s₁ + a)) 0 =
      (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) 0 := by
    simp only [Function.comp_apply]; apply congrArg; apply Fin.ext
    rw [bareProdCovGradPerm_val_eq s₁ s₂ _ (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega)]
    simp
  have hS2tup : Matrix.vecTail ((fun i : Fin ((s₁ + a) + (s₂ + (b + 1))) =>
        v ((bareProdCovGradPerm s₁ s₂ (a := a) (b := b))
          (Fin.cast (by omega : (s₁ + a) + (s₂ + (b + 1)) = (s₁ + s₂) + a + b + 1) i))) ∘
        Fin.natAdd (s₁ + a)) =
      Matrix.vecTail (fun i : Fin (((s₁ + a) + (s₂ + b)) + 1) =>
        v (Fin.cast (by omega : ((s₁ + a) + (s₂ + b)) + 1 = (s₁ + s₂) + a + b + 1) i)) ∘
        Fin.natAdd (s₁ + a) := by
    funext k; simp only [Matrix.vecTail, Function.comp_apply]
    apply congrArg; apply Fin.ext
    rw [bareProdCovGradPerm_val_gt s₁ s₂ _ (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega)]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_natAdd]; omega
  rw [hS1dir, hS1tup, hS1pass, hS2pass, hS2dir, hS2tup]

/-! ## The assembled `RfnsBilinearProduct` instances -/

/-- **The generic bare-tensor-product `RfnsBilinearProduct g₀ s₁ s₂ (s₁ + s₂)`.**  The bare fibrewise
model tensor product packaged as a `RfnsBilinearProduct`, in the **rfns-direct** style (`prod` is a
`SmoothCcTensor`-valued section, the envelope is the intrinsic `riemannianFiberNormSq`; no Hom-bundle
CLM, no model `NormedSpace`): its `prod` field is the rank-normalised bare product `bareProd`; its
`covGrad_prod` field is the exact two-section covariant Leibniz `bareProd_covGrad` (the cross term
vanishes — the tensor-product map is parallel); its `mu` field is the constant `1`, with `mu_nonneg`
(`zero_le_one`) and `rfns_prod_le` (`bareProd_rfns_le`) its nonnegativity and the multiplicative bound.

On this instance the diagonal two-product `rfns` jet grid
`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` is instantiated for any pair of
factor sections.  Reusable (R1), decoupled from any specific factors. -/
noncomputable def bareTensorRfnsBilinearProduct (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) :
    RfnsBilinearProduct g₀ s₁ s₂ (s₁ + s₂) where
  prod := fun S T => bareProd (I := I) g₀ s₁ s₂ S T
  covGradPerm := bareProdCovGradPerm s₁ s₂
  covGrad_prod := fun S T => bareProd_covGrad (I := I) g₀ s₁ s₂ S T
  mu := 1
  mu_nonneg := zero_le_one
  rfns_prod_le := fun S T x => bareProd_rfns_le (I := I) g₀ s₁ s₂ S T x

/-- **The DeTurck-Cartan quadratic-arm `RfnsBilinearProduct g₀ 3 3 6`.**  The witness for the quadratic
`D∘D` Rest arm of the covariant Faà-di-Bruno split of the Lie half of the Ricci–DeTurck linearization:
the bare fibrewise model tensor product of two `(0, 3)`-connection-difference-type sections, the
`(3, 3, 6)` specialisation of the generic bare-tensor-product engine `bareTensorRfnsBilinearProduct`.

On this instance the quadratic arm of the DeTurck-Cartan covariant top/rest split
(`symLoweredDeTurckVF_iteratedCovGrad_topRest_split`, the P1b consumer) cites the diagonal two-product
`rfns` jet grid `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le`
```
rfns(∇^j (D₁ ⊗ D₂))(x) ≤ C j · ∑_{i ≤ j} rfns(∇^i D₁)(x) · (∑_{l ≤ j − i} rfns(∇^l D₂)(x)),
```
the exact diagonal-convolution `≤ j`-jet shape of the `connDiff ∧ connDiff` quadratic cross term (one
difference connection-difference factor against the fixed factor, the high derivative on the diagonal).
Non-vacuous (the bare product is genuinely nonzero, `mu = 1`). -/
noncomputable def deTurckCartanRfnsBilinearProduct (g₀ : SmoothRiemannianMetric I M) :
    RfnsBilinearProduct g₀ 3 3 6 :=
  bareTensorRfnsBilinearProduct (I := I) g₀ 3 3

/-- **The diagonal `rfns` jet grid for the DeTurck-Cartan quadratic `D∘D` arm.**  The consumer-facing
specialisation of `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` at the assembled
instance `deTurckCartanRfnsBilinearProduct`: for the two connection-difference factors `D₁`, `D₂` (each a
rank-`(0, 3)` factor), there is a nonnegative order-dependent constant `C`, uniform over the factors and
the base point, with the diagonal (convolution) product grid
```
rfns(∇^j (D₁ ⊗ D₂))(x) ≤ C j · ∑_{i ≤ j} rfns(∇^i D₁)(x) · (∑_{l ≤ j − i} rfns(∇^l D₂)(x)).
```
This is the exact pointwise shape the quadratic arm of the P1b consumer
`symLoweredDeTurckVF_iteratedCovGrad_topRest_split` consumes. -/
theorem exists_rfns_iteratedCovGrad_deTurckCartanProd_diagGrid_le (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 3) (T : SmoothCcTensor g₀ 0 3) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (x : M) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + j) x
          ((iteratedCovGrad g₀ 0 6 j
            ((deTurckCartanRfnsBilinearProduct (I := I) g₀).prod (a := 0) (b := 0) S T)).toSection x) ≤
        C j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((iteratedCovGrad g₀ 0 3 i S).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad g₀ 0 3 l T).toSection x) :=
  (deTurckCartanRfnsBilinearProduct (I := I) g₀).exists_rfns_iteratedCovGrad_prod_diagGrid_le S T

end Connection
end Integral
end DifferentialGeometry

end
