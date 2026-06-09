import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

/-!
# The intrinsic frame-summed Weitzenböck bracket remainder fibre order

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible **pointwise** quantitative content of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect once the pure-Riemann channel is peeled off: the *intrinsic
frame-summed* moving-frame bracket remainder

```
∑ᵢ remDiffBracketFib g s S x i,   Bᵢ := smoothOrthoFrame g x i
```

is **order-`≤ 2`** in `S`, with a valence-dependent uniform fibre bound by the sum of the fibre norms of
`∇²S`, `∇S` and `S`. Here `remDiffBracketFib` (`MovingFrameRemainderFrameSumBridge`) is the named
moving-frame remainder `remDiffFib − remDiffGenuineFib` of the frame summand: the difference of the
per-direction third-order summand `remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x
(∇·(∇²_{Bᵢ, Bᵢ} S)(x))` and its pure-Riemann genuine curvature fibre `remDiffGenuineFib` (the slot-`0`
uncurry of `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`).

## Why this is the irreducible pointwise atom (frame-summed, not per-direction)

By the sorry-free frame-sum representation `pointwiseTensorCurv_toSection_eq_frame_sum`
(`Bochner/PointwiseTensorBochner`) the defect's section value is `∑ᵢ remDiffFib g s S x i`, each summand
splits as `remDiffFib = remDiffGenuineFib + remDiffBracketFib` (`remDiffFib_eq_genuine_add_bracket`), and
the pure-Riemann genuine fibres frame-sum to the concrete pure-Riemann section value
`∑ᵢ remDiffGenuineFib = (GcurvSection g s S).toSection x`
(`remDiffGenuineFib_sum_eq_GcurvSection_toSection`), so the frame-summed bracket remainder is exactly the
defect with the pure-Riemann trace removed,
`∑ᵢ remDiffBracketFib g s S x i = (pointwiseTensorCurv g s S − GcurvSection g s S).toSection x`.

The order is `≤ 2` only **after the frame sum**: each per-direction summand `remDiffFib g s S x i` is
genuinely `∇³S`-order — both `∇²_{Bᵢ, Bᵢ}(∇S)` and `∇(∇²_{Bᵢ, Bᵢ} S)` are individually third covariant
derivatives of `S` — and the top-order `∇³S` terms cancel only in the *trace* `∑ᵢ ∇²_{Bᵢ, Bᵢ}`, by the
rank-`(0, s + 1)` Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
(`IntegratedOrder2WeitzenbockCurvature`). After the cancellation the surviving frame-summed remainder
carries the differentiated-curvature `(∇R) S` channel (`rfns(S)`-order) and the `∇²S`-order frame-bracket
discrepancy, with every curvature coefficient absorbed uniformly over the compact manifold (the `‖R‖_∞` /
`‖∇R‖_∞` `g`-norm sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The `∇³S`-cancellation and the
`∇²S`-order bound are *false term-by-term* through the non-tensorial per-direction `smoothExtensionTangent`
reading (chart-selection-unbounded on `S²`); **only the intrinsic frame-summed remainder is `∇²S`-order**.

## Why this is homed here (the upstream cut)

The aggregate order-`2` commutator-defect fibre order (`exists_pointwiseTensorCurv_fiberOrder_bound`,
`Order2DefectFiberOrder`) and the four-carrier moving-frame remainder fibre bound
(`fourCarrierRemainder_fiberNormSq_bound_upstream`, `MovingFrameDiffCurvTraceSection`) both *consume* this
pointwise content; the latter additionally re-expresses it through the gauge-glued differentiated-curvature
carrier `genuineDiffCurvSection`, which is itself defined downstream in the moving-frame divergence spine.
Stating the remainder bound for the intrinsic frame sum `∑ᵢ remDiffBracketFib`, which depends only on the
sorry-free frame-sum bridge `MovingFrameRemainderFrameSumBridge`, homes it strictly *upstream* of that
spine, so the downstream consumers read it without an import cycle through the `L²` chain.

## Main result

* `exists_bracketThirdCurvField_frameSum_fiberNormSq_bound` — the **intrinsic frame-summed Weitzenböck
  bracket remainder fibre order**: a valence-dependent nonnegative constant `C : ℕ → ℝ` such that at every
  covariant rank `s`, every smooth compactly-supported `(0, s)`-tensor `S`, and *every point* `x`,
  ```
  rfns(∑ᵢ remDiffBracketFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
  ```
  Stated for the intrinsic fibre norm `rfns` of the single frame-summed tensor throughout — never a
  per-direction `M → E` quantity — so it is trap-screened (T1-clean).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq` (`rfns`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- Two `(0, s)`-tensor fibre elements agreeing on every model tuple are equal. -/
private lemma tensor0S_eq_of_toModel_eq {s : ℕ} {x : M} {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' :=
  Tensor0SSpace.toModel_injective (ContinuousMultilinearMap.ext h)

set_option linter.unusedSectionVars false in
/-- `Tensor0SSpace.toModel` commutes with finite sums. -/
private lemma tensor0S_toModel_sum {s : ℕ} {x : M} {ι : Type*} (t : Finset ι)
    (f : ι → Tensor0SSpace s I x) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) = ∑ i ∈ t, Tensor0SSpace.toModel (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Tensor0SSpace.toModel_add, ih]

set_option linter.unusedSectionVars false in
/-- An `(0, t)`-tensor subtraction, read as a continuous linear map, distributes over the
argument. -/
private lemma rs_sub_apply {t : ℕ} {x : M} (A B : TensorRSSpace 0 t I x)
    (τ : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A - B) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A) τ -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from B) τ := rfl

set_option linter.unusedSectionVars false in
/-- A finite sum of `(0, t)`-tensors, read as a continuous linear map, distributes over the
argument. -/
private lemma rs_sum_apply {t : ℕ} {x : M} {ι : Type*} (fs : Finset ι)
    (F : ι → TensorRSSpace 0 t I x) (τ : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from ∑ i ∈ fs, F i) τ =
      ∑ i ∈ fs, (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from F i) τ := by
  classical
  induction fs using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a fs' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

set_option linter.unusedSectionVars false in
/-- Slot-`0` additivity of the model reading on a `cons` tuple. -/
private lemma toModel_cons_add_slot0 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 1) I x)
    (u v : E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons (u + v) rest) =
      Tensor0SSpace.toModel W (Fin.cons u rest) + Tensor0SSpace.toModel W (Fin.cons v rest) := by
  classical
  have h := ContinuousMultilinearMap.map_update_add (Tensor0SSpace.toModel W)
    (Fin.cons u rest) (0 : Fin (t + 1)) u v
  rw [Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero] at h
  exact h

set_option linter.unusedSectionVars false in
/-- Slot-`0` homogeneity of the model reading on a `cons` tuple. -/
private lemma toModel_cons_smul_slot0 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 1) I x)
    (c : ℝ) (u : E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons (c • u) rest) =
      c * Tensor0SSpace.toModel W (Fin.cons u rest) := by
  classical
  have h := ContinuousMultilinearMap.map_update_smul (Tensor0SSpace.toModel W)
    (Fin.cons u rest) (0 : Fin (t + 1)) c u
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  rw [h, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- Slot-`0` finite linear expansion of the model reading on a `cons` tuple. -/
private lemma toModel_cons_sum_slot0 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 1) I x)
    {ι : Type*} (fs : Finset ι) (c : ι → ℝ) (v : ι → E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons (∑ j ∈ fs, c j • v j) rest) =
      ∑ j ∈ fs, c j * Tensor0SSpace.toModel W (Fin.cons (v j) rest) := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ContinuousMultilinearMap.map_coord_zero (Tensor0SSpace.toModel W) (0 : Fin (t + 1))
        (by rw [Fin.cons_zero])
  | insert a fs' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, toModel_cons_add_slot0,
        toModel_cons_smul_slot0, ih]

set_option linter.unusedSectionVars false in
/-- Slot-`1` additivity of the model reading on a double-`cons` tuple, reduced to slot `0`
through the leading-slot curry. -/
private lemma toModel_cons_add_slot1 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 2) I x)
    (u : E) (a b : E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons u (Fin.cons (a + b) rest)) =
      Tensor0SSpace.toModel W (Fin.cons u (Fin.cons a rest)) +
        Tensor0SSpace.toModel W (Fin.cons u (Fin.cons b rest)) := by
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W) (v0 := u) (vs := Fin.cons (a + b) rest),
    ← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W) (v0 := u) (vs := Fin.cons a rest),
    ← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W) (v0 := u) (vs := Fin.cons b rest)]
  exact toModel_cons_add_slot0 (I := I) (M := M)
    (tensor0S_curry (I := I) (M := M) (t + 1) x W u) a b rest

set_option linter.unusedSectionVars false in
/-- Slot-`1` homogeneity of the model reading on a double-`cons` tuple. -/
private lemma toModel_cons_smul_slot1 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 2) I x)
    (u : E) (c : ℝ) (a : E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons u (Fin.cons (c • a) rest)) =
      c * Tensor0SSpace.toModel W (Fin.cons u (Fin.cons a rest)) := by
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W) (v0 := u) (vs := Fin.cons (c • a) rest),
    ← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W) (v0 := u) (vs := Fin.cons a rest)]
  exact toModel_cons_smul_slot0 (I := I) (M := M)
    (tensor0S_curry (I := I) (M := M) (t + 1) x W u) c a rest

set_option linter.unusedSectionVars false in
/-- Slot-`1` finite linear expansion of the model reading on a double-`cons` tuple. -/
private lemma toModel_cons_sum_slot1 {t : ℕ} {x : M} (W : Tensor0SSpace (t + 2) I x)
    (u : E) {ι : Type*} (fs : Finset ι) (c : ι → ℝ) (v : ι → E) (rest : Fin t → E) :
    Tensor0SSpace.toModel W (Fin.cons u (Fin.cons (∑ j ∈ fs, c j • v j) rest)) =
      ∑ j ∈ fs, c j * Tensor0SSpace.toModel W (Fin.cons u (Fin.cons (v j) rest)) := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := W) (v0 := u) (vs := Fin.cons 0 rest)]
      exact ContinuousMultilinearMap.map_coord_zero
        (Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) (t + 1) x W u))
        (0 : Fin (t + 1)) (by rw [Fin.cons_zero])
  | insert a fs' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, toModel_cons_add_slot1,
        toModel_cons_smul_slot1, ih]

set_option linter.unusedSectionVars false in
/-- The scalar-extraction functional evaluates to `1` on the unit `(0, 0)`-tensor. -/
private lemma tensor00Scalar_unitZeroSec (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

set_option linter.unusedSectionVars false in
/-- Every `(0, 0)`-tensor is its unit-scalar multiple of the unit `(0, 0)`-tensor. -/
private lemma tensor0S_zero_span (x : M) (τ : Tensor0SSpace 0 I x) :
    τ = tensor00Scalar (I := I) (M := M) x τ • unitZeroSec (I := I) (M := M) x := by
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [show v = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun k : Fin 0 => k.elim0) = 1 from by
    rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply]]
  rw [show Tensor0SSpace.toModel τ (fun k : Fin 0 => k.elim0) =
      tensor00Scalar (I := I) (M := M) x τ from
    (tensor00Scalar_apply (I := I) (M := M) x τ (fun k : Fin 0 => k.elim0)).symm]
  rw [smul_eq_mul, mul_one]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper of a model tensor evaluates at the unit to the tensor itself. -/
private lemma tensor0SAsRS_unit_eval (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) = C := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) =
      tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) • C from
    tensor0SAsRS_apply (I := I) (M := M) x C (unitZeroSec (I := I) (M := M) x)]
  rw [tensor00Scalar_unitZeroSec (I := I) (M := M) x, one_smul]

set_option linter.unusedSectionVars false in
/-- Wrapping the unit evaluation of an `(0, t)`-tensor reconstructs the tensor. -/
private lemma tensor0SAsRS_rs_unit (t : ℕ) (x : M) (W : TensorRSSpace 0 t I x) :
    tensor0SAsRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
            (unitZeroSec (I := I) (M := M) x))) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  conv_rhs => rw [tensor0S_zero_span (I := I) (M := M) x τ]
  rw [ContinuousLinearMap.map_smul]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper is additive. -/
private lemma tensor0SAsRS_add (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C + D) =
      tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D := by
  have h : (tensor0SAsRS (I := I) (M := M) x (C + D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
        (tensor0SAsRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C + D) =
      tensor00Scalar (I := I) (M := M) x τ • C + tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.add_apply,
      smul_eq_mul]
    ring
  exact h

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper distributes over subtraction. -/
private lemma tensor0SAsRS_sub (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C - D) =
      tensor0SAsRS (I := I) (M := M) x C - tensor0SAsRS (I := I) (M := M) x D := by
  have h : (tensor0SAsRS (I := I) (M := M) x (C - D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) -
        (tensor0SAsRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C - D) =
      tensor00Scalar (I := I) (M := M) x τ • C - tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul]
    ring
  exact h

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper sends `0` to `0`. -/
private lemma tensor0SAsRS_zero (t : ℕ) (x : M) :
    tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace t I x) = 0 := by
  have h : (tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace t I x) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) = 0 := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (0 : Tensor0SSpace t I x) = 0
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_zero, smul_zero]
  exact h

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper commutes with finite sums. -/
private lemma tensor0SAsRS_sum (t : ℕ) (x : M) {ι : Type*} (fs : Finset ι)
    (F : ι → Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (∑ i ∈ fs, F i) =
      ∑ i ∈ fs, tensor0SAsRS (I := I) (M := M) x (F i) := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact tensor0SAsRS_zero (I := I) (M := M) t x
  | insert a fs' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tensor0SAsRS_add, ih]

/-- **The intrinsic frame-summed Weitzenböck bracket remainder fibre order (posited genuine pointwise
leaf).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth compactly-supported
`(0, s)`-tensor `S`, and *every point* `x`, the intrinsic fibre norm of the *frame-summed* moving-frame
bracket remainder `∑ᵢ remDiffBracketFib g s S x i` (`Bᵢ := smoothOrthoFrame g x i`) — the order-`2`
rough-Laplacian / covariant-gradient commutator defect with the pure-Riemann channel peeled off — is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S = covGrad g 0 (s + 1)
(covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(∑ᵢ remDiffBracketFib g s S x i)(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the frame-summed remainder.** The frame-summed
bracket remainder is exactly the defect with the pure-Riemann trace removed,
`∑ᵢ remDiffBracketFib g s S x i = (pointwiseTensorCurv g s S − GcurvSection g s S).toSection x` (the
sorry-free frame-sum identities `pointwiseTensorCurv_toSection_eq_frame_sum`,
`remDiffFib_eq_genuine_add_bracket`, `remDiffGenuineFib_sum_eq_GcurvSection_toSection`). Reading the rough
Laplacian as the `g`-metric trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}` of the second covariant derivative and commuting the
new gradient slot past the two trace slots by the rank-`(0, s + 1)` Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), the top-order
`∇³S` terms cancel *in the trace*: the difference is a sum of curvature contractions — the pure-Riemann
`R(∇S)` trace (already removed as `GcurvSection`, `rfns(∇S)`-order), the differentiated-curvature `(∇R) S`
contraction (`rfns(S)`-order) and the `∇²S`-order frame-bracket discrepancy — with every curvature
coefficient absorbed uniformly over the compact manifold (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the `‖R‖_∞` / `‖∇R‖_∞` `g`-norm sups). The
`∇³S`-cancellation and the `∇²S`-order bound are *false term-by-term* through the non-tensorial
per-direction `smoothExtensionTangent` reading (chart-selection-unbounded on `S²`, deleted as the false
chartJ route): each per-direction summand `remDiffFib g s S x i` is itself genuinely `∇³S`-order, and the
cancellation occurs only after the frame sum `∑ᵢ`. **Only the intrinsic frame-summed remainder is
`∇²S`-order.** The bound is stated for the intrinsic fibre norm `rfns` of the single frame-summed tensor
`∑ᵢ remDiffBracketFib g s S x i` throughout (never a per-direction `M → E` quantity), so it is
trap-screened (T1-clean).

**Why this is the upstream cut.** The pointwise frame-summed Bochner identity that would reduce this bound
to its concrete order-`≤ 2` curvature carriers is available only in *integrated* (`L²`-pairing) form
(`bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace`, `BracketDiscrepancyNullity`), and the
gauge-glued differentiated-curvature carrier `genuineDiffCurvSection` it would anchor on is defined
downstream in the moving-frame divergence spine; the downstream pointwise producers
(`exists_pointwiseTensorCurv_fiberOrder_bound`, `fourCarrierRemainder_fiberNormSq_bound_upstream`) all
transit this very content, so they cannot supply it without a cycle. This is therefore the precise
intrinsic frame-summed pointwise frontier of the curvature line, homed here above the moving-frame spine;
the body is `sorry` (the genuine classical pointwise third-order tensor Bochner–Weitzenböck curvature-term
derivation, frame-summed) and consumers transitively depend on its `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects `C ≡ 0`).** With `C s = 0` the bound would force
`rfns(∑ᵢ remDiffBracketFib g s S x i)(x) = 0`, i.e. `pointwiseTensorCurv g s S = GcurvSection g s S` at
every point. At `s = 0` the pure-Riemann trace `GcurvSection g 0 f` is the curvature of a scalar, so the
bound would force the scalar commutator defect `Curv f = Δ_∇(∇f) − ∇(Δ_∇ f)` to coincide with the
pure-Riemann trace pointwise — false on a non-flat manifold (`R ≠ 0`) for a non-harmonic `f`, since the
defect additionally carries the differentiated-curvature `(∇R) f` and the genuine Ricci-trace channels
(the integrated Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq` gives the nonzero pairing
`⟨Curv f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²}`, nonzero when curvature is present, so the remainder is
not always zero). So `C` is genuinely positive, and the remainder genuinely uses `S`. -/
theorem exists_bracketThirdCurvField_frameSum_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (∑ i : Fin (Module.finrank ℝ E),
              remDiffBracketFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) :=
  sorry

end Connection
end Integral
end DifferentialGeometry

end
