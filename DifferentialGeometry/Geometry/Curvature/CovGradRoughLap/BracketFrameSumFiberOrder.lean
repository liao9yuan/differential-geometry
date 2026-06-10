import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalFrameField
import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
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
set_option backward.isDefEq.respectTransparency false
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
private local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
private local instance : Module.Finite ℝ E := inferInstance

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

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper is `ℝ`-homogeneous. -/
private lemma tensor0SAsRS_smul (t : ℕ) (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (c • C) = c • tensor0SAsRS (I := I) (M := M) x C := by
  have h : (tensor0SAsRS (I := I) (M := M) x (c • C) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      c • (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (c • C) =
      c • (tensor00Scalar (I := I) (M := M) x τ • C)
    rw [smul_comm]
  exact h

set_option linter.unusedSectionVars false in
/-- **Quadratic homogeneity of the squared fibre norm.** `rfns(c • A) = c² · rfns(A)`. -/
private lemma riemannianFiberNormSq_smul (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M)
    (c : ℝ) (A : TensorRSSpace r t I x) :
    riemannianFiberNormSq (I := I) (M := M) g r t x (c • A) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r t x A := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r t x (c • A),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r t x A,
    TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
/-- **Per-slice domination from the slot-`0` Parseval split.** Each centre-frame bare slot-`0`
curried slice of a `(0, t + 1)`-tensor is fibre-dominated by the whole. -/
private lemma rfns_bareSlice_le (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (T : TensorRSSpace 0 (t + 1) I x) (j : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x j x))) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x T := by
  classical
  rw [riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame (I := I) (M := M) g t x T
    (fun i => smoothOrthoFrame (I := I) g x i x) rfl
    (fun i j' => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j')]
  exact Finset.single_le_sum
    (f := fun i : Fin (Module.finrank ℝ E) =>
      riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x i x))))
    (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 t x _)
    (Finset.mem_univ j)

set_option linter.unusedSectionVars false in
/-- **Slot-`0` slice domination at an arbitrary direction.** For a `(0, t + 1)`-tensor fibre
element `A` (in `Tensor0SSpace` form) and any tangent vector `v`,
`rfns(wrap (curry A v)) ≤ n · g(v, v) · rfns(wrap A)`, by expanding `v` over the centre
orthonormal frame, `n`-sub-additivity, quadratic homogeneity, and per-slice domination. -/
private lemma rfns_currySlice_le (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (A : Tensor0SSpace (t + 1) I x) (v : TangentSpace I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A v)) ≤
      (Module.finrank ℝ E : ℝ) * g.inner x v v *
        riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
          (tensor0SAsRS (I := I) (M := M) x A) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set e : Fin n → TangentSpace I x := fun j => smoothOrthoFrame (I := I) g x j x with he
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set c : Fin n → ℝ := fun j => g.inner x (e j) v with hc
  have hv : (∑ j : Fin n, c j • e j) = v :=
    orthonormal_tangent_expansion (I := I) (M := M) g x e horth v
  have hslice : tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A v) =
      ∑ j : Fin n, c j • tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A (e j)) := by
    rw [← hv, map_sum]
    rw [show (∑ j : Fin n, tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A (c j • e j)) =
        ∑ j : Fin n, c j • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A (e j) from
      Finset.sum_congr rfl (fun j _ => map_smul _ (c j) (e j))]
    rw [tensor0SAsRS_sum]
    exact Finset.sum_congr rfl (fun j _ => tensor0SAsRS_smul (I := I) (M := M) t x (c j) _)
  have hAunit : (tensor0SAsRS (I := I) (M := M) x A :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x)
      (unitZeroSec (I := I) (M := M) x) = A :=
    tensor0SAsRS_unit_eval (I := I) (M := M) (t + 1) x A
  have hdom : ∀ j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A (e j))) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
          (tensor0SAsRS (I := I) (M := M) x A) := by
    intro j
    have h := rfns_bareSlice_le (I := I) (M := M) g t x
      (tensor0SAsRS (I := I) (M := M) x A) j
    rw [hAunit] at h
    exact h
  have hsum_sq : (∑ j : Fin n, c j ^ 2) = g.inner x v v := by
    have h := parseval_family_inner_mul_sum (I := I) (M := M) g x e
      (orthonormal_tangent_expansion (I := I) (M := M) g x e horth) v v
    rw [← h]
    exact Finset.sum_congr rfl (fun j _ => by rw [hc]; ring)
  set W : Fin n → TensorRSSpace 0 t I x := fun j =>
    tensor0SAsRS (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A (e j)) with hW
  set R : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
    (tensor0SAsRS (I := I) (M := M) x A) with hR
  rw [show tensor0SAsRS (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x A v) =
      ∑ j : Fin n, c j • W j from hslice]
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 t x (∑ j : Fin n, c j • W j) ≤
      (n : ℝ) * ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • W j) := by
    have h := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 t x
      (Finset.univ : Finset (Fin n)) (fun j => c j • W j)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • W j)) ≤
      g.inner x v v * R := by
    have hstep : ∀ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • W j) ≤ c j ^ 2 * R := by
      intro j
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g 0 t x (c j) (W j)]
      exact mul_le_mul_of_nonneg_left (hdom j) (sq_nonneg (c j))
    calc (∑ j : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • W j))
        ≤ ∑ j : Fin n, c j ^ 2 * R := Finset.sum_le_sum (fun j _ => hstep j)
      _ = g.inner x v v * R := by rw [← Finset.sum_mul, hsum_sq]
  calc riemannianFiberNormSq (I := I) (M := M) g 0 t x (∑ j : Fin n, c j • W j)
      ≤ (n : ℝ) * ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • W j) := h1
    _ ≤ (n : ℝ) * (g.inner x v v * R) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
    _ = (n : ℝ) * g.inner x v v * R := by ring

set_option linter.unusedSectionVars false in
/-- **Slot-`0` reading domination at an arbitrary direction (covariant-gradient form).** For a
`(0, t + 1)`-tensor `T` and any tangent vector `v`, the slot-`0` reading
`(covGradBundleEquiv 0 t x).symm T v` is fibre-bounded by `n · g(v, v) · rfns(T)`. -/
private lemma rfns_symm_reading_le (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (T : TensorRSSpace 0 (t + 1) I x) (v : TangentSpace I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        ((covGradBundleEquiv (I := I) (M := M) 0 t x).symm T v) ≤
      (Module.finrank ℝ E : ℝ) * g.inner x v v *
        riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x T := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set e : Fin n → TangentSpace I x := fun j => smoothOrthoFrame (I := I) g x j x with he
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set c : Fin n → ℝ := fun j => g.inner x (e j) v with hc
  have hv : (∑ j : Fin n, c j • e j) = v :=
    orthonormal_tangent_expansion (I := I) (M := M) g x e horth v
  set Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 t I x :=
    (covGradBundleEquiv (I := I) (M := M) 0 t x).symm T with hΦ
  have hread : Φ v = ∑ j : Fin n, c j • Φ (e j) := by
    rw [← hv, map_sum]
    exact Finset.sum_congr rfl (fun j _ => map_smul Φ (c j) (e j))
  have hdom : ∀ j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x (Φ (e j)) ≤
        riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x T :=
    fun j => riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le (I := I) (M := M) g t x T
      (fun i => smoothOrthoFrame (I := I) g x i) (fun i j' => horth i j') j
  have hsum_sq : (∑ j : Fin n, c j ^ 2) = g.inner x v v := by
    have h := parseval_family_inner_mul_sum (I := I) (M := M) g x e
      (orthonormal_tangent_expansion (I := I) (M := M) g x e horth) v v
    rw [← h]
    exact Finset.sum_congr rfl (fun j _ => by rw [hc]; ring)
  set R : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x T with hRdef
  rw [hread]
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 t x (∑ j : Fin n, c j • Φ (e j)) ≤
      (n : ℝ) * ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • Φ (e j)) := by
    have h := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 t x
      (Finset.univ : Finset (Fin n)) (fun j => c j • Φ (e j))
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • Φ (e j))) ≤
      g.inner x v v * R := by
    have hstep : ∀ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • Φ (e j)) ≤ c j ^ 2 * R := by
      intro j
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g 0 t x (c j) (Φ (e j))]
      exact mul_le_mul_of_nonneg_left (hdom j) (sq_nonneg (c j))
    calc (∑ j : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • Φ (e j)))
        ≤ ∑ j : Fin n, c j ^ 2 * R := Finset.sum_le_sum (fun j _ => hstep j)
      _ = g.inner x v v * R := by rw [← Finset.sum_mul, hsum_sq]
  calc riemannianFiberNormSq (I := I) (M := M) g 0 t x (∑ j : Fin n, c j • Φ (e j))
      ≤ (n : ℝ) * ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x (c j • Φ (e j)) := h1
    _ ≤ (n : ℝ) * (g.inner x v v * R) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
    _ = (n : ℝ) * g.inner x v v * R := by ring

set_option linter.unusedSectionVars false in
/-- **The Parseval-family slot-`0` split of the fibre norm.** For a global Parseval frame family
`F` (reproducing every tangent vector at every point) and a `(0, t + 1)`-tensor `T` at `x`, the
fibre norm splits over the family values:
`rfns(T) = ∑ₐ rfns(wrap (curry (T unit) (F a x)))`. -/
private lemma rfns_eq_sum_parsevalSlice (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    {N : ℕ} (F : Fin N → Π b : M, TangentSpace I b)
    (hFrepr : ∀ (y : M) (u : TangentSpace I y),
      (∑ a : Fin N, g.inner y (F a y) u • F a y) = u)
    (T : TensorRSSpace 0 (t + 1) I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x T =
      ∑ a : Fin N,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
              ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x)
                (unitZeroSec (I := I) (M := M) x))
              (F a x))) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set e : Fin n → TangentSpace I x := fun j => smoothOrthoFrame (I := I) g x j x with he
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set Tu : Tensor0SSpace (t + 1) I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x)
      (unitZeroSec (I := I) (M := M) x) with hTu
  set sl : TangentSpace I x → TensorRSSpace 0 t I x := fun v =>
    tensor0SAsRS (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x Tu v) with hsl
  have hsl_add : ∀ u v : TangentSpace I x, sl (u + v) = sl u + sl v := by
    intro u v
    rw [hsl]
    simp only
    rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x Tu), tensor0SAsRS_add]
  have hsl_smul : ∀ (c : ℝ) (v : TangentSpace I x), sl (c • v) = c • sl v := by
    intro c v
    rw [hsl]
    simp only
    rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x Tu),
      tensor0SAsRS_smul]
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u v => tensorInnerPointwise (I := I) (M := M) g 0 t x
        (TensorRSSpace.toModel (sl u)) (TensorRSSpace.toModel (sl v)))
      (fun u u' v => by
        beta_reduce
        rw [hsl_add, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left])
      (fun c u v => by
        beta_reduce
        rw [hsl_smul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, smul_eq_mul])
      (fun u v v' => by
        beta_reduce
        rw [hsl_add, TensorRSSpace.toModel_add, tensorInnerPointwise_add_right])
      (fun c u v => by
        beta_reduce
        rw [hsl_smul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right, smul_eq_mul])
    with hB
  have hBdiag : ∀ v : TangentSpace I x,
      B v v = riemannianFiberNormSq (I := I) (M := M) g 0 t x (sl v) := by
    intro v
    rw [hB]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x (sl v)).symm
  have hpars := parseval_family_sum_bilin_eq (I := I) (M := M) g x
    (fun a : Fin N => F a x) (hFrepr x) e horth B
  have hortho_split := riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame
    (I := I) (M := M) g t x T e rfl horth
  rw [hortho_split]
  calc (∑ j : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 t x (sl (e j)))
      = ∑ j : Fin n, B (e j) (e j) :=
        Finset.sum_congr rfl (fun j _ => (hBdiag (e j)).symm)
    _ = ∑ a : Fin N, B (F a x) (F a x) := hpars.symm
    _ = ∑ a : Fin N, riemannianFiberNormSq (I := I) (M := M) g 0 t x (sl (F a x)) :=
        Finset.sum_congr rfl (fun a _ => hBdiag (F a x))

set_option linter.unusedSectionVars false in
/-- **Uniform `g`-norm bound of a fixed smooth tangent field over the closed manifold.** The
scalar `x ↦ g(P x, P x)` is continuous (the metric inner section is smooth and `P` is a smooth
section), hence bounded on the compact manifold. -/
private lemma exists_inner_field_sup (g : SmoothRiemannianMetric I M)
    {P : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M, g.inner x (P x) (P x) ≤ K := by
  classical
  have htotal : Continuous (fun m : M => TotalSpace.mk' ℝ
      (E := Bundle.Trivial M ℝ) m (g.inner m (P m) (P m))) :=
    Continuous.clm_bundle_apply₂ (b := fun m : M => m)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z)
      (E₃ := Bundle.Trivial M ℝ)
      g.contMDiff.continuous hP.continuous hP.continuous
  have hcont : Continuous (fun m : M => g.inner m (P m) (P m)) := by
    have hsnd : Continuous (fun p : TotalSpace ℝ (Bundle.Trivial M ℝ) =>
        (Bundle.Trivial.homeomorphProd M ℝ p).2) :=
      continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous
    exact hsnd.comp htotal
  have hCpt := (isCompact_univ (X := M)).image hcont
  obtain ⟨K₀, hK₀⟩ := hCpt.bddAbove
  refine ⟨max K₀ 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hK₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)

set_option linter.unusedSectionVars false in
/-- **Base-point-uniform proportional curvature-operator fibre bound at covariant rank `t`.**
The supremum over the compact manifold of the continuous proportional envelope. -/
private lemma exists_uniform_riemannOp_proportional (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 t I x),
      riemannianFiberNormSq (I := I) (M := M) g 0 t x
          (riemannOp (tensorCov (I := I) g 0 t) x v w T) ≤
        C * g.inner x v v * g.inner x w w *
          riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
      (I := I) (M := M) g t
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfac : 0 ≤ g.inner x v v * g.inner x w w *
      riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
    mul_nonneg (mul_nonneg hvv hww) (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 t x T)
  have hstep := hCcurv_bound x v w T
  have hmono : Ccurv x * g.inner x v v * g.inner x w w *
      riemannianFiberNormSq (I := I) (M := M) g 0 t x T ≤
      max C₀ 0 * g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
    have h := mul_le_mul_of_nonneg_right hCcurv_le hfac
    calc Ccurv x * g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 t x T
        = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T) := by ring
      _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T) := h
      _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by ring
  exact le_trans hstep hmono

set_option linter.unusedSectionVars false in
/-- **Wrap-transport of the abstract covariant derivative of a unit-evaluated section.** For a
smooth `(0, t)`-tensor section `σ`, the `(0, t)`-tensor wrapper of the abstract covariant
derivative of its unit-evaluation reconstructs the `tensorCov`-derivative of `σ`. -/
private lemma tensor0SAsRS_nab_unitEval (g : SmoothRiemannianMetric I M) (t : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯)
    (x : M) (v : TangentSpace I x) :
    tensor0SAsRS (I := I) (M := M) x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
              (unitZeroSec (I := I) (M := M) y)) x v) =
      (tensorCov (I := I) g 0 t).toFun (fun y : M => σ y) x v := by
  rw [← covDeriv_unit_eval_eq_genVal (I := I) (M := M) g t σ x v]
  exact tensor0SAsRS_rs_unit (I := I) (M := M) t x _

set_option linter.unusedSectionVars false in
/-- **Wrap-transport of the abstract Riemann curvature of a unit-evaluated section.** For a
smooth `(0, t)`-tensor section `σ` and smooth tangent fields `X, Y`, the `(0, t)`-tensor wrapper
of the abstract `(0, t)`-curvature of the unit-evaluation of `σ` is the `tensorCov`-level Riemann
curvature of `σ`. -/
private lemma tensor0SAsRS_riemannSec_unitEval (g : SmoothRiemannianMetric I M) (t : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g))
          X Y
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
              (unitZeroSec (I := I) (M := M) y)) x) =
      riemannSec (tensorCov (I := I) g 0 t) X Y (fun y : M => σ y) x := by
  classical
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g) with hnab
  set V : Π y : M, Tensor0SSpace t I y := fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
      (unitZeroSec (I := I) (M := M) y) with hV
  set σX : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 t) X (fun z : M => σ z) y)
      (covApplyRS_contMDiff (I := I) g 0 t σ.contMDiff hX) with hσX
  set σY : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 t) Y (fun z : M => σ z) y)
      (covApplyRS_contMDiff (I := I) g 0 t σ.contMDiff hY) with hσY
  have hXunit : covApply nab X V = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σX y)
        (unitZeroSec (I := I) (M := M) y)) := by
    rw [show covApply nab X V =
        covApply nab X (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) from rfl]
    rw [← covApply_unit_eval_eq_genVal (I := I) (M := M) g t σ X]
    rfl
  have hYunit : covApply nab Y V = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σY y)
        (unitZeroSec (I := I) (M := M) y)) := by
    rw [show covApply nab Y V =
        covApply nab Y (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) from rfl]
    rw [← covApply_unit_eval_eq_genVal (I := I) (M := M) g t σ Y]
    rfl
  rw [riemannSec_def nab X Y V x, riemannSec_def (tensorCov (I := I) g 0 t) X Y
    (fun y : M => σ y) x]
  rw [hXunit, hYunit]
  rw [tensor0SAsRS_sub, tensor0SAsRS_sub]
  rw [tensor0SAsRS_nab_unitEval (I := I) (M := M) g t σY x (X x),
    tensor0SAsRS_nab_unitEval (I := I) (M := M) g t σX x (Y x),
    tensor0SAsRS_nab_unitEval (I := I) (M := M) g t σ x
      (VectorField.mlieBracket I X Y x)]
  rfl

set_option linter.unusedSectionVars false in
/-- **The Θ-bridge.** The double leading-slot curry of the unit-evaluated two-free-slot
curvature-operator Hom-field action `Θ s · S`, contracted at the values of smooth fields
`X, Y`, is the abstract `(0, s)`-tensor Riemann curvature of the unit-evaluated section. -/
private lemma curry2_thetaAction_eq_riemannSec (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Θ : ∀ s' : ℕ, HomTensorRSField (E := E) (M := M) 0 s' (s' + 2) I)
    (hΘ : ∀ (s' : ℕ) (S : SmoothCcTensor g 0 s') (x : M) (u w : TangentSpace I x)
      (m : Fin s' → TangentSpace I x),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
          (appFullSec (I := I) (M := M) g 0 s' (s' + 2) (Θ s') S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s', Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s' I x from
            S.toSection x) (unitZeroSec (I := I) (M := M) x))
        (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))))
    (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (y : M) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from
            (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection y)
            (unitZeroSec (I := I) (M := M) y))
          (X y))
        (Y y) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        X Y (unitEvalSection (I := I) (M := M) g s S) y := by
  classical
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro m
  have hLHS : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from
            (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection y)
            (unitZeroSec (I := I) (M := M) y))
          (X y))
        (Y y)) m =
      - ∑ k : Fin s, Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            S.toSection y) (unitZeroSec (I := I) (M := M) y))
        (Function.update m k (riemannOp (LeviCivita (I := I) g) y (X y) (Y y) (m k))) := by
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from
          (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection y)
          (unitZeroSec (I := I) (M := M) y))
        (X y)) (v0 := Y y) (vs := m)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from
        (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection y)
        (unitZeroSec (I := I) (M := M) y)) (v0 := X y) (vs := Fin.cons (Y y) m)]
    exact hΘ s S y (X y) (Y y) m
  rw [hLHS]
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk X hX with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY with hYs_def
  have hVsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun z : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun w : M => Tensor0SSpace s I w) z
        (unitEvalSection (I := I) (M := M) g s S z)) :=
    contMDiff_unitEvalSection (I := I) (M := M) g s S
  have hRHS := riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g s Xs Ys
    (unitEvalSection (I := I) (M := M) g s S) hVsm y m
  rw [show riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        X Y (unitEvalSection (I := I) (M := M) g s S) y =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => Xs b) (fun b => Ys b) (unitEvalSection (I := I) (M := M) g s S) y from rfl]
  rw [hRHS]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hbase : baseSlotCurv (I := I) g Xs Ys y (m k) =
      riemannOp (LeviCivita (I := I) g) y (X y) (Y y) (m k) := by
    rw [baseSlotCurv]
    have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => smoothExtensionTangent (I := I) y (m k) b)) :=
      smoothExtensionTangent_contMDiff (I := I) y (m k)
    have h := riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g)
      (X := fun b => Xs b) (Y := fun b => Ys b)
      (Z := fun b : M => smoothExtensionTangent (I := I) y (m k) b) (x := y)
      hX hY hext
    rw [h]
    beta_reduce
    rw [smoothExtensionTangent_eq (I := I) y (m k)]
    rfl
  rw [hbase]
  rfl

set_option linter.unusedSectionVars false in
/-- The metric square `g(v, v)` is nonnegative. -/
private lemma g_inner_self_nonneg (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h0 | h0
  · rw [h0]; simp
  · exact (g.pos x v h0).le

/-- Monotone product chaining: `n · gv · X ≤ n · K · Y` from `gv ≤ K`, `X ≤ Y`. -/
private lemma chain_step {n' gv K X Y : ℝ} (hn : 0 ≤ n') (hg : gv ≤ K)
    (hK : 0 ≤ K) (hXY : X ≤ Y) (hX : 0 ≤ X) :
    n' * gv * X ≤ n' * K * Y :=
  mul_le_mul (mul_le_mul_of_nonneg_left hg hn) hXY hX (mul_nonneg hn hK)

set_option linter.unusedSectionVars false in
/-- **Two-slice domination.** For a `(0, t + 2)`-tensor fibre element `A` whose wrap is
fibre-bounded by `R`, the doubly-sliced wrap at `(u, v)` is bounded by
`n · KV · (n · KU · R)` for any `g`-square bounds `KU, KV` of the slice directions. -/
private lemma rfns_two_slices_le (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (A : Tensor0SSpace (t + 2) I x) (u v : TangentSpace I x) {KU KV R : ℝ}
    (hU : g.inner x u u ≤ KU) (hV : g.inner x v v ≤ KV)
    (hKU : 0 ≤ KU) (hKV : 0 ≤ KV)
    (hR : riemannianFiberNormSq (I := I) (M := M) g 0 (t + 2) x
      (tensor0SAsRS (I := I) (M := M) x A) ≤ R) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (t + 1) x A u) v)) ≤
      (Module.finrank ℝ E : ℝ) * KV * ((Module.finrank ℝ E : ℝ) * KU * R) := by
  set n : ℕ := Module.finrank ℝ E with hn
  have h1 := rfns_currySlice_le (I := I) (M := M) g t x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (t + 1) x A u) v
  have h2 := rfns_currySlice_le (I := I) (M := M) g (t + 1) x A u
  have hmid : riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
      (tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (t + 1) x A u)) ≤
      (n : ℝ) * KU * R :=
    le_trans h2 (chain_step (Nat.cast_nonneg n) hU hKU hR
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (t + 2) x _))
  exact le_trans h1 (chain_step (Nat.cast_nonneg n) hV hKV hmid
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (t + 1) x _))

set_option linter.unusedSectionVars false in
/-- **The Θ-atom bound: the differentiated abstract curvature field is order `≤ 1`.** For
fixed smooth fields `P, Q` and the two-free-slot curvature Hom-field family `Θ`, there is a
uniform nonnegative `K` (depending on `g, s, P, Q, Θ` only) with, for every `S` and `x`,
`rfns(wrap(∇_{P x}(R(P,Q)V-field))) ≤ K · (rfns(∇S)(x) + rfns(S)(x))` — through the
contracted-`Θ`-action reading, the slot-`0` Leibniz peels, and the windowed fibre bound. -/
private lemma exists_thetaAtom_bound (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Θ : ∀ s' : ℕ, HomTensorRSField (E := E) (M := M) 0 s' (s' + 2) I)
    (hΘ : ∀ (s' : ℕ) (S : SmoothCcTensor g 0 s') (x : M) (u w : TangentSpace I x)
      (m : Fin s' → TangentSpace I x),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
          (appFullSec (I := I) (M := M) g 0 s' (s' + 2) (Θ s') S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s', Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s' I x from
            S.toSection x) (unitZeroSec (I := I) (M := M) x))
        (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))))
    {P Q : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (fun y : M =>
                riemannSec
                  (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                  P Q (unitEvalSection (I := I) (M := M) g s S) y)
              x (P x))) ≤
        K * (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  obtain ⟨cc, hcc0, hccB⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g 0 s (s + 2) (Θ s)
  obtain ⟨KP, hKP0, hKP⟩ := exists_inner_field_sup (I := I) (M := M) g hP
  obtain ⟨KQ, hKQ0, hKQ⟩ := exists_inner_field_sup (I := I) (M := M) g hQ
  have hDPPsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) P P)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hP hP
  have hDPQsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) P Q)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hP hQ
  obtain ⟨KPP, hKPP0, hKPP⟩ := exists_inner_field_sup (I := I) (M := M) g hDPPsm
  obtain ⟨KPQ, hKPQ0, hKPQ⟩ := exists_inner_field_sup (I := I) (M := M) g hDPQsm
  have hKnn : 0 ≤ 4 * ((n : ℝ) * KQ * ((n : ℝ) * KP * ((n : ℝ) * KP * cc 1)) +
      (n : ℝ) * KQ * ((n : ℝ) * KPP * cc 0) + (n : ℝ) * KPQ * ((n : ℝ) * KP * cc 0)) := by
    have h1 : 0 ≤ (n : ℝ) * KQ * ((n : ℝ) * KP * ((n : ℝ) * KP * cc 1)) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKQ0)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0) (hcc0 1)))
    have h2 : 0 ≤ (n : ℝ) * KQ * ((n : ℝ) * KPP * cc 0) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKQ0)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKPP0) (hcc0 0))
    have h3 : 0 ≤ (n : ℝ) * KPQ * ((n : ℝ) * KP * cc 0) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKPQ0)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0) (hcc0 0))
    linarith
  refine ⟨4 * ((n : ℝ) * KQ * ((n : ℝ) * KP * ((n : ℝ) * KP * cc 1)) +
      (n : ℝ) * KQ * ((n : ℝ) * KPP * cc 0) + (n : ℝ) * KPQ * ((n : ℝ) * KP * cc 0)),
    hKnn, fun S x => ?_⟩
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hnab
  set Y1 : SmoothCcTensor g 0 (s + 2) :=
    appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S with hY1
  set Yf : Π y : M, Tensor0SSpace (s + 2) I y := fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 2) I y from Y1.toSection y)
      (unitZeroSec (I := I) (M := M) y) with hYf
  set E1 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hE1
  set E0 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hE0
  have hE1nn : 0 ≤ E1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hE0nn : 0 ≤ E0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- Smoothness data for the two slot-`0` Leibniz peels.
  have hYfsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 2) I z) y (Yf y)) :=
    contMDiff_unitEvalSection (I := I) (M := M) g (s + 2) Y1
  have hcurYf : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace (s + 1) I z)) y
        (Tensor0SNabla.curriedSection I M Yf y)) :=
    (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M) Yf).mp hYfsm
  set W' : Π y : M, Tensor0SSpace (s + 1) I y := fun y : M =>
    Tensor0SNabla.curriedSection I M Yf y (P y) with hW'
  have hW'sm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y (W' y)) :=
    ContMDiff.clm_bundle_apply (b := id) hcurYf hP
  have hcurW' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M W' y)) :=
    (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M) W').mp hW'sm
  have hPat := (hP x).mdifferentiableAt (by simp)
  have hQat := (hQ x).mdifferentiableAt (by simp)
  -- Peel 1 (rank `s`): contract the trailing slot field `Q`.
  have hpeel1 := abstract_succ_covDeriv_unfold_at_genVal (I := I) (M := M) g s W'
    (Vfield := P) (Y := Q) (x := x)
    ((hcurW' x).mdifferentiableAt (by simp)) hPat hQat
  -- Peel 2 (rank `s + 1`): contract the inner slot field `P`.
  have hpeel2 := abstract_succ_covDeriv_unfold_at_genVal (I := I) (M := M) g (s + 1) Yf
    (Vfield := P) (Y := P) (x := x)
    ((hcurYf x).mdifferentiableAt (by simp)) hPat hPat
  -- Identify the doubly-contracted field with the curvature field.
  have hcontr_eq : (fun y : M => Tensor0SNabla.curriedSection I M W' y (Q y)) =
      (fun y : M => riemannSec nab P Q (unitEvalSection (I := I) (M := M) g s S) y) := by
    funext y
    rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) W' y]
    rw [show W' y = Tensor0SNabla.curriedSection I M Yf y (P y) from rfl]
    rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) Yf y]
    exact curry2_thetaAction_eq_riemannSec (I := I) (M := M) g s Θ hΘ S hP hQ y
  -- The two rearranged peels.
  have hA : nab.toFun (fun y : M => Tensor0SNabla.curriedSection I M W' y (Q y)) x (P x) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (LeviCivita (I := I) g)).toFun W' x (P x)) (Q x) +
        Tensor0SNabla.curriedSection I M W' x
          ((LeviCivita (I := I) g).toFun Q x (P x)) :=
    sub_eq_iff_eq_add.mp hpeel1.symm
  have hB : (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g)).toFun W' x (P x) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
            (LeviCivita (I := I) g)).toFun Yf x (P x)) (P x) +
        Tensor0SNabla.curriedSection I M Yf x
          ((LeviCivita (I := I) g).toFun P x (P x)) := by
    have h2 := sub_eq_iff_eq_add.mp hpeel2.symm
    rw [show (fun y : M => Tensor0SNabla.curriedSection I M Yf y (P y)) = W' from rfl] at h2
    exact h2
  -- The three-term Leibniz expansion of the target derivative.
  have hsplit : nab.toFun (fun y : M =>
      riemannSec nab P Q (unitEvalSection (I := I) (M := M) g s S) y) x (P x) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
            ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
              (LeviCivita (I := I) g)).toFun Yf x (P x)) (P x)) (Q x) +
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x (Yf x)
            ((LeviCivita (I := I) g).toFun P x (P x))) (Q x) +
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x (Yf x) (P x))
          ((LeviCivita (I := I) g).toFun Q x (P x)) := by
    rw [← hcontr_eq, hA, hB]
    rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
      ContinuousLinearMap.add_apply]
    rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) Yf x]
    rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) W' x]
    rw [show W' x = Tensor0SNabla.curriedSection I M Yf x (P x) from rfl]
    rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) Yf x]
  -- Wrap the three terms and bound each.
  rw [hsplit, tensor0SAsRS_add, tensor0SAsRS_add]
  set w1 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
          (LeviCivita (I := I) g)).toFun Yf x (P x)) (P x)) (Q x)) with hw1
  set w2 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x (Yf x)
        ((LeviCivita (I := I) g).toFun P x (P x))) (Q x)) with hw2
  set w3 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x (Yf x) (P x))
      ((LeviCivita (I := I) g).toFun Q x (P x))) with hw3
  -- The `∇Y₁` window bound.
  have hgradY1 : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 3) x
      ((covGrad (I := I) (M := M) g 0 (s + 2) Y1).toSection x) ≤ cc 1 * (E0 + E1) := by
    have h := hccB S 1 x
    rw [show PDE.RicciFlow.iteratedCovGrad g 0 (s + 2) 1
        (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S) =
        covGrad (I := I) (M := M) g 0 (s + 2) Y1 from rfl] at h
    rw [show (∑ i ∈ Finset.range 2,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((PDE.RicciFlow.iteratedCovGrad g 0 s i S).toSection x)) = E0 + E1 from by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rfl] at h
    exact h
  have hY1x : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
      (Y1.toSection x) ≤ cc 0 * E0 := by
    have h := hccB S 0 x
    rw [show (∑ i ∈ Finset.range 1,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((PDE.RicciFlow.iteratedCovGrad g 0 s i S).toSection x)) = E0 from by
      rw [Finset.sum_range_one]
      rfl] at h
    exact h
  -- The wrapped second-level tensors.
  have hwrapBIG : tensor0SAsRS (I := I) (M := M) x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
        (LeviCivita (I := I) g)).toFun Yf x (P x)) =
      (covGradBundleEquiv (I := I) (M := M) 0 (s + 2) x).symm
        ((covGrad (I := I) (M := M) g 0 (s + 2) Y1).toSection x) (P x) := by
    rw [tensor0SAsRS_nab_unitEval (I := I) (M := M) g (s + 2) Y1.toSection x (P x)]
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 (s + 2) Y1 x]
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hwrapYf : tensor0SAsRS (I := I) (M := M) x (Yf x) = Y1.toSection x :=
    tensor0SAsRS_rs_unit (I := I) (M := M) (s + 2) x (Y1.toSection x)
  -- Inner-level bounds.
  have hb_BIG : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
      (tensor0SAsRS (I := I) (M := M) x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
          (LeviCivita (I := I) g)).toFun Yf x (P x))) ≤
      (n : ℝ) * KP * (cc 1 * (E0 + E1)) := by
    rw [hwrapBIG]
    refine le_trans (rfns_symm_reading_le (I := I) (M := M) g (s + 2) x
      ((covGrad (I := I) (M := M) g 0 (s + 2) Y1).toSection x) (P x)) ?_
    exact chain_step (Nat.cast_nonneg n) (hKP x) hKP0 hgradY1
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 3) x _)
  have hb_Yf : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
      (tensor0SAsRS (I := I) (M := M) x (Yf x)) ≤ cc 0 * E0 := by
    rw [hwrapYf]; exact hY1x
  -- Per-atom two-slice bounds.
  have hbw1 : riemannianFiberNormSq (I := I) (M := M) g 0 s x w1 ≤
      (n : ℝ) * KQ * ((n : ℝ) * KP * ((n : ℝ) * KP * (cc 1 * (E0 + E1)))) := by
    rw [hw1]
    exact rfns_two_slices_le (I := I) (M := M) g s x _ (P x) (Q x)
      (hKP x) (hKQ x) hKP0 hKQ0 hb_BIG
  have hbw2 : riemannianFiberNormSq (I := I) (M := M) g 0 s x w2 ≤
      (n : ℝ) * KQ * ((n : ℝ) * KPP * (cc 0 * E0)) := by
    rw [hw2]
    refine rfns_two_slices_le (I := I) (M := M) g s x (Yf x)
      ((LeviCivita (I := I) g).toFun P x (P x)) (Q x) ?_ (hKQ x) hKPP0 hKQ0 hb_Yf
    exact hKPP x
  have hbw3 : riemannianFiberNormSq (I := I) (M := M) g 0 s x w3 ≤
      (n : ℝ) * KPQ * ((n : ℝ) * KP * (cc 0 * E0)) := by
    rw [hw3]
    refine rfns_two_slices_le (I := I) (M := M) g s x (Yf x) (P x)
      ((LeviCivita (I := I) g).toFun Q x (P x)) (hKP x) ?_ hKP0 hKPQ0 hb_Yf
    exact hKPQ x
  -- Assemble by `2`-sub-additivity.
  set C1 : ℝ := (n : ℝ) * KQ * ((n : ℝ) * KP * ((n : ℝ) * KP * cc 1)) with hC1
  set C2 : ℝ := (n : ℝ) * KQ * ((n : ℝ) * KPP * cc 0) with hC2
  set C3 : ℝ := (n : ℝ) * KPQ * ((n : ℝ) * KP * cc 0) with hC3
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKQ0)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0) (hcc0 1)))
  have hC2nn : 0 ≤ C2 := by
    rw [hC2]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKQ0)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKPP0) (hcc0 0))
  have hC3nn : 0 ≤ C3 := by
    rw [hC3]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKPQ0)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKP0) (hcc0 0))
  have hbw1' : riemannianFiberNormSq (I := I) (M := M) g 0 s x w1 ≤ C1 * (E0 + E1) :=
    le_trans hbw1 (le_of_eq (by rw [hC1]; ring))
  have hbw2' : riemannianFiberNormSq (I := I) (M := M) g 0 s x w2 ≤ C2 * (E0 + E1) := by
    refine le_trans hbw2 ?_
    have h1 : (n : ℝ) * KQ * ((n : ℝ) * KPP * (cc 0 * E0)) = C2 * E0 := by rw [hC2]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) hC2nn
  have hbw3' : riemannianFiberNormSq (I := I) (M := M) g 0 s x w3 ≤ C3 * (E0 + E1) := by
    refine le_trans hbw3 ?_
    have h1 : (n : ℝ) * KPQ * ((n : ℝ) * KP * (cc 0 * E0)) = C3 * E0 := by rw [hC3]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) hC3nn
  have htotal : riemannianFiberNormSq (I := I) (M := M) g 0 s x (w1 + w2 + w3) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (w1 + w2) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w3 :=
    riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x (w1 + w2) w3
  have htotal2 : riemannianFiberNormSq (I := I) (M := M) g 0 s x (w1 + w2) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w1 +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w2 :=
    riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x w1 w2
  have hgoal : riemannianFiberNormSq (I := I) (M := M) g 0 s x (w1 + w2 + w3) ≤
      4 * (C1 + C2 + C3) * (E0 + E1) := by
    have h4 : riemannianFiberNormSq (I := I) (M := M) g 0 s x (w1 + w2 + w3) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w1 +
          4 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w2 +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x w3 := by linarith
    have hC3E : C3 * (E0 + E1) ≤ 2 * (C3 * (E0 + E1)) := by
      have : 0 ≤ C3 * (E0 + E1) := mul_nonneg hC3nn (by linarith)
      linarith
    nlinarith [hbw1', hbw2', hbw3', h4]
  refine le_trans hgoal (le_of_eq (by ring))

set_option linter.unusedSectionVars false in
/-- **Wrap-transport of the gradient slice.** The wrapped abstract derivative of the
unit-evaluated section, read at a tangent vector `v`, is the slot-`0` reading of the
covariant gradient. -/
private lemma tensor0SAsRS_nabV_eq_symm_reading (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    tensor0SAsRS (I := I) (M := M) x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x v) =
      (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) v := by
  rw [show unitEvalSection (I := I) (M := M) g s S = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y)) from rfl]
  rw [tensor0SAsRS_nab_unitEval (I := I) (M := M) g s S.toSection x v]
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x]
  rw [ContinuousLinearEquiv.symm_apply_apply]

set_option linter.unusedSectionVars false in
/-- **First-order slice bound.** `rfns(wrap(∇_v V)) ≤ n · g(v,v) · rfns(∇S(x))`. -/
private lemma rfns_nabV_le (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensor0SAsRS (I := I) (M := M) x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (unitEvalSection (I := I) (M := M) g s S) x v)) ≤
      (Module.finrank ℝ E : ℝ) * g.inner x v v *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [tensor0SAsRS_nabV_eq_symm_reading (I := I) (M := M) g s S x v]
  exact rfns_symm_reading_le (I := I) (M := M) g s x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) v

set_option linter.unusedSectionVars false in
/-- **The SHAPE-2 curvature-atom bound (order-`0` variant).** For fixed smooth fields `P, Q`,
the wrapped abstract curvature of the unit-evaluated section is uniformly bounded by
`rfns(S)(x)`. -/
private lemma exists_riemannAtom_bound (g : SmoothRiemannianMetric I M) (s : ℕ)
    {P Q : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              P Q (unitEvalSection (I := I) (M := M) g s S) x)) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  classical
  obtain ⟨Cp, hCp0, hCp⟩ := exists_uniform_riemannOp_proportional (I := I) (M := M) g s
  obtain ⟨KP, hKP0, hKP⟩ := exists_inner_field_sup (I := I) (M := M) g hP
  obtain ⟨KQ, hKQ0, hKQ⟩ := exists_inner_field_sup (I := I) (M := M) g hQ
  refine ⟨Cp * KP * KQ, by positivity, fun S x => ?_⟩
  rw [show unitEvalSection (I := I) (M := M) g s S = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y)) from rfl]
  rw [tensor0SAsRS_riemannSec_unitEval (I := I) (M := M) g s S.toSection hP hQ x]
  have hop : riemannSec (tensorCov (I := I) g 0 s) P Q
      (fun y : M => S.toSection y) x =
      riemannOp (tensorCov (I := I) g 0 s) x (P x) (Q x) (S.toSection x) :=
    riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hP hQ
      S.toSection.contMDiff
  rw [hop]
  refine le_trans (hCp x (P x) (Q x) (S.toSection x)) ?_
  have hRnn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have h1 : Cp * g.inner x (P x) (P x) ≤ Cp * KP :=
    mul_le_mul_of_nonneg_left (hKP x) hCp0
  have h2 : Cp * g.inner x (P x) (P x) * g.inner x (Q x) (Q x) ≤ Cp * KP * KQ :=
    mul_le_mul h1 (hKQ x) (g_inner_self_nonneg (I := I) (M := M) g x (Q x))
      (mul_nonneg hCp0 hKP0)
  exact mul_le_mul_of_nonneg_right h2 hRnn

set_option linter.unusedSectionVars false in
/-- **The SHAPE-2 curvature-atom bound (order-`1` variant).** For fixed smooth fields
`P, Q, Z`, the wrapped abstract curvature applied to the once-derived unit-evaluated section
`∇_Z V` is uniformly bounded by `rfns(∇S)(x)`. -/
private lemma exists_riemannGradAtom_bound (g : SmoothRiemannianMetric I M) (s : ℕ)
    {P Q Z : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              P Q
              (covApply
                (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                Z (unitEvalSection (I := I) (M := M) g s S)) x)) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  obtain ⟨Cp, hCp0, hCp⟩ := exists_uniform_riemannOp_proportional (I := I) (M := M) g s
  obtain ⟨KP, hKP0, hKP⟩ := exists_inner_field_sup (I := I) (M := M) g hP
  obtain ⟨KQ, hKQ0, hKQ⟩ := exists_inner_field_sup (I := I) (M := M) g hQ
  obtain ⟨KZ, hKZ0, hKZ⟩ := exists_inner_field_sup (I := I) (M := M) g hZ
  refine ⟨Cp * KP * KQ * ((n : ℝ) * KZ), by positivity, fun S x => ?_⟩
  set σZ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 s) Z (fun z : M => S.toSection z) y)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hZ) with hσZ
  have hZunit : covApply
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      Z (unitEvalSection (I := I) (M := M) g s S) = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σZ y)
        (unitZeroSec (I := I) (M := M) y)) := by
    rw [show unitEvalSection (I := I) (M := M) g s S = (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
          (unitZeroSec (I := I) (M := M) y)) from rfl]
    rw [← covApply_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection Z]
    rfl
  rw [hZunit]
  rw [tensor0SAsRS_riemannSec_unitEval (I := I) (M := M) g s σZ hP hQ x]
  have hσZsm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (σZ y)) := σZ.contMDiff
  have hop : riemannSec (tensorCov (I := I) g 0 s) P Q (fun y : M => σZ y) x =
      riemannOp (tensorCov (I := I) g 0 s) x (P x) (Q x) (σZ x) :=
    riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hP hQ hσZsm
  rw [hop]
  refine le_trans (hCp x (P x) (Q x) (σZ x)) ?_
  have hσZx : (σZ x : TensorRSSpace 0 s I x) =
      (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (Z x) := by
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hread : riemannianFiberNormSq (I := I) (M := M) g 0 s x (σZ x) ≤
      (n : ℝ) * KZ * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    rw [hσZx]
    refine le_trans (rfns_symm_reading_le (I := I) (M := M) g s x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) (Z x)) ?_
    exact chain_step (Nat.cast_nonneg n) (hKZ x) hKZ0 (le_refl _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  have h1 : Cp * g.inner x (P x) (P x) ≤ Cp * KP :=
    mul_le_mul_of_nonneg_left (hKP x) hCp0
  have h2 : Cp * g.inner x (P x) (P x) * g.inner x (Q x) (Q x) ≤ Cp * KP * KQ :=
    mul_le_mul h1 (hKQ x) (g_inner_self_nonneg (I := I) (M := M) g x (Q x))
      (mul_nonneg hCp0 hKP0)
  calc Cp * g.inner x (P x) (P x) * g.inner x (Q x) (Q x) *
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (σZ x)
      ≤ Cp * KP * KQ * ((n : ℝ) * KZ *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) :=
        mul_le_mul h2 hread
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
          (mul_nonneg (mul_nonneg hCp0 hKP0) hKQ0)
    _ = Cp * KP * KQ * ((n : ℝ) * KZ) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by ring

set_option linter.unusedSectionVars false in
/-- **The SHAPE-3 second-order atom bound.** For fixed smooth fields `Y, D` and a global
smooth Parseval frame family `F`, the wrapped second derivative `∇_{D x}(∇_Y V)` is uniformly
bounded by the three-term jet budget `rfns(∇²S) + rfns(∇S) + rfns(S)` at `x`: each
Parseval-family slice of `∇(∇_Y S)` is, by the first-order leading-slot commutation, a slice
of `∇²S` plus a curvature atom plus a first-order correction. -/
private lemma exists_secondOrderAtom_bound (g : SmoothRiemannianMetric I M) (s : ℕ)
    {N : ℕ} (F : Fin N → Π b : M, TangentSpace I b)
    (hFsm : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F a)))
    (hFrepr : ∀ (y : M) (u : TangentSpace I y),
      (∑ a : Fin N, g.inner y (F a y) u • F a y) = u)
    {Y D : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hD : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% D)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (covApply
                (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
                Y (unitEvalSection (I := I) (M := M) g s S))
              x (D x))) ≤
        K * (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  obtain ⟨KD, hKD0, hKD⟩ := exists_inner_field_sup (I := I) (M := M) g hD
  obtain ⟨KY, hKY0, hKY⟩ := exists_inner_field_sup (I := I) (M := M) g hY
  choose KR hKR0 hKR using
    (fun b : Fin N => exists_riemannAtom_bound (I := I) (M := M) g s hY (hFsm b))
  choose KD2 hKD20 hKD2 using
    (fun b : Fin N => exists_inner_field_sup (I := I) (M := M) g
      (covApply_contMDiff (cov := LeviCivita (I := I) g) (hFsm b) hY))
  choose KFb hKFb0 hKFb using
    (fun b : Fin N => exists_inner_field_sup (I := I) (M := M) g (hFsm b))
  set Cb : Fin N → ℝ := fun b =>
    4 * ((n : ℝ) * KFb b * ((n : ℝ) * KY)) + 4 * KR b + 2 * ((n : ℝ) * KD2 b) with hCb
  have hCb0 : ∀ b, 0 ≤ Cb b := by
    intro b
    rw [hCb]
    have h1 : 0 ≤ (n : ℝ) * KFb b * ((n : ℝ) * KY) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hKFb0 b))
        (mul_nonneg (Nat.cast_nonneg n) hKY0)
    have h2 : 0 ≤ KR b := hKR0 b
    have h3 : 0 ≤ (n : ℝ) * KD2 b := mul_nonneg (Nat.cast_nonneg n) (hKD20 b)
    linarith
  refine ⟨(n : ℝ) * KD * (∑ b : Fin N, Cb b),
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hKD0)
      (Finset.sum_nonneg (fun b _ => hCb0 b)), fun S x => ?_⟩
  set E2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
    ((covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hE2
  set E1 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hE1
  set E0 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hE0
  have hE2nn : 0 ≤ E2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 2) x _
  have hE1nn : 0 ≤ E1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hE0nn : 0 ≤ E0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The once-derived section and its compactly-supported packaging.
  set σY : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hY) with hσY
  set CCY : SmoothCcTensor g 0 s :=
    { toSection := σY
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hCCY
  -- Step 1: wrap-transport of the target into the slot-`0` reading of `∇(∇_Y S)`.
  have hYunit : covApply
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      Y (unitEvalSection (I := I) (M := M) g s S) = (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σY y)
        (unitZeroSec (I := I) (M := M) y)) := by
    rw [show unitEvalSection (I := I) (M := M) g s S = (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
          (unitZeroSec (I := I) (M := M) y)) from rfl]
    rw [← covApply_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection Y]
    rfl
  have hwrap : tensor0SAsRS (I := I) (M := M) x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
        (covApply
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          Y (unitEvalSection (I := I) (M := M) g s S))
        x (D x)) =
      (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s CCY).toSection x) (D x) := by
    rw [hYunit]
    rw [tensor0SAsRS_nab_unitEval (I := I) (M := M) g s σY x (D x)]
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 s CCY x]
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hwrap]
  -- Step 2: the inner bound on `rfns(∇(∇_Y S))(x)` by the Parseval split + commutation.
  have hinner : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s CCY).toSection x) ≤
      (∑ b : Fin N, Cb b) * (E2 + E1 + E0) := by
    rw [rfns_eq_sum_parsevalSlice (I := I) (M := M) g s x F hFrepr
      ((covGrad (I := I) (M := M) g 0 s CCY).toSection x)]
    have hper : ∀ b : Fin N,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              (((covGrad (I := I) (M := M) g 0 s CCY).toSection x :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                (unitZeroSec (I := I) (M := M) x))
              (F b x))) ≤ Cb b * (E2 + E1 + E0) := by
      intro b
      -- The slice as the `D`-side of the first-order commutation.
      have hDside : (covGrad (I := I) (M := M) g 0 s CCY).toSection x =
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x) :=
        covGrad_toSection_apply (I := I) (M := M) g 0 s CCY x
      have hcomm := covGrad_covDeriv_leadingSlot_commutation (I := I) (M := M) g s S
        (Y := Y) (Z := F b) hY (hFsm b) x
      -- Rearrange: D-slice = A-slice − curvature + first-order correction.
      have hslice_eq : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (((covGrad (I := I) (M := M) g 0 s CCY).toSection x :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x))
          (F b x) =
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (tensorCov (I := I) g 0 (s + 1)).toFun
                (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
              (unitZeroSec (I := I) (M := M) x)) (F b x) -
          riemannSec
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            Y (F b) (unitEvalSection (I := I) (M := M) g s S) x +
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (unitEvalSection (I := I) (M := M) g s S) x
            ((LeviCivita (I := I) g).toFun Y x (F b x)) := by
        rw [hDside, sub_eq_iff_eq_add.mp hcomm]
        abel
      rw [hslice_eq, tensor0SAsRS_add, tensor0SAsRS_sub]
      -- Bound the three wrapped atoms.
      set wA : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (tensorCov (I := I) g 0 (s + 1)).toFun
              (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
            (unitZeroSec (I := I) (M := M) x)) (F b x)) with hwA
      set wR : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          Y (F b) (unitEvalSection (I := I) (M := M) g s S) x) with hwR
      set wV : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun Y x (F b x))) with hwV
      -- A-slice bound: two slot readings of `∇²S`.
      have hbA : riemannianFiberNormSq (I := I) (M := M) g 0 s x wA ≤
          (n : ℝ) * KFb b * ((n : ℝ) * KY * E2) := by
        rw [hwA]
        have h1 := rfns_currySlice_le (I := I) (M := M) g s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (tensorCov (I := I) g 0 (s + 1)).toFun
              (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
            (unitZeroSec (I := I) (M := M) x)) (F b x)
        refine le_trans h1 ?_
        have hwrapA : tensor0SAsRS (I := I) (M := M) x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (tensorCov (I := I) g 0 (s + 1)).toFun
                (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
              (unitZeroSec (I := I) (M := M) x)) =
            (covGradBundleEquiv (I := I) (M := M) 0 (s + 1) x).symm
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) (Y x) := by
          rw [tensor0SAsRS_rs_unit (I := I) (M := M) (s + 1) x _]
          rw [covGrad_toSection_apply (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) x]
          rw [ContinuousLinearEquiv.symm_apply_apply]
        have h2 : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (tensor0SAsRS (I := I) (M := M) x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (tensorCov (I := I) g 0 (s + 1)).toFun
                  (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
                (unitZeroSec (I := I) (M := M) x))) ≤
            (n : ℝ) * KY * E2 := by
          rw [hwrapA]
          refine le_trans (rfns_symm_reading_le (I := I) (M := M) g (s + 1) x
            ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) (Y x)) ?_
          exact chain_step (Nat.cast_nonneg n) (hKY x) hKY0 (le_refl E2) hE2nn
        exact chain_step (Nat.cast_nonneg n) (hKFb b x) (hKFb0 b) h2
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
      have hbR : riemannianFiberNormSq (I := I) (M := M) g 0 s x wR ≤ KR b * E0 := by
        rw [hwR]; exact hKR b S x
      have hbV : riemannianFiberNormSq (I := I) (M := M) g 0 s x wV ≤
          (n : ℝ) * KD2 b * E1 := by
        rw [hwV]
        refine le_trans (rfns_nabV_le (I := I) (M := M) g s S x
          ((LeviCivita (I := I) g).toFun Y x (F b x))) ?_
        exact chain_step (Nat.cast_nonneg n) (hKD2 b x) (hKD20 b) (le_refl E1) hE1nn
      -- Sub-additive assembly of `wA − wR + wV`.
      have hsub1 : riemannianFiberNormSq (I := I) (M := M) g 0 s x (wA - wR + wV) ≤
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (wA - wR) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x wV :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x (wA - wR) wV
      have hsub2 : riemannianFiberNormSq (I := I) (M := M) g 0 s x (wA - wR) ≤
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x wA +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x wR :=
        riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 s x wA wR
      have hsum_nn : 0 ≤ E2 + E1 + E0 := by linarith
      have hfinal : riemannianFiberNormSq (I := I) (M := M) g 0 s x (wA - wR + wV) ≤
          Cb b * (E2 + E1 + E0) := by
        have hA' : (n : ℝ) * KFb b * ((n : ℝ) * KY * E2) ≤
            ((n : ℝ) * KFb b * ((n : ℝ) * KY)) * (E2 + E1 + E0) := by
          have hc : 0 ≤ (n : ℝ) * KFb b * ((n : ℝ) * KY) :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hKFb0 b))
              (mul_nonneg (Nat.cast_nonneg n) hKY0)
          have h1 : (n : ℝ) * KFb b * ((n : ℝ) * KY * E2) =
              ((n : ℝ) * KFb b * ((n : ℝ) * KY)) * E2 := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_left (by linarith) hc
        have hR' : KR b * E0 ≤ KR b * (E2 + E1 + E0) :=
          mul_le_mul_of_nonneg_left (by linarith) (hKR0 b)
        have hV' : (n : ℝ) * KD2 b * E1 ≤ ((n : ℝ) * KD2 b) * (E2 + E1 + E0) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (Nat.cast_nonneg n) (hKD20 b))
        rw [hCb]
        nlinarith [hbA, hbR, hbV, hsub1, hsub2,
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x wA,
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x wR,
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x wV]
      exact hfinal
    refine le_trans (Finset.sum_le_sum (fun b _ => hper b)) ?_
    rw [← Finset.sum_mul]
  -- Step 3: the outer slot reading.
  refine le_trans (rfns_symm_reading_le (I := I) (M := M) g s x
    ((covGrad (I := I) (M := M) g 0 s CCY).toSection x) (D x)) ?_
  have h := chain_step (Nat.cast_nonneg n) (hKD x) hKD0 hinner
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  refine le_trans h (le_of_eq (by ring))

set_option linter.unusedSectionVars false in
/-- **The Parseval-family trace of the rough Laplacian.** At every point, the rough Laplacian
of a smooth `(0, t)`-tensor section is the fixed-family trace of the second covariant
derivative over the global Parseval frame family. -/
private lemma rawConnLap_eq_parseval_trace (g : SmoothRiemannianMetric I M) (t : ℕ)
    {N : ℕ} (F : Fin N → Π b : M, TangentSpace I b)
    (hFsm : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F a)))
    (hFrepr : ∀ (y : M) (u : TangentSpace I y),
      (∑ a : Fin N, g.inner y (F a y) u • F a y) = u)
    (T : Π b : M, TensorRSSpace 0 t I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y (T y)))
    (y : M) :
    rawTensorConnLap (I := I) g 0 t T y =
      ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 t (F a) (F a) T y := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set e : Fin n → TangentSpace I y := fun j => smoothOrthoFrame (I := I) g y j y with he
  have horth : ∀ i j : Fin n, g.inner y (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j
  set Ψ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 t I y :=
    rawTensorConnLap_psi_bilinAt (I := I) g 0 t T hT y with hΨ
  set B : TangentSpace I y →ₗ[ℝ] TangentSpace I y →ₗ[ℝ] TensorRSSpace 0 t I y :=
    LinearMap.mk₂ ℝ (fun u v => Ψ u v)
      (fun u u' v => by beta_reduce; rw [map_add, ContinuousLinearMap.add_apply])
      (fun c u v => by beta_reduce; rw [map_smul, ContinuousLinearMap.smul_apply])
      (fun u v v' => by beta_reduce; rw [map_add])
      (fun c u v => by beta_reduce; rw [map_smul]) with hB
  have hframe := rawTensorConnLap_eq_frame_trace (I := I) g 0 t T hT y e horth
  have hpars := parseval_family_sum_bilin_eq (I := I) (M := M) g y
    (fun a : Fin N => F a y) (hFrepr y) e horth B
  have hBval : ∀ u v : TangentSpace I y, B u v = Ψ u v := fun u v => rfl
  have hψa : ∀ a : Fin N, Ψ (F a y) (F a y) =
      tensorSecondCovDeriv (I := I) g 0 t (F a) (F a) T y := by
    intro a
    have hFa_at := ((hFsm a) y).mdifferentiableAt (by simp)
    have happly := rawTensorConnLap_psi_bilinAt_apply (I := I) g 0 t T hT
      (X := F a) (Y := F a) hFa_at hFa_at
    rw [hΨ, happly, tensorSecondCovDeriv_def]
  calc rawTensorConnLap (I := I) g 0 t T y
      = ∑ i : Fin n, Ψ (e i) (e i) := hframe
    _ = ∑ i : Fin n, B (e i) (e i) :=
        Finset.sum_congr rfl (fun i _ => (hBval (e i) (e i)).symm)
    _ = ∑ a : Fin N, B (F a y) (F a y) := hpars.symm
    _ = ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 t (F a) (F a) T y := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hBval (F a y) (F a y), hψa a]

set_option linter.unusedSectionVars false in
/-- **The Parseval-family representation of the order-`2` commutator defect.** The section
value of `pointwiseTensorCurv g s S` at `x` is the fixed-family sum of per-direction
third-order differences over the global Parseval frame family. -/
private lemma pointwiseTensorCurv_eq_parseval_sum (g : SmoothRiemannianMetric I M) (s : ℕ)
    {N : ℕ} (F : Fin N → Π b : M, TangentSpace I b)
    (hFsm : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F a)))
    (hFrepr : ∀ (y : M) (u : TangentSpace I y),
      (∑ a : Fin N, g.inner y (F a y) u • F a y) = u)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      ∑ a : Fin N,
        (tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                (fun z : M => S.toSection z) y) x)) := by
  classical
  rw [pointwiseTensorCurv_toSection_eq_sub (I := I) (M := M) g s S x]
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y
        ((covGrad (I := I) (M := M) g 0 s S).toSection y)) :=
    (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
  have hS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  have hAside : (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toSection x =
      ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x := by
    rw [rawTensorConnLapSmooth_toSection_apply]
    exact rawConnLap_eq_parseval_trace (I := I) (M := M) g (s + 1) F hFsm hFrepr
      (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) hT x
  have hDside : (covGrad (I := I) (M := M) g 0 s
      (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x =
      ∑ a : Fin N, covGradBundleEquiv (I := I) (M := M) 0 s x
        ((tensorCov (I := I) g 0 s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
            (fun z : M => S.toSection z) y) x) := by
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
      (rawTensorConnLapSmooth (I := I) g 0 s S) x]
    rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 s S).toSection y) =
        (fun y : M => ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
          (fun z : M => S.toSection z) y) from by
      funext y
      rw [rawTensorConnLapSmooth_toSection_apply]
      exact rawConnLap_eq_parseval_trace (I := I) (M := M) g s F hFsm hFrepr
        (fun z : M => S.toSection z) hS y]
    have hσ : ∀ a : Fin N,
        MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
          (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
            (E := fun z : M => TensorRSSpace 0 s I z) y
            (tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
              (fun z : M => S.toSection z) y)) x :=
      fun a => (tensorSecondCovDeriv_section_contMDiff (I := I) g 0 s hS
        (hFsm a)).mdifferentiable (by norm_num) x
    rw [tensorCov_toFun_finset_sum (I := I) g 0 s Finset.univ
      (fun a (y : M) => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
        (fun z : M => S.toSection z) y) hσ]
    exact map_sum (covGradBundleEquiv (I := I) (M := M) 0 s x) _ _
  rw [hAside, hDside, ← Finset.sum_sub_distrib]

set_option linter.unusedSectionVars false in
/-- **The pure-Riemann genuine trace fibre bound.** `rfns(GcurvSection g s S)(x) ≤ K · rfns(∇S)(x)`
with `K` uniform: the genuine trace is the frame sum of slot-`0` uncurried curvature
contractions of slot-`0` readings of `∇S`, each controlled by the uniform proportional
curvature bound at unit frame directions. -/
private lemma exists_gcurv_bound (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  obtain ⟨Cp, hCp0, hCp⟩ := exists_uniform_riemannOp_proportional (I := I) (M := M) g s
  refine ⟨(n : ℝ) * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * Cp))),
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (Nat.cast_nonneg n) hCp0))),
    fun S x => ?_⟩
  set E1 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hE1
  have hE1nn : 0 ≤ E1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  rw [← remDiffGenuineFib_sum_eq_GcurvSection_toSection (I := I) (M := M) g s S x]
  have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 (s + 1) x
    (Finset.univ : Finset (Fin n))
    (fun i => remDiffGenuineFib (I := I) (M := M) g s S x i)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  refine le_trans hcard ?_
  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (remDiffGenuineFib (I := I) (M := M) g s S x i) ≤ (n : ℝ) * (Cp * ((n : ℝ) * E1)) := by
    intro i
    rw [remDiffGenuineFib]
    refine riemannianFiberNormSq_covGradBundleEquiv_le_card_mul (I := I) (M := M) g s x
      (remDiffGenuineDirCLM (I := I) (M := M) g s S x i) (Cp * ((n : ℝ) * E1))
      (fun v hv => ?_)
    have happ : remDiffGenuineDirCLM (I := I) (M := M) g s S x i v =
        riemannOp (tensorCov (I := I) g 0 s) x
          (smoothOrthoFrame (I := I) g x i x) v
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) := by
      rw [remDiffGenuineDirCLM, LinearMap.coe_toContinuousLinearMap']
      rfl
    rw [happ]
    refine le_trans (hCp x (smoothOrthoFrame (I := I) g x i x) v
      (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
        (fun y : M => S.toSection y) x)) ?_
    have hBi : g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) = 1 := by
      have h := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
      rwa [if_pos rfl] at h
    rw [hBi, hv]
    have hread : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) ≤ (n : ℝ) * E1 := by
      have heq : covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x =
          (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)
            (smoothOrthoFrame (I := I) g x i x) := by
        rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
          ContinuousLinearEquiv.symm_apply_apply]
        rfl
      rw [heq]
      refine le_trans (rfns_symm_reading_le (I := I) (M := M) g s x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)
        (smoothOrthoFrame (I := I) g x i x)) ?_
      rw [hBi]
      rw [mul_one]
    have hone : Cp * 1 * 1 * riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) =
        Cp * riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) := by ring
    rw [hone]
    exact mul_le_mul_of_nonneg_left hread hCp0
  have hsum : (∑ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (remDiffGenuineFib (I := I) (M := M) g s S x i)) ≤
      (n : ℝ) * ((n : ℝ) * (Cp * ((n : ℝ) * E1))) := by
    refine le_trans (Finset.sum_le_sum (fun i _ => hper i)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)) (le_of_eq (by ring))

set_option linter.unusedSectionVars false in
/-- **The per-pair slice bound.** For Parseval-family indices `a, b`, the wrapped slot-`0`
slice at `F b x` of the per-direction third-order difference `A_a − D_a` (the `(F a, F a)`
frame summand of the defect) is uniformly bounded by the three-term jet budget: by the
second-order leading-slot commutation it is the differentiated-curvature atom plus the
curvature-on-gradient atom plus the seven Christoffel-residual atoms, each of fixed-field
shape. -/
private lemma exists_perPair_slice_bound (g : SmoothRiemannianMetric I M) (s : ℕ)
    {N : ℕ} (F : Fin N → Π b : M, TangentSpace I b)
    (hFsm : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F a)))
    (hFrepr : ∀ (y : M) (u : TangentSpace I y),
      (∑ a : Fin N, g.inner y (F a y) u • F a y) = u)
    (Θ : ∀ s' : ℕ, HomTensorRSField (E := E) (M := M) 0 s' (s' + 2) I)
    (hΘ : ∀ (s' : ℕ) (S : SmoothCcTensor g 0 s') (x : M) (u w : TangentSpace I x)
      (m : Fin s' → TangentSpace I x),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
          (appFullSec (I := I) (M := M) g 0 s' (s' + 2) (Θ s') S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s', Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s' I x from
            S.toSection x) (unitZeroSec (I := I) (M := M) x))
        (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))))
    (a b : Fin N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                  (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
                (unitZeroSec (I := I) (M := M) x)) (F b x) -
              tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 s x
                    ((tensorCov (I := I) g 0 s).toFun
                      (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                        (fun z : M => S.toSection z) y) x))
                  (unitZeroSec (I := I) (M := M) x)) (F b x))) ≤
        K * (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (VectorField.mlieBracket I (F a) (F b))) :=
    mlieBracket_contMDiff (I := I) (hFsm a) (hFsm b)
  have hDab : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (F a) (F b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hFsm a) (hFsm b)
  have hDaa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (F a) (F a))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hFsm a) (hFsm a)
  have hDaab : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g) (F a)
        (covApply (LeviCivita (I := I) g) (F a) (F b)))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hFsm a) hDab
  have hDaab2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (covApply (LeviCivita (I := I) g)
        (covApply (LeviCivita (I := I) g) (F a) (F a)) (F b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hDaa (hFsm b)
  obtain ⟨Kθ, hKθ0, hKθ⟩ :=
    exists_thetaAtom_bound (I := I) (M := M) g s Θ hΘ (hFsm a) (hFsm b)
  obtain ⟨KR3, hKR30, hKR3⟩ :=
    exists_riemannGradAtom_bound (I := I) (M := M) g s (hFsm a) (hFsm b) (hFsm a)
  obtain ⟨K1, hK10, hK1⟩ := exists_secondOrderAtom_bound (I := I) (M := M) g s F hFsm hFrepr
    (hFsm a) hbr
  obtain ⟨K2, hK20, hK2⟩ := exists_secondOrderAtom_bound (I := I) (M := M) g s F hFsm hFrepr
    hbr (hFsm a)
  obtain ⟨K3, hK30, hK3⟩ := exists_secondOrderAtom_bound (I := I) (M := M) g s F hFsm hFrepr
    hDab (hFsm a)
  obtain ⟨K4, hK40, hK4⟩ := exists_inner_field_sup (I := I) (M := M) g hDaab
  obtain ⟨K5, hK50, hK5⟩ := exists_secondOrderAtom_bound (I := I) (M := M) g s F hFsm hFrepr
    (hFsm b) hDaa
  obtain ⟨K6, hK60, hK6⟩ := exists_inner_field_sup (I := I) (M := M) g hDaab2
  obtain ⟨K7, hK70, hK7⟩ := exists_secondOrderAtom_bound (I := I) (M := M) g s F hFsm hFrepr
    hDaa (hFsm b)
  have hKnn : 0 ≤ 512 * (Kθ + KR3 + K1 + K2 + K3 + ((n : ℝ) * K4) + K5 +
      ((n : ℝ) * K6) + K7) := by
    have h4 : 0 ≤ (n : ℝ) * K4 := mul_nonneg (Nat.cast_nonneg n) hK40
    have h6 : 0 ≤ (n : ℝ) * K6 := mul_nonneg (Nat.cast_nonneg n) hK60
    linarith
  refine ⟨512 * (Kθ + KR3 + K1 + K2 + K3 + ((n : ℝ) * K4) + K5 + ((n : ℝ) * K6) + K7),
    hKnn, fun S x => ?_⟩
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hnab
  set V := unitEvalSection (I := I) (M := M) g s S with hV
  set E2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
    ((covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hE2
  set E1 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hE1
  set E0 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hE0
  have hE2nn : 0 ≤ E2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 2) x _
  have hE1nn : 0 ≤ E1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hE0nn : 0 ≤ E0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have hsum_nn : 0 ≤ E2 + E1 + E0 := by linarith
  have hcomm := covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S
    (B := F a) (w := F b) (hFsm a) (hFsm b) x
  -- The eleven-atom resolution of the slice.
  have hval : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) (F b x) -
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (F b x) =
      nab.toFun (fun y : M => riemannSec nab (F a) (F b) V y) x (F a x) +
        riemannSec nab (F a) (F b) (covApply nab (F a) V) x +
        (nab.toFun (covApply nab (F a) V) x (VectorField.mlieBracket I (F a) (F b) x) +
          nab.toFun (covApply nab (VectorField.mlieBracket I (F a) (F b)) V) x (F a x) +
          nab.toFun V x ((covApply (LeviCivita (I := I) g) (F a)
            (covApply (LeviCivita (I := I) g) (F a) (F b))) x) +
          nab.toFun V x ((covApply (LeviCivita (I := I) g)
            (covApply (LeviCivita (I := I) g) (F a) (F a)) (F b)) x) +
          nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F a)) V) x
            (F b x) -
          (nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F b)) V) x (F a x) +
            nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F b)) V) x
              (F a x)) -
          nab.toFun (covApply nab (F b) V) x
            ((covApply (LeviCivita (I := I) g) (F a) (F a)) x)) := by
    rw [hcomm]
    rw [nablaTensorCurvSec_def, secondOrderChristoffelResidual_def]
    rw [two_smul, two_smul]
    abel
  rw [hval]
  -- Wrap and name the atoms.
  set T1 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (fun y : M => riemannSec nab (F a) (F b) V y) x (F a x)) with hT1
  set T2 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (riemannSec nab (F a) (F b) (covApply nab (F a) V) x) with hT2
  set T3 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (covApply nab (F a) V) x (VectorField.mlieBracket I (F a) (F b) x)) with hT3
  set T4 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (covApply nab (VectorField.mlieBracket I (F a) (F b)) V) x (F a x)) with hT4
  set T5 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun V x ((covApply (LeviCivita (I := I) g) (F a)
      (covApply (LeviCivita (I := I) g) (F a) (F b))) x)) with hT5
  set T6 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun V x ((covApply (LeviCivita (I := I) g)
      (covApply (LeviCivita (I := I) g) (F a) (F a)) (F b)) x)) with hT6
  set T7 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F a)) V) x
      (F b x)) with hT7
  set T8 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F b)) V) x
      (F a x)) with hT8
  set T9 : TensorRSSpace 0 s I x := tensor0SAsRS (I := I) (M := M) x
    (nab.toFun (covApply nab (F b) V) x
      ((covApply (LeviCivita (I := I) g) (F a) (F a)) x)) with hT9
  have hwrap_eq : tensor0SAsRS (I := I) (M := M) x
      (nab.toFun (fun y : M => riemannSec nab (F a) (F b) V y) x (F a x) +
        riemannSec nab (F a) (F b) (covApply nab (F a) V) x +
        (nab.toFun (covApply nab (F a) V) x (VectorField.mlieBracket I (F a) (F b) x) +
          nab.toFun (covApply nab (VectorField.mlieBracket I (F a) (F b)) V) x (F a x) +
          nab.toFun V x ((covApply (LeviCivita (I := I) g) (F a)
            (covApply (LeviCivita (I := I) g) (F a) (F b))) x) +
          nab.toFun V x ((covApply (LeviCivita (I := I) g)
            (covApply (LeviCivita (I := I) g) (F a) (F a)) (F b)) x) +
          nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F a)) V) x
            (F b x) -
          (nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F b)) V) x (F a x) +
            nab.toFun (covApply nab (covApply (LeviCivita (I := I) g) (F a) (F b)) V) x
              (F a x)) -
          nab.toFun (covApply nab (F b) V) x
            ((covApply (LeviCivita (I := I) g) (F a) (F a)) x))) =
      T1 + T2 + (T3 + T4 + T5 + T6 + T7 - (T8 + T8) - T9) := by
    rw [tensor0SAsRS_add, tensor0SAsRS_add, tensor0SAsRS_sub, tensor0SAsRS_sub,
      tensor0SAsRS_add, tensor0SAsRS_add, tensor0SAsRS_add, tensor0SAsRS_add,
      tensor0SAsRS_add]
  rw [hwrap_eq]
  -- Atom bounds.
  have hb1 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T1 ≤ Kθ * (E2 + E1 + E0) := by
    rw [hT1]
    refine le_trans (hKθ S x) ?_
    have h1 : Kθ * (E1 + E0) ≤ Kθ * (E2 + E1 + E0) :=
      mul_le_mul_of_nonneg_left (by linarith) hKθ0
    exact h1
  have hb2 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T2 ≤ KR3 * (E2 + E1 + E0) := by
    rw [hT2]
    refine le_trans (hKR3 S x) ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hKR30
  have hb3 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T3 ≤ K1 * (E2 + E1 + E0) := by
    rw [hT3]; exact hK1 S x
  have hb4 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T4 ≤ K2 * (E2 + E1 + E0) := by
    rw [hT4]; exact hK2 S x
  have hb5 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T5 ≤
      (n : ℝ) * K4 * (E2 + E1 + E0) := by
    rw [hT5]
    refine le_trans (rfns_nabV_le (I := I) (M := M) g s S x _) ?_
    refine le_trans (chain_step (Nat.cast_nonneg n) (hK4 x) hK40 (le_refl E1) hE1nn) ?_
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (Nat.cast_nonneg n) hK40)
  have hb6 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T6 ≤
      (n : ℝ) * K6 * (E2 + E1 + E0) := by
    rw [hT6]
    refine le_trans (rfns_nabV_le (I := I) (M := M) g s S x _) ?_
    refine le_trans (chain_step (Nat.cast_nonneg n) (hK6 x) hK60 (le_refl E1) hE1nn) ?_
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (Nat.cast_nonneg n) hK60)
  have hb7 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T7 ≤ K7 * (E2 + E1 + E0) := by
    rw [hT7]; exact hK7 S x
  have hb8 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T8 ≤ K3 * (E2 + E1 + E0) := by
    rw [hT8]; exact hK3 S x
  have hb9 : riemannianFiberNormSq (I := I) (M := M) g 0 s x T9 ≤ K5 * (E2 + E1 + E0) := by
    rw [hT9]; exact hK5 S x
  -- Sub-additive assembly.
  have hs1 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x
    (T1 + T2) (T3 + T4 + T5 + T6 + T7 - (T8 + T8) - T9)
  have hs2 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x T1 T2
  have hs3 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 s x
    (T3 + T4 + T5 + T6 + T7 - (T8 + T8)) T9
  have hs4 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 s x
    (T3 + T4 + T5 + T6 + T7) (T8 + T8)
  have hs5 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x
    (T3 + T4 + T5 + T6) T7
  have hs6 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x (T3 + T4 + T5) T6
  have hs7 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x (T3 + T4) T5
  have hs8 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x T3 T4
  have hs9 := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x T8 T8
  nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hsum_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T1,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T2,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T3,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T4,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T5,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T6,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T7,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T8,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T9]

set_option linter.unusedSectionVars false in
/-- **The per-rank frame-summed bracket remainder fibre bound.** At covariant rank `s` there
is a single nonnegative `C₀` with
`rfns(∑ᵢ remDiffBracketFib g s S x i) ≤ C₀ · (rfns(∇²S) + rfns(∇S) + rfns(S))(x)` for every
`S, x`: the frame sum is the defect minus the pure-Riemann trace; the defect is the
Parseval-family trace of per-direction third-order differences, whose family slices are
bounded by the per-pair commutation atoms; the pure-Riemann trace is order `1`. -/
private lemma exists_bracket_bound_at_rank (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          (∑ i : Fin (Module.finrank ℝ E),
            remDiffBracketFib (I := I) (M := M) g s S x i) ≤
        C0 * (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  obtain ⟨N, F, hFsm, hFrepr⟩ := exists_smooth_parseval_frame_family (I := I) (M := M) g
  obtain ⟨Θ, hΘ⟩ := exists_slotFreeCurvOpField_baseSlot_eval (I := I) (M := M) g
  choose Kp hKp0 hKp using (fun p : Fin N × Fin N =>
    exists_perPair_slice_bound (I := I) (M := M) g s F hFsm hFrepr Θ hΘ p.1 p.2)
  obtain ⟨KG, hKG0, hKG⟩ := exists_gcurv_bound (I := I) (M := M) g s
  have hKsum_nn : 0 ≤ ∑ p : Fin N × Fin N, Kp p :=
    Finset.sum_nonneg (fun p _ => hKp0 p)
  refine ⟨2 * ((N : ℝ) * ∑ p : Fin N × Fin N, Kp p) + 2 * KG, by
    have h1 : 0 ≤ (N : ℝ) * ∑ p : Fin N × Fin N, Kp p :=
      mul_nonneg (Nat.cast_nonneg N) hKsum_nn
    linarith, fun S x => ?_⟩
  set E2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
    ((covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hE2
  set E1 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hE1
  set E0 : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hE0
  have hE2nn : 0 ≤ E2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 2) x _
  have hE1nn : 0 ≤ E1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hE0nn : 0 ≤ E0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The identity: the frame-summed bracket remainder is the defect minus the genuine trace.
  have hid : (∑ i : Fin n, remDiffBracketFib (I := I) (M := M) g s S x i) =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (GcurvSection (I := I) (M := M) g s S).toSection x := by
    have hsplit : ∀ i : Fin n, remDiffBracketFib (I := I) (M := M) g s S x i =
        remDiffFib (I := I) (M := M) g s S x i -
          remDiffGenuineFib (I := I) (M := M) g s S x i := fun i => rfl
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib]
    rw [remDiffGenuineFib_sum_eq_GcurvSection_toSection (I := I) (M := M) g s S x]
    congr 1
    rw [pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
    exact Finset.sum_congr rfl (fun i _ => rfl)
  rw [hid]
  -- Replace the defect by its Parseval-family representation.
  rw [pointwiseTensorCurv_eq_parseval_sum (I := I) (M := M) g s F hFsm hFrepr S x]
  -- Two-term sub-additivity.
  set TA : TensorRSSpace 0 (s + 1) I x := ∑ a : Fin N,
    (tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
      covGradBundleEquiv (I := I) (M := M) 0 s x
        ((tensorCov (I := I) g 0 s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
            (fun z : M => S.toSection z) y) x)) with hTA
  have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (s + 1) x TA
    ((GcurvSection (I := I) (M := M) g s S).toSection x)
  -- The Parseval slot-split bound on the defect sum.
  have hTA_bound : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x TA ≤
      ((N : ℝ) * ∑ p : Fin N × Fin N, Kp p) * (E2 + E1 + E0) := by
    rw [rfns_eq_sum_parsevalSlice (I := I) (M := M) g s x F hFrepr TA]
    have hper_b : ∀ b : Fin N,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((TA : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                (unitZeroSec (I := I) (M := M) x))
              (F b x))) ≤
        ((N : ℝ) * ∑ a : Fin N, Kp (a, b)) * (E2 + E1 + E0) := by
      intro b
      have hunit : (TA : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (unitZeroSec (I := I) (M := M) x) =
          ∑ a : Fin N,
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
              (unitZeroSec (I := I) (M := M) x) -
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              covGradBundleEquiv (I := I) (M := M) 0 s x
                ((tensorCov (I := I) g 0 s).toFun
                  (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                    (fun z : M => S.toSection z) y) x))
              (unitZeroSec (I := I) (M := M) x)) := by
        rw [hTA]
        rw [rs_sum_apply (I := I) (M := M) Finset.univ _ (unitZeroSec (I := I) (M := M) x)]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [rs_sub_apply (I := I) (M := M) _ _ (unitZeroSec (I := I) (M := M) x)]
      rw [hunit, map_sum]
      rw [ContinuousLinearMap.sum_apply]
      rw [show (∑ a : Fin N,
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
              (unitZeroSec (I := I) (M := M) x) -
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              covGradBundleEquiv (I := I) (M := M) 0 s x
                ((tensorCov (I := I) g 0 s).toFun
                  (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                    (fun z : M => S.toSection z) y) x))
              (unitZeroSec (I := I) (M := M) x)) (F b x)) =
          ∑ a : Fin N,
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                  (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
                (unitZeroSec (I := I) (M := M) x)) (F b x) -
              tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 s x
                    ((tensorCov (I := I) g 0 s).toFun
                      (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                        (fun z : M => S.toSection z) y) x))
                  (unitZeroSec (I := I) (M := M) x)) (F b x)) from by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [map_sub (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.sub_apply]]
      rw [tensor0SAsRS_sum]
      have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 s x
        (Finset.univ : Finset (Fin N))
        (fun a => tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
              (unitZeroSec (I := I) (M := M) x)) (F b x) -
            tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                covGradBundleEquiv (I := I) (M := M) 0 s x
                  ((tensorCov (I := I) g 0 s).toFun
                    (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                      (fun z : M => S.toSection z) y) x))
                (unitZeroSec (I := I) (M := M) x)) (F b x)))
      rw [Finset.card_univ, Fintype.card_fin] at hcard
      refine le_trans hcard ?_
      have hsum_le : (∑ a : Fin N,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  tensorSecondCovDeriv (I := I) g 0 (s + 1) (F a) (F a)
                    (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
                  (unitZeroSec (I := I) (M := M) x)) (F b x) -
                tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 s x
                      ((tensorCov (I := I) g 0 s).toFun
                        (fun y : M => tensorSecondCovDeriv (I := I) g 0 s (F a) (F a)
                          (fun z : M => S.toSection z) y) x))
                    (unitZeroSec (I := I) (M := M) x)) (F b x)))) ≤
          (∑ a : Fin N, Kp (a, b)) * (E2 + E1 + E0) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun a _ => hKp (a, b) S x)
      refine le_trans (mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg N))
        (le_of_eq (by ring))
    refine le_trans (Finset.sum_le_sum (fun b _ => hper_b b)) ?_
    have hswap : (∑ b : Fin N, ((N : ℝ) * ∑ a : Fin N, Kp (a, b)) * (E2 + E1 + E0)) =
        ((N : ℝ) * ∑ p : Fin N × Fin N, Kp p) * (E2 + E1 + E0) := by
      rw [Fintype.sum_prod_type, ← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    rw [← hswap]
  -- The genuine-trace bound and the final arithmetic.
  have hG_bound : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤ KG * (E2 + E1 + E0) := by
    refine le_trans (hKG S x) ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hKG0
  have hNK_nn : 0 ≤ (N : ℝ) * ∑ p : Fin N × Fin N, Kp p :=
    mul_nonneg (Nat.cast_nonneg N) hKsum_nn
  nlinarith [hsub, hTA_bound, hG_bound,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x TA,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((GcurvSection (I := I) (M := M) g s S).toSection x)]

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
intrinsic frame-summed pointwise frontier of the curvature line, homed here above the moving-frame spine.

**Proof (sorry-free).** The frame sum is the defect minus the pure-Riemann trace (`hid`). The
defect is re-read as the **global Parseval frame family** trace `∑ₐ ∇²_{Wₐ, Wₐ}` of *fixed*
smooth fields (`exists_smooth_parseval_frame_family`, through the bilinear value form
`rawTensorConnLap_psi_bilinAt` and the trace conversion `parseval_family_sum_bilin_eq`), so
every direction in the derivation is a fixed global smooth field with compactness-uniform
`g`-jets — no anchor-frame jet survives. The fibre norm splits over the family slot-`0` slices
(`rfns_eq_sum_parsevalSlice`); each per-pair slice is resolved by the second-order leading-slot
commutation `covGrad_covDeriv_leadingSlot_secondOrder_commutation` into the differentiated
abstract curvature atom, the curvature-on-gradient atom, and seven Christoffel-residual atoms.
The differentiated-curvature atom is bounded `S`-uniformly through the two-free-slot curvature
operator Hom-field `Θ` (`exists_slotFreeCurvOpField_baseSlot_eval`): the curvature field is the
two-slot contraction of `Θ s · S`, its derivative Leibniz-peels
(`abstract_succ_covDeriv_unfold_at_genVal`) onto slices of `∇(Θ s · S)`, and the windowed fibre
bound `exists_appFullSec_iteratedCovGrad_window_bound` gives the order-`≤ 1` envelope. The
curvature atoms use the uniformised proportional bound
(`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` + compactness); the
Christoffel-residual atoms are slices of `∇(∇_Y S)` resolved by the first-order commutation
`covGrad_covDeriv_leadingSlot_commutation` into `∇²S`-slices (consuming the `rfns(∇²S)` budget),
curvature atoms, and first-order corrections; the pure-Riemann trace is order `1`
(`exists_gcurv_bound`).

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
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  refine ⟨fun s => Real.sqrt (exists_bracket_bound_at_rank (I := I) (M := M) g s).choose,
    fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hspec := (exists_bracket_bound_at_rank (I := I) (M := M) g s).choose_spec
  have hsq : Real.sqrt (exists_bracket_bound_at_rank (I := I) (M := M) g s).choose ^ 2 =
      (exists_bracket_bound_at_rank (I := I) (M := M) g s).choose :=
    Real.sq_sqrt hspec.1
  rw [hsq]
  exact hspec.2 S x

end Connection
end Integral
end DifferentialGeometry

end
