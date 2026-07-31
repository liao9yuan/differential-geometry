import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCovSumCross
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingUnif
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge

/-!
# Generic-rank jet tower match, and the discharge of brick E4's `Kjet`

Brick **E4** (`Analysis/Sobolev/Embedding/SobolevEmbeddingUnif.lean`) proves the
class-uniform fibre-Morrey bound `fibreMorrey_unif_base` modulo one abstract
input, `hjet`: the cross-metric transfer of covariant jets

`‖∇^{gBase, j} T‖_{L²(gBase)} ≤ Kjet · ∑_{i < w} ‖∇^{g₀, i} T‖_{L²(g₀)}`,
`w = finrank ℝ E / 2 + 2`.

That input could not be discharged inside `Analysis/`, because its producers are
the pointwise cross-metric tower bounds of `UnifCovSumCross.lean`, phrased with
`MetricCovDerivOrderBoundOn` — a predicate of `HCGCompactness/AllTimesBounds.lean`,
downstream of `Analysis/`.  This file is the `HCGCompactness/`-homed discharge.

## The currency mismatch, and the missing lemma

The pointwise producers speak `iterCov`/`covStep` on `Tensor0SField`; the Morrey
chain speaks `iteratedCovGrad` on `SmoothCcTensor`.  The tower match between the
two existed only in a specialized private form (`MetricCovDerivBridge.lean`, rank
`(0,2)`, `metricCcTensor` only).  `iterCovGrad_unit_eq` below is its generic-rank
version, obtained by the same induction on the order.

## Main statements

* `ccUnitField` — the unit-value `Tensor0SField` of a `(0, s)` `SmoothCcTensor`
  (the metric-free smooth core the two formalisms share).
* `iterCovGrad_unit_eq` — **the tower match**: the unit-value of the abstract
  `iteratedCovGrad` tower is the intrinsic `iterCov` tower of `ccUnitField`.
* `rfns0_unit_eq` — the fibre-inner bridge `riemannianFiberNormSq = normSq0S` at
  generic rank `(0, s)`.
* `rfns_iterCovGrad_eq` — the two composed: the Morrey chain's pointwise currency
  written in the cross-metric layer's currency.
* `jetTowerPt`, `sqrtRfns_cross_le` — the pointwise cross-metric jet bound at
  orders `≤ 2`, with a closed constant in `(Λ, Λ', Λ'', finrank ℝ E, s)`.
* `kjetConst`, `jetCross_l2` — its `L²` face, across the two volume measures.
* `kjet_of_class` — E4's `hjet` slot, supplied from `Λ`-class data alone.
* `fibreMorrey_unif_class` — brick E4 with **no** abstract input left: the
  fibre-Morrey bound for every metric of the `Λ`-class, with a constant that is a
  closed function of `(gBase, Λ, Λ', Λ'', dim, s)`.

## Order budget

`iterCovG1_two` (unconditional, `N = 2`) covers orders `≤ 2`, which is the whole
supercritical window at `finrank ℝ E = 3` (`range (3/2 + 2) = range 3`).  So the
lane's only `sorry`, `hAcc_of_jets` (`UnifCovSumN3.lean`), is **not** on this
path.  `kjet_of_class` therefore carries the dimension hypothesis
`finrank ℝ E / 2 + 2 = 3`.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ### The shared smooth core -/

set_option linter.unusedSectionVars false in
/-- **The unit-value tensor field of a `(0, s)` smooth compactly-supported tensor.**

A `SmoothCcTensor g 0 s` is a section of `TensorRSSpace 0 s`, i.e. of
`Tensor0SSpace 0 →L Tensor0SSpace s`; evaluating it at the (parallel) unit
`(0,0)`-tensor produces a genuine `(0, s)`-tensor field.  This is the object the
intrinsic tower `iterCov` consumes, and it does not mention `g`: the same section
gives the same field for every metric, which is what makes the cross-metric
statements below expressible. -/
def ccUnitField (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s :=
  MixedSection.toMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ W.toSection

set_option linter.unusedSectionVars false in
@[simp] lemma ccUnitField_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) :
    ccUnitField (I := I) g s W x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) := rfl

set_option linter.unusedSectionVars false in
/-- **The unit-value field is metric-free.**  Recasting a `SmoothCcTensor` to
another metric (`SmoothCcTensor.recast`, which keeps the underlying section)
leaves its unit-value field unchanged. -/
@[simp] lemma ccUnitField_recast (g g' : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) :
    ccUnitField (I := I) g' s (W.recast (g' := g')) = ccUnitField (I := I) g s W := rfl

/-! ### The tower match -/

/-- **Tower match at generic rank (no arity cast).**

For a smooth compactly-supported `(0, s)`-tensor `W` and every order `j`, the
unit-value of the abstract iterated covariant gradient
`iteratedCovGrad g 0 s j W` (a `(0, s + j)`-tensor section) is the intrinsic
`iterCov` tower of `ccUnitField g s W` at order `j`.  Both sides live at arity
`s + j`, so no arity cast enters.

Generic-rank version of the private `(0,2)`/`metricCcTensor` specialization
`iterCovGrad_unit_eq_iterCov` of `MetricCovDerivBridge.lean`, proved by the same
induction: the successor step reads the `covGrad` unit-value
(`covGrad_apply_unit_eval_genVal`), transports the unit through the directional
covariant derivative (`covDeriv_unit_eval_eq_genVal`), applies the chart↔abstract
agreement `nabla0SFun_eq_tensor0SCovariantDerivative`, and recognises the result
as one `covStep` of `iterCov`.  Only the base case is simpler here: `ccUnitField`
is *defined* as the unit-value, so `j = 0` is `rfl`. -/
theorem iterCovGrad_unit_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (j : ℕ) :
    (fun x : M => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + j) I x from
        (iteratedCovGrad (I := I) g 0 s j W).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
      (fun x : M => iterCov (I := I) g s (ccUnitField (I := I) g s W) j x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    set Tj : SmoothCcTensor g 0 (s + j) := iteratedCovGrad (I := I) g 0 s j W with hTj
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((s + j) + 1) I x from
        (covGrad (I := I) (M := M) g 0 (s + j) Tj).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) g s (ccUnitField (I := I) g s W) (j + 1) x
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (v 0)
    have hcons : v = Fin.cons (v 0) (Matrix.vecTail v) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Matrix.vecTail]
    rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g (s + j) Tj x v]
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 (s + j) Tj x (v 0)]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + j) (Tj.toSection) x (v 0)]
    rw [ih]
    rw [← hXx]
    rw [← nabla0SFun_eq_tensor0SCovariantDerivative (I := I) g (s + j) X
      (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x]
    rw [iterCov_succ, covStep_apply]
    have hcons2 : v = Fin.cons (X x) (Matrix.vecTail v) := by rw [hXx]; exact hcons
    conv_rhs => rw [hcons2]
    rw [show Tensor0SSpace.toModel (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + j) (leviCivitaConnectionOfMetric (I := I) g)
          (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x)
          (Fin.cons (X x) (Matrix.vecTail v)) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + j) (leviCivitaConnectionOfMetric (I := I) g)
          (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x
          (Fin.cons (X x) (Matrix.vecTail v)) from rfl]
    rw [totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + j) (leviCivitaConnectionOfMetric (I := I) g) X
      (iterCov (I := I) g s (ccUnitField (I := I) g s W) j) x (Matrix.vecTail v)]
    rfl

/-! ### The fibre-inner bridge -/

set_option linter.unusedSectionVars false in
/-- **`r = 0` index-lowering is unit-evaluation.**  Replica of the (private)
upstream `lowerAllUpperIndices_zero_apply_unitModel`. -/
private lemma lowerAllUpper0_unit (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

set_option linter.unusedSectionVars false in
/-- **Fibre-inner bridge (`(0, s)`).**  The `g`-Riemannian squared fibre norm of a
smooth `(0, s)`-tensor section — the currency of the fibre-Morrey chain — equals
the intrinsic `normSq0S` of its unit-value, the currency of the cross-metric
comparison layer.  Both sides are expanded in one `g`-orthonormal frame.

Generic-rank canonical form of the two private replicas
`MetricCovDerivBridge.rfns_eq_normSq0S_unit` and
`SobolevEmbeddingUnif.rfns0_eq_normSq0S`; those should be collapsed onto this one
when their files are next touched. -/
theorem rfns0_unit_eq (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (W.toSection x) =
      normSq0S (I := I) g x s (ccUnitField (I := I) g s W x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [component0S_apply]
  rw [show ccUnitField (I := I) g s W x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [lowerAllUpper0_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

/-- **The Morrey chain's pointwise currency, in the cross-metric layer's currency.**

The `g`-fibre squared norm of the `j`-th iterated covariant gradient of a
`(0, s)`-tensor `W` is the `normSq0S` of the `j`-th intrinsic `iterCov` tower of
`ccUnitField g s W`.  This is `rfns0_unit_eq` composed with `iterCovGrad_unit_eq`;
it is the exact bridge that lets `iterCovG1_two` bound a member of the
`iteratedCovGrad` jet sum. -/
theorem rfns_iterCovGrad_eq (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j W).toSection x) =
      normSq0S (I := I) g x (s + j)
        (iterCov (I := I) g s (ccUnitField (I := I) g s W) j x) := by
  have h : ccUnitField (I := I) g (s + j) (iteratedCovGrad (I := I) g 0 s j W) x =
      iterCov (I := I) g s (ccUnitField (I := I) g s W) j x :=
    congrFun (iterCovGrad_unit_eq (I := I) g s W j) x
  rw [rfns0_unit_eq (I := I) g (s + j) x (iteratedCovGrad (I := I) g 0 s j W)]
  exact congrArg (normSq0S (I := I) g x (s + j)) h

/-! ### The closed pointwise constant -/

/-- Nonnegativity of the `D_N` constant tower (local replica of the private
`UnifCovSumCross.Dtower_nonneg`). -/
private theorem dtowerNonneg (n : ℕ) {q : ℝ} (hq : 0 ≤ q) (r : ℕ) {Racc : ℕ → ℝ}
    (hR : ∀ m, 0 ≤ Racc m) (N : ℕ) : 0 ≤ Dtower n q r Racc N := by
  induction N with
  | zero => simp [Dtower]
  | succ N ih =>
      have h1 : 0 ≤ Racc N := hR N
      have h2 : (0 : ℝ) ≤ ((r + N : ℕ) : ℝ) * Real.sqrt ((n : ℝ) ^ (r + N + 1)) * q := by
        positivity
      have h3 : (0 : ℝ) ≤ (((r + N : ℕ) : ℝ) * Real.sqrt ((n : ℝ) ^ (r + N + 1)) * q) *
          Dtower n q r Racc N := mul_nonneg h2 ih
      simp only [Dtower]; linarith

/-- Nonnegativity of the `N = 2` accumulator family of `iterCovG1_two`. -/
private lemma raccTwoNonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n r : ℕ) (m : ℕ) :
    0 ≤ (if m = 1 then
      (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
      else 0) := by
  split
  · have h1 : (0 : ℝ) ≤ Λ'' + Λ * Λ' ^ 2 := add_nonneg hΛ'' (mul_nonneg hΛ (sq_nonneg Λ'))
    have h2 : (0 : ℝ) ≤ 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) := mul_nonneg (by positivity) h1
    have h3 : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
      mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ')
    have h4 : (0 : ℝ) ≤ (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) := by positivity
    exact mul_nonneg h4 (add_nonneg h2 h3)
  · exact le_refl 0

/-- **The closed pointwise cross-metric jet constant at orders `≤ 2`.**

`jetTowerPt n Λ Λ' Λ'' r = √(Λ^{r+2}) · (1 + D₁ + D₂)`, where `D₁`, `D₂` are the
`D_N` constant towers of `iterCovG1_le` / `iterCovG1_two` at `N = 1, 2` (the
`N = 1` accumulator vanishes, the `N = 2` one is the `iterCovG1_two` family), and
the leading `√(Λ^{r+2})` is the fibre-norm change of metric on a `(0, r+j)`
tensor, `j ≤ 2`.

Every factor is an explicit function of the comparability constant `Λ`, the
metric-jet constants `Λ'`, `Λ''`, the dimension `n` and the base valence `r`. -/
def jetTowerPt (n : ℕ) (Λ Λ' Λ'' : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (Λ ^ (r + 2)) *
    (1
      + Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1
      + Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
          (fun m => if m = 1 then
            (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
              (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
            else 0) 2)

lemma jetTowerPt_nonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n r : ℕ) : 0 ≤ jetTowerPt n Λ Λ' Λ'' r := by
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ')
  have hD1 : (0 : ℝ) ≤ Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r (fun _ => 0) 1 :=
    dtowerNonneg n hq r (fun _ => le_refl 0) 1
  have hD2 : (0 : ℝ) ≤ Dtower n ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
      (fun m => if m = 1 then
        (r : ℝ) * Real.sqrt ((n : ℝ) ^ (r + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
        else 0) 2 :=
    dtowerNonneg n hq r (raccTwoNonneg hΛ hΛ' hΛ'' n r) 2
  unfold jetTowerPt
  have := Real.sqrt_nonneg (Λ ^ (r + 2))
  nlinarith

/-! ### The pointwise cross-metric jet bound -/

set_option linter.unusedSectionVars false in
/-- `covStep` of the zero field vanishes (local replica of the private
`UnifCovSumCross.covStep_zero'`). -/
private theorem covStepZero (gRef : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) gRef s 0 = 0 := by
  have h := covStep_add (I := I) gRef s 0 0
  rw [add_zero] at h
  have hc : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0 =
      covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hc

set_option linter.unusedSectionVars false in
/-- The fibre norm of the zero tensor vanishes (local replica of the private
`UnifCovSumCross.sqrt_normSq0S_zero`). -/
private theorem sqrtNormSq0SZero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s (0 : Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_of_orthonormal (I := I) g basis hON)]
  rw [show (∑ slots : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]; simp

/-- **The cross-metric jet tower bound at orders `≤ 2`, in `normSq0S` currency.**

For a smooth `(0, s)`-tensor field `U`, the `g₀`-fibre norm of the `j`-th
`gBase`-covariant derivative of `U` (`j ≤ 2`) is bounded by the `D`-tower constant
times the `g₀`-jet sum of `U` over the whole window `k ≤ 2`.  Assembled from
`iterCovG1_le` at `N = 1` (whose accumulator vanishes) and the unconditional
`iterCovG1_two` at `N = 2`. -/
private theorem towerCross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (s : ℕ)
    (U : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    {j : ℕ} (hj : j ≤ 2) (x : M) :
    Real.sqrt (normSq0S (I := I) g₀ x (s + j) (iterCov (I := I) gBase s U j x)) ≤
      (1
        + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
            (fun _ => 0) 1
        + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
            (fun m => if m = 1 then
              (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                  (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
              else 0) 2) *
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hΛ'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x (Set.mem_univ x))
  have hΛ''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x (Set.mem_univ x))
  have hq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ') :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hΛ'nn)
  have hD1 : (0 : ℝ) ≤ Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s (fun _ => 0) 1 :=
    dtowerNonneg _ hq s (fun _ => le_refl 0) 1
  have hD2 : (0 : ℝ) ≤ Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
      (fun m => if m = 1 then
        (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
        else 0) 2 :=
    dtowerNonneg _ hq s (raccTwoNonneg hΛ0 hΛ'nn hΛ''nn _ s) 2
  have hS3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3,
      Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
    Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _)
  interval_cases j
  · -- order `0`: the two towers agree, and this is the `k = 0` term
    have hterm : Real.sqrt (normSq0S (I := I) g₀ x (s + 0) (iterCov (I := I) gBase s U 0 x)) ≤
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
      Finset.single_le_sum
        (f := fun k => Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s U k x)))
        (fun k _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by norm_num))
    nlinarith
  · -- order `1`: `iterCovG1_le` with a vanishing accumulator
    have hacc : ∀ m, m < 1 →
        Real.sqrt (normSq0S (I := I) g₀ x (s + m + 1)
            (covStep (I := I) g₀ (s + m) (telescAccum (I := I) gBase g₀ s U m) x)) ≤
          (fun _ : ℕ => (0 : ℝ)) m * ∑ k ∈ Finset.range (m + 2),
            Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) := by
      intro m hm
      have hm0 : m = 0 := Nat.lt_one_iff.mp hm
      subst hm0
      rw [show telescAccum (I := I) gBase g₀ s U 0 = 0 from rfl,
        covStepZero (I := I) g₀ (s + 0)]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sqrtNormSq0SZero, zero_mul, le_refl]
    have h1 := iterCovG1_le (I := I) gBase g₀ s U x (fun _ => (0 : ℝ))
      (fun _ => le_refl 0) hEq hjet (Set.mem_univ x) 1 hacc
    have hsubset : Finset.range 2 ⊆ Finset.range 3 := by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    have hsub : ∑ k ∈ Finset.range 2,
        Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) ≤
        ∑ k ∈ Finset.range 3,
          Real.sqrt (normSq0S (I := I) g₀ x (s + k) (iterCov (I := I) g₀ s U k x)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => Real.sqrt_nonneg _)
    nlinarith
  · -- order `2`: the unconditional `iterCovG1_two`
    have h2 := iterCovG1_two (I := I) gBase g₀ s U x hEq hjet hJet1 hJet2 (Set.mem_univ x)
    nlinarith

/-- **The pointwise cross-metric jet bound, in the Morrey chain's currency.**

For a `Λ`-comparable pair with metric-jet bounds `Λ'` (order 1, both directions)
and `Λ''` (order 2), and every `(0, s)` smooth compactly-supported tensor `T` and
order `j ≤ 2`, the `gBase`-fibre norm of `∇^{gBase, j} T` is bounded pointwise by
`jetTowerPt` times the `g₀`-fibre-norm jet sum of `T` over `k ≤ 2`.

This is `towerCross_le` read through the tower match `rfns_iterCovGrad_eq` on both
sides, preceded by the fibre change of metric `covsumCross_fibNorm`. -/
theorem sqrtRfns_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 2) (x : M) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x)) ≤
      jetTowerPt (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
            ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x)) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  -- rewrite both sides into `normSq0S`/`iterCov` currency
  have hL : riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        ((iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))).toSection x) =
      normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x) := by
    rw [rfns_iterCovGrad_eq (I := I) gBase s j (T.recast (g' := gBase)) x,
      ccUnitField_recast (I := I) g₀ gBase s T]
  have hR : ∀ k : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) =
      normSq0S (I := I) g₀ x (s + k)
        (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x) :=
    fun k => rfns_iterCovGrad_eq (I := I) g₀ s k T x
  rw [hL]
  rw [show (∑ k ∈ Finset.range 3,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x))) =
      ∑ k ∈ Finset.range 3,
        Real.sqrt (normSq0S (I := I) g₀ x (s + k)
          (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) from
    Finset.sum_congr rfl (fun k _ => by rw [hR k])]
  -- fibre change of metric, then the tower bound
  have hfib := covsumCross_fibNorm (I := I) g₀ gBase
    (metricUniformEquivalentOn_symm (I := I) hEq) x (s + j)
    (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)
  have htow := towerCross_le (I := I) gBase g₀ hEq hjet hJet1 hJet2 s
    (ccUnitField (I := I) g₀ s T) hj x
  have hle : Λ ^ (s + j) ≤ Λ ^ (s + 2) := by
    refine pow_le_pow_right₀ hEq.1 ?_
    omega
  have hpow : Real.sqrt (Λ ^ (s + j)) ≤ Real.sqrt (Λ ^ (s + 2)) := Real.sqrt_le_sqrt hle
  have hnn : (0 : ℝ) ≤ Real.sqrt (normSq0S (I := I) g₀ x (s + j)
      (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) := Real.sqrt_nonneg _
  unfold jetTowerPt
  calc Real.sqrt (normSq0S (I := I) gBase x (s + j)
        (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x))
      ≤ Real.sqrt (Λ ^ (s + j)) * Real.sqrt (normSq0S (I := I) g₀ x (s + j)
          (iterCov (I := I) gBase s (ccUnitField (I := I) g₀ s T) j x)) := hfib
    _ ≤ Real.sqrt (Λ ^ (s + 2)) *
          ((1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun _ => 0) 1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun m => if m = 1 then
                  (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                      (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
                  else 0) 2) *
            ∑ k ∈ Finset.range 3,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x))) :=
        mul_le_mul hpow htow hnn (Real.sqrt_nonneg _)
    _ = Real.sqrt (Λ ^ (s + 2)) *
          (1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun _ => 0) 1
            + Dtower (Module.finrank ℝ E) ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) s
                (fun m => if m = 1 then
                  (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
                    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
                      (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
                  else 0) 2) *
            ∑ k ∈ Finset.range 3,
              Real.sqrt (normSq0S (I := I) g₀ x (s + k)
                (iterCov (I := I) g₀ s (ccUnitField (I := I) g₀ s T) k x)) := by ring

/-! ### The `L²` face -/

/-- **The closed cross-metric `L²` jet-transfer constant.**

`kjetConst n Λ Λ' Λ'' s = √(3·√(Λⁿ)) · jetTowerPt n Λ Λ' Λ'' s`: the pointwise
constant, times `√3` from one Cauchy–Schwarz over the three-term window and
`√(√(Λⁿ))` from the cross-metric volume comparison `volumeMeasure_cross_le`. -/
def kjetConst (n : ℕ) (Λ Λ' Λ'' : ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (3 * Real.sqrt (Λ ^ n)) * jetTowerPt n Λ Λ' Λ'' s

lemma kjetConst_nonneg {Λ Λ' Λ'' : ℝ} (hΛ : 0 ≤ Λ) (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (n s : ℕ) : 0 ≤ kjetConst n Λ Λ' Λ'' s :=
  mul_nonneg (Real.sqrt_nonneg _) (jetTowerPt_nonneg hΛ hΛ' hΛ'' n s)

/-- **The cross-metric `L²` jet transfer (brick E4's `Kjet`, orders `≤ 2`).**

For `Λ`-comparable `gBase`, `g₀` with metric-jet bounds `Λ'` (order 1) and `Λ''`
(order 2), every `(0, s)` smooth compactly-supported tensor `T` and every order
`j ≤ 2`:

`‖∇^{gBase, j} T‖_{L²(gBase)} ≤ kjetConst · ∑_{k ≤ 2} ‖∇^{g₀, k} T‖_{L²(g₀)}`.

The proof squares the pointwise bound `sqrtRfns_cross_le`, applies Cauchy–Schwarz
over the three-term window, transports the integral from `dV_{gBase}` to
`dV_{g₀}` through `volumeMeasure_cross_le`, and finally absorbs
`∑ ‖·‖² ≤ (∑ ‖·‖)²`. -/
theorem jetCross_l2
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) {j : ℕ} (hj : j ≤ 2) :
    ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ≤
      kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  set P : ℝ := jetTowerPt (Module.finrank ℝ E) Λ Λ' Λ'' s with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact jetTowerPt_nonneg hΛ0 hΛ' hΛ'' _ s
  set c : ℝ := Real.sqrt (Λ ^ Module.finrank ℝ E) with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; exact Real.sqrt_nonneg _
  set μB := riemannianVolumeMeasure (I := I) (M := M) gBase with hμB
  set μ0 := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ0
  set A : SmoothCcTensor gBase 0 (s + j) :=
    iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase)) with hA
  set b : ℕ → ℝ := fun k => ‖iteratedCovGrad (I := I) g₀ 0 s k T‖ with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  set R : ℕ → M → ℝ := fun k x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + k) x
    ((iteratedCovGrad (I := I) g₀ 0 s k T).toSection x) with hR
  have hRnn : ∀ k x, 0 ≤ R k x := fun k x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + k) x _
  set F : M → ℝ := fun x => 3 * P ^ 2 * ∑ k ∈ Finset.range 3, R k x with hF
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    have : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3, R k x :=
      Finset.sum_nonneg (fun k _ => hRnn k x)
    have h2 : (0 : ℝ) ≤ 3 * P ^ 2 := by positivity
    exact mul_nonneg h2 this
  -- pointwise squared bound
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ≤ F x := by
    intro x
    have h := sqrtRfns_cross_le (I := I) gBase g₀ hEq hjet hJet1 hJet2 s T hj x
    have hLnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x
        (A.toSection x) := riemannianFiberNormSq_nonneg (I := I) (M := M) gBase 0 (s + j) x _
    have hcs : (∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 ≤
        3 * ∑ k ∈ Finset.range 3, R k x := by
      have hch := sq_sum_le_card_mul_sum_sq (s := Finset.range 3)
        (f := fun k => Real.sqrt (R k x))
      rw [Finset.card_range] at hch
      have hsq : ∑ k ∈ Finset.range 3, Real.sqrt (R k x) ^ 2 =
          ∑ k ∈ Finset.range 3, R k x :=
        Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hRnn k x))
      rw [hsq] at hch
      exact_mod_cast hch
    have hsq2 : riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ≤
        (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [Real.sq_sqrt hLnn] at this
    have hstep : (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 ≤ F x := by
      have hmul := mul_le_mul_of_nonneg_left hcs (sq_nonneg P)
      calc (P * ∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2
          = P ^ 2 * (∑ k ∈ Finset.range 3, Real.sqrt (R k x)) ^ 2 := by ring
        _ ≤ P ^ 2 * (3 * ∑ k ∈ Finset.range 3, R k x) := hmul
        _ = F x := by rw [hF]; ring
    exact le_trans hsq2 hstep
  -- integrability
  have hIntA : Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x)) μB :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) gBase 0 (s + j) A
  have hIntR : ∀ k, Integrable (R k) μ0 := fun k =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + k) _
  have hIntF0 : Integrable F μ0 := by
    rw [hF]
    exact (integrable_finset_sum (Finset.range 3) (fun k _ => hIntR k)).const_mul (3 * P ^ 2)
  have hmeasle : μB ≤ ENNReal.ofReal c • μ0 := (volumeMeasure_cross_le (I := I) gBase g₀ hEq).2
  have hIntFs : Integrable F (ENNReal.ofReal c • μ0) :=
    hIntF0.smul_measure ENNReal.ofReal_ne_top
  have hIntFB : Integrable F μB := hIntFs.mono_measure hmeasle
  -- the integral chain
  have hnormA : ‖A‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ∂μB := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) A, hμB]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M)
      gBase (s + j) A
  have hnormB : ∀ k, b k ^ 2 = ∫ x, R k x ∂μ0 := by
    intro k
    rw [hb, hR, hμ0]
    simp only
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 s k T)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M)
      g₀ (s + k) (iteratedCovGrad (I := I) g₀ 0 s k T)
  have hIF0 : ∫ x, F x ∂μ0 = 3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2 := by
    rw [hF]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finset_sum (Finset.range 3) (fun k _ => hIntR k)]
    exact (Finset.sum_congr rfl (fun k _ => (hnormB k))).symm
  have hchain : ‖A‖ ^ 2 ≤ c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) := by
    rw [hnormA]
    calc ∫ x, riemannianFiberNormSq (I := I) (M := M) gBase 0 (s + j) x (A.toSection x) ∂μB
        ≤ ∫ x, F x ∂μB := MeasureTheory.integral_mono hIntA hIntFB hpt
      _ ≤ ∫ x, F x ∂(ENNReal.ofReal c • μ0) :=
          MeasureTheory.integral_mono_measure hmeasle
            (Filter.Eventually.of_forall hFnn) hIntFs
      _ = c * ∫ x, F x ∂μ0 := by
          rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hcnn, smul_eq_mul]
      _ = c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) := by rw [hIF0]
  -- absorb `∑ b² ≤ (∑ b)²` and take square roots
  have hsumsq : ∑ k ∈ Finset.range 3, b k ^ 2 ≤ (∑ k ∈ Finset.range 3, b k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => hbnn k)
  have hSnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range 3, b k := Finset.sum_nonneg (fun k _ => hbnn k)
  have hfinal : ‖A‖ ^ 2 ≤
      (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s * ∑ k ∈ Finset.range 3, b k) ^ 2 := by
    have hexp : (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ k ∈ Finset.range 3, b k) ^ 2 =
          3 * c * P ^ 2 * (∑ k ∈ Finset.range 3, b k) ^ 2 := by
      rw [kjetConst, ← hPdef, ← hcdef, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3 * c)]
    rw [hexp]
    have hstep : c * (3 * P ^ 2 * ∑ k ∈ Finset.range 3, b k ^ 2) ≤
        3 * c * P ^ 2 * (∑ k ∈ Finset.range 3, b k) ^ 2 := by
      have h1 : (0 : ℝ) ≤ 3 * P ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsumsq h1]
    exact le_trans hchain hstep
  have hKnn : (0 : ℝ) ≤ kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
      ∑ k ∈ Finset.range 3, b k :=
    mul_nonneg (kjetConst_nonneg hΛ0 hΛ' hΛ'' _ s) hSnn
  have := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hKnn] at this

/-! ### Discharging brick E4 -/

/-- **Brick E4's `Kjet`, supplied from `Λ`-class data.**

At `finrank ℝ E / 2 + 2 = 3` (in particular `dim = 3`) the supercritical window
is `{0, 1, 2}`, so the unconditional order-`≤ 2` transfer `jetCross_l2` covers it
exactly.  This is literally the `hjet` slot of `fibreMorrey_unif_base`. -/
theorem kjet_of_class
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (hdim : Module.finrank ℝ E / 2 + 2 = 3)
    (s : ℕ) (S : SmoothCcTensor g₀ 0 s)
    (j : ℕ) (hj : j ∈ Finset.range (Module.finrank ℝ E / 2 + 2)) :
    ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
      kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s *
        ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s i S‖ := by
  rw [hdim] at hj ⊢
  have hj2 : j ≤ 2 := by
    have := Finset.mem_range.mp hj
    omega
  exact jetCross_l2 (I := I) gBase g₀ hEq hjet hJet1 hJet2 hΛ' hΛ'' s S hj2

/-- **Brick E4, with no abstract input left.**

Every metric `g₀` that is `Λ`-comparable to the fixed background `gBase`, with
`gBase`↔`g₀` metric jets bounded by `Λ'` (order 1) and `Λ''` (order 2), satisfies
the fibre-Morrey / Sobolev-embedding bound with the single closed constant

`morreyUnifConst Λ (baseMorreyConst gBase 0 s) (kjetConst dim Λ Λ' Λ'' s) dim s`,

a function of the fixed background, the class data `(Λ, Λ', Λ'')`, the dimension
and the valence only — never of the individual `g₀`.  This is
`fibreMorrey_unif_base` with its `hjet` slot discharged by `kjet_of_class`. -/
theorem fibreMorrey_unif_class
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ Λ'')
    (hΛ' : 0 ≤ Λ') (hΛ'' : 0 ≤ Λ'')
    (hdim : Module.finrank ℝ E / 2 + 2 = 3)
    (s : ℕ) (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUnifConst Λ (baseMorreyConst (I := I) (M := M) gBase 0 s)
          (kjetConst (Module.finrank ℝ E) Λ Λ' Λ'' s) (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 :=
  fibreMorrey_unif_base (I := I) gBase g₀ hEq.1
    (fun y v => hEq.2 y (Set.mem_univ y) v) s
    (fun S j hj =>
      kjet_of_class (I := I) gBase g₀ hEq hjet hJet1 hJet2 hΛ' hΛ'' hdim s S j hj) T x

end RicciFlow
end PDE
end DifferentialGeometry

end
