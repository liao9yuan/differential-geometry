import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetBound

/-!
# Parametric operator-field jet bounds

This file converts compact-slab pointwise bounds for a jointly smooth
operator-field family into one time-uniform `L²` jet window for its action.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Pointwise squared coefficient-jet bounds give the corresponding squared
`L²` bound for one covariant derivative of a tensor action. -/
theorem app_jet_sq_le
    (g : SmoothRiemannianMetric I M) (b c j : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b) (B : ℕ → ℝ)
    (hB : ∀ i, i ≤ j → 0 ≤ B i)
    (hΦ : ∀ i, i ≤ j → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) :
    ‖iteratedCovGrad (I := I) g 0 c j
        (appCc (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1), B i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  set F : M → ℝ := fun x => appCcGdiag (E := E) j *
    ∑ i ∈ Finset.range (j + 1), B i *
      ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
          ((iteratedCovGrad (I := I) g 0 b l W).toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F μ := by
    rw [hF_def]
    exact (MeasureTheory.integrable_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (B i))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + j) x
          ((iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c Φ W)).toSection x) ≤ F x := by
    intro x
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le
        (I := I) (M := M) g b c Φ W j x) ?_
    rw [hF_def]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact mul_le_mul (hΦ i hij x) le_rfl
      (Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + l) x _))
      (hB i hij)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + j)
    (iteratedCovGrad (I := I) g 0 c j
      (appCc (I := I) (M := M) g b c Φ W)) F hF_int hpt
  refine le_trans hnorm (le_of_eq ?_)
  rw [hF_def, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (B i))]
  apply congrArg (fun z : ℝ => appCcGdiag (E := E) j * z)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
        (iteratedCovGrad (I := I) g 0 b l W))]
  apply congrArg (fun z : ℝ => B i * z)
  exact Finset.sum_congr rfl (fun l _ => by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (b + l)])

/-- **The head/tail `L²` Leibniz assembly of `appCc`: one Hölder side per
Leibniz index.**

`app_jet_sq_le` puts the coefficient in `L^∞` at *every* Leibniz index.  This
sibling makes the opposite choice from index `1` on: index `0` keeps the
coefficient in `L^∞` (one pointwise cap `B` on `Φ` itself) with the whole data
window in `L²`, while every index `i ≥ 1` puts the *data window* `l ≤ j - i` in
`L^∞` (its own cap `D i`) and reads the coefficient jet `∇ⁱΦ` in `L²`:

`‖∇ʲ(appCc Φ W)‖² ≤ appCcGdiag j · (B · ∑_{l ≤ j} ‖∇ˡW‖²
    + ∑_{1 ≤ i ≤ j} D i · ‖∇ⁱΦ‖²)`.

This is the shape needed when the coefficient's *top* jets are expensive in
`L^∞` — a coefficient whose `L²` tower already spends the state's own jets, so
that the extra `+2` orders of the fibre Sobolev embedding would overshoot the
budget — while the data is a low-order object whose sup norm is affordable.
The constant is fixed before every argument and no Sobolev ball occurs. -/
theorem app_jet_sq_head
    (g : SmoothRiemannianMetric I M) (b c j : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b) (B : ℝ) (D : ℕ → ℝ)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) ≤ B)
    (hW : ∀ i, 1 ≤ i → ∀ x : M,
      ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
            ((iteratedCovGrad (I := I) g 0 b l W).toSection x) ≤ D i) :
    ‖iteratedCovGrad (I := I) g 0 c j
        (appCc (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
      appCcGdiag (E := E) j *
        (B * ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2 +
          ∑ i ∈ Finset.Icc 1 j, D i *
            ‖iteratedCovGrad (I := I) g b c i Φ‖ ^ 2) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hWint : ∀ l : ℕ, MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
        ((iteratedCovGrad (I := I) g 0 b l W).toSection x)) μ := fun l =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
      (iteratedCovGrad (I := I) g 0 b l W)
  have hCint : ∀ i : ℕ, MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i Φ).toSection x)) μ := fun i =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g b (c + i)
      (iteratedCovGrad (I := I) g b c i Φ)
  set F : M → ℝ := fun x => appCcGdiag (E := E) j *
    (B * ∑ l ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
          ((iteratedCovGrad (I := I) g 0 b l W).toSection x) +
      ∑ i ∈ Finset.Icc 1 j, D i *
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x)) with hF_def
  have hF_int : MeasureTheory.Integrable F μ := by
    rw [hF_def]
    exact (((MeasureTheory.integrable_finset_sum (Finset.range (j + 1))
        (fun l _ => hWint l)).const_mul B).add
      (MeasureTheory.integrable_finset_sum (Finset.Icc 1 j)
        (fun i _ => (hCint i).const_mul (D i)))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + j) x
          ((iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c Φ W)).toSection x) ≤ F x := by
    intro x
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le
        (I := I) (M := M) g b c Φ W j x) ?_
    rw [hF_def]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
    have hsplit : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 j := by simp
    conv_lhs => rw [hsplit]
    rw [Finset.sum_insert hnotmem]
    refine add_le_add ?_ (Finset.sum_le_sum (fun i hi => ?_))
    · simp only [iteratedCovGrad_zero, Nat.add_zero, Nat.sub_zero]
      exact mul_le_mul_of_nonneg_right (hΦ x)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + l) x _))
    · rw [Finset.mem_Icc] at hi
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hW i hi.1 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + i) x _)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + j)
    (iteratedCovGrad (I := I) g 0 c j
      (appCc (I := I) (M := M) g b c Φ W)) F hF_int hpt
  refine le_trans hnorm (le_of_eq ?_)
  rw [hF_def, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add
      ((MeasureTheory.integrable_finset_sum (Finset.range (j + 1))
        (fun l _ => hWint l)).const_mul B)
      (MeasureTheory.integrable_finset_sum (Finset.Icc 1 j)
        (fun i _ => (hCint i).const_mul (D i)))]
  apply congrArg (fun z : ℝ => appCcGdiag (E := E) j * z)
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum (Finset.range (j + 1))
        (fun l _ => hWint l)]
    apply congrArg (fun z : ℝ => B * z)
    exact Finset.sum_congr rfl (fun l _ => by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
          (I := I) (M := M) g 0 (b + l)])
  · rw [MeasureTheory.integral_finset_sum (Finset.Icc 1 j)
      (fun i _ => (hCint i).const_mul (D i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul]
    apply congrArg (fun z : ℝ => D i * z)
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g b (c + i)]

/-- **The mixed per-index Hölder split of the `appCc` Leibniz sum.**

`app_jet_sq_le` puts the coefficient in `L^∞` at *every* Leibniz index and
`app_jet_sq_head` does so at index `0` only; this engine takes the choice as a
parameter.  At the indices `i ∈ S` the coefficient jet `∇ⁱΦ` is capped
pointwise (`B i`) and its companion data window `l ≤ j - i` is read in `L²`; at
the indices `i ∉ S` the roles are exchanged — the data window is capped
pointwise (`D i`) and `∇ⁱΦ` is read in `L²`:

`‖∇ʲ(appCc Φ W)‖² ≤ appCcGdiag j · (∑_{i ∈ S} B i · ∑_{l ≤ j-i} ‖∇ˡW‖²`
  `+ ∑_{i ∈ range (j+1) \ S} D i · ‖∇ⁱΦ‖²)`.

`S = range (j+1)` is `app_jet_sq_le` and `S = {0}` is `app_jet_sq_head`.  The
intended use is a threshold `S = range j`: a coefficient sup costs the fibre
Sobolev embedding's `+2` orders on top of the coefficient's own tower index, so
it stays inside an order budget exactly while that tower index is below the top
one, and the last Leibniz index is priced from the data side instead.  The
constant is fixed before every argument and no Sobolev ball occurs. -/
theorem app_jet_sq_split
    (g : SmoothRiemannianMetric I M) (b c j : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (j + 1)) (B D : ℕ → ℝ)
    (hΦ : ∀ i ∈ S, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i)
    (hW : ∀ i ∈ Finset.range (j + 1) \ S, ∀ x : M,
      ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
            ((iteratedCovGrad (I := I) g 0 b l W).toSection x) ≤ D i) :
    ‖iteratedCovGrad (I := I) g 0 c j
        (appCc (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
      appCcGdiag (E := E) j *
        (∑ i ∈ S, B i * ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2 +
          ∑ i ∈ Finset.range (j + 1) \ S, D i *
            ‖iteratedCovGrad (I := I) g b c i Φ‖ ^ 2) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hWint : ∀ l : ℕ, MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
        ((iteratedCovGrad (I := I) g 0 b l W).toSection x)) μ := fun l =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
      (iteratedCovGrad (I := I) g 0 b l W)
  have hCint : ∀ i : ℕ, MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i Φ).toSection x)) μ := fun i =>
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g b (c + i)
      (iteratedCovGrad (I := I) g b c i Φ)
  set F : M → ℝ := fun x => appCcGdiag (E := E) j *
    (∑ i ∈ S, B i * ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
          ((iteratedCovGrad (I := I) g 0 b l W).toSection x) +
      ∑ i ∈ Finset.range (j + 1) \ S, D i *
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x)) with hF_def
  have hF_int : MeasureTheory.Integrable F μ := by
    rw [hF_def]
    exact ((MeasureTheory.integrable_finset_sum S (fun i _ =>
        (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i))
          (fun l _ => hWint l)).const_mul (B i))).add
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1) \ S)
        (fun i _ => (hCint i).const_mul (D i)))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + j) x
          ((iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c Φ W)).toSection x) ≤ F x := by
    intro x
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le
        (I := I) (M := M) g b c Φ W j x) ?_
    rw [hF_def]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
    rw [← Finset.sum_sdiff hS]
    have hdiff : (∑ i ∈ Finset.range (j + 1) \ S,
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
            ((iteratedCovGrad (I := I) g b c i Φ).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
              ((iteratedCovGrad (I := I) g 0 b l W).toSection x)) ≤
        ∑ i ∈ Finset.range (j + 1) \ S, D i *
          riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
            ((iteratedCovGrad (I := I) g b c i Φ).toSection x) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [mul_comm (D i)]
      exact mul_le_mul_of_nonneg_left (hW i hi x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + i) x _)
    have hin : (∑ i ∈ S,
        riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
            ((iteratedCovGrad (I := I) g b c i Φ).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
              ((iteratedCovGrad (I := I) g 0 b l W).toSection x)) ≤
        ∑ i ∈ S, B i * ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
            ((iteratedCovGrad (I := I) g 0 b l W).toSection x) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      exact mul_le_mul_of_nonneg_right (hΦ i hi x)
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + l) x _))
    linarith only [hdiff, hin]
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + j)
    (iteratedCovGrad (I := I) g 0 c j
      (appCc (I := I) (M := M) g b c Φ W)) F hF_int hpt
  refine le_trans hnorm (le_of_eq ?_)
  rw [hF_def, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add
      (MeasureTheory.integrable_finset_sum S (fun i _ =>
        (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i))
          (fun l _ => hWint l)).const_mul (B i)))
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1) \ S)
        (fun i _ => (hCint i).const_mul (D i)))]
  apply congrArg (fun z : ℝ => appCcGdiag (E := E) j * z)
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [MeasureTheory.integral_finset_sum S (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i))
        (fun l _ => hWint l)).const_mul (B i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum (Finset.range (j + 1 - i))
        (fun l _ => hWint l)]
    apply congrArg (fun z : ℝ => B i * z)
    exact Finset.sum_congr rfl (fun l _ => by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
          (I := I) (M := M) g 0 (b + l)])
  · rw [MeasureTheory.integral_finset_sum (Finset.range (j + 1) \ S)
      (fun i _ => (hCint i).const_mul (D i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul]
    apply congrArg (fun z : ℝ => D i * z)
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g b (c + i)]

/-- A common pointwise coefficient-jet envelope gives one `L²` action-jet
window for an arbitrary parameter family. -/
theorem app_jet_of_bdd
    (g : SmoothRiemannianMetric I M) (b c : ℕ) {α : Type*}
    (Φ : α → SmoothCcTensor g b c) (K : Set α) (B : ℕ → ℝ)
    (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ K → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i (Φ t)).toSection x) ≤ B i) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t, t ∈ K → ∀ (W : SmoothCcTensor g 0 b) (j : ℕ),
        ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c (Φ t) W)‖ ≤
          C j * ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ := by
  classical
  let C : ℕ → ℝ := fun j =>
    appCcGdiag (E := E) j * (∑ i ∈ Finset.range (j + 1), B i) + 1
  refine ⟨C, fun j => ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (appCcGdiag_nonneg (E := E) j)
        (Finset.sum_nonneg fun i _ => hB_nn i)) zero_le_one
  · intro t ht W j
    have hsq := app_jet_sq_le (I := I) (M := M) g b c j (Φ t) W B
      (fun i _ => hB_nn i) (fun i _ x => hB i t ht x)
    set J : ℝ := ∑ l ∈ Finset.range (j + 1),
      ‖iteratedCovGrad (I := I) g 0 b l W‖ with hJ_def
    set A : ℝ := appCcGdiag (E := E) j *
      (∑ i ∈ Finset.range (j + 1), B i) with hA_def
    have hJ_nn : 0 ≤ J := by
      rw [hJ_def]
      exact Finset.sum_nonneg fun l _ => norm_nonneg _
    have hA_nn : 0 ≤ A := by
      rw [hA_def]
      exact mul_nonneg (appCcGdiag_nonneg (E := E) j)
        (Finset.sum_nonneg fun i _ => hB_nn i)
    have hinner : ∀ i ∈ Finset.range (j + 1),
        (∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ J ^ 2 := by
      intro i hi
      let Jsmall : ℝ := ∑ l ∈ Finset.range (j + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 b l W‖
      have hJsmall_nn : 0 ≤ Jsmall := by
        exact Finset.sum_nonneg fun l _ => norm_nonneg _
      have hsmall : Jsmall ≤ J := by
        rw [hJ_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.sub_le (j + 1) i))
          (fun l _ _ => norm_nonneg _)
      have hsquares : (∑ l ∈ Finset.range (j + 1 - i),
          ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ Jsmall ^ 2 := by
        exact Finset.sum_sq_le_sq_sum_of_nonneg
          (fun l _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 b l W))
      exact hsquares.trans (by nlinarith)
    have hgrid :
        (∑ i ∈ Finset.range (j + 1), B i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤
          (∑ i ∈ Finset.range (j + 1), B i) * J ^ 2 := by
      calc
        (∑ i ∈ Finset.range (j + 1), B i *
            ∑ l ∈ Finset.range (j + 1 - i),
              ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤
            ∑ i ∈ Finset.range (j + 1), B i * J ^ 2 := by
              exact Finset.sum_le_sum fun i hi =>
                mul_le_mul_of_nonneg_left (hinner i hi) (hB_nn i)
        _ = (∑ i ∈ Finset.range (j + 1), B i) * J ^ 2 := by
          rw [Finset.sum_mul]
    have hsqA :
        ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c (Φ t) W)‖ ^ 2 ≤
          A * J ^ 2 := by
      refine hsq.trans ?_
      rw [hA_def]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hgrid
          (appCcGdiag_nonneg (E := E) j))
    have hA_le : A ≤ (A + 1) ^ 2 := by
      nlinarith [sq_nonneg A]
    have htarget :
        ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c (Φ t) W)‖ ^ 2 ≤
          ((A + 1) * J) ^ 2 := by
      calc
        _ ≤ A * J ^ 2 := hsqA
        _ ≤ (A + 1) ^ 2 * J ^ 2 :=
          mul_le_mul_of_nonneg_right hA_le (sq_nonneg J)
        _ = ((A + 1) * J) ^ 2 := by ring
    change ‖iteratedCovGrad (I := I) g 0 c j
        (appCc (I := I) (M := M) g b c (Φ t) W)‖ ≤ (A + 1) * J
    exact le_of_sq_le_sq htarget (mul_nonneg (add_nonneg hA_nn zero_le_one) hJ_nn)

/-- A jointly smooth family of operator fields has one `L²` action-jet
window on a compact time slab.  The window may depend on the jet order, but
not on time in the slab or on the input tensor. -/
theorem param_app_jet
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun z : M => TensorRSSpace b c I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t, t ∈ K → ∀ (W : SmoothCcTensor g 0 b) (j : ℕ),
        ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g b c (Φ t) W)‖ ≤
          C j * ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ := by
  obtain ⟨B, hB_nn, hB⟩ :=
    joint_jet_bdd (I := I) (M := M) g b c Φ hK hKS hjoint
  exact app_jet_of_bdd (I := I) (M := M) g b c Φ K B hB_nn hB

end Connection
end Integral
end DifferentialGeometry

end
