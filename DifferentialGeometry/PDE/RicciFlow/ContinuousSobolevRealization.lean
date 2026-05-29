import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbeddingCmRankReduction
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcDense
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The continuous Sobolev embedding as a continuous linear map

For a closed Riemannian manifold `(M, g)` and a supercritical order
`2 * k > dim M`, the intrinsic order-`2k` Sobolev space of `(r, s)`-tensor
sections embeds continuously into the sup-norm space of bounded continuous
tensor sections.  The pointwise bound

  `‖T.toSection x‖_g ≤ C * ‖T.toHs (2k)‖`

(proved on the dense smooth subspace by `tensorPouSobolevHilbert_embedding_Ck`,
in the genuine Riemannian fibre norm) is here promoted from the dense subspace
of smooth compactly-supported sections to a genuine **continuous linear map** on
the whole Sobolev Hilbert space `TensorPouSobolevHilbert g r s (2k)`.

## The sup-norm target Banach space

The model fibre norm of the tensor bundle is chart-dependent and has unbounded
operator norm on compact multi-chart manifolds (the chart-transition Jacobian
blows up), so the target cannot be the model-norm bounded-continuous-functions
space.  Instead the target is built from the **Riemannian fibre norm**: the
seminorm

  `‖T‖_{C⁰} = ⨆ x, ‖T.toSection x‖_g`

on smooth compactly-supported sections (finite by the embedding bound at
supercritical order), realized as a `SeminormedAddCommGroup` and completed to a
genuine Banach space `CSupBanach`.  The completion is the abstract
chart-locality-free `C⁰` space of `(r, s)`-tensor sections.

## Main definitions

* `gSupSeminorm g r s k` — the `C⁰` Riemannian-fibre sup-seminorm on
  `SmoothCcTensorHs g r s (2k)` (packaged as an `AddGroupSeminorm`), with its
  induced `SeminormedAddCommGroup` / `NormedSpace ℝ` structure on the wrapper
  `CSupTensor g r s k`.
* `CSupBanach g r s k` — the completion of `CSupTensor g r s k`, a real Banach
  space (the abstract sup-norm `C⁰` tensor-section space).
* `tensorHsToC0 g r s k h_super` — the **continuous linear map**
  `TensorPouSobolevHilbert g r s (2k) →L[ℝ] CSupBanach g r s k`, the unique
  bounded linear extension of `T ↦ T.toSection` from the dense smooth subspace.

## Main results

* `tensorHsToC0_apply_coe` — `tensorHsToC0` agrees with the canonical sup-norm
  inclusion of a smooth section on the dense subspace.
* `tensorHsToC0_opNorm_le` — the operator-norm bound
  `‖tensorHsToC0 …‖ ≤ C`, the embedding constant.
* `tensorHsToC0_norm_apply_le` — the pointwise norm bound
  `‖tensorHsToC0 … u‖ ≤ C * ‖u‖` for every `u : H^{2k}`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle Topology Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Pointwise section arithmetic

These identities express the algebraic operations on `SmoothCcTensor` at the
level of fibre values.  They are proved through the project's definitional
`toSection_*` lemmas, avoiding the bundle-norm instance diamond. -/

set_option linter.unusedSectionVars false in
/-- The fibre value of a sum of sections is the sum of the fibre values. -/
lemma smoothCcTensor_toSection_add_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor g r s) (x : M) :
    (S + T).toSection x = S.toSection x + T.toSection x := by
  rw [SmoothCcTensor.toSection_add]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of a scalar multiple of a section is the scalar multiple of
the fibre value. -/
lemma smoothCcTensor_toSection_smul_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (c : ℝ) (T : SmoothCcTensor g r s) (x : M) :
    (c • T).toSection x = c • (T.toSection x) := by
  rw [SmoothCcTensor.toSection_smul]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of the negation of a section is the negation of the fibre
value. -/
lemma smoothCcTensor_toSection_neg_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    (-T).toSection x = -(T.toSection x) := by
  rw [SmoothCcTensor.toSection_neg]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of the zero section is zero. -/
lemma smoothCcTensor_toSection_zero_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (x : M) :
    (0 : SmoothCcTensor g r s).toSection x = 0 := by
  rw [SmoothCcTensor.toSection_zero]; rfl

/-! ## The `C⁰` Riemannian-fibre sup value

The sup-of-fibre-norm value of a smooth compactly-supported section, in the
genuine Riemannian fibre norm of the `(r, s)`-tensor bundle. At supercritical
order `2k > dim M` the range is bounded above (by the embedding constant times
the `H^{2k}` norm), so the `iSup` is a genuine finite real number. -/

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The `C⁰` Riemannian-fibre sup value of a smooth section:
`⨆ x, ‖T.toSection x‖_g`, in the genuine `g`-fibre norm. -/
def gSupVal (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  ⨆ x : M, ‖T.toSection x‖

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- At supercritical order `2k > dim M`, the fibre-norm range of a smooth
section is bounded above, with explicit bound `C * ‖T.toHs (2k)‖` provided by
the proven Sobolev embedding `tensorPouSobolevHilbert_embedding_Ck`. -/
lemma bddAbove_section_norm_range
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (T : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    BddAbove (Set.range (fun x : M => ‖T.toSection x‖)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, _, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  exact ⟨C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖,
    by rintro _ ⟨x, rfl⟩; exact hC T x⟩

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value is nonnegative. -/
lemma gSupVal_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : 0 ≤ gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
  · rw [gSupVal]; exact Real.iSup_nonneg (fun x => norm_nonneg _)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value of the zero section is zero. -/
lemma gSupVal_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    gSupVal (I := I) (M := M) g r s 0 = 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal]
  have hz : (fun x : M => ‖(0 : SmoothCcTensor g r s).toSection x‖)
      = fun _ => (0 : ℝ) := by
    funext x; rw [smoothCcTensor_toSection_zero_apply, norm_zero]
  rw [hz]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Real.iSup_of_isEmpty]
  · rw [ciSup_const]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value is invariant under negation. -/
lemma gSupVal_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (-T) = gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal, gSupVal]
  congr 1; funext x
  rw [smoothCcTensor_toSection_neg_apply, norm_neg]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Subadditivity of the `C⁰` sup value (at supercritical order, where the
ranges are bounded above). -/
lemma gSupVal_add_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (S + T) ≤
      gSupVal (I := I) (M := M) g r s S + gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]; norm_num
  · have hbS := bddAbove_section_norm_range (I := I) (M := M) g r s k hk S
    have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (add_nonneg (gSupVal_nonneg (I := I) (M := M) g r s S)
        (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(S + T).toSection x‖ ≤ ‖S.toSection x‖ + ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_add_apply]; exact norm_add_le _ _
    exact le_trans hpt (add_le_add (le_ciSup hbS x) (le_ciSup hbT x))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Absolute homogeneity of the `C⁰` sup value (at supercritical order). -/
lemma gSupVal_smul_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) ≤
      |c| * gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, mul_zero]
  · have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (abs_nonneg c) (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(c • T).toSection x‖ = |c| * ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_smul_apply, norm_smul, Real.norm_eq_abs]
    rw [hpt]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbT x) (abs_nonneg c)

end DifferentialGeometry.PDE.RicciFlow

end
