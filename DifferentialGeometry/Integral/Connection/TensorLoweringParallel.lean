import DifferentialGeometry.Integral.Connection.TensorRSMetricCompatible
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement

/-!
# The metric index-lowering map and the Levi-Civita tensor connections

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, the metric induces, on every mixed `(r, s)`-tensor fibre, the index-lowering
map `lowerAllUpperIndices g r s x` that turns an `(r, s)`-tensor into a covariant
`(0, r + s)`-tensor by contracting each of the `r` upper slots against `g(x)`.

This file develops foundational structure of that index-lowering map that feeds
into the statement that the Levi-Civita-induced tensor connections are
intertwined by index lowering: the metric used to lower indices is itself
`∇`-parallel (`∇g = 0`), hence `∇` commutes with index lowering.

## The index-lowering map as a fibrewise linear equivalence

A non-degenerate metric lowers indices *reversibly*: `lowerAllUpperIndices g r s x`
is injective (`lowerAllUpperIndices_injective`), and its source `TensorRSModel r s ℝ E`
and target `Tensor0SModel (r + s) ℝ E` are finite-dimensional of the *same*
dimension `(finrank ℝ E) ^ (r + s)`. Hence the lowering map is bijective and, being
continuous-linear between finite-dimensional spaces, a continuous linear
equivalence `lowerAllUpperIndicesEquiv g r s x`.

Packaging the lowering map as an equivalence is the natural foundation for the
parallel-transport statement: the equivalence intertwines
`tensorRSCovariantDerivative I M r s (LeviCivita g)` with
`tensor0SCovariantDerivative I M (r + s) (LeviCivita g)`, equivalently the lifted
section `liftedTensorSection g r s S` has covariant derivative
`loweredCovDerivAt g r s S` equal to the lowering of the genuine
`(r, s)`-covariant derivative of `S`.

## The empty contraction at rank `0`

At `r = 0` the index-lowering map contracts *no* upper slots: the separable
`(0, 0)`-form `separableFormAt g x 0` is the metric-independent unit
`(0, 0)`-tensor `constOfIsEmpty 1` (`separableFormAt_zero`). Consequently the
rank-`0` lowering map carries no metric content — it is the canonical
`(0, 0)`-currying isomorphism `Hom(ℝ, T⁰ₛ) ≅ T⁰ₛ` followed by the slot-relabelling
`Fin s ≃ Fin (0 + s)`.

## Main results

* `separableFormAt_zero` — the rank-`0` separable form is the unit `(0, 0)`-tensor
  `constOfIsEmpty 1`, independent of the metric and the base point.
* `lowerAllUpperIndices_bijective` — the index-lowering map is bijective.
* `lowerAllUpperIndicesEquiv` — the index-lowering map as a continuous linear
  equivalence `TensorRSModel r s ℝ E ≃L[ℝ] Tensor0SModel (r + s) ℝ E`.
* `lowerAllUpperIndicesEquiv_apply`, `lowerAllUpperIndicesEquiv_symm_apply_apply`,
  `lowerAllUpperIndicesEquiv_apply_symm_apply` — its computation / round-trip
  lemmas.
* `lowerAllUpperIndices_eq_zero_iff` — the lowering map detects the zero tensor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open TensorMetricLowering
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## The rank-`0` separable form is the metric-independent unit tensor -/

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- The rank-`0` separable `(0, 0)`-form is the unit continuous multilinear map
`constOfIsEmpty 1`: contracting *no* upper slots against the metric leaves the
metric-independent empty product `1`. -/
lemma separableFormAt_zero
    (g : SmoothRiemannianMetric I M) (x : M) (w : Fin 0 → E) :
    separableFormAt (I := I) (M := M) g x 0 w =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [separableFormAt_apply]
  simp

/-! ## The index-lowering map detects the zero tensor

The pointwise metric-induced inner product is positive definite, so the
index-lowering map `lowerAllUpperIndices g r s x` is injective: this is
`lowerAllUpperIndices_injective`. We record the resulting kernel
characterisation. -/

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- The index-lowering map detects the zero tensor: `lowerAllUpperIndices g r s x T`
is the zero covariant `(0, r + s)`-tensor if and only if `T` is the zero
`(r, s)`-tensor. -/
lemma lowerAllUpperIndices_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x T = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact lowerAllUpperIndices_injective (I := I) (M := M) g r s x
      (h.trans (map_zero _).symm)
  · rw [h, map_zero]

/-! ## The index-lowering map as a continuous linear equivalence

The source `TensorRSModel r s ℝ E` and the target `Tensor0SModel (r + s) ℝ E` are
finite-dimensional `ℝ`-vector spaces of the *same* dimension `(finrank ℝ E) ^ (r + s)`.
A non-degenerate metric lowers indices injectively, so the lowering map — an
injective continuous-linear map between finite-dimensional spaces of equal
dimension — is bijective, hence a continuous linear equivalence. -/

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- The dimension of the model `(0, n)`-tensor fibre `Tensor0SModel n ℝ E` is
`(finrank ℝ E) ^ n`. -/
lemma finrank_tensor0SModel_eq (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) = (Module.finrank ℝ E) ^ n := by
  exact finrank_continuousMultilinearMap (𝕜 := ℝ) (F := E) n

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- The model `(r, s)`-tensor fibre and the model covariant `(0, r + s)`-tensor
fibre have equal `ℝ`-dimension `(finrank ℝ E) ^ (r + s)`. -/
lemma finrank_tensorRSModel_eq_finrank_tensor0SModel (r s : ℕ) :
    Module.finrank ℝ (TensorRSModel r s ℝ E) =
      Module.finrank ℝ (Tensor0SModel (r + s) ℝ E) := by
  rw [finrank_tensorRSModel, finrank_tensor0SModel_eq]

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **The index-lowering map is bijective.** Injectivity comes from the
non-degeneracy of the metric (`lowerAllUpperIndices_injective`); surjectivity
follows because the source and target are finite-dimensional of equal dimension. -/
theorem lowerAllUpperIndices_bijective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Function.Bijective (lowerAllUpperIndices (I := I) (M := M) g r s x) := by
  refine ⟨lowerAllUpperIndices_injective (I := I) (M := M) g r s x, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_tensorRSModel_eq_finrank_tensor0SModel (E := E) r s)).mp
    (lowerAllUpperIndices_injective (I := I) (M := M) g r s x)

/-- **The index-lowering map as a continuous linear equivalence.** A non-degenerate
metric lowers all `r` upper indices of a mixed `(r, s)`-tensor reversibly: the
lowering map `lowerAllUpperIndices g r s x` is a continuous linear equivalence
`TensorRSModel r s ℝ E ≃L[ℝ] Tensor0SModel (r + s) ℝ E`. The inverse is the
all-index *raising* map. -/
def lowerAllUpperIndicesEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    TensorRSModel r s ℝ E ≃L[ℝ] Tensor0SModel (r + s) ℝ E :=
  -- The linear-equivalence form built from bijectivity, upgraded to a
  -- continuous linear equivalence: both directions are linear maps between
  -- finite-dimensional `ℝ`-spaces, hence continuous.
  (LinearEquiv.ofBijective
      (lowerAllUpperIndices (I := I) (M := M) g r s x).toLinearMap
      (lowerAllUpperIndices_bijective (I := I) (M := M) g r s x)).toContinuousLinearEquiv

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- The forward direction of `lowerAllUpperIndicesEquiv` is the index-lowering
map `lowerAllUpperIndices`. -/
@[simp]
lemma lowerAllUpperIndicesEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x T =
      lowerAllUpperIndices (I := I) (M := M) g r s x T := rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- The index-lowering equivalence as a bundled continuous linear map is the
underlying index-lowering map. -/
lemma lowerAllUpperIndicesEquiv_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ((lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x :
        TensorRSModel r s ℝ E →L[ℝ] Tensor0SModel (r + s) ℝ E)) =
      lowerAllUpperIndices (I := I) (M := M) g r s x := by
  ext T
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- Round-trip: raising back the indices recovers the original `(r, s)`-tensor. -/
@[simp]
lemma lowerAllUpperIndicesEquiv_symm_apply_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm
        (lowerAllUpperIndices (I := I) (M := M) g r s x T) = T := by
  have h := (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm_apply_apply T
  rwa [lowerAllUpperIndicesEquiv_apply] at h

omit [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- Round-trip: lowering the indices of a raised covariant `(0, r + s)`-tensor
recovers the original tensor. -/
@[simp]
lemma lowerAllUpperIndicesEquiv_apply_symm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (U : Tensor0SModel (r + s) ℝ E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x
        ((lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).symm U) = U := by
  have h := (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).apply_symm_apply U
  rwa [lowerAllUpperIndicesEquiv_apply] at h

/-! ## The metric-lowered section through the index-lowering equivalence

The metric-lowered `(0, r + s)`-tensor section `liftedTensorSection g r s S`
(`Integral/Connection/TensorRSMetricCompatible.lean`) is, fibrewise, the
index-lowering equivalence applied to the model coercion of `S`. We record this
identification, and the resulting recovery of `S` from its lift through the
fibrewise inverse of the index-lowering equivalence. -/

/-- The model coercion of the metric-lowered section `liftedTensorSection g r s S`
at `y` is the index-lowering equivalence `lowerAllUpperIndicesEquiv g r s y`
applied to the model coercion of `S y`. -/
lemma toModel_liftedTensorSection_eq_equiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y) =
      lowerAllUpperIndicesEquiv (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (S y)) := by
  rw [toModel_liftedTensorSection, lowerAllUpperIndicesEquiv_apply]

/-- The model coercion of `S y` is recovered from the metric-lowered section by
the fibrewise inverse of the index-lowering equivalence. -/
lemma toModel_eq_symm_liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    TensorRSSpace.toModel (S y) =
      (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s y).symm
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y)) := by
  rw [toModel_liftedTensorSection_eq_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

end Connection
end Integral
end DifferentialGeometry

end
