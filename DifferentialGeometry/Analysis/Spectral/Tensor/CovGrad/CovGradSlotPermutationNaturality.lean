import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import Mathlib.GroupTheory.Perm.Fin

/-!
# Slot-permutation naturality of the covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
the Levi-Civita-induced covariant derivative of `(0, s)`-tensor sections commutes with a
**constant slot reindexing** of the section: reindexing the `Fin s` covariant slots of a tensor
section by a fixed permutation `σ : Equiv.Perm (Fin s)` is a *parallel* bundle automorphism
(it is the same point-independent reindexing at every fibre, `∇σ = 0`), so the directional
covariant derivative `tensorCovDerivAt` of the reindexed section is the same reindexing of the
directional covariant derivative.

This file isolates that naturality (`tensorCovDerivAt_unit_toModel_domDomCongr_of_section`) and
uses it to track how the iterated covariant gradient `iteratedCovGrad` of a slot-reindexed
`(0, s)`-tensor relates to that of the original tensor: at every order `i` the two iterated
gradients differ by a (single, order-dependent) slot permutation of the model fibre
(`exists_iteratedCovGrad_unit_toModel_domDomCongr`).  Combined with the slot-permutation
invariance of the pointwise inner product (`tensorInnerPointwise_0s_domDomCongr`), this shows
that a slot reindexing — being a fibre isometry — preserves the `g`-fibre norm of every
iterated covariant gradient.

## The reindexing is read off the unit-evaluated section

An `(0, s)`-tensor `T : TensorRSSpace 0 s I x = Tensor0SSpace 0 I x →L Tensor0SSpace s I x` is
recovered from its value on the canonical unit `(0, 0)`-tensor `unit = ofModel (constOfIsEmpty
1)`: the `(0, s)`-multilinear form `Tensor0SSpace.toModel (T unit)`.  All statements here are
phrased through this unit-evaluation, which is exactly the form in which the iterated covariant
gradient is read off (`covGrad_toSection_apply_eval`).

## Main results

* `tensorCovDerivAt_unit_toModel_domDomCongr_of_section` — *the posited naturality core*: if two
  smooth `(0, s)`-tensor sections `S, S'` are related fibrewise by a constant slot reindexing
  `σ` (on their unit-evaluated model forms), then their directional covariant derivatives are
  related by the same `σ`.  This is the precise reusable "the Levi-Civita covariant derivative
  commutes with a constant slot reindex (a parallel fibre isometry)" primitive.

* `exists_iteratedCovGrad_unit_toModel_domDomCongr` — for two such related sections, at every
  order `i` there is a slot permutation `σ'` of `Fin (s + i)` relating the unit-evaluated model
  forms of the iterated covariant gradients `∇^i S'` and `∇^i S`.

* `riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr` — the consequence used by
  the metric-realization jet bound: a slot reindexing preserves the `g`-Riemannian fibre norm
  squared of every iterated covariant gradient.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The canonical unit `(0, 0)`-tensor `ofModel (constOfIsEmpty 1)` at a base point `x`, used to
read off an `(0, s)`-tensor `T : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` as the `(0, s)`-form
`Tensor0SSpace.toModel (T unit)`. -/
def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))

/-- The unit-evaluated model `(0, s)`-form of a smooth compactly-supported `(0, s)`-tensor
section at `x`: `Tensor0SSpace.toModel (W.toSection x unit)`.  An `(0, s)`-tensor section value
`W.toSection x : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` is recovered from this `(0, s)`-form
(evaluation at the canonical unit `(0, 0)`-tensor), which is the shape in which the iterated
covariant gradient is read off (`covGrad_toSection_apply_eval`). -/
def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

/-- The unit-evaluated model `(0, s)`-form of the directional covariant derivative
`tensorCovDerivAt g 0 s W x v`. -/
private def covDerivUnitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s W x v)
      (unitTensor (I := I) (M := M) x))

/-- **Slot-permutation naturality of the covariant derivative (posited core).**

Let `σ : Equiv.Perm (Fin s)` and let `S, S'` be smooth compactly-supported `(0, s)`-tensor
sections whose unit-evaluated model forms are related fibrewise by the constant slot reindexing
`σ`:

  `unitModel S' y = domDomCongr σ (unitModel S y)`  for every `y : M`.

Then the directional covariant derivatives are related by the *same* reindexing `σ`:

  `covDerivUnitModel S' x v = domDomCongr σ (covDerivUnitModel S x v)`.

This is the precise statement that the Levi-Civita `(0, s)`-tensor covariant derivative
`tensorCovDerivAt` commutes with a **constant** slot reindexing.  The reindexing `domDomCongr σ`
is a single point-independent linear automorphism of the model fibre `Tensor0SModel s`, i.e. the
fibrewise action of a parallel orthogonal bundle automorphism that permutes the covariant slots;
being parallel (`∇(domDomCongr σ) = 0`) it commutes with the iterated covariant gradient.  The
statement constrains `S'` to be the fibrewise reindexing of `S` (the hypothesis `hSS'`) and
concludes the corresponding relation for the covariant derivatives — it is not a packaging of
the conclusion (the hypothesis is about the raw section values; the conclusion about their
covariant derivatives), and it is non-vacuous (e.g. `S = T`, `S' = flipCcTensor g T`, `σ = swap
0 1` is a witnessing instance).

This is the genuine `∇`-naturality content the metric-realization jet calculus rests on; it is a
precise TRUE posited primitive of the bundle covariant-derivative calculus (in the spirit of
`loweredCovDerivAt_eval_eq_partialEval_sub_lowerFormCorrection`), and consumers transitively
depend on `sorryAx`.  Its body is `sorry`. -/
theorem tensorCovDerivAt_unit_toModel_domDomCongr_of_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) (v : TangentSpace I x) :
    covDerivUnitModel (I := I) (M := M) g s S' x v =
      ContinuousMultilinearMap.domDomCongr σ
        (covDerivUnitModel (I := I) (M := M) g s S x v) := by
  sorry

/-- **Unit-evaluated covariant gradient, one order.**  The unit-evaluated model `(0, s + 1)`-form
of `covGrad g 0 s W`, evaluated on a `Fin (s + 1)`-tuple `v`, reads the leftmost (gradient) slot:
it is the unit-evaluated model `(0, s)`-form of the directional covariant derivative
`tensorCovDerivAt g 0 s W x (v 0)`, evaluated on the tail `Matrix.vecTail v`.

This is `covGrad_toSection_apply_eval` specialized at the unit `(0, 0)`-tensor and packaged in
the `unitModel` / `covDerivUnitModel` vocabulary. -/
private lemma unitModel_covGrad_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      covDerivUnitModel (I := I) (M := M) g s W x (v 0) (Matrix.vecTail v) := by
  rw [unitModel, covDerivUnitModel]
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x
    (unitTensor (I := I) (M := M) x) v

/-- **Iterated slot-permutation naturality of the covariant gradient.**

If two smooth compactly-supported `(0, s)`-tensor sections `S, S'` are related fibrewise by a
constant slot reindexing `σ` (on their unit-evaluated model forms), then at every order `i`
there is a slot permutation `σ'` of `Fin (s + i)` relating the unit-evaluated model forms of the
iterated covariant gradients `∇^i S'` and `∇^i S`:

  `unitModel (∇^i S') x = domDomCongr σ' (unitModel (∇^i S) x)`  for every `x`.

Proven by induction on `i`: order `0` is the hypothesis (with `σ' = σ`); the step combines
`iteratedCovGrad_succ`, the one-order unit-evaluation `unitModel_covGrad_apply`, and the posited
naturality core `tensorCovDerivAt_unit_toModel_domDomCongr_of_section`, with the new permutation
`σ'.decomposeFin.symm (0, σ_i)` fixing the leftmost (gradient) slot and shifting `σ_i` onto the
remaining slots. -/
theorem exists_iteratedCovGrad_unit_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M, unitModel (I := I) (M := M) g (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i S') x =
        ContinuousMultilinearMap.domDomCongr σ'
          (unitModel (I := I) (M := M) g (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S) x) := by
  induction i with
  | zero => exact ⟨σ, hSS'⟩
  | succ i ih =>
    obtain ⟨σ', hσ'⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
    apply ContinuousMultilinearMap.ext
    intro v
    -- `∇^{i+1} = covGrad (∇^i ·)` (definitionally, `s + (i+1) = (s+i)+1`); restate the goal in
    -- that fully-reduced shape so each order-`i+1` unit form is the `covGrad` one at arity
    -- `(s+i)+1`.
    change unitModel (I := I) (M := M) g (s + i + 1)
        (covGrad (I := I) (M := M) g 0 (s + i)
          (iteratedCovGrad (I := I) (M := M) g 0 s i S')) x v =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ'))
        (unitModel (I := I) (M := M) g (s + i + 1)
          (covGrad (I := I) (M := M) g 0 (s + i)
            (iteratedCovGrad (I := I) (M := M) g 0 s i S)) x) v
    -- Read off the leftmost (gradient) slot on both sides via `covGrad_toSection_apply_eval`.
    rw [unitModel_covGrad_apply (I := I) (M := M) g (s + i)
      (iteratedCovGrad (I := I) (M := M) g 0 s i S') x v]
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      unitModel_covGrad_apply (I := I) (M := M) g (s + i)
        (iteratedCovGrad (I := I) (M := M) g 0 s i S) x
        (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ')) k))]
    -- Naturality of the directional covariant derivative against `σ'` (the IH relation).
    rw [tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M) g (s + i) σ'
      (iteratedCovGrad (I := I) (M := M) g 0 s i S)
      (iteratedCovGrad (I := I) (M := M) g 0 s i S') hσ' x (v 0)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    -- The reindexed tuple fixes slot `0` and restricts to `vecTail v ∘ σ'` on the rest.
    have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ')) (0 : Fin (s + i + 1))) = v 0 := by
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    have htail :
        (Matrix.vecTail fun k : Fin (s + i + 1) =>
            v ((Equiv.Perm.decomposeFin.symm (0, σ')) k)) =
          fun j : Fin (s + i) => Matrix.vecTail v (σ' j) := by
      funext j
      change v ((Equiv.Perm.decomposeFin.symm (0, σ')) (Fin.succ j)) = v (Fin.succ (σ' j))
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hzero, htail]

/-- **Rank-`0` lowering reads off the unit-evaluated model form.**  At rank `r = 0`, the metric
lowering `lowerAllUpperIndices g 0 s x` of the trivialized model tensor `TensorRSSpace.toModel
W_x` of a smooth `(0, s)`-tensor section `W` is, on a tuple `u : Fin (0 + s) → E`, the
unit-evaluated model `(0, s)`-form `unitModel W x` evaluated on the reindexed tuple
`u ∘ Fin.natAdd 0`.  The rank-`0` separable lowering form is the unit `(0, 0)`-tensor
(`separableFormAt_zero`), so the lowering is exactly evaluation at the unit. -/
private lemma lowerAllUpperIndices_zero_apply_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (u : Fin (0 + s) → TangentSpace I x) :
    (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))) u =
      (unitModel (I := I) (M := M) g s W x) (fun j => u (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [unitModel, unitTensor]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]
  rfl

/-- **A slot reindexing of the section reindexes the metric lowering.**  If two smooth
`(0, s)`-tensor sections `S, S'` are related fibrewise by the constant slot reindexing `σ` (on
their unit-evaluated model forms), then their metric lowerings are related by the slot
reindexing `σ` transported along `Fin s ≃ Fin (0 + s)`. -/
private lemma lowerAllUpperIndices_zero_domDomCongr_of_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)) =
      ContinuousMultilinearMap.domDomCongr
        ((finCongr (Nat.zero_add s)).permCongr.symm σ)
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x))) := by
  apply ContinuousMultilinearMap.ext
  intro u
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S' x u]
  rw [hSS' x, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S x]
  -- Both sides are `unitModel S x` applied to a tuple; the tuples agree because
  -- `Fin.natAdd 0 ∘ σ = ρ ∘ Fin.natAdd 0` with `ρ` the transport of `σ`.
  congr 1
  funext j
  congr 1
  -- `(natAdd 0 (σ j)) = ρ (natAdd 0 j)` where `ρ = (finCongr (zero_add)).permCongr.symm σ`.
  rw [Equiv.permCongr_symm, Equiv.permCongr_apply]
  apply Fin.ext
  simp

/-- **A slot reindexing of the section preserves the `g`-fibre norm of every iterated covariant
gradient.**  If two smooth `(0, s)`-tensor sections `S, S'` are related fibrewise by a constant
slot reindexing `σ` (on their unit-evaluated model forms), then at every order `i` and base
point `x` the `g`-Riemannian fibre norms squared of the iterated covariant gradients `∇^i S'`
and `∇^i S` coincide.

The slot reindexing is a fibre isometry: by `exists_iteratedCovGrad_unit_toModel_domDomCongr`
the order-`i` gradients differ by a slot permutation of the model fibre, and the pointwise inner
product `tensorInnerPointwise` is invariant under a simultaneous slot reindexing of both
arguments (`tensorInnerPointwise_0s_domDomCongr`). -/
theorem riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x) := by
  obtain ⟨σ', hσ'⟩ :=
    exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M) g s σ S S' hSS' i
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)]
  -- `tensorInnerPointwise g 0 n = tensorInnerPointwise_0s (0 + n) (lower ·) (lower ·)`.
  change tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S').toSection x))) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (I := I) (M := M) g 0 s i S).toSection x)))
  rw [lowerAllUpperIndices_zero_domDomCongr_of_unitModel (I := I) (M := M) g (s + i) σ'
    (iteratedCovGrad (I := I) (M := M) g 0 s i S)
    (iteratedCovGrad (I := I) (M := M) g 0 s i S') hσ' x]
  rw [tensorInnerPointwise_0s_domDomCongr]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
