import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGrad
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovariantLeibniz
import DifferentialGeometry.Integral.L2.PointwiseInner.SlotPermutation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The covector-prepend section construction

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file packages the *covector-prepend* cross term that appears in
the covariant Leibniz rule.

The covariant Leibniz rule for a smooth-scalar-weighted tensor section produces a
cross term of the shape `dζ ⊗ S` — the exterior derivative `dζ` of a smooth
scalar `ζ : C^∞⟮I, M; ℝ⟯`, tensored as an extra covariant slot onto an
`(r, s)`-tensor section `S`. To pair such a cross term against the section-level
covariant gradient `covGrad`, the `dζ ⊗ S` datum must itself be packaged as a
genuine `(r, s + 1)`-tensor section, carrying the *same* leftmost-slot convention
that `covGrad` uses. This file builds that packaging.

## Main constructions

* `prependCovGradSlot g r s ζ S` — tensor the exterior derivative of a smooth
  scalar `ζ` as the leftmost covariant slot onto a smooth compactly-supported
  `(r, s)`-tensor section `S`, producing a smooth compactly-supported
  `(r, s + 1)`-tensor section.

## Main results

* `prependCovGradSlot_add`, `prependCovGradSlot_smul` — `ℝ`-linearity of
  `prependCovGradSlot` in the section `S`.
* `prependCovGradSlot_toSection_apply` — the pointwise-evaluation formula: at a
  point `x`, the underlying section value of `prependCovGradSlot g r s ζ S` is the
  image, under the fibrewise covariant-gradient bundle equivalence
  `covGradBundleEquiv r s x`, of the continuous linear map
  `v ↦ (extDerivFun ζ x v) • S.toSection x`.
* `prependCovGradSlot_toSection_apply_eval` — the pointwise-evaluation formula
  expanded on a `(0, r)`-tensor and a `Fin (s + 1)`-tuple: the leftmost covariant
  slot carries the tangent direction `v 0`, which is read off as the scalar
  `dζ(v 0) = extDerivFun ζ x (v 0)`.
* `tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad` — the cross-left
  metric-isometry bridge: for all smooth compactly-supported `(r, s)`-tensor
  sections `w`, `S` and every smooth scalar `ζ`, the inverse-Gram-weighted
  cross term `tensorCovDerivCrossLeft g r s ζ w S` of the covariant Leibniz
  rule coincides, pointwise, with the genuine one-rank-higher tensor pointwise
  inner product `tensorInnerPointwise g r (s + 1)` of the section-level
  covariant gradient `covGrad g r s w` and the covector-prepend section
  `prependCovGradSlot g r s ζ S`.

## Strategy

The covector-prepend cross term is identified, without building any new bundle
machinery, from the section-level covariant gradient `covGrad` and the
smooth-scalar weighting `scalarSmul` already available. The pointwise covariant
Leibniz rule `tensorCovDerivAt_scalarSmul` reads

  `tensorCovDerivAt g r s (ζ • S) x v
     = ζ x • tensorCovDerivAt g r s S x v + (extDerivFun ζ x v) • S.toSection x`,

so the directional `dζ ⊗ S` cross term is exactly the difference

  `tensorCovDerivAt g r s (ζ • S) x v − ζ x • tensorCovDerivAt g r s S x v`.

Transporting both sides through the fibrewise covariant-gradient bundle
equivalence `covGradBundleEquiv` — which is `ℝ`-linear, and which `covGrad`
already uses — the section-level `(r, s + 1)`-tensor packaging of `dζ ⊗ S` is the
difference of two genuine smooth compactly-supported `(r, s + 1)`-tensor sections:

  `prependCovGradSlot g r s ζ S
     = covGrad g r s (ζ • S) − ζ • covGrad g r s S`.

Both summands are smooth and compactly supported by construction, so no fresh
smoothness or compact-support argument is needed; `ℝ`-linearity in `S` is the
`ℝ`-linearity of `covGrad` and of `scalarSmul`, and the pointwise-evaluation
formula is the pointwise covariant Leibniz rule transported through the bundle
equivalence.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The covector-prepend section construction

The section-level packaging of the `dζ ⊗ S` cross term is, by the pointwise
covariant Leibniz rule transported through the covariant-gradient bundle
equivalence, the difference of two genuine smooth compactly-supported
`(r, s + 1)`-tensor sections: the section-level covariant gradient `covGrad` of
the smooth-scalar-weighted section `ζ • S`, minus the smooth scalar `ζ` times the
section-level covariant gradient `covGrad` of `S`. -/

/-- **The covector-prepend section construction.** Tensor the exterior derivative
of a smooth scalar `ζ` as the leftmost covariant slot onto a smooth
compactly-supported `(r, s)`-tensor section `S`, producing a smooth
compactly-supported `(r, s + 1)`-tensor section.

It is defined as the difference of two section-level covariant gradients:
`covGrad g r s (ζ • S)` minus `ζ • covGrad g r s S`. By the pointwise covariant
Leibniz rule this difference carries exactly the directional `dζ ⊗ S` cross term;
the directional cross term `v ↦ (extDerivFun ζ x v) • S.toSection x` is placed in
the leftmost covariant slot — the slot convention produced by the covariant
derivative and used by `covGrad`. -/
noncomputable def prependCovGradSlot (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) : SmoothCcTensor g r (s + 1) :=
  covGrad (I := I) (M := M) g r s (scalarSmul (I := I) (M := M) g r s ζ S) -
    scalarSmul (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S)

/-- The underlying smooth section of `prependCovGradSlot g r s ζ S` is the
difference of the underlying sections of `covGrad g r s (ζ • S)` and of
`ζ • covGrad g r s S`. -/
lemma prependCovGradSlot_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) :
    (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection := rfl

/-! ## The directional covector-prepend cross term

The directional `dζ ⊗ S` cross term, as a continuous-linear-map–valued
gradient-bundle element, is `v ↦ (extDerivFun ζ x v) • S.toSection x`. By the
pointwise covariant Leibniz rule it equals the difference of the directional
covariant derivative of `ζ • S` and the `ζ`-scaled directional covariant
derivative of `S`. -/

/-- The directional `dζ ⊗ S` cross term at a base point `x`, as an element of the
covariant-gradient bundle fibre `TangentSpace I x →L[ℝ] TensorRSSpace r s I x`:
the continuous linear map sending a tangent vector `v` to the scalar `dζ(v)`
times the fixed `(r, s)`-tensor `S.toSection x`. It is the right-scalar-multiplied
continuous linear map `(extDerivFun ζ x).smulRight (S.toSection x)`. -/
private noncomputable def prependGradCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  (extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)

/-- The directional `dζ ⊗ S` cross term, evaluated at a tangent direction `v`,
equals the scalar `extDerivFun ζ x v` times the fixed `(r, s)`-tensor
`S.toSection x`. -/
private lemma prependGradCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) (v : E) :
    prependGradCLM (I := I) (M := M) g r s ζ S x v =
      (extDerivFun (I := I) (ζ : M → ℝ) x v) • S.toSection x := by
  rw [prependGradCLM, ContinuousLinearMap.smulRight_apply]

/-! ### `ℝ`-linearity of `ContinuousLinearMap.smulRight` in the second slot

For a fixed continuous linear functional `φ`, the right-scalar-multiplied
continuous linear map `φ.smulRight (·)` is `ℝ`-linear in its second argument: this
is the `ℝ`-linearity of `t ↦ (φ v) • t` for each direction `v`. These two
elementary `ContinuousLinearMap` identities are not named lemmas in Mathlib, so
they are recorded here for use in the linearity proofs below. -/

/-- For a fixed continuous linear functional `φ`, the map `φ.smulRight (·)` is
additive in its second argument. -/
private lemma smulRight_add_right (r s : ℕ) {x : M}
    (φ : TangentSpace I x →L[ℝ] ℝ) (t₁ t₂ : TensorRSSpace r s I x) :
    φ.smulRight (t₁ + t₂) = φ.smulRight t₁ + φ.smulRight t₂ := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    smul_add]

/-- For a fixed continuous linear functional `φ`, the map `φ.smulRight (·)` is
`ℝ`-homogeneous in its second argument. -/
private lemma smulRight_smul_right (r s : ℕ) {x : M}
    (φ : TangentSpace I x →L[ℝ] ℝ) (c : ℝ) (t : TensorRSSpace r s I x) :
    φ.smulRight (c • t) = c • φ.smulRight t := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, smul_comm]

/-- The directional `dζ ⊗ S` cross term equals the directional covariant
derivative of the smooth-scalar-weighted section `ζ • S` minus the `ζ`-scaled
directional covariant derivative of `S`.

This is the pointwise covariant Leibniz rule `tensorCovDerivAt_scalarSmul`, read
as an equality of continuous-linear-map–valued gradient-bundle elements. -/
private lemma prependGradCLM_eq_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    prependGradCLM (I := I) (M := M) g r s ζ S x =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ S).toSection y) x -
        (ζ : M → ℝ) x •
          tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
            (fun y : M => S.toSection y) x := by
  -- Compare the two continuous linear maps direction by direction.
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    prependGradCLM_apply]
  -- The two covariant-derivative terms are, by definition, `tensorCovDerivAt`.
  have hweighted :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ S).toSection y) x v =
        tensorCovDerivAt (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S) x v := rfl
  have hplain :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => S.toSection y) x v =
        tensorCovDerivAt (I := I) (M := M) g r s S x v := rfl
  rw [hweighted, hplain]
  -- The pointwise covariant Leibniz rule, rearranged.
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ S x v]
  rw [add_sub_cancel_left]

/-! ## The pointwise-evaluation formula

The underlying section value of `prependCovGradSlot g r s ζ S` at a point `x` is
the image, under the fibrewise covariant-gradient bundle equivalence
`covGradBundleEquiv r s x`, of the directional `dζ ⊗ S` cross term. -/

/-- **Pointwise-evaluation formula for the covector-prepend section
construction.**

At a base point `x`, the underlying section value of `prependCovGradSlot g r s ζ S`
is the image, under the fibrewise covariant-gradient bundle equivalence
`covGradBundleEquiv r s x`, of the directional `dζ ⊗ S` cross term — the
continuous linear map `v ↦ (extDerivFun ζ x v) • S.toSection x` sending a tangent
vector `v` to the scalar `dζ(v)` times the fixed `(r, s)`-tensor `S.toSection x`. -/
theorem prependCovGradSlot_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) := by
  -- The underlying section value of the difference is the pointwise difference.
  rw [prependCovGradSlot_toSection]
  rw [show ((covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection) x =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toSection x -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toSection x from rfl]
  -- Expand the `covGrad` term via its pointwise-evaluation formula, and the
  -- `scalarSmul` term via the underlying-section formula and `covGrad`'s.
  rw [covGrad_toSection_apply, scalarSmul_toSection_apply, covGrad_toSection_apply]
  -- `covGradBundleEquiv r s x` is `ℝ`-linear: pull the scalar and the difference
  -- through it.
  rw [← map_smul (covGradBundleEquiv (I := I) (M := M) r s x), ← map_sub]
  -- The argument is, by the covariant Leibniz rule, the directional cross term.
  rw [← prependGradCLM_eq_sub (I := I) (M := M) g r s ζ S x]
  rw [prependGradCLM]

/-- **Pointwise-evaluation formula, expanded on a tensor and a tuple.**

The underlying section value of `prependCovGradSlot g r s ζ S` at `x` is an
`(r, s + 1)`-tensor, i.e. a continuous linear map
`Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x`. Evaluated at a
`(0, r)`-tensor `D` and a `Fin (s + 1)`-tuple of tangent vectors `v`, it reads off
the tangent direction `v 0` from the leftmost covariant slot: the result is the
scalar `dζ(v 0) = extDerivFun ζ x (v 0)` times the `(r, s)`-tensor `S.toSection x`,
evaluated at `D` and the remaining `Fin s`-tuple `Matrix.vecTail v`. -/
theorem prependCovGradSlot_toSection_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) • S.toSection x) D)
        (Matrix.vecTail v) := by
  rw [prependCovGradSlot_toSection_apply]
  -- The fibrewise gradient-bundle equivalence reads the tangent direction off the
  -- leftmost slot; `(extDerivFun ζ x).smulRight (S.toSection x) (v 0)` is exactly
  -- `(extDerivFun ζ x (v 0)) • S.toSection x`.
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r s x
    ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) D v]
  rw [ContinuousLinearMap.smulRight_apply]

/-! ## `ℝ`-linearity of the covector-prepend section construction

`ℝ`-linearity in the section `S` is run through the pointwise-evaluation formula,
where the directional cross term `v ↦ (extDerivFun ζ x v) • S.toSection x` is
manifestly `ℝ`-linear in `S` — the slot `S.toSection x` of
`ContinuousLinearMap.smulRight`, via `smulRight_add_right` / `smulRight_smul_right`
— and the fibrewise bundle equivalence `covGradBundleEquiv r s x` is
`ℝ`-linear. -/

/-- The covector-prepend section construction is additive in the section `S`. -/
theorem prependCovGradSlot_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S₁ S₂ : SmoothCcTensor g r s) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (S₁ + S₂) =
      prependCovGradSlot (I := I) (M := M) g r s ζ S₁ +
        prependCovGradSlot (I := I) (M := M) g r s ζ S₂ := by
  -- Compare the two `SmoothCcTensor`s through their underlying section values.
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  -- The underlying section value of a sum is the pointwise sum.
  rw [show ((prependCovGradSlot (I := I) (M := M) g r s ζ S₁ +
        prependCovGradSlot (I := I) (M := M) g r s ζ S₂).toSection x) =
      (prependCovGradSlot (I := I) (M := M) g r s ζ S₁).toSection x +
        (prependCovGradSlot (I := I) (M := M) g r s ζ S₂).toSection x from rfl]
  -- Reduce all three section values via the pointwise-evaluation formula.
  rw [prependCovGradSlot_toSection_apply, prependCovGradSlot_toSection_apply,
    prependCovGradSlot_toSection_apply]
  -- The directional cross term `(extDerivFun ζ x).smulRight (·)` is additive in
  -- the section value `(S₁ + S₂).toSection x = S₁.toSection x + S₂.toSection x`;
  -- the fibrewise bundle equivalence `covGradBundleEquiv r s x` is `ℝ`-linear.
  rw [show ((S₁ + S₂).toSection x) = S₁.toSection x + S₂.toSection x from rfl,
    smulRight_add_right (I := I) r s, map_add]

/-- The covector-prepend section construction is `ℝ`-homogeneous in the section
`S`. -/
theorem prependCovGradSlot_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (c : ℝ) (S : SmoothCcTensor g r s) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (c • S) =
      c • prependCovGradSlot (I := I) (M := M) g r s ζ S := by
  -- Compare the two `SmoothCcTensor`s through their underlying section values.
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  -- The underlying section value of a scalar multiple is the pointwise scalar
  -- multiple.
  rw [show ((c • prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) =
      c • (prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x from rfl]
  -- Reduce both section values via the pointwise-evaluation formula.
  rw [prependCovGradSlot_toSection_apply, prependCovGradSlot_toSection_apply]
  -- The directional cross term `(extDerivFun ζ x).smulRight (·)` is
  -- `ℝ`-homogeneous in the section value `(c • S).toSection x = c • S.toSection x`;
  -- the fibrewise bundle equivalence `covGradBundleEquiv r s x` is `ℝ`-linear.
  rw [show ((c • S).toSection x) = c • S.toSection x from rfl,
    smulRight_smul_right (I := I) r s, map_smul]

/-- The covector-prepend section construction sends the zero section to the zero
section. -/
@[simp] theorem prependCovGradSlot_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) :
    prependCovGradSlot (I := I) (M := M) g r s ζ (0 : SmoothCcTensor g r s) = 0 := by
  have h := prependCovGradSlot_smul (I := I) (M := M) g r s ζ (0 : ℝ) 0
  rwa [zero_smul, zero_smul] at h

/-! ## The cross-left metric-isometry bridge

The covariant Leibniz rule for the pointwise covariant-derivative inner product
produces the *cross-left* term `tensorCovDerivCrossLeft g r s ζ w S` — an
inverse-Gram-weighted double sum over the model-fibre basis pairing the exterior
derivative `dζ` of a smooth scalar against the `(r, s)`-tensor pointwise inner
product of the directional covariant derivatives `∇w` and the section `S`. To
pass that term to a limit it must be re-expressed as a genuine
`(r, s + 1)`-tensor pointwise inner product.

This section proves precisely that: `tensorCovDerivCrossLeft g r s ζ w S`
coincides, pointwise, with the genuine one-rank-higher tensor pointwise inner
product `tensorInnerPointwise g r (s + 1)` of the section-level covariant
gradient `covGrad g r s w` (whose extra covariant slot carries the
differentiation direction) and the covector-prepend section
`prependCovGradSlot g r s ζ S` (whose extra covariant slot carries the covector
`dζ`, with `S` undifferentiated in the remaining `(r, s)` slots).

The proof is the exact analogue of the metric-isometry bridge for two
covariant gradients: both sides expand — via the explicit closed form
`tensorInnerPointwise_0s_eq_sum` — to the same explicit inverse-Gram-weighted
sum
`∑ᵢ ∑ⱼ (G⁻¹)ᵢⱼ · (∂ⱼζ) · tensorInnerPointwise_{(r,s)}(∇ᵢw, S)`,
and the reconciliation of the slot orderings is the same tuple-splitting
`Fin.insertNthEquiv` bookkeeping at the differentiation slot. The only
structural difference from the two-gradient bridge: the second tensor's extra
slot is the covector slot of `prependCovGradSlot` — which, on a model-basis
tuple, contributes only the scalar `extDerivFun ζ x (chartModelBasis l)` — rather
than the differentiation slot of a second covariant gradient. -/

/-! ### Evaluating an `(r, s)`-tensor through the model coercion

The model coercion `TensorRSSpace.toModel` is an `arrowCongr` of the two
identity-on-carriers fibre-coercion equivalences `Tensor0SSpace.toModel`, so
evaluating the model coercion of an `(r, s)`-tensor on a model `(0, r)`-tensor
is evaluating the tensor itself on the corresponding fibre `(0, r)`-tensor. -/

/-- Evaluation of the model coercion of an `(r, s)`-tensor. For a tensor
`T : TensorRSSpace r s I x` and a model `(0, r)`-tensor `Dm`, the
`(0, s)`-model tensor `(TensorRSSpace.toModel T) Dm` is the model coercion of
`T` applied to the fibre `(0, r)`-tensor `Tensor0SSpace.ofModel Dm`. -/
private lemma crossLeft_tensorRSSpace_toModel_apply
    (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (Dm : Tensor0SModel r ℝ E) :
    (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E from
        TensorRSSpace.toModel T) Dm =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T)
          (Tensor0SSpace.ofModel Dm)) :=
  rfl

/-! ### The covariant gradient through the model coercion

Transporting `covGrad_toSection_apply_eval` through the model coercion
`TensorRSSpace.toModel` (via `crossLeft_tensorRSSpace_toModel_apply` on both the
domain and codomain factors) yields the evaluation formula for the covariant
gradient at the level of the model fibres: it reads the differentiation
direction `v 0` off the leftmost covariant slot and reduces to the directional
covariant derivative. -/

/-- **Model-fibre evaluation of the covariant gradient.** For a smooth
compactly-supported `(r, s)`-tensor section `w`, the model coercion of the
section value `(covGrad g r s w).toSection x` — an `(r, s + 1)`-model tensor —
evaluated on a model `(0, r)`-tensor `Dm` and a `Fin (s + 1)`-tuple `v`, equals
the model coercion of the directional covariant derivative
`tensorCovDerivAt g r s w x (v 0)` evaluated on `Dm` and the tail of `v`. -/
private lemma crossLeft_covGrad_toModel_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (Dm : Tensor0SModel r ℝ E) (v : Fin (s + 1) → E) :
    (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s w).toSection x)) Dm v =
      (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)))
        Dm (Matrix.vecTail v) := by
  -- View the model coercion of the `(r, s + 1)`-tensor explicitly as a
  -- continuous linear map of model fibres.
  change (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E from
      TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s w).toSection x)) Dm v = _
  -- Push the model coercion on the covariant gradient through to the fibre
  -- coercion `Tensor0SSpace.toModel`.
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r (s + 1) x
        ((covGrad (I := I) (M := M) g r s w).toSection x) Dm]
  -- Apply the defining evaluation formula for the section-level covariant
  -- gradient at the fibre `(0, r)`-tensor `Tensor0SSpace.ofModel Dm`.
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s w x
        (Tensor0SSpace.ofModel Dm) v]
  -- Pull the directional covariant derivative back to the model coercion.
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r s x
        (tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)) Dm]

/-! ### The covector-prepend section through the model coercion

Transporting `prependCovGradSlot_toSection_apply_eval` through the model
coercion yields the evaluation formula for the covector-prepend section at the
level of the model fibres: the leftmost covariant slot carries the tangent
direction `v 0`, contributing the scalar `dζ(v 0) = extDerivFun ζ x (v 0)`, and
the section `S` is evaluated on the model `(0, r)`-tensor and the tail of `v`. -/

/-- **Model-fibre evaluation of the covector-prepend section.** For a smooth
compactly-supported `(r, s)`-tensor section `S` and a smooth scalar `ζ`, the
model coercion of the section value `(prependCovGradSlot g r s ζ S).toSection x`
— an `(r, s + 1)`-model tensor — evaluated on a model `(0, r)`-tensor `Dm` and a
`Fin (s + 1)`-tuple `v`, equals the scalar `extDerivFun ζ x (v 0)` times the
model coercion of the section value `S.toSection x` evaluated on `Dm` and the
tail of `v`. -/
private lemma crossLeft_prependCovGradSlot_toModel_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (Dm : Tensor0SModel r ℝ E) (v : Fin (s + 1) → E) :
    (TensorRSSpace.toModel
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) Dm v =
      (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) •
        ((TensorRSSpace.toModel (S.toSection x)) Dm (Matrix.vecTail v)) := by
  -- View the model coercion of the `(r, s + 1)`-tensor explicitly as a
  -- continuous linear map of model fibres.
  change (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E from
      TensorRSSpace.toModel
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) Dm v = _
  -- Push the model coercion on the covector-prepend section through to the
  -- fibre coercion `Tensor0SSpace.toModel`.
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r (s + 1) x
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x) Dm]
  -- Apply the defining evaluation formula for the covector-prepend section at
  -- the fibre `(0, r)`-tensor `Tensor0SSpace.ofModel Dm`.
  rw [prependCovGradSlot_toSection_apply_eval (I := I) (M := M) g r s ζ S x
        (Tensor0SSpace.ofModel Dm) v]
  -- The leftmost covariant slot carries `dζ(v 0)`; the remaining slot value is
  -- the `(r, s)`-tensor `S.toSection x` scaled by `dζ(v 0)`.
  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) • S.toSection x)
          (Tensor0SSpace.ofModel Dm) =
      (extDerivFun (I := I) (ζ : M → ℝ) x (v 0)) •
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            S.toSection x) (Tensor0SSpace.ofModel Dm)) from rfl]
  -- The fibre coercion `Tensor0SSpace.toModel` is `ℝ`-linear: pull out the
  -- scalar `dζ(v 0)`.
  rw [Tensor0SSpace.toModel_smul]
  -- Pull the `(r, s)`-tensor `S.toSection x` back to the model coercion.
  rw [crossLeft_tensorRSSpace_toModel_apply (I := I) r s x (S.toSection x) Dm]
  rfl

/-! ### Slot bookkeeping for the differentiation slot

The mixed pointwise inner product `tensorInnerPointwise g r (s + 1)` lowers the
`r` upper slots first, so in the resulting covariant `(0, r + (s + 1))`-tensor
the differentiation slot sits at index `r`. The lemmas below identify that
index `r` slot and the action of the omit-index-`r` embedding
`(crossDiffSlot r s).succAbove : Fin (r + s) → Fin (r + (s + 1))` on the upper
and covariant blocks. -/

/-- The index of the differentiation slot inside the lowered covariant
`(0, r + (s + 1))`-tensor: it sits at position `r`, after the `r` lowered upper
slots and before the `s` genuine covariant slots. -/
private def crossDiffSlot (r s : ℕ) : Fin (r + (s + 1)) :=
  ⟨r, by omega⟩

/-- The differentiation slot is the `natAdd`-image of the leftmost covariant
slot: `lowerAllUpperIndices` maps the covariant block to the `natAdd r`
positions, and the gradient / prepend convention places the extra slot at the
leftmost of the `s + 1` covariant slots. -/
private lemma crossLeft_natAdd_zero_eq_diffSlot (r s : ℕ) :
    (Fin.natAdd r (0 : Fin (s + 1)) : Fin (r + (s + 1))) = crossDiffSlot r s := by
  apply Fin.ext
  simp [crossDiffSlot, Fin.natAdd]

/-- The omit-index-`r` embedding sends the `r` upper-slot positions
(`castAdd s` into `Fin (r + s)`) to the `r` upper-slot positions
(`castAdd (s + 1)` into `Fin (r + (s + 1))`): both blocks occupy positions
`0, …, r - 1`, which lie below the differentiation slot. -/
private lemma crossDiffSlot_succAbove_castAdd (r s : ℕ) (a : Fin r) :
    (crossDiffSlot r s).succAbove (Fin.castAdd s a) = Fin.castAdd (s + 1) a := by
  apply Fin.ext
  have hcond : (Fin.castSucc (Fin.castAdd s a) : Fin (r + (s + 1)))
      < crossDiffSlot r s := by
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_castAdd, crossDiffSlot]
    exact a.isLt
  rw [Fin.succAbove, if_pos hcond]
  simp only [Fin.val_castSucc, Fin.val_castAdd]

/-- The omit-index-`r` embedding sends the `s` covariant-slot positions
(`natAdd r` into `Fin (r + s)`) to the `s` genuine covariant-slot positions
(`natAdd r ∘ Fin.succ` into `Fin (r + (s + 1))`): the `Fin (r + s)` covariant
block occupies positions `r, …, r + s - 1`, which lie at or above the
differentiation slot, so each is shifted up by one. -/
private lemma crossDiffSlot_succAbove_natAdd (r s : ℕ) (a : Fin s) :
    (crossDiffSlot r s).succAbove (Fin.natAdd r a) =
      Fin.natAdd r (Fin.succ a) := by
  apply Fin.ext
  have hcond : ¬ (Fin.castSucc (Fin.natAdd r a) : Fin (r + (s + 1)))
      < crossDiffSlot r s := by
    rw [Fin.lt_def, not_lt]
    simp only [Fin.val_castSucc, Fin.val_natAdd, crossDiffSlot]
    omega
  rw [Fin.succAbove, if_neg hcond]
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

/-! ### The lowered covariant gradient on an `insertNth` basis tuple

The covariant `(0, r + (s + 1))`-tensor `lowerAllUpperIndices g r (s + 1) x A`,
where `A` is the model coercion of the covariant gradient `covGrad g r s w`,
evaluated on a model-basis tuple indexed by
`Fin.insertNth (crossDiffSlot r s) k i`, reduces to the covariant
`(0, r + s)`-tensor `lowerAllUpperIndices g r s x (TensorRSSpace.toModel (∇_{eₖ}w))`
evaluated on the model-basis tuple indexed by `i`.

`lowerAllUpperIndices` places the `r` upper slots before the covariant slots,
so the differentiation slot of `covGrad` lands at index `r = crossDiffSlot r s`;
splitting the tuple at `crossDiffSlot r s` (via `insertNth`) isolates the
differentiation direction `eₖ` and identifies the remaining `r + s` slots with
the slots of the directional covariant derivative, by the embedding identities
`crossDiffSlot_succAbove_castAdd` and `crossDiffSlot_succAbove_natAdd`. -/

/-- **The lowered covariant gradient on an `insertNth` basis tuple.** For a
smooth compactly-supported `(r, s)`-tensor section `w`, an index `k` and a
slot-index tuple `i`, the lowered covariant gradient
`lowerAllUpperIndices g r (s + 1) x (TensorRSSpace.toModel (covGrad g r s w))`,
evaluated on the basis tuple indexed by `Fin.insertNth (crossDiffSlot r s) k i`,
equals the lowered directional covariant derivative
`lowerAllUpperIndices g r s x (TensorRSSpace.toModel (∇_{eₖ}w))` evaluated on
the basis tuple indexed by `i`. -/
private lemma crossLeft_lower_covGrad_insertNth_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (i : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (fun a : Fin (r + (s + 1)) => (chartModelBasis E)
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s w x
            ((chartModelBasis E) k)))
        (fun a : Fin (r + s) => (chartModelBasis E) (i a)) := by
  classical
  set I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E) :=
    Fin.insertNth (crossDiffSlot r s) k i with hI'
  -- Unfold both `lowerAllUpperIndices` evaluations.
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  -- The differentiation direction read off the `(s + 1)`-block is `eₖ`: the
  -- leftmost covariant slot of `covGrad` is `natAdd r 0 = crossDiffSlot r s`,
  -- where `I'` takes value `k`.
  have hdir : (chartModelBasis E) (I' (Fin.natAdd r (0 : Fin (s + 1)))) =
      (chartModelBasis E) k := by
    rw [crossLeft_natAdd_zero_eq_diffSlot, hI', Fin.insertNth_apply_same]
  -- The upper-slot model tuples coincide.
  have hupper : (fun a : Fin r =>
        (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))) =
      (fun a : Fin r => (chartModelBasis E) (i (Fin.castAdd s a))) := by
    funext a
    show (chartModelBasis E) (I' (Fin.castAdd (s + 1) a)) =
      (chartModelBasis E) (i (Fin.castAdd s a))
    rw [← crossDiffSlot_succAbove_castAdd r s a, hI',
      Fin.insertNth_apply_succAbove]
  -- The genuine covariant model tuples coincide.
  have hcov : Matrix.vecTail
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j))) =
      (fun a : Fin s => (chartModelBasis E) (i (Fin.natAdd r a))) := by
    funext a
    change (chartModelBasis E) (I' (Fin.natAdd r (Fin.succ a))) =
      (chartModelBasis E) (i (Fin.natAdd r a))
    rw [← crossDiffSlot_succAbove_natAdd r s a, hI',
      Fin.insertNth_apply_succAbove]
  -- Evaluate the covariant gradient through the model-fibre formula, then feed
  -- in the three tuple identities.
  rw [crossLeft_covGrad_toModel_apply (I := I) (M := M) g r s w x
        (separableFormAt (I := I) (M := M) g x r
          (fun a : Fin r => (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))))
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j)))]
  rw [hdir, hupper, hcov]

/-! ### The lowered covector-prepend section on an `insertNth` basis tuple

The covariant `(0, r + (s + 1))`-tensor `lowerAllUpperIndices g r (s + 1) x A`,
where `A` is the model coercion of the covector-prepend section
`prependCovGradSlot g r s ζ S`, evaluated on a model-basis tuple indexed by
`Fin.insertNth (crossDiffSlot r s) l j`, reduces to the scalar
`extDerivFun ζ x (chartModelBasis l)` times the lowered section value
`lowerAllUpperIndices g r s x (TensorRSSpace.toModel (S.toSection x))` evaluated
on the model-basis tuple indexed by `j`.

The slot bookkeeping is identical to the covariant-gradient case: the leftmost
covariant slot of `prependCovGradSlot` lands at index `r = crossDiffSlot r s`;
splitting the tuple there isolates the leftmost covariant slot, which the
covector-prepend section reads off as the scalar `dζ` of the basis vector `eₗ`,
and identifies the remaining `r + s` slots with the slots of `S`. -/

/-- **The lowered covector-prepend section on an `insertNth` basis tuple.** For
a smooth compactly-supported `(r, s)`-tensor section `S` and a smooth scalar
`ζ`, an index `l` and a slot-index tuple `j`, the lowered covector-prepend
section
`lowerAllUpperIndices g r (s + 1) x (TensorRSSpace.toModel (prependCovGradSlot g r s ζ S))`,
evaluated on the basis tuple indexed by `Fin.insertNth (crossDiffSlot r s) l j`,
equals the scalar `extDerivFun ζ x (chartModelBasis l)` times the lowered
section value `lowerAllUpperIndices g r s x (TensorRSSpace.toModel (S.toSection x))`
evaluated on the basis tuple indexed by `j`. -/
private lemma crossLeft_lower_prependCovGradSlot_insertNth_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M)
    (l : Fin (Module.finrank ℝ E))
    (j : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x))
        (fun a : Fin (r + (s + 1)) => (chartModelBasis E)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l)) *
        lowerAllUpperIndices (I := I) (M := M) g r s x
          (TensorRSSpace.toModel (S.toSection x))
          (fun a : Fin (r + s) => (chartModelBasis E) (j a)) := by
  classical
  set J' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E) :=
    Fin.insertNth (crossDiffSlot r s) l j with hJ'
  -- Unfold both `lowerAllUpperIndices` evaluations.
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  -- The covector direction read off the `(s + 1)`-block is `eₗ`: the leftmost
  -- covariant slot of `prependCovGradSlot` is `natAdd r 0 = crossDiffSlot r s`,
  -- where `J'` takes value `l`.
  have hdir : (chartModelBasis E) (J' (Fin.natAdd r (0 : Fin (s + 1)))) =
      (chartModelBasis E) l := by
    rw [crossLeft_natAdd_zero_eq_diffSlot, hJ', Fin.insertNth_apply_same]
  -- The upper-slot model tuples coincide.
  have hupper : (fun a : Fin r =>
        (chartModelBasis E) (J' (Fin.castAdd (s + 1) a))) =
      (fun a : Fin r => (chartModelBasis E) (j (Fin.castAdd s a))) := by
    funext a
    show (chartModelBasis E) (J' (Fin.castAdd (s + 1) a)) =
      (chartModelBasis E) (j (Fin.castAdd s a))
    rw [← crossDiffSlot_succAbove_castAdd r s a, hJ',
      Fin.insertNth_apply_succAbove]
  -- The genuine covariant model tuples coincide.
  have hcov : Matrix.vecTail
        (fun a : Fin (s + 1) => (chartModelBasis E) (J' (Fin.natAdd r a))) =
      (fun a : Fin s => (chartModelBasis E) (j (Fin.natAdd r a))) := by
    funext a
    change (chartModelBasis E) (J' (Fin.natAdd r (Fin.succ a))) =
      (chartModelBasis E) (j (Fin.natAdd r a))
    rw [← crossDiffSlot_succAbove_natAdd r s a, hJ',
      Fin.insertNth_apply_succAbove]
  -- Evaluate the covector-prepend section through the model-fibre formula.
  rw [crossLeft_prependCovGradSlot_toModel_apply (I := I) (M := M) g r s ζ S x
        (separableFormAt (I := I) (M := M) g x r
          (fun a : Fin r => (chartModelBasis E) (J' (Fin.castAdd (s + 1) a))))
        (fun a : Fin (s + 1) => (chartModelBasis E) (J' (Fin.natAdd r a)))]
  -- The covector slot reads off `dζ(eₗ)`; the remaining slots are the slots of
  -- `S`, by the upper / covariant tuple identities.
  rw [hdir, hupper, hcov, smul_eq_mul]

/-! ### Splitting the differentiation slot out of the inverse-Gram product

The inverse-Gram product over the `r + (s + 1)` covariant slots of the lowered
`(r, s + 1)`-tensor factors, by `Fin.prod_univ_succAbove` at the differentiation
slot `crossDiffSlot r s`, into the inverse-Gram weight of the differentiation
direction and the inverse-Gram product over the remaining `r + s` slots. -/

/-- Splitting the inverse-Gram product at the differentiation slot. For
slot-index tuples `i j` and differentiation indices `k l`, the product of
inverse-Gram entries over all `r + (s + 1)` covariant slots of the
`insertNth`-assembled tuples equals the inverse-Gram weight `(G⁻¹)ₖₗ` of the
differentiation direction times the product over the remaining `r + s`
slots. -/
private lemma crossLeft_gramInv_prod_insertNth_split
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (k l : Fin (Module.finrank ℝ E))
    (i j : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ k l *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a) := by
  rw [show (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (crossDiffSlot r s))
          ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (crossDiffSlot r s)) *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹
            ((Fin.insertNth (crossDiffSlot r s) k i : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((crossDiffSlot r s).succAbove a))
            ((Fin.insertNth (crossDiffSlot r s) l j : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((crossDiffSlot r s).succAbove a))
      from Fin.prod_univ_succAbove _ (crossDiffSlot r s)]
  rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-! ### Reindexing a slot-tuple sum at the differentiation slot

A finite sum over `Fin (r + (s + 1))`-indexed slot tuples is reindexed, through
the tuple-splitting equivalence `Fin.insertNthEquiv` at the differentiation slot
`crossDiffSlot r s`, into an iterated sum over a differentiation index and a
`Fin (r + s)`-indexed slot tuple. -/

/-- Reindexing a sum over `Fin (r + (s + 1))`-indexed slot tuples through the
tuple-splitting equivalence `Fin.insertNthEquiv` at the differentiation slot:
the sum equals the iterated sum over a differentiation index `k` and a
`Fin (r + s)`-indexed slot tuple `i`, of the summand at the assembled tuple
`Fin.insertNth (crossDiffSlot r s) k i`. -/
private lemma crossLeft_sum_reindex_diffSlot (r s : ℕ)
    (F : (Fin (r + (s + 1)) → Fin (Module.finrank ℝ E)) → ℝ) :
    ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
          F (Fin.insertNth (crossDiffSlot r s) k i) := by
  have h1 : ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ ki : Fin (Module.finrank ℝ E) ×
          (Fin (r + s) → Fin (Module.finrank ℝ E)),
        F (Fin.insertNth (crossDiffSlot r s) ki.1 ki.2) :=
    (Equiv.sum_comp
      (Fin.insertNthEquiv (fun _ : Fin (r + (s + 1)) => Fin (Module.finrank ℝ E))
        (crossDiffSlot r s)) F).symm
  rw [h1, Fintype.sum_prod_type]

/-! ### The cross-left metric-isometry bridge -/

/-- **The cross-left metric-isometry bridge.**

For a closed smooth Riemannian manifold `(M, g)`, a smooth scalar `ζ`, and
smooth compactly-supported `(r, s)`-tensor sections `w`, `S`, the
inverse-Gram-weighted cross-left term `tensorCovDerivCrossLeft g r s ζ w S` of
the covariant Leibniz rule — the inverse-Gram-weighted double sum pairing the
exterior derivative `dζ` against the `(r, s)`-tensor pointwise inner product of
the directional covariant derivatives of `w` and the section `S` — equals, at
every point `x`, the genuine one-rank-higher tensor pointwise inner product
`tensorInnerPointwise g r (s + 1)` of the section-level covariant gradient
`covGrad g r s w` and the covector-prepend section `prependCovGradSlot g r s ζ S`.

Both sides are the same metric contraction, written with the `r + (s + 1)`
covariant slots in a different order: the mixed inner product
`tensorInnerPointwise g r (s + 1)` places the differentiation slot at index `r`,
after the `r` lowered upper slots; the cross-left term separates the
differentiation contraction as an outer inverse-Gram-weighted double sum. The
identity holds unconditionally — no extra hypothesis on `w`, `S`, `ζ`, or `x`.

This re-expresses the cross-left term of the covariant Leibniz rule as a
genuine `(r, s + 1)`-tensor pointwise inner product, so that it can be passed to
a limit. -/
theorem tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) := by
  classical
  -- Abbreviations: the inverse Gram matrix, the lowered directional covariant
  -- derivatives of `w`, and the lowered section value of `S`.
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv_def
  set lowW : Fin (Module.finrank ℝ E) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    fun k => lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) k)))
    with hlowW_def
  set lowS : ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (S.toSection x))
    with hlowS_def
  -- The common explicit four-fold inverse-Gram-weighted sum: the
  -- differentiation contraction `(k, l)` wrapped around the genuine `(r, s)`
  -- contraction `(i, j)`, with the covector factor `dζ(eₗ)` on the `l` slot,
  -- and the slot orders arranged as `(k, i, l, j)` to match the
  -- differentiation-slot reindexing of the right-hand side.
  set common : ℝ :=
    ∑ k : Fin (Module.finrank ℝ E),
      ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
            Ginv k l *
              ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                (lowW k) (fun a => (chartModelBasis E) (i a)) *
                  ((extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l)) *
                    lowS (fun a => (chartModelBasis E) (j a))))
    with hcommon_def
  -- Step 1: the left-hand side equals the common sum.
  have hLHS : tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      common := by
    rw [tensorCovDerivCrossLeft_def]
    -- Expand each genuine `(r, s)` pointwise inner product into its explicit
    -- inverse-Gram-weighted sum, and distribute the differentiation weight and
    -- the covector factor.
    have hexpand : ∀ k l : Fin (Module.finrank ℝ E),
        Ginv k l *
            (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) l) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s w x
                    ((chartModelBasis E) k)))
                (S.toFun x)) =
          ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
            ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
              Ginv k l *
                ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                  (lowW k) (fun a => (chartModelBasis E) (i a)) *
                    ((extDerivFun (I := I) (ζ : M → ℝ) x
                        ((chartModelBasis E) l)) *
                      lowS (fun a => (chartModelBasis E) (j a)))) := by
      intro k l
      -- The `(r, s)` pointwise inner product is, by definition, the lowered
      -- covariant `(0, r + s)` pairing of the lowered tensors.
      rw [show tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) k)))
              (S.toFun x) =
            tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (lowW k) lowS from by
        rw [hlowW_def, hlowS_def]
        rfl]
      rw [tensorInnerPointwise_0s_eq_sum]
      -- Associate the two outer scalar factors `Ginv k l` and `dζ(eₗ)` so the
      -- product distributes cleanly over the explicit double sum.
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => hexpand k l))]
    -- The left-hand side now reads `∑_k ∑_l ∑_i ∑_j …`; the common sum reads
    -- `∑_k ∑_i ∑_l ∑_j …`. Commute the `∑_l` and `∑_i` sums.
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  -- Step 2: the right-hand side equals the common sum.
  have hRHS : tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s w).toSection x))
        (TensorRSSpace.toModel
          ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) =
      common := by
    -- Expand the mixed `(r, s + 1)` pointwise inner product into its explicit
    -- inverse-Gram-weighted sum over `Fin (r + (s + 1))`-indexed slot tuples.
    rw [show tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
            (TensorRSSpace.toModel
              ((covGrad (I := I) (M := M) g r s w).toSection x))
            (TensorRSSpace.toModel
              ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)) =
          tensorInnerPointwise_0s (I := I) (M := M) (r + (s + 1)) g x
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((covGrad (I := I) (M := M) g r s w).toSection x)))
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((prependCovGradSlot (I := I) (M := M) g r s ζ S).toSection x)))
        from rfl]
    rw [tensorInnerPointwise_0s_eq_sum]
    -- Reindex the outer `I`-sum at the differentiation slot, via
    -- `Fin.insertNthEquiv`.
    rw [crossLeft_sum_reindex_diffSlot]
    -- Match the reindexed summand to the common-sum summand.
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- Reindex the inner `J`-sum at the differentiation slot.
    rw [crossLeft_sum_reindex_diffSlot]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Split the inverse-Gram product at the differentiation slot, and evaluate
    -- the lowered covariant gradient and the lowered covector-prepend section
    -- on the `insertNth` basis tuples.
    rw [crossLeft_gramInv_prod_insertNth_split (I := I) (M := M) g x r s k l i j]
    rw [crossLeft_lower_covGrad_insertNth_basis (I := I) (M := M) g r s w x k i]
    rw [crossLeft_lower_prependCovGradSlot_insertNth_basis
          (I := I) (M := M) g r s ζ S x l j]
    rw [hlowW_def, hlowS_def]
    ring
  -- Conclude: both sides equal the common sum.
  rw [hLHS, hRHS]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
