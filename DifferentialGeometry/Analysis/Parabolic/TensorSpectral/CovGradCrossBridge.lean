import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGrad
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovariantLeibniz

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

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
