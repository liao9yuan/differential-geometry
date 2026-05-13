import DifferentialGeometry.Integral.Connection.HomBundleNabla
import DifferentialGeometry.Integral.Connection.Tensor0SNabla

/-!
# Covariant derivative on the (r,s)-tensor bundle

Given a `CovariantDerivative cov` on the tangent bundle `TM` (of class `C^∞`), this file
constructs the bundled `CovariantDerivative` on the `(r, s)`-tensor bundle
`fun x => TensorRSSpace r s I x = Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x`.

## Strategy

The (r,s)-tensor bundle is by definition the Hom-bundle from the `(0,r)`-tensor bundle
to the `(0,s)`-tensor bundle. Using the recursive covariant derivative on the `(0,r)`-
and `(0,s)`-tensor bundles (from `Tensor0SNabla.lean`), the induced covariant derivative
on `Hom(T^0_r M, T^0_s M)` is obtained as a direct specialization of the generic
Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` (from `GenHomNabla.lean`).

## Main declarations

* `tensorRSCovariantDerivative r s cov` : the bundled `CovariantDerivative` on the
  `(r, s)`-tensor bundle, built from the induced covariant derivatives on `(0,r)`- and
  `(0,s)`-tensors.
* `tensorRSCovariantDerivative_contMDiff r s cov` : smoothness instance.
* `tensorRSCovariantDerivative_apply` : the pointwise product-rule formula
  `(∇^{(r,s)}_v τ)(w) = (∇^{(0,s)}_v (τ w)) − τ (∇^{(0,r)}_v w)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace TensorRSNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The bundled `(r, s)`-tensor covariant derivative

Specialization of the generic Hom-bundle covariant derivative
(`HomConnectionGen.homBundleCovariantDerivativeGen`) to `U = Tensor0SSpace r` and
`V = Tensor0SSpace s`.

The two ingredient covariant derivatives are:

* `Tensor0SNabla.tensor0SCovariantDerivative I M r cov` on the `(0,r)`-tensor bundle.
* `Tensor0SNabla.tensor0SCovariantDerivative I M s cov` on the `(0,s)`-tensor bundle.

Both come with `ContMDiffCovariantDerivative ∞` instances established in
`Tensor0SNabla.lean`. -/

/-- The `(r, s)`-tensor bundle covariant derivative obtained by specializing the generic
Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` to
`U = Tensor0SSpace r` (source) and `V = Tensor0SSpace s` (target). -/
noncomputable def tensorRSCovariantDerivative (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

/-- Smoothness of `tensorRSCovariantDerivative`: inherited from the `C^∞` instances of the
underlying `(0,r)`- and `(0,s)`-tensor covariant derivatives via the generic Hom-bundle
smoothness instance. -/
noncomputable instance tensorRSCovariantDerivative_contMDiff (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (tensorRSCovariantDerivative I M r s cov) ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)

/-! ### Pointwise apply lemma -/

/-- Pointwise characterization of `tensorRSCovariantDerivative`. For a smooth `(r,s)`-tensor
section `τ` and a smooth `(0,r)`-tensor section `w`, the value of the covariant derivative
applied bilinearly to a tangent vector `v ∈ T_xM` and `w x ∈ Tensor0SSpace r I x` is

`cov_s (fun y => τ y (w y)) x v − τ x (cov_r w x v)`,

which is the standard product-rule formula

`(∇^(r,s)_v τ)(w x) = ∇^(0,s)_v (τ · w) − τ (∇^(0,r)_v w)`.

Here `cov_r` and `cov_s` abbreviate the induced covariant derivatives on the `(0,r)`- and
`(0,s)`-tensor bundles respectively. -/
theorem tensorRSCovariantDerivative_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M r s cov τ x v) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov
        (fun y =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from τ y) (w y)) x v -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
        (Tensor0SNabla.tensor0SCovariantDerivative I M r cov w x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
    (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
    (Tensor0SNabla.tensor0SCovariantDerivative I M r cov)
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov)
    τ w x v

/-! ### Compile-time sanity checks

Given a `C^∞` covariant derivative on `TM`, the specialization produces a `C^∞`
covariant derivative on the `(r,s)`-tensor bundle for a range of `(r,s)` pairs. -/

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel 1 2 ℝ E)
      (fun x : M => TensorRSSpace 1 2 I x) :=
  tensorRSCovariantDerivative I M 1 2 cov

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (tensorRSCovariantDerivative I M 1 2 cov) ∞ :=
  inferInstance

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (TensorRSModel 2 1 ℝ E)
      (fun x : M => TensorRSSpace 2 1 I x) :=
  tensorRSCovariantDerivative I M 2 1 cov

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative
      (tensorRSCovariantDerivative I M 2 1 cov) ∞ :=
  inferInstance

end TensorRSNabla

end
