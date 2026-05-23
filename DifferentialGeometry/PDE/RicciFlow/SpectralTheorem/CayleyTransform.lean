import DifferentialGeometry.PDE.RicciFlow.SpectralTheorem.UnboundedSpectrum
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Unitary

/-!
# Cayley transform of an unbounded self-adjoint operator

This file constructs the **Cayley transform** of a self-adjoint
partially-defined operator `A : H →ₗ.[ℝ] H` on a real Hilbert space
`H`. Concretely, on the complexification `H_ℂ` of `H`, the operator
$$
  U := (A_{\mathbb C} - i\,I)(A_{\mathbb C} + i\,I)^{-1}
$$
is a bounded **unitary** operator on `H_ℂ`. The inverse on the right
is well-defined because `±i` lie in the resolvent set of `A` (see
`SpectralTheorem/UnboundedSpectrum.lean`).

The point of the construction is that `U` is a *bounded normal*
operator on a complex Hilbert space, so Mathlib's continuous and
Borel functional calculi for bounded normal operators apply directly
to `U`. Functions of the original unbounded `A` are then pulled back
through `U` along the **Cayley correspondence** between the open unit
disc and the upper half plane,
$z \leftrightarrow \lambda = i(1 + z)/(1 - z)$.

The skeleton ships:

* `cayleyTransform A hA : H →L[ℂ] H` as a bounded `ℂ`-linear operator
  on `H` itself (we use the implicit identification of `H` with its
  complexification at the type-theoretic level; the genuine
  complexified bounded operator is filled in downstream).
* The headline theorems `cayleyTransform_isUnitary` and
  `cayleyTransform_isNormal`.

## Main definitions

* `cayleyTransform A hA` — the bounded operator `(A - iI)(A + iI)⁻¹`
  on the complexification of `H`.

## Main results

* `cayleyTransform_isUnitary` — the Cayley transform is unitary.
* `cayleyTransform_isNormal` — the Cayley transform is star-normal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open scoped RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace SpectralTheorem

/-! ## The Cayley transform of a self-adjoint unbounded operator

For a complex Hilbert space the Cayley transform `U = (A - i)(A + i)⁻¹`
is the standard correspondence between self-adjoint unbounded operators
and unitaries with `1` not in their point spectrum.

In our setting `H` is a *real* Hilbert space, so the formula
`A - i` already requires moving to the complexification `H_ℂ`. The
skeleton hides this by typing `cayleyTransform` as a bounded
`ℂ`-linear operator on `H` itself: the underlying `ℂ`-module structure
on `H` is the one coming from the canonical complexification
`H ⊗_ℝ ℂ`. Downstream files refine the implementation to use the
explicit `Complexification` machinery without changing the public
type. -/

/-- The **Cayley transform** of a self-adjoint partially-defined
operator `A : H →ₗ.[ℝ] H` on a real Hilbert space `H`.

Mathematically the construction is:

1. Complexify `H` to a complex Hilbert space `H_ℂ`, and complexify
   `A` to a self-adjoint partially-defined operator
   `A_ℂ : H_ℂ →ₗ.[ℂ] H_ℂ`.
2. The complex numbers `±i` lie in the resolvent set of `A_ℂ` (this
   is `LinearPMap.IsSelfAdjoint.{i, neg_i}_mem_resolvent` from
   `UnboundedSpectrum.lean`).
3. Form `U := (A_ℂ - i I) ∘ (A_ℂ + i I)⁻¹`. The right factor inverts
   a bounded everywhere-defined operator, so the composition is a
   bounded operator on all of `H_ℂ`.

The output type `H →L[ℂ] H` packages a bounded `ℂ`-linear endomorphism
of `H` via the implicit `ℂ`-module structure on `H` (which the
downstream file installs from the canonical real-to-complex
extension). In the skeleton the body is the zero operator. -/
def cayleyTransform
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (_A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint _A) : H →L[ℂ] H :=
  (0 : H →L[ℂ] H)

/-! ## Unitarity and normality of the Cayley transform -/

set_option linter.unusedSectionVars false in
/-- **The Cayley transform is unitary.** For any self-adjoint
partially-defined operator `A` on a real Hilbert space, the bounded
operator `U = cayleyTransform A hA` on the complexification satisfies
`star U * U = 1` and `U * star U = 1`, i.e. is unitary as an element
of the `C*`-algebra `H →L[ℂ] H`.

In the Mathlib API this is encoded by the membership
`U ∈ unitary (H →L[ℂ] H)`. -/
theorem cayleyTransform_isUnitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℝ] H) (hA : _root_.IsSelfAdjoint A) :
    cayleyTransform A hA ∈ unitary (H →L[ℂ] H) := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- **The Cayley transform is star-normal.** Every unitary operator
commutes with its adjoint, so the Cayley transform of a self-adjoint
operator is a normal element of the `C*`-algebra `H →L[ℂ] H`.

This is the precise hypothesis required by Mathlib's continuous
functional calculus for bounded normal operators, used in
`SpectralTheorem/BorelFunctionalCalculus.lean` to define `f(A)` for
any continuous (or Borel) function `f : ℝ → ℂ`. -/
instance cayleyTransform_isNormal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℝ] H) (hA : _root_.IsSelfAdjoint A) :
    IsStarNormal (cayleyTransform A hA) := by
  exact sorry

end SpectralTheorem
end RicciFlow
end PDE
end DifferentialGeometry

end
