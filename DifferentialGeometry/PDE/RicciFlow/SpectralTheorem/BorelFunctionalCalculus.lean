import DifferentialGeometry.PDE.RicciFlow.SpectralTheorem.UnboundedSpectrum
import DifferentialGeometry.PDE.RicciFlow.SpectralTheorem.CayleyTransform
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Borel functional calculus on an unbounded self-adjoint operator

This file constructs `f(A)` for any Borel-measurable function
`f : ℝ → ℂ` and any self-adjoint partially-defined operator
`A : H →ₗ.[ℝ] H` on a real Hilbert space `H`, via pull-back through
the **Cayley transform** `U = cayleyTransform A hA`.

The strategy:

* `U` is a bounded normal operator on the complexification of `H`
  (proved in `CayleyTransform.lean`).
* Mathlib's continuous (and Borel) functional calculus applies to `U`
  out of the box, so we have a `*`-homomorphism
  `C(σ(U), ℂ) → H →L[ℂ] H` (with the spectrum `σ(U)` contained in the
  unit circle).
* The Cayley map `z ↦ i(1 + z)/(1 - z)` is a holomorphic bijection
  between the open unit disc and the upper half plane that extends to
  a homeomorphism between the unit circle (minus `1`) and the real
  line.
* For any Borel `f : ℝ → ℂ`, the composite `g(z) := f(i(1+z)/(1-z))`
  is a Borel function on the unit circle (extended arbitrarily at `1`,
  but `1` is not in the spectrum of `U` when `A` is densely defined).
  We then define `f(A) := g(U)` via Mathlib's CFC on `U`.

The skeleton ships:

* `borelFC A hA f hf : H →L[ℂ] H` for any Borel `f`.
* Bare-signature versions of:
  - `borelFC_const`, the constant law `f(A) = c · I` when `f ≡ c`;
  - `borelFC_id_eq_A`, the identification of `borelFC (id)` with `A`
    itself (as partially-defined operators), in skeleton form;
  - `borelFC_resolvent`, the identification of `borelFC (μ ↦ (λ - μ)⁻¹)`
    with the resolvent `(λ I - A)⁻¹`, in skeleton form.

The genuine analytic content (existence of the CFC for the bounded
normal `U`, the Cayley identification, the spectral mapping theorem on
`U`) is filled in downstream.

## Main definitions

* `borelFC A hA f hf` — `f(A)` for a Borel `f : ℝ → ℂ`.

## Main results

* `borelFC_const` — `borelFC` of the constant function `c` is `c • I`.
* `borelFC_id_eq_A` — placeholder identification `borelFC (id) ≡ A`.
* `borelFC_resolvent` — placeholder identification
  `borelFC (μ ↦ 1/(λ - μ)) ≡ (λ • I - A)⁻¹`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open scoped RealInnerProductSpace InnerProductSpace MeasureTheory

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace SpectralTheorem

/-! ## The Borel functional calculus -/

/-- The **Borel functional calculus** of a self-adjoint
partially-defined operator `A : H →ₗ.[ℝ] H` on a real Hilbert space,
evaluated at a Borel-measurable function `f : ℝ → ℂ`.

Mathematically `borelFC A hA f` is the bounded `ℂ`-linear operator on
the complexification of `H` obtained by applying Mathlib's bounded-
normal continuous (or Borel) functional calculus to the Cayley
transform `U = cayleyTransform A hA`, after pulling `f` back through
the Cayley map `z ↦ i(1+z)/(1-z)` from the unit circle to the real
line.

In the skeleton the body is the zero operator. -/
def borelFC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (_A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint _A)
    (_f : ℝ → ℂ) (_hf : Measurable _f) : H →L[ℂ] H :=
  (0 : H →L[ℂ] H)

/-! ## Algebraic identities for the Borel functional calculus -/

set_option linter.unusedSectionVars false in
/-- **Constant law.** The Borel functional calculus applied to the
constant function `fun _ => c` returns `c • I`, the scalar multiple
of the identity on the complexification of `H`.

This is one of the defining axioms of a functional calculus (a unital
`*`-homomorphism from the bounded Borel functions on the spectrum to
bounded operators sends constants to scalar multiples of the
identity). -/
theorem borelFC_const
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℝ] H) (hA : _root_.IsSelfAdjoint A) (c : ℂ) :
    borelFC A hA (fun _ => c) measurable_const =
      c • (1 : H →L[ℂ] H) := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- **Identity law (skeleton).** The Borel functional calculus applied
to the identity function `id : ℝ → ℝ` (viewed as `ℝ → ℂ` by the
canonical inclusion) returns the original unbounded operator `A` on
its operator domain.

The precise identification is `borelFC A hA (fun μ => (μ : ℂ)) … ≡ A_ℂ`
as partially-defined operators on the complexification of `H`. The
skeleton ships the placeholder `True`; the genuine statement is fixed
downstream once the complexification API and the `LinearPMap`
extension of `borelFC` are committed to. -/
theorem borelFC_id_eq_A
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (_A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint _A) :
    True := by
  trivial

set_option linter.unusedSectionVars false in
/-- **Resolvent law (skeleton).** For every `λ ∈ resolventSet A`, the
Borel functional calculus applied to the resolvent function
`μ ↦ 1/(λ - μ)` returns the resolvent
`(λ • I - A_ℂ)⁻¹` as a bounded operator on the complexification of
`H`.

This is the analytic bridge between the Borel functional calculus
and the classical resolvent operator, and is the main consequence of
the spectral mapping theorem applied through the Cayley correspondence.

The skeleton ships the placeholder `True`; the precise statement is
fixed downstream once the resolvent / inverse API on `LinearPMap` is
committed to. -/
theorem borelFC_resolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint A)
    {lam : ℂ} (_hlam : lam ∈ LinearPMap.resolventSet A) :
    True := by
  trivial

end SpectralTheorem
end RicciFlow
end PDE
end DifferentialGeometry

end
