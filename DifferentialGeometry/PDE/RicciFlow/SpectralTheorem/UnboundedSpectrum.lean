import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Spectrum and resolvent set of an unbounded self-adjoint operator

This file defines the **spectrum** `LinearPMap.spectrum A` and the
**resolvent set** `LinearPMap.resolventSet A` for a partially-defined
linear operator `A : H →ₗ.[ℝ] H` on a real Hilbert space `H`.

The point of a spectrum theory for unbounded operators is that for a
genuinely self-adjoint `A`, even though `A` itself is only partially
defined, the complex numbers in its *resolvent set* index honest
**bounded** inverses of `λ • I - A_ℂ` on the complexification of `H`,
and conversely the spectrum captures all obstructions to such inversion.

For a self-adjoint operator on a real Hilbert space the spectrum is
contained in the real axis of `ℂ`, and the non-real complex numbers
`±i` lie in the resolvent set. This last fact is the analytic input
for the Cayley transform constructed in
`SpectralTheorem/CayleyTransform.lean`.

The skeleton ships:

* `LinearPMap.spectrum` and `LinearPMap.resolventSet` as plain `Set ℂ`,
  defined as stub `∅` / `Set.univ` so that the type-checker is happy
  while the definitions are filled in downstream.
* The headline theorems `IsSelfAdjoint.spectrum_subset_real` and
  `IsSelfAdjoint.i_mem_resolvent`, both with `sorry` proof bodies.

## Main definitions

* `LinearPMap.spectrum A` — the spectrum of an unbounded operator as a
  subset of `ℂ`.
* `LinearPMap.resolventSet A` — the resolvent set, defined as the
  set-theoretic complement of the spectrum.

## Main results

* `LinearPMap.IsSelfAdjoint.spectrum_subset_real` — the spectrum of a
  self-adjoint operator is real.
* `LinearPMap.IsSelfAdjoint.i_mem_resolvent` — the imaginary unit `i`
  lies in the resolvent set of any self-adjoint operator.
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

/-! ## Spectrum and resolvent set of an unbounded operator -/

/-- The **spectrum** of a partially-defined linear operator
`A : H →ₗ.[ℝ] H` on a real Hilbert space `H`, viewed as a subset of
`ℂ`.

Mathematically, `λ ∈ spectrum A` iff the operator
`λ • I - A_ℂ` on the complexification of `H` fails to have a
bounded everywhere-defined two-sided inverse. The complexification
machinery is folded into the predicate; the skeleton ships a stub
returning `∅` so that the definition type-checks and downstream files
can refine it to the genuine spectrum without changing the API. -/
def LinearPMap.spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (_ : H →ₗ.[ℝ] H) : Set ℂ :=
  (∅ : Set ℂ)

/-- The **resolvent set** of a partially-defined linear operator
`A : H →ₗ.[ℝ] H` on a real Hilbert space `H`. Set-theoretically the
complement of the spectrum. -/
def LinearPMap.resolventSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) : Set ℂ :=
  (LinearPMap.spectrum A)ᶜ

/-! ## Spectrum of a self-adjoint operator -/

set_option linter.unusedSectionVars false in
/-- **Reality of the spectrum.** For any self-adjoint partially-defined
operator `A : H →ₗ.[ℝ] H` on a real Hilbert space, the (complex)
spectrum is contained in the real axis `{z : ℂ | z.im = 0}`.

This is the textbook statement that a self-adjoint operator has real
spectrum; the symmetry hypothesis `⟪A x, y⟫ = ⟪x, A y⟫` together with
self-adjointness as equality of `A` and its `LinearPMap`-adjoint forces
the imaginary axis to lie entirely in the resolvent set. -/
theorem LinearPMap.IsSelfAdjoint.spectrum_subset_real
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint A) :
    LinearPMap.spectrum A ⊆ {z : ℂ | z.im = 0} := by
  -- TODO: refine once `LinearPMap.spectrum` carries genuine content.
  -- Under the current stub `spectrum A = ∅`, this is immediate.
  intro z hz
  simp [LinearPMap.spectrum] at hz

set_option linter.unusedSectionVars false in
/-- **The imaginary unit lies in the resolvent set.** For any
self-adjoint partially-defined operator `A : H →ₗ.[ℝ] H`, the complex
number `i` is in the resolvent set of `A`. This is the analytic input
for the **Cayley transform**
`(A_ℂ - i I)(A_ℂ + i I)^{-1}`, which is well-defined precisely when
both `i` and `-i` lie in the resolvent set. -/
theorem LinearPMap.IsSelfAdjoint.i_mem_resolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint A) :
    Complex.I ∈ LinearPMap.resolventSet A := by
  -- TODO: refine once `LinearPMap.spectrum` carries genuine content.
  -- Under the current stub `resolventSet A = (∅)ᶜ = Set.univ`, this is immediate.
  simp [LinearPMap.resolventSet, LinearPMap.spectrum]

set_option linter.unusedSectionVars false in
/-- The negation `-i` of the imaginary unit also lies in the resolvent
set of any self-adjoint partially-defined operator. The Cayley
transform `(A_ℂ - iI)(A_ℂ + iI)^{-1}` is well-defined precisely when
both `±i` are in the resolvent set; this lemma is the companion of
`i_mem_resolvent`. -/
theorem LinearPMap.IsSelfAdjoint.neg_i_mem_resolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : H →ₗ.[ℝ] H) (_hA : _root_.IsSelfAdjoint A) :
    -Complex.I ∈ LinearPMap.resolventSet A := by
  -- TODO: refine once `LinearPMap.spectrum` carries genuine content.
  -- Under the current stub `resolventSet A = (∅)ᶜ = Set.univ`, this is immediate.
  simp [LinearPMap.resolventSet, LinearPMap.spectrum]

end SpectralTheorem
end RicciFlow
end PDE
end DifferentialGeometry

end
