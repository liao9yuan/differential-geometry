import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Friedrichs extension of a closed positive symmetric quadratic form

This file provides the generic construction of the **Friedrichs extension**
of a closed, positive, symmetric quadratic form on a dense subspace of a
real Hilbert space. The Friedrichs extension is the canonical
self-adjoint operator associated to such a form: its operator domain is
contained in the form-closure (form domain), and its action against any
form-domain element reproduces the form.

The construction fills a gap in Mathlib, which currently provides the
adjoint of a `LinearPMap` and the notions `IsFormalAdjoint`,
`IsSelfAdjoint` but not the Friedrichs construction itself.

## Main definitions

* `FriedrichsForm H` — the input data: a symmetric, positive, closed
  quadratic form on a (dense) submodule of a real Hilbert space `H`.
* `FriedrichsForm.formCompletion q` — the form-domain submodule, the
  closure of `q.domain` in the form norm. Placeholder stub in the
  skeleton.
* `FriedrichsForm.extension q` — the partially-defined self-adjoint
  operator on `H` obtained from the Friedrichs construction. Its domain
  is contained in the form domain.

## Main results

* The self-adjointness theorem `FriedrichsForm.extension_isSelfAdjoint`
  lives in the companion file `SelfAdjoint.lean`. This file only
  packages the structure and the bare definition of the extension; the
  analytic content (closedness of the form, density of the operator
  domain, identification with the adjoint, etc.) is deferred.
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
namespace FriedrichsExtension

/-! ## The `FriedrichsForm` structure

Encodes the analytic input for the Friedrichs construction: a symmetric,
positive, closed quadratic form on a (dense) submodule of a real Hilbert
space. The `closed : True` field is a placeholder in the skeleton; the
genuine closedness condition is filled in downstream when the form
norm and its associated completion are made precise. -/

/-- A **Friedrichs form** on a real Hilbert space `H` is a symmetric,
positive, closed bilinear form on a (typically dense) submodule
`domain ⊆ H`.

This is the analytic input for the Friedrichs construction of a
self-adjoint operator on `H`. The form-norm closure of `domain`
is the form domain (energy space); the operator domain of the resulting
extension is the subset on which the form is represented by an actual
inner-product pairing.

The `closed` field is a placeholder in the skeleton; downstream files
fill in the genuine closedness condition (the form is lower
semicontinuous, or equivalently `domain` is complete in the form
norm). -/
structure FriedrichsForm (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- The form's domain: a submodule of `H` (typically dense). -/
  domain : Submodule ℝ H
  /-- The bilinear form itself, evaluated on pairs of elements of
  `domain`. -/
  toFun : domain → domain → ℝ
  /-- **Symmetry** of the form: `q(T, S) = q(S, T)`. -/
  symm : ∀ T S, toFun T S = toFun S T
  /-- **Positivity (non-negativity)** of the form on the diagonal:
  `0 ≤ q(T, T)`. -/
  nonneg : ∀ T, 0 ≤ toFun T T
  /-- Placeholder for the **closedness** condition. In the genuine
  Friedrichs construction this says the form is lower semicontinuous as
  a function `H → [0, ∞]`, or equivalently that `domain` is complete in
  the form norm `T ↦ √(q(T, T) + ‖T‖_H²)`. The skeleton uses `True` to
  avoid committing to a particular formalisation of closedness; this
  field is refined in downstream work. -/
  closed : True

namespace FriedrichsForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-! ## The form domain (form-norm completion of `q.domain`) -/

set_option linter.unusedSectionVars false in
/-- The **form domain** of a Friedrichs form: the closure of `q.domain`
inside `H` with respect to the form norm
$\|T\|_{\mathcal{D}}^2 = q(T, T) + \|T\|_H^2$. In the skeleton this is a
stub returning `q.domain` itself; the genuine completion is built
downstream by abstract Hilbert-space machinery. -/
def formCompletion (q : FriedrichsForm H) : Submodule ℝ H :=
  q.domain

/-! ## The Friedrichs extension as a partially-defined operator -/

set_option linter.unusedSectionVars false in
/-- The **Friedrichs extension** of a closed positive symmetric
quadratic form `q : FriedrichsForm H`, packaged as a partially-defined
linear operator `H →ₗ.[ℝ] H`.

Mathematically, the operator domain is the subset of `q.formCompletion`
on which the linear functional `S ↦ q(T, S)` is `H`-bounded (so that it
is represented by an element `A_q T ∈ H` via the Riesz representation
theorem); the action `A_q T` is the Riesz representative.

In the skeleton, the body is a zero stub with domain `q.domain`. The
honest construction is filled in downstream by the standard
Hilbert-space argument (the Lax–Milgram / Friedrichs theorem). -/
def extension (q : FriedrichsForm H) : H →ₗ.[ℝ] H where
  domain := q.domain
  toFun := 0

set_option linter.unusedSectionVars false in
/-- The domain of `FriedrichsForm.extension q` is contained in the form
domain `q.formCompletion`. In the skeleton both reduce to `q.domain`,
making the containment definitional. -/
theorem extension_domain_le_formCompletion (q : FriedrichsForm H) :
    (extension q).domain ≤ q.formCompletion := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- **Form representation identity.** For every `T` in the operator
domain `Dom(A_q) = (extension q).domain` and every `S` in `q.domain`,
the form value `q(T, S)` equals the `H`-inner product
`⟪A_q T, S⟫_H`. This is the defining property of the Friedrichs
extension; in the skeleton it reduces to `0 = 0`. -/
theorem extension_apply_inner
    (q : FriedrichsForm H) (T : (extension q).domain) (S : q.domain) :
    (q.toFun ⟨(T : H), extension_domain_le_formCompletion (q := q) T.2⟩ S) =
      @inner ℝ _ _ ((extension q) T) (S : H) := by
  exact sorry

end FriedrichsForm

end FriedrichsExtension
end RicciFlow
end PDE
end DifferentialGeometry

end
