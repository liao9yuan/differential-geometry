import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.Construction
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.FormDirichlet
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.Symmetric
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.NegSemiBounded
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Self-adjointness of the Friedrichs extension

This file states the headline self-adjointness theorem for the
generic `FriedrichsForm.extension` constructed in
`Construction.lean`, and then specialises it to the Dirichlet form of
the connection Laplacian `Δ_∇` on the metric `L²` Hilbert space of
`(r, s)`-tensor fields.

## Main results (generic)

* `FriedrichsForm.extension_isSelfAdjoint` — the partially-defined
  operator `FriedrichsForm.extension q` on `H` is self-adjoint in the
  sense of `LinearPMap.IsSelfAdjoint`.

## Main definitions (specialised)

* `connLaplacianL2_friedrichs g r s` — the Friedrichs extension of the
  Dirichlet form of the connection Laplacian, packaged as a
  partially-defined operator on `TensorL2 r s g`.

## Main results (specialised)

* `connLaplacianL2_friedrichs_isSelfAdjoint` — the Friedrichs
  extension of the connection-Laplacian Dirichlet form is
  self-adjoint.
* `connLaplacianL2_le_friedrichs` — the original partially-defined
  operator `connLaplacianL2 g r s` (acting on smooth, compactly-supported
  sections) is contained in its Friedrichs extension, in the
  `LinearPMap` partial order.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace FriedrichsExtension

/-! ## Self-adjointness of the generic Friedrichs extension -/

set_option linter.unusedSectionVars false in
/-- **Self-adjointness of the Friedrichs extension.** The
partially-defined operator `FriedrichsForm.extension q` on `H` produced
by the Friedrichs construction from a closed, positive, symmetric
quadratic form `q` is self-adjoint.

This is the textbook Friedrichs theorem: every closed, positive,
symmetric form on a dense subspace of a Hilbert space arises as the
form `T ↦ ⟪A T, T⟫` of a unique self-adjoint operator `A` whose form
domain is the form-closure of the original domain. -/
theorem FriedrichsForm.extension_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (q : FriedrichsForm H) :
    _root_.IsSelfAdjoint (FriedrichsForm.extension q) := by
  exact sorry

end FriedrichsExtension
end RicciFlow
end PDE
end DifferentialGeometry

/-! ## Specialisation to the connection-Laplacian Dirichlet form -/

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The Friedrichs form attached to the connection Laplacian -/

set_option linter.unusedSectionVars false in
/-- The Dirichlet form `dirichletForm g r s`, repackaged as a
`FriedrichsForm` on the `L²` Hilbert space `TensorL2 r s g`.

The domain is the canonical image submodule
`smoothCcToL2Submodule g r s` of smooth, compactly-supported
`(r, s)`-tensor sections under the dense embedding
`SmoothCcTensor.toL2`. In the skeleton, the bilinear form is the zero
form (mirroring the skeleton `dirichletForm`); downstream files lift the
honest Dirichlet form and prove its symmetry / positivity / closedness
from the `dirichletForm` lemmas of `FormDirichlet.lean`. -/
def connDirichletFriedrichsForm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    FriedrichsExtension.FriedrichsForm (TensorL2 r s g) where
  domain := smoothCcToL2Submodule (I := I) g r s
  toFun _ _ := 0
  symm _ _ := rfl
  nonneg _ := le_refl _
  closed := trivial

/-! ## The Friedrichs extension of the connection Laplacian -/

set_option linter.unusedSectionVars false in
/-- The **Friedrichs extension** of the connection (rough) Laplacian
`Δ_∇` on the metric `L²` Hilbert space of `(r, s)`-tensor fields,
obtained by applying the generic `FriedrichsForm.extension` construction
to the Dirichlet form `connDirichletFriedrichsForm g r s`.

The output is a partially-defined operator
`TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g` whose domain contains
the original smooth-compactly-supported domain of `connLaplacianL2 g r s`
and which is self-adjoint (see
`connLaplacianL2_friedrichs_isSelfAdjoint`). -/
def connLaplacianL2_friedrichs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g :=
  FriedrichsExtension.FriedrichsForm.extension
    (connDirichletFriedrichsForm (I := I) g r s)

set_option linter.unusedSectionVars false in
/-- **Self-adjointness of the Friedrichs extension of `Δ_∇`.** The
partially-defined operator `connLaplacianL2_friedrichs g r s` on
`TensorL2 r s g` is self-adjoint.

This is the immediate specialisation of
`FriedrichsForm.extension_isSelfAdjoint` to the Dirichlet form of the
connection Laplacian. -/
theorem connLaplacianL2_friedrichs_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    _root_.IsSelfAdjoint (connLaplacianL2_friedrichs (I := I) g r s) := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- **Friedrichs extension contains the original operator.** In the
partial order `≤` on `LinearPMap` (graph inclusion), the original
partially-defined operator `connLaplacianL2 g r s` is contained in its
Friedrichs extension `connLaplacianL2_friedrichs g r s`. This expresses
that the Friedrichs construction genuinely extends the action of `Δ_∇`
from the smooth, compactly-supported domain to the larger (form-
completion) domain on which self-adjointness holds. -/
theorem connLaplacianL2_le_friedrichs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    connLaplacianL2 (I := I) g r s ≤
      connLaplacianL2_friedrichs (I := I) g r s := by
  exact sorry

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
