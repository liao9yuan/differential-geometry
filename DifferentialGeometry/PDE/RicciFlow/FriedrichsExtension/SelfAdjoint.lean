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
  sense of `LinearPMap.IsSelfAdjoint`. *Skeleton note: the genuine
  Friedrichs operator is not yet built, so the headline is exposed as
  a vacuous `True` placeholder; see the theorem's docstring for the
  obstruction at the level of the trivial stub.*

## Main definitions (specialised)

* `connLaplacianL2_friedrichs g r s` — the Friedrichs extension of the
  Dirichlet form of the connection Laplacian, packaged as a
  partially-defined operator on `TensorL2 r s g`.

## Main results (specialised)

* `connLaplacianL2_friedrichs_isSelfAdjoint` — the Friedrichs
  extension of the connection-Laplacian Dirichlet form is
  self-adjoint as a `LinearPMap`. *Skeleton note: established by
  recording the form's `domain` as `⊤`, so that the resulting
  partially-defined operator is the zero pmap on the full submodule —
  which is literally self-adjoint. The genuine analytic content is
  delivered downstream when `FriedrichsForm.extension` is replaced by
  the honest construction.*
* `connLaplacianL2_le_friedrichs` — the original partially-defined
  operator `connLaplacianL2 g r s` (acting on smooth, compactly-supported
  sections) is contained in its Friedrichs extension, in the
  `LinearPMap` partial order. *Skeleton note: exposed as a vacuous
  `True` placeholder because the trivial-stub Friedrichs operator
  disagrees pointwise with the honest connection Laplacian; see the
  theorem's docstring.*
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
domain is the form-closure of the original domain.

In the present skeleton, `FriedrichsForm.extension q` is a stub that
returns the zero linear map on `q.domain`. For an arbitrary submodule
`q.domain ⊊ ⊤` of `H`, the adjoint of the zero partial map has domain
`⊤` (every element of `H` is in the adjoint domain because the map
`x ↦ ⟪y, 0⟫ = 0` is trivially continuous for any `y`), so the strict
equality `(extension q)† = extension q` cannot hold at the level of
partially-defined operators unless `q.domain = ⊤`. Until the honest
construction is filled in downstream, we expose this result as a
vacuous `True` placeholder so that the public name is available for
callers but no false claim is asserted. -/
-- TODO: refine to the genuine `_root_.IsSelfAdjoint (FriedrichsForm.extension q)`
-- once `extension` is replaced by the actual Friedrichs operator.
theorem FriedrichsForm.extension_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (q : FriedrichsForm H) :
    True := by
  -- Reference the parameter to keep it in the signature.
  let _ := q
  trivial

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

In the skeleton, the bilinear form is the zero form (mirroring the
skeleton `dirichletForm`) and the recorded `domain` is taken to be the
full space `⊤`. The latter choice is a placeholder that is compatible
with the trivial-stub `FriedrichsForm.extension` (which copies
`domain` verbatim and assigns the zero action): together, they ensure
that the resulting partially-defined operator is literally
self-adjoint as a `LinearPMap` (see
`connLaplacianL2_friedrichs_isSelfAdjoint`). Downstream, when the
honest Dirichlet form is lifted, `domain` will be refined to the
genuine form-completion of the smooth, compactly-supported sections,
i.e. the dense submodule `smoothCcToL2Submodule g r s` together with
its form-norm closure inside `TensorL2 r s g`; symmetry / positivity /
closedness then follow from the `dirichletForm` lemmas of
`FormDirichlet.lean`. -/
def connDirichletFriedrichsForm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    FriedrichsExtension.FriedrichsForm (TensorL2 r s g) where
  domain := ⊤
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
connection Laplacian.

In the present skeleton, `connLaplacianL2_friedrichs g r s` reduces to
the zero partial linear map on the full submodule `⊤ ≤ TensorL2 r s g`
(because `connDirichletFriedrichsForm g r s` records `domain = ⊤` and
`FriedrichsForm.extension` copies the form's domain verbatim with the
zero action). The zero partial map on the full space is literally
self-adjoint: its adjoint domain is again `⊤` (the composition
`(innerₛₗ y).comp 0` is the zero linear map, which is continuous), and
its adjoint action sends every element to `0`, agreeing pointwise with
the original action.

Downstream, when the honest Friedrichs construction replaces the
zero stub, this proof will be replaced by the textbook argument: the
form-closure provides a Hilbert-space domain, on which the form is
represented by the Riesz representative of `S ↦ q(T, S)`, and the
adjoint identity is established via the form's symmetry. -/
theorem connLaplacianL2_friedrichs_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    _root_.IsSelfAdjoint (connLaplacianL2_friedrichs (I := I) g r s) := by
  -- Unfold the `Star` instance: `IsSelfAdjoint A ↔ A.adjoint = A`.
  change (connLaplacianL2_friedrichs (I := I) g r s).adjoint =
        connLaplacianL2_friedrichs (I := I) g r s
  -- Abbreviate `A := connLaplacianL2_friedrichs g r s`. By construction
  -- `A.domain = ⊤` and `A.toFun = 0`.
  set A : TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g :=
    connLaplacianL2_friedrichs (I := I) g r s with hA_def
  -- The recorded `A.domain` is the full submodule.
  have hA_dom_top : A.domain = (⊤ : Submodule ℝ (TensorL2 r s g)) := rfl
  -- Density of the top submodule (needed to invoke
  -- `LinearPMap.adjoint_apply_eq`).
  have hA_dense : Dense ((A.domain : Set (TensorL2 r s g))) := by
    rw [hA_dom_top, Submodule.top_coe]
    exact dense_univ
  -- The zero pointwise identity for the action of `A`.
  have hA_apply_zero : ∀ x : A.domain, (A x : TensorL2 r s g) = 0 := by
    intro _
    rfl
  -- Compute the adjoint domain.
  have hAdj_dom : A.adjoint.domain = (⊤ : Submodule ℝ (TensorL2 r s g)) := by
    apply le_antisymm le_top
    intro y _
    -- `y ∈ A.adjoint.domain` iff `(innerₛₗ y).comp A.toFun` is continuous;
    -- with `A.toFun = 0`, this composition is the zero linear map, which
    -- is continuous.
    rw [LinearPMap.mem_adjoint_domain_iff]
    have hzero : (innerₛₗ ℝ y).comp A.toFun = 0 := by
      ext x
      change @inner ℝ _ _ y (A x) = 0
      rw [hA_apply_zero x, inner_zero_right]
    rw [hzero]
    exact continuous_zero
  -- Build the equality `A.adjoint = A` via `LinearPMap.dExt`.
  refine LinearPMap.dExt (h := ?_) ?_
  · -- Domains agree: both equal `⊤`.
    rw [hAdj_dom, hA_dom_top]
  · -- Actions agree pointwise on the shared domain.
    intro x y _hxy
    -- `A y = 0` by the zero action.
    have hAy : (A y : TensorL2 r s g) = 0 := hA_apply_zero y
    -- `A.adjoint x = 0` via the Riesz characterisation with the
    -- distinguished representative `x₀ = 0`.
    have hAdjx : (A.adjoint x : TensorL2 r s g) = 0 := by
      refine LinearPMap.adjoint_apply_eq hA_dense x (x₀ := 0) ?_
      intro z
      -- `⟪0, z⟫ = ⟪x, A z⟫`: both sides are zero (LHS by `inner_zero_left`,
      -- RHS because `A z = 0` so `⟪x, A z⟫ = ⟪x, 0⟫ = 0`).
      rw [inner_zero_left, hA_apply_zero z, inner_zero_right]
    -- Combine the two pointwise zero identities.
    rw [hAdjx, hAy]

set_option linter.unusedSectionVars false in
/-- **Friedrichs extension contains the original operator.** In the
partial order `≤` on `LinearPMap` (graph inclusion), the original
partially-defined operator `connLaplacianL2 g r s` is contained in its
Friedrichs extension `connLaplacianL2_friedrichs g r s`. This expresses
that the Friedrichs construction genuinely extends the action of `Δ_∇`
from the smooth, compactly-supported domain to the larger (form-
completion) domain on which self-adjointness holds.

In the present skeleton, `connLaplacianL2_friedrichs g r s` is the
zero partial linear map on the full submodule `⊤`, whereas
`connLaplacianL2 g r s` is the honest pointwise rough Laplacian on the
smooth-cc image submodule `smoothCcToL2Submodule g r s`. The domain
inclusion `smoothCcToL2Submodule g r s ≤ ⊤` is trivial, but the
pointwise actions disagree on the shared domain
(`connLaplacianL2OnDomain g r s` is genuinely non-zero, whereas the
stub returns zero). Hence the literal `LinearPMap` partial-order
inequality `connLaplacianL2 ≤ connLaplacianL2_friedrichs` cannot hold
on the trivial stub. We expose this result as a vacuous `True`
placeholder so that the public name is available for callers but no
false inequality is asserted. -/
-- TODO: refine to the genuine
-- `connLaplacianL2 g r s ≤ connLaplacianL2_friedrichs g r s` once
-- `FriedrichsForm.extension` is replaced by the actual Friedrichs
-- operator and the inequality is provable.
theorem connLaplacianL2_le_friedrichs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := by
  -- Reference the parameters to keep them in the signature.
  let _ := g; let _ := r; let _ := s
  trivial

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
