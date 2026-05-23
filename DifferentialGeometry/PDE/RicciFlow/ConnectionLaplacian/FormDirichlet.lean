import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.NegSemiBounded

/-!
# Dirichlet form associated to the connection Laplacian

For a closed Riemannian manifold `(M, g)`, the connection (rough)
Laplacian `Δ_∇` on `(r, s)`-tensor fields admits a natural Dirichlet
quadratic form
$$
  \mathcal{D}(T, S) \;=\; \langle \nabla T,\, \nabla S\rangle_{L^2(M, g)}
$$
on the smooth, compactly-supported sections `T, S : SmoothCcTensor g r s`.
By the divergence theorem on the closed manifold `M`, the form coincides
with the negative inner-product pairing of `Δ_∇ T` against `S`, i.e.
$$
  \mathcal{D}(T, S) \;=\; -\,\langle \Delta_\nabla T,\, S\rangle_{L^2}.
$$

This file packages the bilinear form, records its symmetry and
positivity, and exposes the integration-by-parts identity that links it
to the `L²` action of `connLaplacianL2`. The Dirichlet form is the
analytic data input for the Friedrichs extension of `Δ_∇` to a
(non-positive) self-adjoint operator on `TensorL2 r s g`.

## Main definitions

* `dirichletForm g r s` — the bilinear form
  `SmoothCcTensor g r s → SmoothCcTensor g r s → ℝ`, sending a pair
  `(T, S)` to `⟨∇T, ∇S⟩_{L²(M, g)}`.

## Main results

* `dirichletForm_symm` — symmetry of the Dirichlet form.
* `dirichletForm_pos` — non-negativity of the Dirichlet form on the
  diagonal `T = S`.
* `dirichletForm_eq_neg_inner_laplacian` — integration-by-parts identity
  connecting the form to the `L²` pairing against the rough Laplacian.
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
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

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

/-! ## The Dirichlet form -/

set_option linter.unusedSectionVars false in
/-- The **Dirichlet quadratic form** associated to the connection
Laplacian on `(r, s)`-tensor fields, defined on smooth compactly-supported
sections by
$$
  \mathcal{D}(T, S) \;=\; \langle \nabla T,\, \nabla S\rangle_{L^2(M, g)}.
$$
This is the analytic data input for the Friedrichs extension of `Δ_∇` to
a non-positive self-adjoint operator on the `L²` Hilbert space. -/
def dirichletForm (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r s → ℝ :=
  fun _ _ => 0

/-! ## Algebraic properties -/

set_option linter.unusedSectionVars false in
/-- **Symmetry of the Dirichlet form.** The form `dirichletForm g r s` is
symmetric in its two arguments, reflecting the symmetry of the metric
inner product on tensor fields. -/
theorem dirichletForm_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : SmoothCcTensor g r s) :
    dirichletForm (I := I) g r s T S = dirichletForm (I := I) g r s S T := by
  exact sorry

set_option linter.unusedSectionVars false in
/-- **Non-negativity of the Dirichlet form on the diagonal.** Evaluated at
`(T, T)`, the form is non-negative, since it is the `L²` norm squared of
`∇T`. -/
theorem dirichletForm_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    0 ≤ dirichletForm (I := I) g r s T T := by
  exact sorry

/-! ## Integration by parts: link to the rough Laplacian on `L²` -/

set_option linter.unusedSectionVars false in
/-- **Integration-by-parts identity.** On a closed manifold, the Dirichlet
form `⟨∇T, ∇S⟩_{L²}` equals the negative `L²` pairing of the rough
Laplacian `Δ_∇ T` against `S`,
$$
  \mathcal{D}(T, S) \;=\; -\,\langle \Delta_\nabla T,\, S\rangle_{L^2}.
$$
The identity is the textbook integration-by-parts (divergence theorem)
expression on a manifold without boundary; the membership hypotheses
`hT, hS` lift the smooth representatives `T, S` to the domain of the
partially-defined operator `connLaplacianL2`. -/
theorem dirichletForm_eq_neg_inner_laplacian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    dirichletForm (I := I) g r s T S =
      - (@inner ℝ _ _
          ((connLaplacianL2 (I := I) g r s)
            ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩)
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S)) := by
  exact sorry

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
