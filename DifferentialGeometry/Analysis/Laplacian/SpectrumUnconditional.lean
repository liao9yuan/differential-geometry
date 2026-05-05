import DifferentialGeometry.Analysis.Laplacian.Spectrum
import DifferentialGeometry.Analysis.Laplacian.Compactness

/-!
# Unconditional spectral theorems for the L²-side resolvent

For a closed Riemannian manifold `(M, g)`, the L²-side resolvent operator
of the variational Laplacian is a compact, self-adjoint operator on
`Lp ℝ 2 μ_g`. Combined with `Compactness.lean` (which proves compactness
unconditionally) the conditional spectral theorems become unconditional.

This file repackages those theorems by discharging the
`IsCompactOperator (resolventL2 g)` hypothesis using
`resolventL2_isCompactOperator`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)]

/-! ## Unconditional finite-dimensionality of nonzero eigenspaces -/

/-- **Finite-dimensionality of nonzero resolvent eigenspaces, unconditional.**
For a closed Riemannian manifold `(M, g)`, every eigenspace of
`resolventL2 g` at a non-zero scalar is finite-dimensional.

This is the unconditional version of the corresponding conditional
result, with the compactness hypothesis discharged via
`resolventL2_isCompactOperator`. -/
theorem resolventEigenspace_finiteDim_unconditional
    (g : SmoothRiemannianMetric I M)
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (resolventEigenspace (I := I) (M := M) g μ) :=
  resolventEigenspace_finiteDim (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g) hμ

/-! ## Unconditional spectral totality -/

/-- **Spectral totality, unconditional.** For a closed Riemannian manifold
`(M, g)`, the eigenspaces of `resolventL2 g` span a dense subspace of
`Lp ℝ 2 μ_g`: the orthogonal complement of their supremum is trivial.

This is the unconditional version of the corresponding conditional
result, with the compactness hypothesis discharged via
`resolventL2_isCompactOperator`. -/
theorem resolventEigenspaces_iSup_orthogonal_eq_bot_unconditional
    (g : SmoothRiemannianMetric I M) :
    (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ)ᗮ = ⊥ :=
  resolventEigenspaces_iSup_orthogonal_eq_bot (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g)

/-! ## Unconditional discreteness of the resolvent spectrum -/

/-- **Discreteness of the resolvent spectrum, unconditional.** For a
closed Riemannian manifold `(M, g)` and any `ε > 0`, only finitely many
eigenvalues `μ` of `resolventL2 g` satisfy `|μ| ≥ ε`.

This is the unconditional version of the corresponding conditional
result, with the compactness hypothesis discharged via
`resolventL2_isCompactOperator`. -/
theorem resolvent_eigenvalues_finite_above_unconditional
    (g : SmoothRiemannianMetric I M) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite { μ : ℝ |
      Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } :=
  resolvent_eigenvalues_finite_above (I := I) (M := M) g
    (resolventL2_isCompactOperator (I := I) (M := M) g) hε

end Laplacian
end Analysis
end DifferentialGeometry

end
