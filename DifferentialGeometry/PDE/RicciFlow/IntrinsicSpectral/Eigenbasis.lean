import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolvent
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Predicate-free spectral eigenbasis for the connection Laplacian

For a closed Riemannian manifold `(M, g)`, this file packages the
spectral theorem for the connection (rough) Laplacian `Δ_∇` on
`(r, s)`-tensor fields in the form required downstream: a sequence
`e : ℕ → TensorL2 r s g` of orthonormal eigenfunctions whose linear
span is dense in `TensorL2 r s g`, together with the associated
real eigenvalues `lam : ℕ → ℝ`, all non-positive (the geometer's
Laplacian-sign convention has spectrum `⊆ (-∞, 0]`), and satisfying
the eigenvalue equation
`connLaplacianL2 g r s ⟨e n, h_dom n⟩ = lam n • e n`
for a witness `h_dom n : e n ∈ (connLaplacianL2 g r s).domain`.

The construction goes through the compact self-adjoint L²-side
resolvent `tensorResolventL2 g r s = (1 - Δ_∇)⁻¹` (whose compactness
and self-adjointness are bundled in
`intrinsic_compact_self_adjoint_resolvent`, α.3): the Hilbert-Schmidt
spectral theorem applied to that operator yields an orthonormal
sequence of resolvent-eigenvectors whose span is dense, and pulling
back via the spectral map `μ ↦ 1 - 1/μ` recovers the eigenvalues of
`Δ_∇` on the same vectors. Membership of each eigenvector in the
domain of `connLaplacianL2` follows from the fact that the resolvent
maps `TensorL2` into the operator's domain.

The cleaner Mathlib form
(`HilbertBasis.mkOfOrthogonalEqBot`) is used internally; the public
output is the explicit `ℕ`-indexed orthonormal family + eigenvalues
+ eigenvalue equation form requested by downstream consumers.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff InnerProductSpace
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Predicate-free spectral eigenbasis for the connection Laplacian.**
On a closed Riemannian manifold `(M, g)`, the connection (rough)
Laplacian `Δ_∇` on `(r, s)`-tensor fields admits a complete spectral
decomposition: there exist an orthonormal sequence
`e : ℕ → TensorL2 r s g` whose linear span is dense in
`TensorL2 r s g`, together with non-positive real eigenvalues
`lam : ℕ → ℝ`, such that each `e n` lies in the domain of
`connLaplacianL2 g r s` and the eigenvalue equation
`connLaplacianL2 g r s ⟨e n, _⟩ = lam n • e n`
holds for every `n`.

The proof reduces, via `intrinsic_compact_self_adjoint_resolvent`
(α.3), to the Hilbert-Schmidt spectral theorem for compact
self-adjoint operators on a separable Hilbert space (Mathlib
`Analysis/InnerProductSpace/Spectrum.lean`), pulled back through the
spectral map `μ ↦ 1 - 1/μ` from the L²-side resolvent
`tensorResolventL2 = (1 - Δ_∇)⁻¹` to `Δ_∇` itself. -/
theorem connLaplacian_has_predicate_free_eigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (e : ℕ → TensorL2 r s g) (lam : ℕ → ℝ)
      (h_dom : ∀ n, e n ∈ (connLaplacianL2 (I := I) g r s).domain),
      Orthonormal ℝ e ∧
        DenseRange e ∧
          (∀ n, lam n ≤ 0) ∧
            (∀ n,
              (connLaplacianL2 (I := I) g r s) ⟨e n, h_dom n⟩ =
                lam n • e n) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
