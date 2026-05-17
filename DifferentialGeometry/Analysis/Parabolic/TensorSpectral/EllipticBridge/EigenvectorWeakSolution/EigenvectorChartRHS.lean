import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2

/-!
# The main-Dirichlet limit of the eigenvector weak-solution assembly

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, the per-component
elliptic-regularity analysis realises the chart `P₀`-component of the abstract
connection-Laplacian eigenvector as a chart-local weak elliptic solution.

The variational-identity assembly applies the source-free per-approximant chart
bilinear identity to the partition-of-unity-weighted smooth approximants
`Tₙ := pouSmul g r s α wₙ`, with `wₙ := eigenvectorSmoothApprox g r s h_uniform i n`
the canonical smooth `H¹`-approximating sequence of the eigenvector resolvent.
Its Dirichlet term splits, by the covariant Leibniz rule, into the
genuine-gradient **main-Dirichlet** term

```
mainDir(n) := ∫ tensorCovDerivPointwiseInner g r s wₙ (scalarSmul ζ_α S)
```

(`ζ_α := chartAtlasPOU I M α`, `S` a fixed smooth `(r, s)`-tensor test section)
corrected by two cross terms. The cross terms' `n → ∞` limits are pre-proven in
the sibling cross-limit files; this file proves the `n → ∞` limit of the
main-Dirichlet term.

## The limit

By the smooth-`H¹`-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto`, the main-Dirichlet pairing of `wₙ` against the
*fixed* smooth section `S'` converges to

```
⟪eigenvectorResolvent …, smoothToTensorH1Compl S'⟫_{H¹}
  − ⟪TensorH1ComplToTensorL2 (eigenvectorResolvent …), S'.toCcTensor⟫_{L²}.
```

The eigenvector weak equation `eigenWeakEquation` rewrites the first `H¹` pairing
as the `L²` pairing `⟪S'.toCcTensor, φ⟫` of `S'` against the eigenvector `φ`; the
rescaling identity `eigenvector_eq_resolvent_smul` identifies
`TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`. Hence the
main-Dirichlet limit is the closed-form `(1 − μ) · ⟪S'.toCcTensor, φ⟫`.

## Main results

* `mainDir_tendsto` — the `n → ∞` limit of the main-Dirichlet term.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The `L²`-coercion of the eigenvector resolvent

The eigenbasis vector `φ := tensorResolventEigenbasisVec h_uniform i` satisfies,
by `eigenvector_eq_resolvent_smul`, the identity
`φ = μ⁻¹ • TensorH1ComplToTensorL2 (eigenvectorResolvent …)`; multiplying through
by the nonzero scalar `μ := i.fst.val` rearranges this to express the
`L²`-coercion of the eigenvector resolvent directly as `μ • φ`. -/

/-- **The `L²`-coercion of the eigenvector resolvent is `μ • φ`.** Multiplying the
rescaling identity `eigenvector_eq_resolvent_smul` through by the nonzero
eigenvalue `μ := i.fst.val` rearranges `φ = μ⁻¹ • TensorH1ComplToTensorL2
(eigenvectorResolvent …)` into `TensorH1ComplToTensorL2 (eigenvectorResolvent …)
= μ • φ`. -/
private lemma resolventL2_eq_mul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s h_uniform i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

/-! ## The main-Dirichlet limit

The main-Dirichlet term `mainDir(n)` is the integrated covariant-gradient
(Dirichlet) pairing of the `n`-th canonical smooth approximant `wₙ` against a
*fixed* smooth compactly-supported `(r, s)`-tensor section `S'`. Its `n → ∞`
limit is extracted from the smooth-`H¹`-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto`, then rewritten in closed form through the
eigenvector weak equation and the resolvent rescaling identity. -/

/-- **The `n → ∞` limit of the main-Dirichlet term.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, and a fixed smooth
compactly-supported `(r, s)`-tensor section `S'`, the main-Dirichlet pairings

```
∫_M ⟨∇(eigenvectorSmoothApprox g r s h_uniform i n).toCcTensor, ∇S'⟩ dμ_g
```

converge, as `n → ∞`, to the closed-form

```
(1 − μ) · ⟪(S' : TensorL2 r s g), tensorResolventEigenbasisVec h_uniform i⟫_{L²}.
```

The proof feeds the canonical-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto` — whose limit is the difference of an `H¹` and an
`L²` pairing — through the eigenvector weak equation `eigenWeakEquation`
(rewriting the `H¹` pairing as the `L²` pairing against the eigenvector) and the
resolvent rescaling identity `resolventL2_eq_mul_eigenvector` (identifying the
`L²`-coercion of the resolvent with `μ • φ`).

This is the one `n → ∞` limit of the eigenvector weak-solution assembly that is
not packaged by the sibling cross-limit / lower-order-limit files; combined with
those, it furnishes the full limit of the source-free per-approximant chart
bilinear identity. -/
theorem mainDir_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S' : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_uniform i n).toCcTensor
          S' x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 ((1 - i.fst.val) *
        ⟪(S' : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i⟫_ℝ)) := by
  classical
  -- View the fixed test section as a smooth compactly-supported `H¹` section.
  set Sh1 : SmoothCcTensorH1 g r s := ⟨S'⟩ with hSh1_def
  have hSh1_to : Sh1.toCcTensor = S' := rfl
  -- The canonical approximating sequence and its `H¹`-convergence.
  have hw_tendsto :
      Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_uniform i n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) :=
    eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s h_uniform i
  -- The Dirichlet-convergence theorem of the canonical approximating sequence.
  have h_dir :=
    smoothApprox_dirichlet_tendsto (I := I) (M := M) g r s h_uniform i Sh1
      hw_tendsto
  -- `⟪R, sToH1 Sh1⟫ = ⟪Sh1.toCcTensor, φ⟫` by the eigenvector weak equation.
  have h_weak :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s h_uniform i,
          smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ =
        ⟪(Sh1.toCcTensor : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i⟫_ℝ :=
    eigenWeakEquation (I := I) (M := M) g r s h_uniform i Sh1
  -- `TensorH1ComplToTensorL2 R = μ • φ`, so the `L²` part is
  -- `μ • ⟪φ, Sh1.toCcTensor⟫ = μ • ⟪Sh1.toCcTensor, φ⟫`.
  have h_l2part :
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i),
          (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        i.fst.val *
          ⟪(Sh1.toCcTensor : TensorL2 r s g),
            tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i⟫_ℝ := by
    rw [resolventL2_eq_mul_eigenvector (I := I) (M := M) g r s h_uniform i,
      inner_smul_left, starRingEnd_apply, star_trivial, real_inner_comm]
  -- Assemble the closed-form limit.
  have h_limit_eq :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s h_uniform i,
            smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ -
          ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i),
            (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        (1 - i.fst.val) *
          ⟪(S' : TensorL2 r s g),
            tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i⟫_ℝ := by
    rw [h_weak, h_l2part, hSh1_to]; ring
  rw [h_limit_eq] at h_dir
  exact h_dir

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_uniform : uniformTensorChartSobolevBound g r s)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (S' : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_uniform i n).toCcTensor
          S' x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 ((1 - i.fst.val) *
        ⟪(S' : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i⟫_ℝ)) :=
  mainDir_tendsto (I := I) (M := M) g r s h_uniform i S'

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
