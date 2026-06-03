import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-!
# `L²` operator bounds for the rough-Laplacian / covariant-gradient commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
genuine **intrinsic curvature `L²` operator bounds** for the rank-generic order-`2` commutator
defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`). They are the
genuine curvature-derivative inputs that the all-valence intrinsic Gårding bootstrap consumes (see
`Analysis/Spectral/Intrinsic/Garding/AllValenceL2DefectBound.lean`), packaged here so that file
assembles the two consumer-shaped estimates on top of them.

All three statements are TRUE per-valence/per-order on a closed manifold: by the rank-generic
pointwise tensor Bochner–Weitzenböck representation (`pointwiseTensorCurv_toSection_eq_frame_sum`,
`Tensor3rdCurv_eq_genuine_add_bracket`), the fibre value of `Curv S` is a contraction of the
Riemann tensor and finitely many of its covariant derivatives against the `≤ 2`-order covariant
gradients of `S`; each coefficient (a covariant derivative of curvature) is continuous on the
compact manifold, hence sup-bounded. Their bodies are `sorry` (the genuine remaining
curvature-derivative content); the precise shape is recorded in each docstring.

## Main statements (posited curvature inputs)

* `exists_pointwiseTensorCurv_l2_bound` — the **single-step defect `L²` norm bound**: at every
  rank `s`, `‖Curv S‖_{L²} ≤ Ccurv s · (‖S‖_{L²} + ‖∇S‖_{L²} + ‖∇²S‖_{L²})`. The defect is a
  second-order operator in `S` with curvature(-derivative) coefficients, so its `L²` operator norm
  is controlled by the `≤ 2`-order gradients (the `∇²S`-term carries the moving-frame
  bracket discrepancy, which at the *norm* level is genuinely `∇²S`-order and so is admitted here).

* `exists_pointwiseTensorCurv_l2_bracketFree_repr` — the **integrated bracket-free curvature
  representation**: at every rank `s` there is a curvature contraction field `G : SmoothCcTensor
  g 0 (s + 1)` (the genuine `R(∇S) + (∇R) S` part of `Curv S`) for which the `L²` cross-pairing of
  `Curv S` against `∇S` equals the `L²` cross-pairing of `G` against `∇S`
  (`⟨Curv S, ∇S⟩ = ⟨G, ∇S⟩`, the moving-frame bracket integrating by parts to zero against `∇S`),
  and `G` is `L²`-controlled by `‖∇S‖_{L²} + ‖S‖_{L²}`. This is the integrated statement: only the
  pairing against `∇S` removes the `∇²S`-order bracket, so the genuine field `G` is order `≤ 1` in
  `S`.

* `exists_covGrad_commutatorDefect_l2_bound` — the **gradient-of-commutator-defect bound**: for
  every gradient order `p`, the covariant gradient of the order-`p` rough-Laplacian /
  iterated-gradient commutator defect
  `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` is `L²`-controlled by the `≤ p + 2`-order gradients of the
  `(0, 2)`-tensor base `U`,
  `‖∇(Defect p)‖_{L²} ≤ Dc p · ∑_{i ≤ p + 2} ‖∇^i U‖_{L²}`. This is the one-higher-derivative
  curvature-coefficient expansion of the iterated commutator (each covariant gradient applied to the
  defect produces one further contraction of a covariant derivative of curvature, all sup-bounded on
  the compact manifold). Combined with the single-step defect bound it closes the all-order
  commutator-defect recursion `Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)`.

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the tensor rank from
`(0, s)` to `(0, s + 1)`; `iteratedCovGrad g 0 s k` is its `k`-fold iterate. All `L²` norms are the
global metric `L²` (semi)norm, which on a `SmoothCcTensor` is exactly its seminorm `‖·‖`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **The single-step commutator-defect `L²` norm bound (posited curvature input, per-valence).**
For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `Ccurv : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `S`, writing `∇S := covGrad g 0 s S` and
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the rough-Laplacian / covariant-gradient
commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S) = pointwiseTensorCurv g s S` is `L²`-bounded by

```
‖Curv S‖_{L²} ≤ Ccurv s · (‖S‖_{L²} + ‖∇S‖_{L²} + ‖∇²S‖_{L²}).
```

By the rank-generic pointwise tensor Bochner–Weitzenböck representation
(`pointwiseTensorCurv_toSection_eq_frame_sum` together with
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` /
`Tensor3rdCurv_eq_genuine_add_bracket`), the fibre value of `Curv S` is a contraction of the
Riemann tensor (the `R(∇S)` term, order `∇S`), its covariant derivative (the `(∇R) S` term, order
`S`) and the moving-frame bracket (the order-`∇²S` discrepancy) against the `≤ 2`-order covariant
gradients of `S`. Each coefficient is continuous on the compact manifold, hence sup-bounded, so the
per-valence constant `Ccurv s` is finite. (The bound includes the `∇²S` term precisely because the
moving-frame bracket discrepancy is genuinely `∇²S`-order at the `L²`-norm level — only an
*integrated pairing* against `∇S` removes it, cf. `exists_pointwiseTensorCurv_l2_bracketFree_repr`.)
This `sorry` is a genuine curvature-derivative leaf, correctly per-valence-quantified. -/
theorem exists_pointwiseTensorCurv_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Ccurv : ℕ → ℝ, (∀ s, 0 ≤ Ccurv s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ‖pointwiseTensorCurv (I := I) (M := M) g s S‖ ≤
        Ccurv s *
          (‖S‖ + ‖covGrad (I := I) (M := M) g 0 s S‖ +
            ‖covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)‖) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The integrated bracket-free curvature representation of the cross term (posited curvature
input, per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and
for every smooth compactly-supported `(0, s)`-tensor `S`, there exists a curvature contraction
field `G : SmoothCcTensor g 0 (s + 1)` — the genuine `R(∇S) + (∇R) S` part of the order-`2`
commutator defect `Curv S := pointwiseTensorCurv g s S` — for which

```
⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}   and   ‖G‖_{L²} ≤ K s · (‖∇S‖_{L²} + ‖S‖_{L²}),
```

with `∇S := covGrad g 0 s S`. The first identity is the *integrated* Bochner statement: fibrewise
`Curv S = G + (moving-frame bracket)` (`pointwiseTensorCurv_toSection_eq_frame_sum`,
`Tensor3rdCurv_eq_genuine_add_bracket`), and the bracket — a total covariant divergence of an
order-`∇S` field — integrates by parts to zero against `∇S`, so only the genuine curvature
contraction `G` survives the `L²` pairing. The genuine field `G = R(∇S) + (∇R) S` is order `≤ 1`
in `S`, controlled by `‖∇S‖_{L²} + ‖S‖_{L²}` via the uniform curvature and differentiated-curvature
sups over the compact manifold (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The constant is valence-dependent
because the `(0, s)`-bundle curvature endomorphism is an `s`-slot derivation, so its operator norm
grows like `(s + 1)·‖R‖_∞`. This `sorry` is the genuine integrated curvature leaf, correctly
per-valence-quantified. -/
theorem exists_pointwiseTensorCurv_l2_bracketFree_repr (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G : SmoothCcTensor g 0 (s + 1),
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) G.toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun ∧
        ‖G‖ ≤ K s * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The gradient-of-commutator-defect `L²` bound (posited curvature input, per-order).** For a
closed smooth Riemannian manifold `(M, g)` there is an *order-dependent* nonnegative constant
`Dc : ℕ → ℝ` such that, for every smooth compactly-supported `(0, 2)`-tensor base `U` and every
gradient order `p`, the covariant gradient of the order-`p` rough-Laplacian / iterated-gradient
commutator defect

```
Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)
          = rawTensorConnLapSmooth g 0 (2 + p) (∇^p U) − ∇^p(Δ_∇ U)
```

(a `(0, 2 + p)`-tensor field, `∇^p U = iteratedCovGrad g 0 2 p U`) satisfies

```
‖∇(Defect p)‖_{L²} ≤ Dc p · ∑_{i ≤ p + 2} ‖∇^i U‖_{L²}.
```

This is the one-higher-derivative iterated curvature-coefficient expansion of the commutator
defect: differentiating the order-`p` defect once more produces, by the iterated Ricci identity,
one further contraction of a covariant derivative of the Riemann tensor against the `≤ p + 2`-order
gradients of `U`, and all curvature-derivative coefficients up to order `p + 1` are continuous on
the compact manifold, hence sup-bounded. Combined with the single-step defect bound
`exists_pointwiseTensorCurv_l2_bound` it closes the all-order commutator-defect recursion
`Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)` (`covGradRoughLap_commutatorDefect_iter_succ_eq` in
`AllValenceL2DefectBound.lean`). The constant is order-dependent because the number of
curvature-derivative terms grows with `p`. This `sorry` is the genuine iterated curvature-derivative
leaf, correctly per-order-quantified. -/
theorem exists_covGrad_commutatorDefect_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ‖covGrad g 0 (2 + p)
            (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
              iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U))‖ ≤
          Dc p * ∑ i ∈ Finset.range (p + 1 + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
