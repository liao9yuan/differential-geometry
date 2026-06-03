import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
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

/-- **The pointwise fibre-norm bound for the order-`2` commutator defect (posited curvature
input, per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Ccurv : ℕ → ℝ` such that, at every covariant rank `s`,
for every smooth compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic
fibre norm of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` is bounded by
`(Ccurv s)²` times the sum of the intrinsic fibre norms of `S`, `∇S = covGrad g 0 s S` and
`∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`:
```
rfns(Curv S)(x) ≤ (Ccurv s)² · ( rfns(S)(x) + rfns(∇S)(x) + rfns(∇²S)(x) ).
```

This is the genuine *pointwise* third-order tensor Bochner–Weitzenböck content. By the rank-generic
frame-sum representation `pointwiseTensorCurv_toSection_eq_frame_sum`, the fibre value of `Curv S`
at `x` is the fixed-frame sum of per-summand third-order covariant-derivative differences; matching
the curried gradient slot to the directional-`W` frame trace
(`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`) decomposes each into the genuine
curvature contraction `tensor3rdCurvGenuine` (the `R(∇S)` term, `rfns(∇S)`-order, and the `(∇R) S`
term, `rfns(S)`-order; fibre-bounded by `riemannianFiberNormSq_tensor3rdCurvGenuine_le` from the
uniform curvature/differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`) plus the frame-bracket discrepancy
`tensor3rdCurvBracket` (the `rfns(∇²S)`-order moving-frame term; fibre-bounded by the uniform
second-covariant-derivative sup of `∇S`). Each coefficient is continuous on the compact manifold,
hence sup-bounded, so the per-valence constant `Ccurv s` (scaling like `(s + 1)·‖R‖_∞` for the
`s`-slot curvature endomorphism) is finite. This is the genuine remaining per-valence
curvature-derivative leaf; the *integrated* `∇²S`-removing form is
`exists_pointwiseTensorCurv_bracketFree_field`. -/
theorem exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Ccurv : ℕ → ℝ, (∀ s, 0 ≤ Ccurv s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
        Ccurv s ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The single-step commutator-defect `L²` norm bound (proved from the pointwise curvature
input).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `Ccurv : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `S`, writing `∇S := covGrad g 0 s S` and
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the rough-Laplacian / covariant-gradient
commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S) = pointwiseTensorCurv g s S` is `L²`-bounded by

```
‖Curv S‖_{L²} ≤ Ccurv s · (‖S‖_{L²} + ‖∇S‖_{L²} + ‖∇²S‖_{L²}).
```

This is **proved** from the pointwise third-order tensor Bochner–Weitzenböck fibre-norm bound
`exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound`
(`rfns(Curv S)(x) ≤ (Ccurv s)²·(rfns(S) + rfns(∇S) + rfns(∇²S))(x)`) through the purely analytic
three-term pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three`
(`‖·‖ = tensorL2Norm ∘ toFun`, the fibre-norm bridge `‖S‖² = ∫ rfns(S)`, integral monotonicity and
`p² + q² + r² ≤ (p + q + r)²`). Its only `sorry`-dependence is through that posited pointwise
curvature input. -/
theorem exists_pointwiseTensorCurv_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Ccurv : ℕ → ℝ, (∀ s, 0 ≤ Ccurv s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ‖pointwiseTensorCurv (I := I) (M := M) g s S‖ ≤
        Ccurv s *
          (‖S‖ + ‖covGrad (I := I) (M := M) g 0 s S‖ +
            ‖covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)‖) := by
  classical
  obtain ⟨Ccurv, hCcurv_nn, hpt⟩ :=
    exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨Ccurv, hCcurv_nn, fun s S => ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three (I := I) (M := M) g
    S (covGrad (I := I) (M := M) g 0 s S)
    (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S))
    (pointwiseTensorCurv (I := I) (M := M) g s S) (Ccurv s) (hCcurv_nn s) (hpt s S)

/-- **The integrated bracket-free curvature field of the cross term (posited curvature input,
per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `S`, there exists a curvature contraction field
`G : SmoothCcTensor g 0 (s + 1)` — the genuine `R(∇S) + (∇R) S` part of the order-`2` commutator
defect `Curv S := pointwiseTensorCurv g s S` — for which the `L²` cross-pairing of `Curv S` against
`∇S = covGrad g 0 s S` equals that of `G` against `∇S` (the moving-frame bracket integrating by
parts to zero), and `G` is *pointwise* fibre-norm-controlled by `∇S` and `S`:
```
⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}   and
rfns(G)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )   (every x).
```

This is the genuine *integrated* third-order tensor Bochner–Weitzenböck content. Fibrewise
`Curv S = tensor3rdCurvGenuine + tensor3rdCurvBracket`
(`pointwiseTensorCurv_toSection_eq_frame_sum`, `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`,
`Tensor3rdCurv_eq_genuine_add_bracket`); the bracket term `tensor3rdCurvBracket` is a total
covariant divergence of an order-`∇S` field, so it integrates by parts to zero against `∇S`
(`green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed` / the covariant integration-by-parts
`integral_tensorInner_covDeriv_integrationByParts`), leaving only the genuine contraction
`G = tensor3rdCurvGenuine` realized as a smooth compactly-supported section. That genuine field is
order `≤ 1` in `S` — the `R(∇S)` term (`rfns(∇S)`-order) and the `(∇R) S` term (`rfns(S)`-order),
fibre-bounded pointwise by `riemannianFiberNormSq_tensor3rdCurvGenuine_le` from the uniform curvature
and differentiated-curvature sups (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The constant is valence-dependent
because the `(0, s)`-bundle curvature endomorphism is an `s`-slot derivation, so its operator norm
grows like `(s + 1)·‖R‖_∞`. This is the genuine integrated curvature leaf (the pointwise fibre bound
on `Curv S` itself is *false* at the `∇²S`-order bracket — only this `L²` pairing removes it). -/
theorem exists_pointwiseTensorCurv_bracketFree_field (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G : SmoothCcTensor g 0 (s + 1),
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) G.toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun ∧
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (G.toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The integrated bracket-free curvature representation of the cross term (proved from the
bracket-free field).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and
for every smooth compactly-supported `(0, s)`-tensor `S`, there exists a curvature contraction
field `G : SmoothCcTensor g 0 (s + 1)` — the genuine `R(∇S) + (∇R) S` part of the order-`2`
commutator defect `Curv S := pointwiseTensorCurv g s S` — for which

```
⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}   and   ‖G‖_{L²} ≤ K s · (‖∇S‖_{L²} + ‖S‖_{L²}),
```

with `∇S := covGrad g 0 s S`. This is **proved** from the bracket-free curvature field
`exists_pointwiseTensorCurv_bracketFree_field`: that input supplies the genuine field `G` with the
`L²` pairing identity (the moving-frame bracket integrating by parts to zero) and the *pointwise*
fibre-norm bound `rfns(G)(x) ≤ (K s)²·(rfns(∇S) + rfns(S))(x)`; the `L²` norm bound
`‖G‖ ≤ K s·(‖∇S‖ + ‖S‖)` is then the purely analytic two-term pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`. Only the pairing against `∇S` removes the
`∇²S`-order bracket, so the genuine field `G = R(∇S) + (∇R) S` is order `≤ 1` in `S`. Its only
`sorry`-dependence is through that posited curvature input. -/
theorem exists_pointwiseTensorCurv_l2_bracketFree_repr (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G : SmoothCcTensor g 0 (s + 1),
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) G.toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun ∧
        ‖G‖ ≤ K s * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) := by
  classical
  obtain ⟨K, hK_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_bracketFree_field (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, hident, hGpt⟩ := hfield s S
  refine ⟨G, hident, ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) S G (K s) (hK_nn s) hGpt

/-- **The pointwise gradient-of-commutator-defect fibre-norm bound (posited curvature input,
per-order).** For a closed smooth Riemannian manifold `(M, g)` there is an *order-dependent*
nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth compactly-supported `(0, 2)`-tensor
base `U`, every gradient order `p`, and *every point* `x`, the intrinsic fibre norm of the covariant
gradient of the order-`p` commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` is bounded by
`(Dc p)²` times the sum of the intrinsic fibre norms of the `≤ p + 2`-order gradients of `U`:
```
rfns(∇(Defect p))(x) ≤ (Dc p)² · ∑_{i ≤ p + 2} rfns(∇^i U)(x).
```

This is the genuine one-higher-derivative iterated curvature-coefficient expansion of the commutator
defect: differentiating `Defect p` once more produces, by the iterated Ricci identity, one further
contraction of a covariant derivative of the Riemann tensor against the `≤ p + 2`-order gradients of
`U` (the top-order term cancelling). Each curvature-derivative coefficient up to order `p + 1` is
continuous on the compact manifold, hence sup-bounded (`exists_bound_riemannianFiberNormSq_smoothCcTensor`
on each finitely-many curvature-contraction term), so the per-order constant `Dc p` is finite. The
constant is order-dependent because the number of curvature-derivative terms — and the slot count of
the tensor-bundle curvature endomorphism — grow with `p`. This is the genuine remaining iterated
curvature-derivative leaf, correctly per-order-quantified. -/
theorem exists_covGrad_commutatorDefect_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x
            ((covGrad g 0 (2 + p)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
                iteratedCovGrad g 0 2 p
                  (rawTensorConnLapSmooth (I := I) g 0 2 U))).toSection x) ≤
          Dc p ^ 2 * ∑ i ∈ Finset.range (p + 1 + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x
              ((iteratedCovGrad g 0 2 i U).toSection x) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The gradient-of-commutator-defect `L²` bound (proved from the pointwise curvature input).**
For a closed smooth Riemannian manifold `(M, g)` there is an *order-dependent* nonnegative constant
`Dc : ℕ → ℝ` such that, for every smooth compactly-supported `(0, 2)`-tensor base `U` and every
gradient order `p`, the covariant gradient of the order-`p` rough-Laplacian / iterated-gradient
commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` satisfies

```
‖∇(Defect p)‖_{L²} ≤ Dc p · ∑_{i ≤ p + 2} ‖∇^i U‖_{L²}.
```

This is **proved** from the pointwise iterated curvature-derivative fibre-norm bound
`exists_covGrad_commutatorDefect_pointwise_fiberNormSq_bound`
(`rfns(∇(Defect p))(x) ≤ (Dc p)²·∑_{i ≤ p+2} rfns(∇^i U)(x)`) through the purely analytic finite-sum
pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` (with per-index
valence `v i = 2 + i`, `N = p + 1 + 2`). Combined with the single-step defect bound
`exists_pointwiseTensorCurv_l2_bound` it closes the all-order commutator-defect recursion
`Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)`. Its only `sorry`-dependence is through that posited
pointwise curvature input. -/
theorem exists_covGrad_commutatorDefect_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ‖covGrad g 0 (2 + p)
            (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
              iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U))‖ ≤
          Dc p * ∑ i ∈ Finset.range (p + 1 + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
  classical
  obtain ⟨Dc, hDc_nn, hpt⟩ :=
    exists_covGrad_commutatorDefect_pointwise_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨Dc, hDc_nn, fun U p => ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g
    (p + 1 + 2) (fun i => 2 + i) (fun i => iteratedCovGrad g 0 2 i U)
    (covGrad g 0 (2 + p)
      (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
        iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U)))
    (Dc p) (hDc_nn p) (hpt U p)

end Connection
end Integral
end DifferentialGeometry

end
