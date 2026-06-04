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
compact manifold, hence sup-bounded. The three consumer-shaped `L²` statements below, the two
intermediate pointwise fibre-norm bounds, the genuine-field IBP-null divergence split, the
integrated genuine-field forms, the order-separated three-term section-field split, the
genuine/bracket section-level divergence decomposition, and the per-order iterated-Ricci
component-field decomposition are all *proved* by fibre subadditivity / inner-product bridges / the
covariant Green identity / order-induction over exactly **two** deepest general-valence curvature
primitives whose bodies are `sorry` (the genuine remaining moving-frame curvature-endomorphism
content): the constructive named-remainder moving-frame third-order Weitzenböck field decomposition
(`exists_pointwiseTensorCurv_genuineCurvature_namedRemainderField`) — explicit genuine fields plus a
single moving-frame remainder field carrying both its `∇²S`-order fibre bound and its integrated
divergence-nullity against `∇S` — and the positive-order iterated-Ricci component-field expansion
(`exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion_succ`); the precise shape is
recorded in each docstring. The order-`2` base case `∇(Defect 0) = ∇ 0 = 0` of the iterated-Ricci
expansion is *proved outright*. The genuine-field / IBP-null-remainder divergence split
(`exists_pointwiseTensorCurv_genuineField_divergenceSplit`) is itself *proved* from the bracket-free
representation — its remainder `Drem := Curv S − G` is `IBP`-null against `∇S` by the left additivity
of the `L²` pairing. Consumers transitively depend on `sorryAx` through the two deepest curvature
primitives named above.

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

/-- **Posited deepest curvature primitive: the constructive named-remainder form of the genuine
moving-frame third-order Weitzenböck field decomposition.** For a closed smooth Riemannian
manifold `(M, g)` there is a *valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at
every covariant rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, the order-`2`
commutator defect `Curv S := pointwiseTensorCurv g s S` admits a *named three-field* split into two
genuine curvature contraction fields `Gcurv, GcurvDeriv` and a single moving-frame remainder field
`Grem`, all smooth compactly-supported `(0, s + 1)`-tensors:
```
Curv S = Gcurv + GcurvDeriv + Grem,
```
with the four genuine Weitzenböck properties

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-Riemann field `R(∇S)`, genuinely
  `rfns(∇S)`-order (the Ricci identity on the gradient field `∇S = covGrad g 0 s S`,
  `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, with the proportional fibre bound
  `riemannOp_covGrad_fiberNormSq_le_gen`);
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · rfns(S)(x)` — the differentiated-curvature field `(∇R) S`,
  genuinely `rfns(S)`-order (`covGradCurvatureContraction`, with its uniform sup upgraded to a bound
  proportional to `rfns(S)`);
* `rfns(Grem)(x) ≤ (Cper s)² · rfns(∇²S)(x)` — the moving-frame / frame-bracket remainder
  (`tensor3rdCurvBracket` plus the frame-trace discrepancy `covGradRoughLapTraceDiscrepancy` and the
  moving-frame residual `covGradRoughLapMovingFrameResidual`), genuinely `rfns(∇²S)`-order after the
  third-order Weitzenböck cancellation of the top-order `∇³S` terms by the iterated Ricci identity;
* `⟨Grem, ∇S⟩_{L²} = 0` — the *integrated* divergence-nullity of the same moving-frame remainder
  (the remainder is a total covariant divergence of an `∇S`-order field, so its `L²` pairing against
  `∇S` vanishes by the covariant Green identity
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`).

This is the genuinely-missing third-order Bochner–Weitzenböck primitive — the deepest curvature core.
The body is `sorry`: bridging the fixed-frame section representation
`pointwiseTensorCurv_toSection_eq_frame_sum` to the directional genuine/bracket split
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` carries the unresolved moving-frame
residual (documented in `FreeDirectionReduction.lean`, `TraceDiscrepancyDecomposition.lean`); the
clean `slot0FrameTraceMatching` is *false* on a normal manifold (S²), so the honest primitive carries
the bracket remainder `Grem` explicitly rather than asserting a clean cancellation. The decomposition
rejects the degenerate witness: `Gcurv = GcurvDeriv = 0`, `Grem = Curv S` makes the `Grem`-bound
`rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)` *false* (the defect carries the `rfns(S)` and `rfns(∇S)` orders
too, and at the `∇²S`-order the bracket pairs to zero against `∇S` only under the genuine integrated
nullity, which `Grem = Curv S` violates since `⟨Curv S, ∇S⟩ = ‖Δ_∇S‖² − ‖∇²S‖² ≠ 0` in general by
`weitzenbock_integrated_covGrad_l2_normSq`).

The named-remainder existence theorem `exists_pointwiseTensorCurv_genuineCurvature_orderSeparatedFields`
is *proved* on top of it by setting the anonymous remainder `Curv S − Gcurv − GcurvDeriv = Grem`
(the section identity is `abel`) and reading the four properties off. -/
theorem exists_pointwiseTensorCurv_genuineCurvature_namedRemainderField
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S = Gcurv + GcurvDeriv + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  sorry

/-- **Posited deepest curvature primitive: the genuine moving-frame third-order Weitzenböck
field decomposition (order-separated genuine fields + `∇²S`-order remainder).** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, there are two smooth compactly-supported *genuine curvature* fields
`Gcurv, GcurvDeriv : SmoothCcTensor g 0 (s + 1)` — the section-level packagings of the
pure-Riemann contraction `R(∇S)` and the differentiated-curvature contraction `(∇R) S` of the
order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` — such that:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` (genuinely `rfns(∇S)`-order),
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · rfns(S)(x)` (genuinely `rfns(S)`-order),
* the **moving-frame remainder** — the *concrete* subtraction `Curv S − Gcurv − GcurvDeriv` —
  satisfies `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · rfns(∇²S)(x)`,

at **every** point `x`, with `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`.

This is the genuinely-missing third-order Bochner–Weitzenböck primitive — the deepest curvature
core. Its construction combines: the fixed-frame representation
`pointwiseTensorCurv_toSection_eq_frame_sum`; the genuine/bracket split
`Tensor3rdCurv_eq_genuine_add_bracket` / `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(the genuine part is `tensor3rdCurvGenuine`, the remainder is `tensor3rdCurvBracket` plus the
frame-trace discrepancy `covGradRoughLapTraceDiscrepancy` and the moving-frame residual
`covGradRoughLapMovingFrameResidual`); the order-separated genuine fibre bound
`riemannianFiberNormSq_tensor3rdCurvGenuine_le` fed by the uniform curvature / differentiated-curvature
sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` upgraded to bounds *proportional* to
`rfns(∇S)` / `rfns(S)`; and the **third-order Weitzenböck cancellation** that, after removing the
genuine curvature contractions, the surviving moving-frame / frame-bracket discrepancy is genuinely
of order `∇²S` (the top-order `∇³S` terms cancel by the iterated Ricci identity; only the
`[Bᵢ, W]`-jet `∇²S`-order discrepancy survives, bounded by the smooth frame data on the compact
`M`). Two genuinely-distinct obstructions are absorbed here (documented in `FreeDirectionReduction.lean`):
the slot-`0` Christoffel / bracket family matching via torsion-freeness, and the moving-frame
vs. fixed-frame derivative residual. The remainder bound through `smoothExtensionTangent` is *false
term-by-term*; only the **sum** (the genuine tensorial remainder) is `∇²S`-order — which is why this
moving-frame cancellation is the irreducible content and the `0`-witness is rejected (`Gcurv =
GcurvDeriv = 0` makes the remainder bound `rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)` *false*, since
`Curv S` also carries the `rfns(S)` and `rfns(∇S)` orders).

The genuine remainder is additionally **a total covariant divergence of an `∇S`-order field**, so
its `L²` pairing against `∇S` vanishes by the covariant Green identity
(`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`); this `⟨Curv S − Gcurv − GcurvDeriv,
∇S⟩_{L²} = 0` is carried here as the genuine integrated divergence-nullity of the same moving-frame
remainder (the integrated half of the same Weitzenböck content, distinct from its pointwise
`∇²S`-order bound). It too rejects the `0`-witness through the remainder bound.

This is **proved** from the constructive named-remainder primitive
`exists_pointwiseTensorCurv_genuineCurvature_namedRemainderField` (which supplies the explicit genuine
fields `Gcurv, GcurvDeriv`, the named remainder field `Grem`, the section identity `Curv S = Gcurv +
GcurvDeriv + Grem`, the three fibre bounds, and the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0`) by
identifying the anonymous subtraction `Curv S − Gcurv − GcurvDeriv` with the named remainder `Grem`
(the section identity is `abel`) and reading the four properties off. Its only `sorry`-dependence is
through that posited curvature input. The order-separated section field theorem
`exists_pointwiseTensorCurv_orderSeparated_field` is in turn *proved* on top of this by naming
`Grem := Curv S − Gcurv − GcurvDeriv` (the section identity is `abel`) and reading the three bounds
off; the genuine/bracket divergence field theorem
`exists_pointwiseTensorCurv_genuineBracket_divergence_field` is *proved* on top of it by taking the
genuine field `G := Gcurv + GcurvDeriv` (merging its two genuine bounds through
`riemannianFiberNormSq_add_le`) and the bracket `Gbrk := Curv S − G`, whose pairing-nullity is the
carried integrated divergence-nullity. -/
theorem exists_pointwiseTensorCurv_genuineCurvature_orderSeparatedFields
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    exists_pointwiseTensorCurv_genuineCurvature_namedRemainderField (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem, hnull⟩ := hfields s S
  -- The named remainder is exactly the canonical subtraction `Curv S − Gcurv − GcurvDeriv`.
  have hGrem_eq : Grem = pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv := by
    rw [hsplit]; abel
  refine ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, ?_, ?_⟩
  · intro x
    have := hrem x
    rwa [hGrem_eq] at this
  · rw [← hGrem_eq]; exact hnull

/-- **Posited deepest curvature child for the order-`2` defect (per-valence, three-term
order-separated *section-level field* decomposition).** The genuine general-valence third-order
tensor Bochner–Weitzenböck content of the order-`2` commutator defect, isolated as an explicit
split of `Curv S = pointwiseTensorCurv g s S` into the two genuine curvature contractions —
separated by their order in `S` — and a moving-frame remainder, all as smooth compactly-supported
*global fields* (not per-point fibre values). By the rank-generic frame-sum representation
`pointwiseTensorCurv_toSection_eq_frame_sum` and the directional-`W` swap
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` (`Tensor3rdCurv_eq_genuine_add_bracket`),
the defect splits as
```
Curv S = Gcurv + GcurvDeriv + Grem,
```
where `Gcurv` is the pure-Riemann term `R(∇S)` (genuinely `rfns(∇S)`-order), `GcurvDeriv` is
the differentiated-curvature term `(∇R) S` (genuinely `rfns(S)`-order) — both fibre-bounded
from the uniform curvature/differentiated-curvature sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` — and `Grem` is the
moving-frame/bracket remainder (`tensor3rdCurvBracket` plus the frame-trace discrepancy and
moving-frame residual), genuinely `rfns(∇²S)`-order.

This says: there is a *valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at
every `s` and `S`, there are smooth compactly-supported fields `Gcurv, GcurvDeriv, Grem :
SmoothCcTensor g 0 (s + 1)` with the section identity `Curv S = Gcurv + GcurvDeriv + Grem`, and at
every `x` the pure-`R` field's fibre value bounded by `rfns(∇S)`, the `∇R` field's by `rfns(S)`,
and the remainder field's by `rfns(∇²S)` (each by `(Cper s)²`, uniformly in `S`). This is the
irreducible general-valence moving-frame curvature-endomorphism `(0, s)`-expansion (the `s = 2`
directional reading is `covGradRoughLapCurv_curry_eq_of_slot0Matching` over the posited
`slot0FrameTraceMatching`; the genuine fibre bounds are
`riemannianFiberNormSq_tensor3rdCurvGenuine_le`); the per-point order-separated form
`exists_pointwiseTensorCurv_genuineRemainder_orderSeparated_bound` is *proved* from it by reading
the section identity off pointwise through `SmoothCcTensor.toSection_add`. -/
theorem exists_pointwiseTensorCurv_orderSeparated_field
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S = Gcurv + GcurvDeriv + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) := by
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    exists_pointwiseTensorCurv_genuineCurvature_orderSeparatedFields (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, _⟩ := hfields s S
  exact ⟨Gcurv, GcurvDeriv, pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv,
    by abel, hcurv, hcurvDeriv, hrem⟩

/-- **The genuine three-term order-separated section decomposition of the order-`2` defect (proved
from the section-level field decomposition, per-valence).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every
covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at *every point*
`x`, the fibre value of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` splits
as `Curv S (x) = Gcurv + GcurvDeriv + Grem`, with the pure-Riemann part `Gcurv` fibre-bounded by
`rfns(∇S)`, the differentiated-curvature part `GcurvDeriv` by `rfns(S)`, and the moving-frame
remainder `Grem` by `rfns(∇²S)` (each by `(Cper s)²`, uniformly in `S`). This is **proved** from the
section-level field decomposition `exists_pointwiseTensorCurv_orderSeparated_field` (which supplies
global fields `Gcurv, GcurvDeriv, Grem` with `Curv S = Gcurv + GcurvDeriv + Grem` and the three
per-point fibre bounds) by reading the section identity off at `x` through
`SmoothCcTensor.toSection_add`. Its only `sorry`-dependence is through that posited curvature input;
the two-term aggregate `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` is in turn
*proved* from this by merging the two genuine pieces through `riemannianFiberNormSq_add_le`. -/
theorem exists_pointwiseTensorCurv_genuineRemainder_orderSeparated_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        ∃ Gcurv GcurvDeriv Grem : TensorRSSpace 0 (s + 1) I x,
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
              Gcurv + GcurvDeriv + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Gcurv ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x GcurvDeriv ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Grem ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  obtain ⟨Cper, hCper_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_orderSeparated_field (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem⟩ := hfield s S
  refine ⟨Gcurv.toSection x, GcurvDeriv.toSection x, Grem.toSection x, ?_,
    hcurv x, hcurvDeriv x, hrem x⟩
  rw [hsplit, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
  simp only [ContMDiffSection.coe_add, Pi.add_apply]

/-- **The genuine + remainder section decomposition of the order-`2` defect (proved from the
order-separated input, per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s`, for
every smooth compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the fibre value of
the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` splits as `Curv S (x) =
Ggen + Grem`, with the genuine curvature part `Ggen` fibre-bounded by `rfns(S) + rfns(∇S)` and the
moving-frame remainder `Grem` by `rfns(∇²S)` (each by `(Cper s)²`, uniformly in `S`). This is
**proved** from the order-separated three-term split
`exists_pointwiseTensorCurv_genuineRemainder_orderSeparated_bound` (`Curv S (x) = Gcurv + GcurvDeriv
+ Grem`, with `Gcurv` bounded by `rfns(∇S)`, `GcurvDeriv` by `rfns(S)`, `Grem` by `rfns(∇²S)`) by
merging the two genuine pieces `Ggen := Gcurv + GcurvDeriv` through the two-term fibre subadditivity
`riemannianFiberNormSq_add_le` (taking `Cper := √2 · Cper`). Its only `sorry`-dependence is through
that posited curvature input; the aggregate fibre-norm bound
`exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound` is in turn *proved* from this. -/
theorem exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        ∃ Ggen Grem : TensorRSSpace 0 (s + 1) I x,
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x = Ggen + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Ggen ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Grem ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  obtain ⟨Cper, hCper_nn, hsplit⟩ :=
    exists_pointwiseTensorCurv_genuineRemainder_orderSeparated_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt 2 * Cper s, fun s => ?_, fun s S x => ?_⟩
  · exact mul_nonneg (Real.sqrt_nonneg 2) (hCper_nn s)
  · obtain ⟨Gcurv, GcurvDeriv, Grem, heq, hcurv, hcurvDeriv, hrem⟩ := hsplit s S x
    refine ⟨Gcurv + GcurvDeriv, Grem, by rw [heq], ?_, ?_⟩
    · have hSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (S.toSection x)
      have hGSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x Gcurv GcurvDeriv
      have hsq2 : (Real.sqrt 2 * Cper s) ^ 2 = 2 * Cper s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsq2]
      calc riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv + GcurvDeriv)
          ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Gcurv +
              2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x GcurvDeriv := hadd
        _ ≤ 2 * (Cper s ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
              2 * (Cper s ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
            have e1 := mul_le_mul_of_nonneg_left hcurv (by norm_num : (0 : ℝ) ≤ 2)
            have e2 := mul_le_mul_of_nonneg_left hcurvDeriv (by norm_num : (0 : ℝ) ≤ 2)
            linarith
        _ = 2 * Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by ring
    · have hsq2 : (Real.sqrt 2 * Cper s) ^ 2 = 2 * Cper s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hHnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x)
      rw [hsq2]
      nlinarith [hrem, hHnn, sq_nonneg (Cper s)]

/-- **The pointwise fibre-norm bound for the order-`2` commutator defect (proved from the
per-summand input, per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Ccurv : ℕ → ℝ` such that, at every covariant rank `s`,
for every smooth compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic
fibre norm of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` is bounded by
`(Ccurv s)²` times the sum of the intrinsic fibre norms of `S`, `∇S = covGrad g 0 s S` and
`∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`:
```
rfns(Curv S)(x) ≤ (Ccurv s)² · ( rfns(S)(x) + rfns(∇S)(x) + rfns(∇²S)(x) ).
```
This is **proved** from the genuine + remainder section-decomposition input
`exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` (`Curv S (x) = Ggen + Grem`, with
`Ggen` fibre-bounded by `rfns(S) + rfns(∇S)` and `Grem` by `rfns(∇²S)`) through the two-term fibre
subadditivity `riemannianFiberNormSq_add_le` (taking `Ccurv s := √2 · Cper s`). Its only
`sorry`-dependence is through that posited curvature input; the *integrated* `∇²S`-removing form is
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
  classical
  obtain ⟨Cper, hCper_nn, hsplit⟩ :=
    exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt 2 * Cper s, fun s => ?_, fun s S x => ?_⟩
  · exact mul_nonneg (Real.sqrt_nonneg 2) (hCper_nn s)
  · obtain ⟨Ggen, Grem, heq, hgen, hrem⟩ := hsplit s S x
    have hSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (S.toSection x)
    have hGSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x)
    have hHSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x Ggen Grem
    rw [heq]
    have hsq2 : (Real.sqrt 2 * Cper s) ^ 2 = 2 * Cper s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hsq2]
    calc riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Ggen + Grem)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Ggen +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Grem := hadd
      _ ≤ 2 * (Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x))) +
            2 * (Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) := by
          have e1 := mul_le_mul_of_nonneg_left hgen (by norm_num : (0 : ℝ) ≤ 2)
          have e2 := mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = 2 * Cper s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) := by ring

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

/-- **Posited deepest curvature child for the integrated bracket-free field: the genuine
section-level genuine/bracket divergence decomposition (per-valence).** The genuine third-order
tensor Bochner–Weitzenböck content, isolated as a *section-level* split of the order-`2` commutator
defect `Curv S = pointwiseTensorCurv g s S` into a genuine curvature field `G` and an explicit
moving-frame bracket field `Gbrk` that is `IBP`-null against the gradient `∇S`. Fibrewise
`Curv S = tensor3rdCurvGenuine + tensor3rdCurvBracket` (`pointwiseTensorCurv_toSection_eq_frame_sum`,
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`, `Tensor3rdCurv_eq_genuine_add_bracket`);
the genuine part `G := R(∇S) + (∇R) S` is order `≤ 1` in `S` (its *pointwise* fibre bound by
`rfns(∇S) + rfns(S)` comes from `riemannianFiberNormSq_tensor3rdCurvGenuine_le` and the uniform
curvature / differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), while the moving-frame bracket
`Gbrk := Curv S − G` is a total covariant divergence of an order-`∇S` field, so its `L²` pairing
`⟨Gbrk, ∇S⟩_{L²}` vanishes by the covariant Green identity
(`green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed` and its general-valence companion
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`).

This says: there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every rank
`s` and for every `S`, there are smooth compactly-supported fields `G, Gbrk : SmoothCcTensor g 0
(s + 1)` with the section identity `Curv S = G + Gbrk`, the integrated `IBP`-vanishing
`⟨Gbrk, ∇S⟩_{L²} = 0`, and the genuine field fibre-bounded by `rfns(∇S) + rfns(S)`. It is the
genuine *structural* curvature leaf: the explicit bracket field is exhibited and its divergence
nullity is asserted independently (the pointwise fibre bound on `Curv S` itself is *false* at the
`∇²S`-order bracket — only the pairing against `∇S` removes it). The pairing form
`exists_pointwiseTensorCurv_bracketFreePairing_field` is *proved* from it by collapsing the bracket
through the left additivity of the `L²` pairing. -/
theorem exists_pointwiseTensorCurv_genuineBracket_divergence_field
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G Gbrk : SmoothCcTensor g 0 (s + 1),
        pointwiseTensorCurv (I := I) (M := M) g s S = G + Gbrk ∧
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gbrk.toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun = 0 ∧
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (G.toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    exists_pointwiseTensorCurv_genuineCurvature_orderSeparatedFields (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt 2 * Cper s, fun s => mul_nonneg (Real.sqrt_nonneg 2) (hCper_nn s),
    fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, _hrem, hnull⟩ := hfields s S
  set G : SmoothCcTensor g 0 (s + 1) := Gcurv + GcurvDeriv with hG
  refine ⟨G, pointwiseTensorCurv (I := I) (M := M) g s S - G, by abel, ?_, fun x => ?_⟩
  · -- The bracket pairs to zero: `Curv S − G = Curv S − Gcurv − GcurvDeriv`.
    have hbrk_eq : (pointwiseTensorCurv (I := I) (M := M) g s S - G) =
        pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv := by
      rw [hG]; abel
    rw [hbrk_eq]; exact hnull
  · -- `rfns(Gcurv + GcurvDeriv) ≤ 2·Cper²·(rfns ∇S + rfns S)`.
    have hsq2 : (Real.sqrt 2 * Cper s) ^ 2 = 2 * Cper s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
      (Gcurv.toSection x) (GcurvDeriv.toSection x)
    have hSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (S.toSection x)
    have hGSnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x)
    rw [hsq2, hG]
    have e1 := mul_le_mul_of_nonneg_left (hcurv x) (by norm_num : (0 : ℝ) ≤ 2)
    have e2 := mul_le_mul_of_nonneg_left (hcurvDeriv x) (by norm_num : (0 : ℝ) ≤ 2)
    have hGSec : (Gcurv + GcurvDeriv).toSection x = Gcurv.toSection x + GcurvDeriv.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hGSec]
    nlinarith [hadd, e1, e2, hSnn, hGSnn, sq_nonneg (Cper s)]

/-- **The integrated bracket-free curvature representation of the cross term (proved from the
genuine/bracket section-level divergence decomposition).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every rank
`s` and for every `S`, there is a smooth compactly-supported genuine field
`G : SmoothCcTensor g 0 (s + 1)` (the `R(∇S) + (∇R) S` part of `Curv S := pointwiseTensorCurv g s S`,
order `≤ 1` in `S`) with `⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}` (the moving-frame bracket integrating by
parts to zero) and the genuine field fibre-bounded by `rfns(∇S) + rfns(S)`. This is **proved** from
the section-level genuine/bracket divergence decomposition
`exists_pointwiseTensorCurv_genuineBracket_divergence_field`: that input supplies the section
identity `Curv S = G + Gbrk`, the integrated `IBP`-vanishing `⟨Gbrk, ∇S⟩_{L²} = 0`, and the genuine
field's fibre bound; the cross-pairing identity then follows by the left additivity of the `L²`
pairing (`tensorL2Inner_add_left` on `G.toFun + Gbrk.toFun = Curv S.toFun`, joint integrability
`SmoothCcTensor.integrable_inner_cross`). Its only `sorry`-dependence is through that posited
curvature input. -/
theorem exists_pointwiseTensorCurv_bracketFreePairing_field
    (g : SmoothRiemannianMetric I M) :
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
  classical
  obtain ⟨K, hK_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_genuineBracket_divergence_field (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, Gbrk, hsplit, hibp, hbound⟩ := hfield s S
  refine ⟨G, ?_, hbound⟩
  have hfun : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun = G.toFun + Gbrk.toFun := by
    rw [hsplit]; exact SmoothCcTensor.toFun_add G Gbrk
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    G (covGrad (I := I) (M := M) g 0 s S)
  have hint₂ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    Gbrk (covGrad (I := I) (M := M) g 0 s S)
  rw [hfun, tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) G.toFun Gbrk.toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun hint₁ hint₂, hibp, add_zero]

/-- **The genuine + remainder section decomposition of the order-`2` defect (proved from the
bracket-free curvature representation, per-valence).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant
rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, there are smooth
compactly-supported fields `G, Drem : SmoothCcTensor g 0 (s + 1)` with the *section-level* identity
`Curv S = G + Drem`, the *integrated IBP-vanishing* `⟨Drem, ∇S⟩_{L²} = 0`, and the genuine field `G`
fibre-bounded by `rfns(∇S) + rfns(S)`. This is **proved** from the bracket-free curvature
representation `exists_pointwiseTensorCurv_bracketFreePairing_field` (which supplies `G` with the
pairing identity `⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}` and the fibre bound) by taking the moving-frame
remainder `Drem := Curv S − G`: then `Curv S = G + Drem` is `add_sub_cancel`, and the IBP-vanishing
`⟨Drem, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²} − ⟨G, ∇S⟩_{L²} = 0` follows from the pairing identity through the
left additivity of the `L²` pairing (`tensorL2Inner_add_left` on `G.toFun + Drem.toFun = Curv S.toFun`,
joint integrability `SmoothCcTensor.integrable_inner_cross`). The genuine field's fibre bound is
inherited verbatim. Its only `sorry`-dependence is through that posited curvature input. -/
theorem exists_pointwiseTensorCurv_genuineField_divergenceSplit
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G Drem : SmoothCcTensor g 0 (s + 1),
        pointwiseTensorCurv (I := I) (M := M) g s S = G + Drem ∧
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) Drem.toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun = 0 ∧
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (G.toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨K, hK_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_bracketFreePairing_field (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, hpair, hbound⟩ := hfield s S
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  refine ⟨G, Curv - G, by abel, ?_, hbound⟩
  have hCurv_eq : Curv = G + (Curv - G) := by abel
  have hfun : (G + (Curv - G)).toFun = G.toFun + (Curv - G).toFun :=
    SmoothCcTensor.toFun_add G (Curv - G)
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) G gradS
  have hint₂ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - G) gradS
  have hsplit : tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) G.toFun gradS.toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - G).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) G.toFun (Curv - G).toFun gradS.toFun
      hint₁ hint₂
  rw [hpair] at hsplit
  linarith [hsplit]

/-- **The integrated bracket-free curvature field in canonical `inner ℝ` form (proved from the
genuine-field / divergence-split input).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for
every smooth compactly-supported `(0, s)`-tensor `S`, there is a curvature contraction field
`G : SmoothCcTensor g 0 (s + 1)` — the genuine `R(∇S) + (∇R) S` part of the order-`2` commutator
defect `Curv S := pointwiseTensorCurv g s S` — for which the canonical real inner-product cross-pairing
of `Curv S` against `∇S = covGrad g 0 s S` equals that of `G` against `∇S` (the moving-frame bracket
integrating by parts to zero), and `G` is *pointwise* fibre-norm-controlled by `∇S` and `S`. This is
**proved** from the genuine-field / divergence-split input
`exists_pointwiseTensorCurv_genuineField_divergenceSplit`: the section-level identity `Curv S = G +
Drem` and the IBP-vanishing `⟨Drem, ∇S⟩_{L²} = 0` give `⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}` by
`tensorL2Inner` bilinearity (`tensorL2Inner_add_left` on `G.toFun + Drem.toFun`), and the canonical
`inner ℝ` form follows by `SmoothCcTensor.inner_def`. Its only `sorry`-dependence is through that
posited curvature input. -/
theorem exists_pointwiseTensorCurv_genuineField_inner (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      ∃ G : SmoothCcTensor g 0 (s + 1),
        (inner ℝ (pointwiseTensorCurv (I := I) (M := M) g s S)
            (covGrad (I := I) (M := M) g 0 s S) : ℝ) =
          (inner ℝ G (covGrad (I := I) (M := M) g 0 s S) : ℝ) ∧
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (G.toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨K, hK_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_genuineField_divergenceSplit (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, Drem, hsplit, hibp, hbound⟩ := hfield s S
  refine ⟨G, ?_, hbound⟩
  have hcurv := SmoothCcTensor.inner_def (I := I) (M := M)
    (pointwiseTensorCurv (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
  have hG := SmoothCcTensor.inner_def (I := I) (M := M) G (covGrad (I := I) (M := M) g 0 s S)
  rw [hcurv, hG, hsplit]
  have hfun : (G + Drem).toFun = G.toFun + Drem.toFun := SmoothCcTensor.toFun_add G Drem
  rw [hfun]
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    G (covGrad (I := I) (M := M) g 0 s S)
  have hint₂ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    Drem (covGrad (I := I) (M := M) g 0 s S)
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) G.toFun Drem.toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun hint₁ hint₂, hibp, add_zero]

/-- **The integrated bracket-free curvature field of the cross term (proved from the genuine-field
input).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, there exists a curvature contraction field `G : SmoothCcTensor g 0 (s + 1)` —
the genuine `R(∇S) + (∇R) S` part of the order-`2` commutator defect `Curv S := pointwiseTensorCurv
g s S` — for which the `L²` cross-pairing of `Curv S` against `∇S = covGrad g 0 s S` equals that of
`G` against `∇S` (the moving-frame bracket integrating by parts to zero), and `G` is *pointwise*
fibre-norm-controlled by `∇S` and `S`:
```
⟨Curv S, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}   and
rfns(G)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )   (every x).
```
This is **proved** from the genuine-field input `exists_pointwiseTensorCurv_genuineField_inner` by
bridging the `tensorL2Inner … .toFun` formulation to the canonical real inner-product-space form
`inner ℝ` on `SmoothCcTensor` (`SmoothCcTensor.inner_def`). Its only `sorry`-dependence is through
that posited curvature input. -/
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
  classical
  obtain ⟨K, hK_nn, hfield⟩ :=
    exists_pointwiseTensorCurv_genuineField_inner (I := I) (M := M) g
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, hpair, hbound⟩ := hfield s S
  refine ⟨G, ?_, hbound⟩
  rw [← SmoothCcTensor.inner_def (I := I) (M := M)
      (pointwiseTensorCurv (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S),
    ← SmoothCcTensor.inner_def (I := I) (M := M) G (covGrad (I := I) (M := M) g 0 s S)]
  exact hpair

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

/-- **Posited iterated-Ricci primitive, positive-order regime: the per-order curvature-derivative
component expansion of `∇(Defect (p + 1))`.** For a closed smooth Riemannian manifold `(M, g)`
there is an *order-dependent* nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth
compactly-supported `(0, 2)`-tensor base `U` and every *positive* gradient order `p + 1`, there is a
family of `(0, 2 + (p + 1) + 1)`-tensor global fields `H i : SmoothCcTensor g 0 (2 + (p + 1) + 1)`
(`i ∈ Fin ((p + 1) + 1 + 2)`) whose sum is the field
`∇(Defect (p + 1)) = ∇(Δ_∇(∇^{p+1} U) − ∇^{p+1}(Δ_∇ U))`, with each component fibre-norm-bounded at
**every** `x` by `(Dc (p + 1))²` times the intrinsic fibre norm of the `i`-th iterated gradient
`∇^i U = iteratedCovGrad g 0 2 i U`:
```
∇(Defect (p + 1)) = ∑_{i < p + 4} H i,   rfns(H i)(x) ≤ (Dc (p + 1))² · rfns(∇^i U)(x).
```
This is the genuinely-missing **iterated Ricci identity** content at positive order — the base case
`p = 0` (`∇(Defect 0) = ∇(Δ_∇ U − Δ_∇ U) = ∇ 0 = 0`) is proved *outright* in
`exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion`, so only the positive-order regime
is posited here. Its construction iterates the single-step Ricci commutator `[Δ_∇, ∇] =
curvature-contraction` (the rank-generic single-step defect `pointwiseTensorCurv`, whose commutator
equation is `pointwiseTensorCurv_commutator_eq`) along the defect recursion `Defect (p + 1) =
∇(Defect p) + Curv (∇^p U)`: each covariant gradient applied to the defect produces one further
contraction of a covariant derivative of curvature; the top-order `∇^{p+3} U` terms cancel by the
single-step Ricci identity, leaving the finite curvature-derivative sum over orders `i ≤ p + 2`, with
all curvature-derivative coefficients continuous on the compact `M`, hence sup-bounded. The
components `H i` are *constrained* to the genuine iterated-Ricci contractions by the per-component
`rfns(∇^i U)`-bounds — a degenerate witness (e.g. `H 0 = ∇(Defect (p + 1))`, rest `0`) is rejected
because then `rfns(H 0) ≤ (Dc (p + 1))² · rfns(U)` would be *false* (`∇(Defect (p + 1))` carries all
orders `≤ p + 3`, not just `rfns(U)`).

The body is `sorry`: this is the genuinely-missing positive-order iterated-Ricci component-field
expansion. The full-order theorem
`exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion` is *proved* on top of it by case
analysis on the order (`p = 0` outright, `p + 1` forwarded here). -/
theorem exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion_succ
    (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ∃ H : Fin ((p + 1) + 1 + 2) → SmoothCcTensor g 0 (2 + (p + 1) + 1),
          covGrad g 0 (2 + (p + 1))
              (rawTensorConnLapSmooth (I := I) g 0 (2 + (p + 1)) (iteratedCovGrad g 0 2 (p + 1) U) -
                iteratedCovGrad g 0 2 (p + 1)
                  (rawTensorConnLapSmooth (I := I) g 0 2 U)) =
            ∑ i : Fin ((p + 1) + 1 + 2), H i ∧
          ∀ (i : Fin ((p + 1) + 1 + 2)) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (p + 1) + 1) x ((H i).toSection x) ≤
              Dc (p + 1) ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i : ℕ)) x
                  ((iteratedCovGrad g 0 2 (i : ℕ) U).toSection x) := by
  sorry

/-- **Posited iterated-Ricci primitive: the per-order curvature-derivative component expansion of
`∇(Defect p)` (section-level field form).** For a closed smooth Riemannian manifold `(M, g)` there
is an *order-dependent* nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth
compactly-supported `(0, 2)`-tensor base `U` and every gradient order `p`, there is a family of
`(0, 2 + p + 1)`-tensor *global fields* `H i : SmoothCcTensor g 0 (2 + p + 1)` (`i ∈ Fin (p + 1 + 2)`)
whose sum is the field `∇(Defect p) = ∇(Δ_∇(∇^p U) − ∇^p(Δ_∇ U))`, with each component
fibre-norm-bounded at **every** `x` by `(Dc p)²` times the intrinsic fibre norm of the `i`-th
iterated gradient `∇^i U = iteratedCovGrad g 0 2 i U`:
```
∇(Defect p) = ∑_{i < p + 3} H i,   rfns(H i)(x) ≤ (Dc p)² · rfns(∇^i U)(x).
```
This is the genuinely-missing **iterated Ricci identity** content. Its construction iterates the
single-step Ricci commutator `[Δ_∇, ∇] = curvature-contraction` (the rank-generic single-step defect
`pointwiseTensorCurv`, whose commutator equation is `pointwiseTensorCurv_commutator_eq`) `p` times
along the defect recursion `Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)`: each covariant gradient
applied to the defect produces one further contraction of a covariant derivative of curvature; the
top-order `∇^{p+3} U` terms cancel by the single-step Ricci identity, leaving the finite
curvature-derivative sum over orders `i ≤ p + 2`, with all curvature-derivative coefficients up to
order `p + 1` continuous on the compact `M`, hence sup-bounded. The base case `p = 0` is genuinely
`∇(Defect 0) = ∇(Δ_∇ U − Δ_∇ U) = ∇ 0 = 0` (all three components vanish); the order-dependence of
`Dc` reflects the growth of the term count and the slot count of the tensor-bundle curvature
endomorphism with `p`. The components `H i` are *constrained* to the genuine iterated-Ricci
contractions by the per-component `rfns(∇^i U)`-bounds — a degenerate witness (e.g. `H 0 =
∇(Defect p)`, rest `0`) is rejected because then `rfns(H 0) ≤ (Dc p)² · rfns(U)` would be *false*
(`∇(Defect p)` carries all orders `≤ p + 2`, not just `rfns(U)`).

This is **proved** by case analysis on the order `p`. The base case `p = 0` is genuinely
`∇(Defect 0) = ∇(Δ_∇ U − Δ_∇ U) = ∇ 0 = 0` (all `3` components taken to be the zero field, the sum
identity `0 = ∑ 0` and each bound `0 ≤ (Dc 0)² · rfns(∇^i U)` immediate from
`riemannianFiberNormSq_zero` and the nonnegativity of the right-hand side); the positive-order regime
`p + 1` is forwarded to the posited iterated-Ricci primitive
`exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion_succ`. The order-dependence of `Dc`
reflects the growth of the term count and the slot count of the tensor-bundle curvature endomorphism
with `p`. The components `H i` are *constrained* to the genuine iterated-Ricci contractions by the
per-component `rfns(∇^i U)`-bounds — a degenerate witness (e.g. `H 0 = ∇(Defect p)`, rest `0`) is
rejected because then `rfns(H 0) ≤ (Dc p)² · rfns(U)` would be *false* (`∇(Defect p)` carries all
orders `≤ p + 2`, not just `rfns(U)`).

The per-order section component theorem `exists_covGrad_commutatorDefect_component_field` is *proved*
on top of it by forwarding the component family, the sum identity, and the per-component bounds; the
per-point component form `exists_covGrad_commutatorDefect_component_fiberNormSq_bound` is in turn
*proved* from that by reading the section identity off pointwise through the additivity of
`toSection`. -/
theorem exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion
    (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ∃ H : Fin (p + 1 + 2) → SmoothCcTensor g 0 (2 + p + 1),
          covGrad g 0 (2 + p)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
                iteratedCovGrad g 0 2 p
                  (rawTensorConnLapSmooth (I := I) g 0 2 U)) =
            ∑ i : Fin (p + 1 + 2), H i ∧
          ∀ (i : Fin (p + 1 + 2)) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x ((H i).toSection x) ≤
              Dc p ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i : ℕ)) x
                  ((iteratedCovGrad g 0 2 (i : ℕ) U).toSection x) := by
  classical
  obtain ⟨Dc, hDc_nn, hsucc⟩ :=
    exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion_succ (I := I) (M := M) g
  refine ⟨Dc, hDc_nn, fun U p => ?_⟩
  match p with
  | 0 =>
      -- Base case: `Defect 0 = Δ_∇ U − Δ_∇ U = 0`, so `∇(Defect 0) = ∇ 0 = 0`.
      refine ⟨fun _ => 0, ?_, ?_⟩
      · have hzero : (rawTensorConnLapSmooth (I := I) g 0 (2 + 0)
              (iteratedCovGrad g 0 2 0 U) -
            iteratedCovGrad g 0 2 0 (rawTensorConnLapSmooth (I := I) g 0 2 U)) = 0 := by
          rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
          abel
        rw [hzero, covGrad_zero, Finset.sum_const, smul_zero]
      · intro i x
        rw [SmoothCcTensor.toSection_zero]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
        rw [riemannianFiberNormSq_zero]
        exact mul_nonneg (sq_nonneg (Dc 0))
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + (i : ℕ)) x _)
  | (q + 1) =>
      exact hsucc U q

/-- **Posited deepest curvature child for the gradient-of-commutator-defect bound (per-order,
per-component, *section-level field* form).** The genuine one-higher-derivative iterated
curvature-coefficient expansion of the commutator defect, isolated *per curvature-derivative
component* as smooth compactly-supported *global fields*. By the iterated Ricci identity, the
covariant gradient of the order-`p` commutator defect `∇(Defect p) = ∇(Δ_∇(∇^p U) − ∇^p(Δ_∇ U))`
expands as a finite sum over orders `i ≤ p + 2` of curvature-derivative contractions of the `i`-th
iterated gradient `∇^i U` (the top-order term cancelling by the single-step Ricci identity
`pointwiseTensorCurv_commutator_eq` applied `p` times), with all curvature-derivative coefficients
up to order `p + 1` continuous on the compact manifold, hence sup-bounded.

This says: there is an *order-dependent* nonnegative constant `Dc : ℕ → ℝ` such that, for every
`(0, 2)`-tensor base `U` and every gradient order `p`, there is a family of `(0, 2 + p + 1)`-tensor
*global fields* `H i : SmoothCcTensor g 0 (2 + p + 1)` (`i ∈ Fin (p + 1 + 2)`, the per-order
curvature-derivative components) whose sum is the field `∇(Defect p)`, with each component
fibre-norm-bounded at every `x` by `(Dc p)²` times the intrinsic fibre norm of `∇^i U`:
```
∇(Defect p) = ∑_{i < p + 3} H i,   rfns(H i)(x) ≤ (Dc p)² · rfns(∇^i U)(x).
```
Each curvature-derivative coefficient is the genuine iterated-Ricci contraction; the constant is
order-dependent because the number of terms and the slot count of the tensor-bundle curvature
endomorphism grow with `p`. This is **proved** from the iterated-Ricci component-expansion primitive
`exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion` by forwarding the component
family, the sum identity, and the per-component bounds; the per-point component form
`exists_covGrad_commutatorDefect_component_fiberNormSq_bound` is in turn *proved* from this by
reading the section identity off pointwise through the additivity of `toSection`. -/
theorem exists_covGrad_commutatorDefect_component_field
    (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ∃ H : Fin (p + 1 + 2) → SmoothCcTensor g 0 (2 + p + 1),
          covGrad g 0 (2 + p)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
                iteratedCovGrad g 0 2 p
                  (rawTensorConnLapSmooth (I := I) g 0 2 U)) =
            ∑ i : Fin (p + 1 + 2), H i ∧
          ∀ (i : Fin (p + 1 + 2)) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x ((H i).toSection x) ≤
              Dc p ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i : ℕ)) x
                  ((iteratedCovGrad g 0 2 (i : ℕ) U).toSection x) := by
  classical
  obtain ⟨Dc, hDc_nn, hexp⟩ :=
    exists_covGrad_commutatorDefect_iteratedRicci_componentExpansion (I := I) (M := M) g
  refine ⟨Dc, hDc_nn, fun U p => ?_⟩
  obtain ⟨H, hsum, hbound⟩ := hexp U p
  exact ⟨H, hsum, hbound⟩

/-- **The per-component iterated curvature-derivative fibre-norm bound (proved from the
section-level field decomposition, per-order).** For a closed smooth Riemannian manifold `(M, g)`
there is an *order-dependent* nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth
compactly-supported `(0, 2)`-tensor base `U`, every gradient order `p`, and *every point* `x`, the
fibre value of the covariant gradient of the order-`p` commutator defect
`Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` is a finite sum of `p + 3` curvature-derivative components
`H i`, each fibre-bounded by `(Dc p)²` times `rfns(∇^i U)`. This is **proved** from the section-level
field decomposition `exists_covGrad_commutatorDefect_component_field` (which supplies global
component fields `H i` with `∇(Defect p) = ∑ i, H i` and the per-point fibre bounds) by reading the
section identity off at `x` through the additivity of `toSection` (`SmoothCcTensor.toSection_add`,
`SmoothCcTensor.toSection_zero`, `ContMDiffSection.coe_add`). Its only `sorry`-dependence is through
that posited curvature input; the aggregate bound
`exists_covGrad_commutatorDefect_pointwise_fiberNormSq_bound` is in turn *proved* from this by the
finite-sum subadditivity `riemannianFiberNormSq_sum_le_card_mul`. -/
theorem exists_covGrad_commutatorDefect_component_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ) (x : M),
        ∃ H : Fin (p + 1 + 2) → TensorRSSpace 0 (2 + p + 1) I x,
          (covGrad g 0 (2 + p)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
                iteratedCovGrad g 0 2 p
                  (rawTensorConnLapSmooth (I := I) g 0 2 U))).toSection x =
            ∑ i : Fin (p + 1 + 2), H i ∧
          ∀ i : Fin (p + 1 + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x (H i) ≤
              Dc p ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i : ℕ)) x
                  ((iteratedCovGrad g 0 2 (i : ℕ) U).toSection x) := by
  classical
  obtain ⟨Dc, hDc_nn, hfield⟩ :=
    exists_covGrad_commutatorDefect_component_field (I := I) (M := M) g
  refine ⟨Dc, hDc_nn, fun U p x => ?_⟩
  obtain ⟨H, hsum, hbound⟩ := hfield U p
  refine ⟨fun i => (H i).toSection x, ?_, fun i => hbound i x⟩
  have hread : ∀ (s : Finset (Fin (p + 1 + 2))),
      (∑ i ∈ s, H i).toSection x = ∑ i ∈ s, (H i).toSection x := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, SmoothCcTensor.toSection_zero]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, SmoothCcTensor.toSection_add]
        simp only [ContMDiffSection.coe_add, Pi.add_apply]
        rw [ih]
  rw [hsum]
  exact hread Finset.univ

/-- **The pointwise gradient-of-commutator-defect fibre-norm bound (proved from the per-component
input, per-order).** For a closed smooth Riemannian manifold `(M, g)` there is an *order-dependent*
nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth compactly-supported `(0, 2)`-tensor
base `U`, every gradient order `p`, and *every point* `x`, the intrinsic fibre norm of the covariant
gradient of the order-`p` commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` is bounded by
`(Dc p)²` times the sum of the intrinsic fibre norms of the `≤ p + 2`-order gradients of `U`:
```
rfns(∇(Defect p))(x) ≤ (Dc p)² · ∑_{i ≤ p + 2} rfns(∇^i U)(x).
```
This is **proved** from the per-component iterated curvature-derivative input
`exists_covGrad_commutatorDefect_component_fiberNormSq_bound` (which exhibits `∇(Defect p)(x)` as a
finite sum of `p + 3` curvature-derivative components, each fibre-bounded by `rfns(∇^i U)`) through
the finite-sum subadditivity `riemannianFiberNormSq_sum_le_card_mul`. Its only `sorry`-dependence is
through that posited curvature input. -/
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
  classical
  obtain ⟨Dc, hDc_nn, hcomp⟩ :=
    exists_covGrad_commutatorDefect_component_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun p => (p + 1 + 2 : ℕ) * Dc p, fun p => ?_, fun U p x => ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _) (hDc_nn p)
  · obtain ⟨H, hsum, hHbound⟩ := hcomp U p x
    set rhs : ℝ := ∑ i ∈ Finset.range (p + 1 + 2),
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x
        ((iteratedCovGrad g 0 2 i U).toSection x) with hrhs
    have hrhs_nn : 0 ≤ rhs :=
      Finset.sum_nonneg (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + i) x _)
    have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 (2 + p + 1) x
      (Finset.univ : Finset (Fin (p + 1 + 2))) H
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have hcomp_sum :
        ∑ i : Fin (p + 1 + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x (H i) ≤
          Dc p ^ 2 * rhs := by
      have hstep :
          ∑ i : Fin (p + 1 + 2),
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x (H i) ≤
            ∑ i : Fin (p + 1 + 2), Dc p ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i : ℕ)) x
                ((iteratedCovGrad g 0 2 (i : ℕ) U).toSection x) :=
        Finset.sum_le_sum (fun i _ => hHbound i)
      refine le_trans hstep ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Dc p))
      rw [hrhs, ← Fin.sum_univ_eq_sum_range
        (fun i => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x
          ((iteratedCovGrad g 0 2 i U).toSection x)) (p + 1 + 2)]
    have hN_nn : (0 : ℝ) ≤ ((p + 1 + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hN_le_sq : ((p + 1 + 2 : ℕ) : ℝ) ≤ ((p + 1 + 2 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((p + 1 + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left 1 (p + 2)
      nlinarith [hN_nn, h1]
    rw [hsum]
    calc riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x (∑ i : Fin (p + 1 + 2), H i)
        ≤ ((p + 1 + 2 : ℕ) : ℝ) *
            ∑ i : Fin (p + 1 + 2),
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + p + 1) x (H i) := hcard
      _ ≤ ((p + 1 + 2 : ℕ) : ℝ) * (Dc p ^ 2 * rhs) :=
          mul_le_mul_of_nonneg_left hcomp_sum hN_nn
      _ ≤ ((p + 1 + 2 : ℕ) : ℝ) ^ 2 * (Dc p ^ 2 * rhs) :=
          mul_le_mul_of_nonneg_right hN_le_sq
            (mul_nonneg (sq_nonneg (Dc p)) hrhs_nn)
      _ = (((p + 1 + 2 : ℕ) : ℝ) * Dc p) ^ 2 * rhs := by ring

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
