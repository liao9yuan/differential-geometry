import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineBracketSectionSplit
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
integrated genuine-field forms, the order-separated three-term section-field split, and the
genuine/bracket section-level divergence decomposition are all *proved* by fibre subadditivity /
inner-product bridges / the covariant Green identity / order-induction over exactly **two** deepest
general-valence curvature primitives whose bodies are `sorry` (the genuine remaining moving-frame
curvature-endomorphism content): the genuine moving-frame third-order Weitzenböck field decomposition
with proportional fibre bounds and the concrete spectral pairing
(`exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing`) — the explicit genuine
`R(∇S)` and `(∇R) S` fields, their `rfns(∇S)` / `rfns(S)`-order fibre bounds, the moving-frame
remainder's `∇²S`-order fibre bound, and the integrated spectral pairing
`⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (the genuine fields carry exactly the
Weitzenböck curvature integral) — and the **covariant-product** primitive
(`exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound`), the iterated-gradient `L²` bound on the
single-step commutator defect `‖∇^m(Curv T)‖ ≤ Cic s m · ∑_{i ≤ m + 2} ‖∇^i T‖`. The bracket-free
pairing form (`exists_pointwiseTensorCurv_genuineFields_proportional_bracketFreePairing`,
`⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`) is *proved* from the spectral-pairing form by
rewriting the concrete spectral scalar back through the already-proved integrated order-`2`
Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`; the named-remainder, order-separated,
and genuine/bracket forms are *proved* from it by naming `Grem := Curv S − Gcurv − GcurvDeriv`,
transferring the fibre bounds, and deriving its integrated nullity by left additivity of the `L²`
pairing. The gradient-of-commutator-defect bound `exists_covGrad_commutatorDefect_l2_bound` is
*proved* from the **general iterated-gradient commutator-defect bound**
`exists_iteratedCovGrad_commutatorDefect_l2_bound` (`‖∇^m(Defect p)‖ ≤ Dc p m · ∑_{i ≤ p + m + 1}
‖∇^i U‖`), which is itself *proved* by induction on `p` (the inductive hypothesis used at `m + 1`)
from the defect recursion `Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)` and the covariant-product
primitive — each covariant gradient through the iterated structure handled by the gradient-commuting
`norm_iteratedCovGrad_covGrad_comm` and gradient-composition `norm_iteratedCovGrad_iteratedCovGrad`
lemmas, the base case being the outright vanishing `Defect 0 = 0`. Consumers transitively depend on
`sorryAx` through the two deepest curvature primitives named above.

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

/-- **Posited deepest curvature primitive (the strictly-more-primitive *spectral-pairing* core):
the genuine third-order Weitzenböck field decomposition with proportional fibre bounds and the
concrete spectral pairing.** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s`
and for every smooth compactly-supported `(0, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` admits two *genuine curvature* fields `Gcurv, GcurvDeriv :
SmoothCcTensor g 0 (s + 1)` — the section-level packagings of the pure-Riemann contraction
`R(∇S)` (the frame-sum of `riemannOp` on the gradient field `∇S = covGrad g 0 s S`, the Ricci
identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` with the proportional fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen` upgraded to a uniform proportional bound over the compact
`M`) and the differentiated-curvature contraction `(∇R) S` (`covGradCurvatureContraction`, its
uniform sup `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` upgraded to a bound
proportional to `rfns(S)`) — with the four genuine third-order Bochner–Weitzenböck properties:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · rfns(S)(x)` — the `∇R` field, genuinely `rfns(S)`-order;
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · rfns(∇²S)(x)` — the moving-frame /
  frame-bracket remainder, genuinely `rfns(∇²S)`-order after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity;
* `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` — the *spectral pairing*: the
  genuine fields carry exactly the Weitzenböck curvature integral. The right-hand side is the
  concrete spectral scalar (the squared `L²` norms of the rough Laplacian `Δ_∇S =
  rawTensorConnLapSmooth g 0 s S` and the iterated gradient `∇²S = covGrad g 0 (s+1) (covGrad g 0
  s S)`), *not* the abstract cross-pairing — that is exactly what makes this the strictly-more-
  primitive form: it states the integrated identity in the terms a fixed-frame computation
  produces, before invoking the Weitzenböck identity to identify it with `⟨Curv S, ∇S⟩_{L²}`.

This is the genuinely-missing third-order Bochner–Weitzenböck curvature core — the deepest
moving-frame curvature endomorphism content at general rank. Its construction bridges the
fixed-frame section representation `pointwiseTensorCurv_toSection_eq_frame_sum` ("no moving-frame
derivative survives") to the directional genuine/bracket split
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` (`Tensor3rdCurv_eq_genuine_add_bracket`),
its genuine part `tensor3rdCurvGenuine` fibre-bounded by `riemannianFiberNormSq_tensor3rdCurvGenuine_le`
fed by the proportional curvature / differentiated-curvature bounds, the surviving moving-frame /
frame-bracket discrepancy (`tensor3rdCurvBracket` plus the frame-trace discrepancy
`covGradRoughLapTraceDiscrepancy` and the moving-frame residual `covGradRoughLapMovingFrameResidual`)
being genuinely `∇²S`-order and a total covariant divergence of an `∇S`-order field, so its
contribution to the `L²` pairing is the Weitzenböck curvature integral `‖Δ_∇S‖² − ‖∇²S‖²` (the
clean `slot0FrameTraceMatching` is *false* on a normal manifold (S²), so the honest primitive
carries the bracket remainder explicitly rather than asserting a clean cancellation). The
decomposition rejects the degenerate witness: with `Gcurv = GcurvDeriv = 0` the spectral pairing
reads `0 = ‖Δ_∇S‖² − ‖∇²S‖²`, which is *false* in general, so the genuine fields must carry the
actual Weitzenböck curvature integral. -/
theorem exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing
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
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun =
            tensorL2Norm (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
              tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
                (covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 :=
  pointwiseTensorCurv_genuineFields_proportional_spectralPairing_core (I := I) (M := M) g

/-- **Posited deepest curvature primitive (the strictly-more-primitive structural core): the
genuine third-order Weitzenböck field decomposition with proportional fibre bounds and the
bracket-free `L²` pairing.** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s`
and for every smooth compactly-supported `(0, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` admits two *genuine curvature* fields `Gcurv, GcurvDeriv :
SmoothCcTensor g 0 (s + 1)` — the section-level packagings of the pure-Riemann contraction
`R(∇S)` (the frame-sum of `riemannOp` on the gradient field `∇S = covGrad g 0 s S`, the Ricci
identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` with the proportional fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen` upgraded to a uniform proportional bound over the compact
`M`) and the differentiated-curvature contraction `(∇R) S` (`covGradCurvatureContraction`, its
uniform sup `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` upgraded to a bound
proportional to `rfns(S)`) — with the four genuine third-order Bochner–Weitzenböck properties:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · rfns(S)(x)` — the `∇R` field, genuinely `rfns(S)`-order;
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · rfns(∇²S)(x)` — the moving-frame /
  frame-bracket remainder (`tensor3rdCurvBracket` plus the frame-trace discrepancy
  `covGradRoughLapTraceDiscrepancy` and the moving-frame residual
  `covGradRoughLapMovingFrameResidual`), genuinely `rfns(∇²S)`-order after the third-order
  Weitzenböck cancellation of the top-order `∇³S` terms by the iterated Ricci identity;
* `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` — the *bracket-free `L²` pairing*: the
  moving-frame / frame-bracket remainder is a total covariant divergence of an `∇S`-order field,
  so it integrates by parts to zero against `∇S` by the covariant Green identity
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`, leaving the genuine fields to
  carry the entire pairing.

This is the genuinely-missing third-order Bochner–Weitzenböck curvature core. It is **proved**
from the strictly-more-primitive *spectral-pairing* form of the same field decomposition,
`exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing`, which exhibits the same
explicit genuine fields with the three proportional fibre bounds but states the integrated
pairing in the strictly-more-primitive *concrete spectral scalar* form
`⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (the genuine fields carry exactly the
Weitzenböck curvature integral). The bracket-free pairing against `Curv S` follows by rewriting
that concrete spectral scalar back to `⟨Curv S, ∇S⟩_{L²}` through the **already-proved** integrated
order-`2` Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`
(`‖∇²S‖²_{L²} = ‖Δ_∇S‖²_{L²} − ⟨Curv S, ∇S⟩_{L²}`, hence `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} −
‖∇²S‖²_{L²}`), using that `pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` *definitionally*. This
reduction is genuine and non-circular: it replaces the abstract cross-pairing `⟨Curv S, ∇S⟩_{L²}`
in the spectral-pairing primitive by the concrete spectral scalar `‖Δ_∇S‖² − ‖∇²S‖²`, a
simplification consumers cannot perform without the Weitzenböck theorem.

The named-remainder form `exists_pointwiseTensorCurv_genuineCurvature_namedRemainderField` follows
by naming `Grem := Curv S − Gcurv − GcurvDeriv` (the section identity is `abel`) and deriving the
integrated nullity `⟨Grem, ∇S⟩_{L²} = 0` from the bracket-free pairing through the left additivity
of the `L²` pairing (`tensorL2Inner_add_left`). The decomposition rejects the degenerate witness:
with `Gcurv = GcurvDeriv = 0` the bracket-free pairing reads `0 = ⟨Curv S, ∇S⟩_{L²}`, which is
*false* in general (it equals `‖Δ_∇S‖² − ‖∇²S‖²` by `weitzenbock_integrated_covGrad_l2_normSq`), so
the genuine fields must carry the actual curvature pairing. -/
theorem exists_pointwiseTensorCurv_genuineFields_proportional_bracketFreePairing
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
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun =
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, hspec⟩ := hfields s S
  refine ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, ?_⟩
  -- Rewrite the concrete spectral scalar `‖Δ_∇S‖² − ‖∇²S‖²` back to the cross-pairing
  -- `⟨Curv S, ∇S⟩` through the already-proved integrated order-`2` Weitzenböck identity.
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g s S
  -- `pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` definitionally, so the cross term in the
  -- Weitzenböck identity is exactly `⟨Curv S, ∇S⟩`.
  have hcross :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
          tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
    have hdef :
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun =
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun := rfl
    rw [hdef]
    linarith [hweitz]
  rw [hspec, ← hcross]

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
It is **proved** from the strictly-more-primitive structural curvature input
`exists_pointwiseTensorCurv_genuineFields_proportional_bracketFreePairing` (which supplies the
explicit genuine fields `Gcurv, GcurvDeriv`, the three proportional fibre bounds, and the
bracket-free `L²` pairing `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`) by naming the
remainder `Grem := Curv S − Gcurv − GcurvDeriv` (the section identity is `abel`), transferring the
three fibre bounds verbatim, and deriving the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0` from the
bracket-free pairing through the left additivity of the `L²` pairing (`tensorL2Inner_add_left` on
`(Gcurv + GcurvDeriv).toFun + Grem.toFun = Curv S.toFun`, joint integrability
`SmoothCcTensor.integrable_inner_cross`). Its only `sorry`-dependence is through that posited
curvature input, whose construction bridges the fixed-frame section representation
`pointwiseTensorCurv_toSection_eq_frame_sum` to the directional genuine/bracket split
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` (the unresolved moving-frame residual
documented in `FreeDirectionReduction.lean`, `TraceDiscrepancyDecomposition.lean`; the clean
`slot0FrameTraceMatching` is *false* on a normal manifold (S²), so the honest primitive carries the
bracket remainder explicitly rather than asserting a clean cancellation). The decomposition rejects
the degenerate witness: `Gcurv = GcurvDeriv = 0`, `Grem = Curv S` makes the `Grem`-bound
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
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    exists_pointwiseTensorCurv_genuineFields_proportional_bracketFreePairing
      (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, hpair⟩ := hfields s S
  refine ⟨Gcurv, GcurvDeriv, pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv,
    by abel, hcurv, hcurvDeriv, hrem, ?_⟩
  -- The named remainder pairs to zero: the bracket-free pairing identity says the genuine
  -- fields `Gcurv + GcurvDeriv` carry the entire `⟨Curv S, ∇S⟩` pairing, so the complementary
  -- remainder `Curv S − Gcurv − GcurvDeriv` pairs to `0` by left additivity of the `L²` pairing.
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hpair] at hsplit
  linarith [hsplit]

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

/-- **`∇^m` is additive.** The iterated covariant gradient `∇^m = iteratedCovGrad g r s m`
distributes over addition of smooth compactly-supported tensors. Proved by induction on `m`
through `covGrad_add`. -/
theorem iteratedCovGrad_add (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (A B : SmoothCcTensor g r s) :
    iteratedCovGrad g r s m (A + B) =
      iteratedCovGrad g r s m A + iteratedCovGrad g r s m B := by
  induction m with
  | zero => simp only [iteratedCovGrad_zero]
  | succ k ih =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_add]

/-- **`∇^m` annihilates the zero tensor.** -/
theorem iteratedCovGrad_zero_tensor (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad g r s m (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => simp only [iteratedCovGrad_zero]
  | succ k ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

/-- **Heterogeneous rank-congruence for `covGrad`.** If two ranks agree (`h : a = b`), then the
once-differentiated tensors `covGrad g r a Y` and `covGrad g r b Z` are heterogeneously equal
whenever `Y` and `Z` are (`hYZ : HEq Y Z`). Proved by `subst` on the rank variable `b` and the
section. The canonical naturality of `covGrad` under a rank reassociation. -/
theorem covGrad_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **The seminorm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously equal smooth
compactly-supported tensors over agreeing ranks have equal `L²` seminorms. Proved by `subst` on the
rank variable. -/
theorem norm_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    ‖Y‖ = ‖Z‖ := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying
`m` covariant gradients to `covGrad g r s X` (the once-differentiated `(r, s + 1)`-tensor) is
heterogeneously equal to the `(m + 1)`-fold iterated gradient of `X`, the two living in the ranks
`(s + 1) + m` and `s + (m + 1)`, which agree as natural numbers. The covariant gradient at the
innermost slot equals it at the outermost slot. Proved by induction on `m` through the
`covGrad` rank-congruence `covGrad_heq_congr`. -/
theorem iteratedCovGrad_covGrad_comm_heq (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **Commuting one covariant gradient through the iterated gradient (norm form).** Applying `m`
covariant gradients to `covGrad g r s X` has the same `L²` norm as the `(m + 1)`-fold iterated
gradient of `X`: the rank reassociation `(s + 1) + m = s + (m + 1)` is invisible to the seminorm.
Proved from the heterogeneous commuting `iteratedCovGrad_covGrad_comm_heq` through the
seminorm rank-cast `norm_heq_congr`. -/
theorem norm_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    ‖iteratedCovGrad g r (s + 1) m (covGrad g r s X)‖ =
      ‖iteratedCovGrad g r s (m + 1) X‖ :=
  norm_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq (g := g) (r := r) (s := s) (m := m) X)

/-- **Heterogeneous composition of iterated covariant gradients.** The `b`-fold iterated gradient
of the `a`-fold iterated gradient of `X` is the `(a + b)`-fold iterated gradient of `X`, the two
living in the ranks `(s + a) + b` and `s + (a + b)`, which agree as natural numbers. Proved by
induction on `b` through the `covGrad` rank-congruence `covGrad_heq_congr`. -/
theorem iteratedCovGrad_iteratedCovGrad_heq (g : SmoothRiemannianMetric I M) (r s a b : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + a) b (iteratedCovGrad g r s a X))
      (iteratedCovGrad g r s (a + b) X) := by
  induction b with
  | zero =>
      rw [iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + a) (j := k)
        (iteratedCovGrad g r s a X)]
      rw [show a + (k + 1) = (a + k) + 1 from by omega,
        iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := a + k) X]
      exact covGrad_heq_congr g r (by omega : (s + a) + k = s + (a + k)) ih

/-- **Composition of iterated covariant gradients (norm form).** The `L²` norm of `∇^b(∇^a X)`
equals that of `∇^{a + b} X`: the rank reassociation `(s + a) + b = s + (a + b)` is invisible to the
seminorm. Proved from `iteratedCovGrad_iteratedCovGrad_heq` through `norm_heq_congr`. -/
theorem norm_iteratedCovGrad_iteratedCovGrad (g : SmoothRiemannianMetric I M) (r s a b : ℕ)
    (X : SmoothCcTensor g r s) :
    ‖iteratedCovGrad g r (s + a) b (iteratedCovGrad g r s a X)‖ =
      ‖iteratedCovGrad g r s (a + b) X‖ :=
  norm_heq_congr g r (by omega : (s + a) + b = s + (a + b))
    (iteratedCovGrad_iteratedCovGrad_heq (g := g) (r := r) (s := s) (a := a) (b := b) X)

/-- **Posited deepest moving-frame curvature-jet primitive: the order-`m` genuine + remainder fibre
decomposition of the iterated covariant gradient of the single-step commutator defect.** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
`Cgr : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every gradient order `m`, for every smooth
compactly-supported `(0, s)`-tensor `T`, and at *every point* `x`, the fibre value of the `m`-fold
iterated covariant gradient of the order-`2` single-step commutator defect
`Curv T := pointwiseTensorCurv g s T` splits as

```
(∇^m(Curv T))(x) = Ggen + Grem,
```

with the *genuine curvature-jet* part `Ggen` fibre-bounded by `(Cgr s m)²` times the sum of the lower
iterated-gradient fibre norms `∑_{i ≤ m + 1} rfns(∇^i T)(x)`, and the *moving-frame remainder* `Grem`
fibre-bounded by `(Cgr s m)²` times the single top-order-but-one fibre norm `rfns(∇^{m + 2} T)(x)`:

```
rfns(Ggen)(x) ≤ (Cgr s m)² · ∑_{i ≤ m + 1} rfns(∇^i T)(x),
rfns(Grem)(x) ≤ (Cgr s m)² · rfns(∇^{m + 2} T)(x).
```

This is the genuine rank-generic *and* order-generic moving-frame third-order Bochner–Weitzenböck
curvature-jet decomposition — the order-`m` generalization of the `m = 0` genuine + remainder split
`exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`Curv T (x) = Ggen + Grem`, `Ggen` bounded by `rfns(T) + rfns(∇T)`, `Grem` by `rfns(∇²T)`). Applying
`∇^m` to the defect `Curv T = Δ_∇(∇T) − ∇(Δ_∇ T)` produces, after the iterated Ricci identity
(`ricci_identity_tensor_commutator_eq_riemannOp`, the rank-generic
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order `∇^{m + 3} T` terms between
the two summands `∇^m(Δ_∇∇T)` and `∇^m(∇Δ_∇T)`, a finite sum of contractions of `∇^{≤ m + 1}`
covariant derivatives of curvature against the iterated gradients `∇^{≤ m + 1} T` (the *genuine
curvature-jet* part `Ggen`, all coefficients sup-bounded on the compact manifold by the uniform
curvature / differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, hence `rfns(∇^{≤ m + 1} T)`-order)
plus the surviving moving-frame / frame-bracket discrepancy (`tensor3rdCurvBracket` and its iterated
analogue, the genuinely `rfns(∇^{m + 2} T)`-order remainder `Grem`). The remainder sits at order
`m + 2` (not `m + 3`) precisely because the top-order `∇^{m + 3} T` terms cancel — the genuine
curvature content a naive per-summand Sobolev order-count cannot recover. The constant is
valence/order-dependent because the tensor-bundle curvature endomorphism is an `O(s + m)`-slot
derivation and the curvature-derivative term count grows with `m`.

It is the strictly-more-primitive *section-split* form that the aggregate fibre bound
`exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound` is *proved* from through the
two-term fibre subadditivity `riemannianFiberNormSq_add_le` and the finite-sum reassembly
`Finset.sum_range_succ` (exactly as the `m = 0` aggregate bound
`exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound` is proved from the `m = 0`
genuine + remainder split). The degenerate witness is rejected because at `m = 0`, `x` arbitrary, the
two bounds read `rfns(Ggen)(x) ≤ (Cgr s 0)²·(rfns(T) + rfns(∇T))(x)` and
`rfns(Grem)(x) ≤ (Cgr s 0)²·rfns(∇²T)(x)` for a split summing to `Curv T (x)`, which is
`exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` — *false* with `Cgr s 0 = 0` on a
non-flat manifold (the defect carries the genuine curvature contraction of `T`). -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cgr : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cgr s m) ∧
      ∀ (s m : ℕ) (T : SmoothCcTensor g 0 s) (x : M),
        ∃ Ggen Grem : TensorRSSpace 0 (s + 1 + m) I x,
          (iteratedCovGrad g 0 (s + 1) m
              (pointwiseTensorCurv (I := I) (M := M) g s T)).toSection x = Ggen + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Ggen ≤
            Cgr s m ^ 2 * ∑ i ∈ Finset.range (m + 2),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((iteratedCovGrad g 0 s i T).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Grem ≤
            Cgr s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
                ((iteratedCovGrad g 0 s (m + 2) T).toSection x) := by
  sorry

/-- **Posited deepest covariant-product curvature primitive: the *pointwise fibre-norm* bound on the
iterated covariant gradient of the single-step commutator defect (rank/order-generic).** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
`Cic : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every gradient order `m`, for every smooth
compactly-supported `(0, s)`-tensor `T`, and at *every point* `x`, the intrinsic fibre norm of the
`m`-fold iterated covariant gradient of the order-`2` single-step commutator defect
`Curv T := pointwiseTensorCurv g s T = Δ_∇(∇T) − ∇(Δ_∇ T)` is bounded by `(Cic s m)²` times the sum of
the intrinsic fibre norms of the lower iterated gradients `∇^i T` (`i ≤ m + 2`):
```
rfns(∇^m(Curv T))(x) ≤ (Cic s m)² · ∑_{i ≤ m + 2} rfns(∇^i T)(x).
```

This is the genuine rank-generic *and* order-generic moving-frame third-order Bochner–Weitzenböck
curvature-jet content — the order-`m` generalization of the `m = 0` fibre bound
`exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound`
(`rfns(Curv T)(x) ≤ (Ccurv s)²·(rfns(T) + rfns(∇T) + rfns(∇²T))(x)`). The defect `Curv T` is a
second-order curvature(-derivative) operator in `T` whose top order *cancels* by the iterated Ricci
identity (`ricci_identity_tensor_commutator_eq_riemannOp`, the rank-generic
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`): applying `∇^m` produces one more contraction of a
covariant derivative of curvature against each one-higher iterated gradient `∇^{≤ m + 2} T`, all
sup-bounded on the compact manifold by the uniform curvature / differentiated-curvature sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The fibre bound holds at order
`m + 2` (not `m + 3`) precisely because the top-order `∇^{m + 3} T` terms cancel between the two
summands `∇^m(Δ_∇∇T)` and `∇^m(∇Δ_∇T)` of the defect — the genuine curvature content that a naive
per-summand Sobolev order-count (which would land at order `m + 3`) cannot recover.

The constant is valence/order-dependent because the tensor-bundle curvature endomorphism is an
`O(s + m)`-slot derivation and the curvature-derivative term count grows with `m` (a single scalar
uniform over all `s, m` is unsatisfiable on a non-flat closed manifold). It is the strictly-more-
primitive *pointwise* form: the `L²` bound
`exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound` is *proved* from it through the purely analytic
finite-sum pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`
(`‖·‖² = ∫ rfns(·)`, integral monotonicity and `∑ pᵢ² ≤ (∑ pᵢ)²`), exactly as the `m = 0` `L²` bound
`exists_pointwiseTensorCurv_l2_bound` is proved from the `m = 0` fibre bound. The degenerate witness
is rejected because at `m = 0`, `x` arbitrary, the bound reads
`rfns(Curv T)(x) ≤ (Cic s 0)²·(rfns(T) + rfns(∇T) + rfns(∇²T))(x)`, which is *false* with `Cic s 0 = 0`
on a non-flat manifold (the defect carries the genuine curvature contraction of `T`). -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Cic : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cic s m) ∧
      ∀ (s m : ℕ) (T : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x
            ((iteratedCovGrad g 0 (s + 1) m
              (pointwiseTensorCurv (I := I) (M := M) g s T)).toSection x) ≤
          Cic s m ^ 2 * ∑ i ∈ Finset.range (m + 3),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
              ((iteratedCovGrad g 0 s i T).toSection x) := by
  classical
  obtain ⟨Cgr, hCgr_nn, hsplit⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound
      (I := I) (M := M) g
  refine ⟨fun s m => Real.sqrt 2 * Cgr s m, fun s m => ?_, fun s m T x => ?_⟩
  · exact mul_nonneg (Real.sqrt_nonneg 2) (hCgr_nn s m)
  · obtain ⟨Ggen, Grem, heq, hgen, hrem⟩ := hsplit s m T x
    set FullSum : ℝ := ∑ i ∈ Finset.range (m + 3),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((iteratedCovGrad g 0 s i T).toSection x) with hFullSum
    set LowSum : ℝ := ∑ i ∈ Finset.range (m + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
          ((iteratedCovGrad g 0 s i T).toSection x) with hLowSum
    have hLowSum_nn : 0 ≤ LowSum :=
      Finset.sum_nonneg (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _)
    have hTop_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
        ((iteratedCovGrad g 0 s (m + 2) T).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + (m + 2)) x _
    have hFull_split : FullSum = LowSum +
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
          ((iteratedCovGrad g 0 s (m + 2) T).toSection x) := by
      rw [hFullSum, hLowSum, Finset.sum_range_succ]
    have hsq2 : (Real.sqrt 2 * Cgr s m) ^ 2 = 2 * Cgr s m ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hCgr_nn' : 0 ≤ Cgr s m := hCgr_nn s m
    rw [heq, hsq2]
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1 + m) x Ggen Grem
    calc riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (Ggen + Grem)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Ggen +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Grem := hadd
      _ ≤ 2 * (Cgr s m ^ 2 * LowSum) +
            2 * (Cgr s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
                ((iteratedCovGrad g 0 s (m + 2) T).toSection x)) := by
          have e1 := mul_le_mul_of_nonneg_left hgen (by norm_num : (0 : ℝ) ≤ 2)
          have e2 := mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = 2 * Cgr s m ^ 2 * FullSum := by rw [hFull_split]; ring

/-- **Posited covariant-product curvature primitive: the iterated covariant gradient of the
single-step commutator defect is `L²`-controlled by the lower iterated gradients of its argument.**
For a closed smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative
constant `Cic : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every gradient order `m`, and for
every smooth compactly-supported `(0, s)`-tensor `T`, the `m`-fold iterated covariant gradient of the
order-`2` single-step commutator defect `Curv T := pointwiseTensorCurv g s T = Δ_∇(∇T) − ∇(Δ_∇ T)`
satisfies

```
‖∇^m(Curv T)‖_{L²} ≤ Cic s m · ∑_{i ≤ m + 2} ‖∇^i T‖_{L²}.
```

This is the genuine **covariant-product (Sobolev) content** isolating the single curvature
contraction's iterated-gradient tower: `Curv T` is a second-order curvature(-derivative) operator in
`T` (a Riemann contraction of `∇T` plus a differentiated-curvature contraction of `T`, with the
moving-frame `∇²T`-order discrepancy that survives at the *norm* level — `tensor3rdCurvBracket`, the
false slot-`0` frame-trace matching on a normal manifold); each further covariant gradient produces
one more contraction of a covariant derivative of curvature against one-higher gradient of `T`, all
sup-bounded on the compact manifold, so the `m`-fold iterated gradient is `L²`-controlled by the
`≤ m + 2`-order gradients of `T`. The constant is valence/order-dependent because the tensor-bundle
curvature endomorphism is an `O(s + m)`-slot derivation and the curvature-derivative term count grows
with `m` (a single scalar uniform over all `s, m` is unsatisfiable on a non-flat closed manifold).
It is strictly more primitive than the iterated commutator `‖∇(Defect p)‖` bound it feeds: it
concerns a *single* curvature contraction `Curv T`, not the `p`-fold iterated rough-Laplacian
commutator, which is recovered by summing this over the telescoping
`Defect p = ∑_{j < p} ∇^{p - 1 - j}(Curv (∇^j U))`. The degenerate witness is rejected because at
`m = 0` the bound is `‖Curv T‖ ≤ Cic s 0 · (‖T‖ + ‖∇T‖ + ‖∇²T‖)`, the genuine single-step defect
norm bound (`exists_pointwiseTensorCurv_l2_bound`), which is *false* with `Cic s 0 = 0` on a non-flat
manifold (the defect carries the genuine curvature contraction of `T`). -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Cic : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cic s m) ∧
      ∀ (s m : ℕ) (T : SmoothCcTensor g 0 s),
        ‖iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T)‖ ≤
          Cic s m * ∑ i ∈ Finset.range (m + 3), ‖iteratedCovGrad g 0 s i T‖ := by
  classical
  obtain ⟨Cic, hCic_nn, hpt⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨Cic, hCic_nn, fun s m T => ?_⟩
  -- The `m`-fold iterated gradient of `Curv T` is bounded fibrewise by `(Cic s m)²·∑_{i<m+3} rfns(∇^i T)`;
  -- the finite-sum pointwise-to-`L²` packaging upgrades it to the `L²` operator bound.
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g
    (c := s + 1 + m) (m + 3) (fun i => s + i) (fun i => iteratedCovGrad g 0 s i T)
    (iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T))
    (Cic s m) (hCic_nn s m) (hpt s m T)

/-- **The iterated-gradient commutator-defect `L²` bound (general gradient order, proved from the
covariant-product curvature input by induction).** For a closed smooth Riemannian manifold `(M, g)`
there is a *order/gradient-dependent* nonnegative constant `Dc : ℕ → ℕ → ℝ` such that, for every
smooth compactly-supported `(0, 2)`-tensor base `U`, every iterated commutator order `p`, and every
extra gradient order `m`, the `m`-fold covariant gradient of the order-`p` rough-Laplacian /
iterated-gradient commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` satisfies

```
‖∇^m(Defect p)‖_{L²} ≤ Dc p m · ∑_{i ≤ p + m + 1} ‖∇^i U‖_{L²}.
```

This is the genuine **iterated Ricci identity at the `L²` level**: each covariant gradient applied to
the iterated commutator defect produces one further curvature-derivative contraction, all sup-bounded
on the compact manifold, so the `m`-fold gradient is `L²`-controlled by the `≤ p + m + 1`-order
gradients of `U`. It is **proved** by induction on `p` (with `m` universally quantified, so the
inductive hypothesis is used at `m + 1`): the base case `p = 0` is the outright vanishing
`Defect 0 = Δ_∇ U − Δ_∇ U = 0`, so `∇^m(Defect 0) = 0`; the inductive step uses the defect recursion
`Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)` (`pointwiseTensorCurv_commutator_eq` and
`covGrad`-additivity) — applying `∇^m` and the triangle inequality bounds `‖∇^m(Defect (p + 1))‖` by
`‖∇^{m + 1}(Defect p)‖` (the inductive hypothesis at `m + 1`, via the gradient-commuting
`norm_iteratedCovGrad_covGrad_comm`) plus `‖∇^m(Curv (∇^p U))‖` (the posited covariant-product input
`exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound`, re-indexed through the gradient-composition
`norm_iteratedCovGrad_iteratedCovGrad`), both within the `≤ (p + 1) + m + 1`-order budget. Its only
`sorry`-dependence is through that posited covariant-product curvature input. -/
theorem exists_iteratedCovGrad_commutatorDefect_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℕ → ℝ, (∀ p m, 0 ≤ Dc p m) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p m : ℕ),
        ‖iteratedCovGrad g 0 (2 + p) m
            (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
              iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U))‖ ≤
          Dc p m * ∑ i ∈ Finset.range (p + m + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
  classical
  obtain ⟨Cic, hCic_nn, hcic⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound (I := I) (M := M) g
  -- Per-order existence of a gradient-indexed constant, proved by induction on `p` (with `m`
  -- universal so the inductive hypothesis applies at `m + 1`); the final `Dc` is its choice.
  have hkey : ∀ p : ℕ, ∃ c : ℕ → ℝ, (∀ m, 0 ≤ c m) ∧
      ∀ (U : SmoothCcTensor g 0 2) (m : ℕ),
        ‖iteratedCovGrad g 0 (2 + p) m
            (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
              iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U))‖ ≤
          c m * ∑ i ∈ Finset.range (p + m + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
    intro p
    induction p with
    | zero =>
        -- `Defect 0 = Δ_∇ U − Δ_∇ U = 0`, hence `∇^m(Defect 0) = 0`.
        refine ⟨fun _ => 0, fun _ => le_refl 0, fun U m => ?_⟩
        have hzero :
            (rawTensorConnLapSmooth (I := I) g 0 (2 + 0) (iteratedCovGrad g 0 2 0 U) -
              iteratedCovGrad g 0 2 0 (rawTensorConnLapSmooth (I := I) g 0 2 U)) = 0 := by
          rw [iteratedCovGrad_zero, iteratedCovGrad_zero]; abel
        rw [hzero, iteratedCovGrad_zero_tensor, norm_zero, zero_mul]
    | succ p' ih =>
        obtain ⟨c', hc'_nn, hc'⟩ := ih
        refine ⟨fun m => c' (m + 1) + Cic (2 + p') m,
          fun m => add_nonneg (hc'_nn (m + 1)) (hCic_nn (2 + p') m), fun U m => ?_⟩
        set GpU : SmoothCcTensor g 0 (2 + p') := iteratedCovGrad g 0 2 p' U with hGpU
        set Defp : SmoothCcTensor g 0 (2 + p') :=
          rawTensorConnLapSmooth (I := I) g 0 (2 + p') GpU -
            iteratedCovGrad g 0 2 p' (rawTensorConnLapSmooth (I := I) g 0 2 U) with hDefp
        -- The defect recursion `Defect (p'+1) = ∇(Defect p') + Curv (∇^{p'} U)`.
        have hcovsub : ∀ (r s : ℕ) (w₁ w₂ : SmoothCcTensor g r s),
            covGrad (I := I) (M := M) g r s (w₁ - w₂) =
              covGrad (I := I) (M := M) g r s w₁ - covGrad (I := I) (M := M) g r s w₂ := by
          intro r s w₁ w₂
          rw [sub_eq_add_neg, sub_eq_add_neg, covGrad_add, ← neg_one_smul ℝ w₂,
            covGrad_smul, neg_one_smul]
        have hrecur :
            (rawTensorConnLapSmooth (I := I) g 0 (2 + (p' + 1)) (iteratedCovGrad g 0 2 (p' + 1) U) -
                iteratedCovGrad g 0 2 (p' + 1) (rawTensorConnLapSmooth (I := I) g 0 2 U)) =
              covGrad (I := I) (M := M) g 0 (2 + p') Defp +
                pointwiseTensorCurv (I := I) (M := M) g (2 + p') GpU := by
          rw [hDefp, hGpU, iteratedCovGrad_succ, iteratedCovGrad_succ,
            pointwiseTensorCurv, hcovsub]
          change (rawTensorConnLapSmooth (I := I) g 0 (2 + p' + 1)
                  (covGrad (I := I) (M := M) g 0 (2 + p') (iteratedCovGrad g 0 2 p' U)) -
                covGrad (I := I) (M := M) g 0 (2 + p')
                  (iteratedCovGrad g 0 2 p' (rawTensorConnLapSmooth (I := I) g 0 2 U))) = _
          abel
        rw [hrecur, iteratedCovGrad_add]
        -- Triangle inequality on the two summands.
        refine le_trans (norm_add_le _ _) ?_
        -- The gradient-of-defect summand: `∇^m(∇(Defect p')) = ∇^{m+1}(Defect p')` (norm).
        have hcomm :
            ‖iteratedCovGrad g 0 (2 + (p' + 1)) m
                (covGrad (I := I) (M := M) g 0 (2 + p') Defp)‖ =
              ‖iteratedCovGrad g 0 (2 + p') (m + 1) Defp‖ :=
          norm_iteratedCovGrad_covGrad_comm (I := I) (M := M) g 0 (2 + p') m Defp
        rw [hcomm]
        -- The inductive hypothesis at `m + 1`.
        have hih := hc' U (m + 1)
        rw [← hGpU, ← hDefp] at hih
        -- The curvature summand: `∇^m(Curv (∇^{p'} U))` via the posited input + composition.
        have hcurv :
            ‖iteratedCovGrad g 0 (2 + (p' + 1)) m
                (pointwiseTensorCurv (I := I) (M := M) g (2 + p') GpU)‖ ≤
              Cic (2 + p') m *
                ∑ i ∈ Finset.range (m + 3),
                  ‖iteratedCovGrad g 0 2 (p' + i) U‖ := by
          refine le_trans (hcic (2 + p') m GpU) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCic_nn (2 + p') m)
          refine le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))
          rw [hGpU, norm_iteratedCovGrad_iteratedCovGrad (I := I) (M := M) g 0 2 p' i U]
        -- Combine both summands; reindex the curvature sum into `range ((p'+1)+m+2)`.
        set FullSum : ℝ := ∑ i ∈ Finset.range (p' + 1 + m + 2), ‖iteratedCovGrad g 0 2 i U‖
          with hFullSum
        have hFullSum_nn : 0 ≤ FullSum := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hc'_nn' : 0 ≤ c' (m + 1) := hc'_nn (m + 1)
        have hCic_nn' : 0 ≤ Cic (2 + p') m := hCic_nn (2 + p') m
        -- `range (p' + (m+1) + 2) = range ((p'+1)+m+2)`.
        have hsum1 :
            ∑ i ∈ Finset.range (p' + (m + 1) + 2), ‖iteratedCovGrad g 0 2 i U‖ = FullSum := by
          rw [hFullSum, show p' + (m + 1) + 2 = p' + 1 + m + 2 from by omega]
        -- The curvature sum `∑_{i<m+3} ‖∇^{p'+i}U‖` embeds (shifted) into `range ((p'+1)+m+2)`.
        have hsum2 :
            ∑ i ∈ Finset.range (m + 3), ‖iteratedCovGrad g 0 2 (p' + i) U‖ ≤ FullSum := by
          rw [hFullSum]
          have hmap :
              ∑ i ∈ Finset.range (m + 3), ‖iteratedCovGrad g 0 2 (p' + i) U‖ =
                ∑ j ∈ (Finset.range (m + 3)).image (fun i => p' + i),
                  ‖iteratedCovGrad g 0 2 j U‖ := by
            rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
          rw [hmap]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
          intro j hj
          simp only [Finset.mem_image, Finset.mem_range] at hj
          obtain ⟨i, hi, rfl⟩ := hj
          simp only [Finset.mem_range]; omega
        calc ‖iteratedCovGrad g 0 (2 + p') (m + 1) Defp‖ +
              ‖iteratedCovGrad g 0 (2 + (p' + 1)) m
                (pointwiseTensorCurv (I := I) (M := M) g (2 + p') GpU)‖
            ≤ c' (m + 1) * ∑ i ∈ Finset.range (p' + (m + 1) + 2), ‖iteratedCovGrad g 0 2 i U‖ +
                Cic (2 + p') m * ∑ i ∈ Finset.range (m + 3),
                  ‖iteratedCovGrad g 0 2 (p' + i) U‖ := add_le_add hih hcurv
          _ ≤ c' (m + 1) * FullSum + Cic (2 + p') m * FullSum :=
              add_le_add (le_of_eq (by rw [hsum1]))
                (mul_le_mul_of_nonneg_left hsum2 hCic_nn')
          _ = (c' (m + 1) + Cic (2 + p') m) * FullSum := by ring
  -- Extract the constant by choice and assemble.
  refine ⟨fun p => (hkey p).choose, fun p m => ((hkey p).choose_spec.1) m, fun U p m => ?_⟩
  exact (hkey p).choose_spec.2 U m

/-- **The gradient-of-commutator-defect `L²` bound (proved from the iterated-gradient
commutator-defect bound).** For a closed smooth Riemannian manifold `(M, g)` there is an
*order-dependent* nonnegative constant `Dc : ℕ → ℝ` such that, for every smooth compactly-supported
`(0, 2)`-tensor base `U` and every gradient order `p`, the covariant gradient of the order-`p`
rough-Laplacian / iterated-gradient commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` satisfies

```
‖∇(Defect p)‖_{L²} ≤ Dc p · ∑_{i ≤ p + 2} ‖∇^i U‖_{L²}.
```

This is **proved** from the general iterated-gradient commutator-defect bound
`exists_iteratedCovGrad_commutatorDefect_l2_bound` specialised to one extra gradient (`m = 1`):
`covGrad g 0 (2 + p) (Defect p) = ∇^1(Defect p)` by `iteratedCovGrad_succ` and `iteratedCovGrad_zero`,
and the sum `range (p + 1 + 2)` is the `m = 1` instance of `range (p + m + 2)`. Combined with the
single-step defect bound `exists_pointwiseTensorCurv_l2_bound` it closes the all-order
commutator-defect recursion `Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)`. Its only `sorry`-dependence
is through the posited covariant-product curvature input
`exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound`. -/
theorem exists_covGrad_commutatorDefect_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
        ‖covGrad g 0 (2 + p)
            (rawTensorConnLapSmooth (I := I) g 0 (2 + p) (iteratedCovGrad g 0 2 p U) -
              iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U))‖ ≤
          Dc p * ∑ i ∈ Finset.range (p + 1 + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
  classical
  obtain ⟨Dc, hDc_nn, hbound⟩ :=
    exists_iteratedCovGrad_commutatorDefect_l2_bound (I := I) (M := M) g
  refine ⟨fun p => Dc p 1, fun p => hDc_nn p 1, fun U p => ?_⟩
  -- `covGrad (Defect p) = ∇^1 (Defect p)`; apply the iterated bound at `m = 1`.
  have hb := hbound U p 1
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero] at hb
  exact hb

end Connection
end Integral
end DifferentialGeometry

end
