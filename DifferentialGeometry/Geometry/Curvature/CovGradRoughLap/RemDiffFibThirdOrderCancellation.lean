import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval

/-!
# The per-direction third-order cancellation of the moving-frame frame summand

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the two
genuinely-irreducible per-direction fibre atoms that the moving-frame frame summand
`remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)`
(`MovingFrameRemainderFrameSumBridge`) splits into once its third-order top-order term has cancelled:

* `remDiffGenuineFib g s S x i` — the pure-Riemann curvature fibre `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, the
  `rfns(∇S)`-order curvature contraction; and
* the genuine `∇³S`-cancellation residue carried by `remDiffFib` itself: the *commutator*
  `Aᵢ − Dᵢ := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)` of the rough-Laplacian frame trace and the
  covariant gradient, which is order-`≤ 2` in `S` because the third-order `∇³S` term cancels through
  the iterated Ricci identity.

## Why the per-direction commutator `remDiffFib` is order-`≤ 2`

The frame summand `remDiffFib g s S x i` is *exactly* the difference `Aᵢ − Dᵢ` of the two frame
summands whose curried unit-evaluation difference is pinned by the rank-generic second-order
leading-slot commutation `covGrad_covDeriv_leadingSlot_secondOrder_commutation`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`, sorry-free): for every smooth tangent
field `w`, the slot-`0` curry at `w` of `(remDiffFib g s S x i)(unit)` equals the abstract third-order
Ricci residue
```
curry (remDiffFib …)(unit)(w)
  = (∇_{Bᵢ} R)(Bᵢ, w) V                                                    -- the (∇R) S class
  + ( R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V) )       -- the R(diff) class
  + ρ,                                                                      -- the Christoffel residual
```
`V := unitEvalSection g s S`, `R = riemannSec (tensor0SCovariantDerivative s (LeviCivita g))`,
`(∇R) = nablaTensorCurvSec`, `ρ = secondOrderChristoffelResidual`. Every right-hand-side summand is
order-`≤ 2` in `S`: the `(∇R) S` and `R(diff) V` classes are curvature contractions of `V` resp.
`∇_{Bᵢ} V` (orders `0` and `1`), and the Christoffel residual `ρ` is a sum of iterated `cov`-covariant
derivatives of `V` along the tangent Christoffel directions of `Bᵢ, w` (each at most a second covariant
derivative of `V`, order `≤ 2`). The intrinsic `(0, s + 1)` fibre norm of `remDiffFib` reconstructs as
the slot-`0` frame-sum of the slot-`s` fibre norms of these curries
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`), so a uniform-over-`(i, a, x)` per-direction fibre
bound on the curvature residue — with the slot-`0` direction realised as the smooth extension
`smoothExtensionTangent x (e a)` of the orthonormal slot-`0` frame vector — gives the per-direction
order-`≤ 2` fibre bound on `remDiffFib`. The `∇³S`-cancellation is *false term-by-term* through the
non-tensorial `smoothExtensionTangent` reading of the individual third covariant derivatives
(chart-selection-unbounded on `S²`); only the intrinsic frame-summand *difference* `Aᵢ − Dᵢ` is
order-`≤ 2`, which is exactly what the commutation identity provides.

## Main results (the two posited per-direction frontiers)

* `exists_remDiffFib_fiberOrder_bound` — the **per-direction commutator fibre order**: the genuine
  `∇³S`-cancellation content, the order-`≤ 2` fibre bound on `remDiffFib g s S x i = Aᵢ − Dᵢ`.
* `exists_remDiffGenuineFib_fiberOrder_bound` — the **per-direction pure-Riemann curvature fibre
  order**: the `rfns(∇S)`-order fibre bound on the pure-Riemann curvature contraction
  `remDiffGenuineFib g s S x i`.

These two are the strictly-smaller, precise, intrinsic frontiers the per-direction bracket-summand
fibre order `exists_remDiffBracketFib_fiberOrder_bound` (`RemDiffBracketFiberOrder`) is assembled from,
via the named split `remDiffBracketFib = remDiffFib − remDiffGenuineFib` and fibre subadditivity. Both
are posited; their next recursion is the curvature-residue uniform-sup route documented above (toward
the pointwise iterated-Ricci identity `covGrad_covDeriv_leadingSlot_secondOrder_commutation`, already
sorry-free), not a re-statement.

## Convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`).
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Posited per-direction moving-frame commutator fibre order (the genuine `∇³S`-cancellation
content).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `C : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor
`S`, point `x`, and frame index `i`, the intrinsic fibre norm of the per-direction frame summand
`remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)`
(`MovingFrameRemainderFrameSumBridge`) — the *commutator* `Aᵢ − Dᵢ` of the rough-Laplacian frame trace
and the covariant gradient, both at the single frame direction `Bᵢ := smoothOrthoFrame g x i` — is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(remDiffFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine, irreducible `∇³S`-cancellation content.** The summand carries the top-order
`∇³S` term `∇²_{Bᵢ, Bᵢ}(∇S)`, so it is **not** order-`≤ 2` term-by-term; the bound holds precisely
because the third-order `∇³S` cancels in the commutator `Aᵢ − Dᵢ` through the iterated Ricci identity.
The curried unit-evaluation difference is pinned, for every smooth slot-`0` direction field `w`, by the
rank-generic second-order leading-slot commutation
`covGrad_covDeriv_leadingSlot_secondOrder_commutation`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`, sorry-free):
```
curry (remDiffFib …)(unit)(w)
  = (∇_{Bᵢ} R)(Bᵢ, w) V + ( R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V) ) + ρ,
```
with `V := unitEvalSection g s S`; every right-hand-side summand is order-`≤ 2` in `S` (the `(∇R) S`
and `R(diff) V` classes contract the `≤ 1`-jet of `V` against curvature; the Christoffel residual `ρ`
is a sum of `≤ 2`-fold covariant derivatives of `V`). Reconstructing the intrinsic `(0, s + 1)` fibre
norm from its slot-`0` frame-sum of curried slot-`s` fibre norms
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`), with the slot-`0` direction realised as
`smoothExtensionTangent x (e a)`, and bounding the curvature residue uniformly over the frame indices
`(i, a)` and the point `x` by compactness gives the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian
fibre norm `rfns` of the single tensor `remDiffFib g s S x i` throughout — it never extracts a
per-direction `M → E` quantity, never reads a chart-selection-unbounded `smoothExtensionTangent` jet of
an individual third covariant derivative. The `∇³S`-cancellation is *false term-by-term* through the
non-tensorial reading of the individual third covariant derivatives (chart-selection-unbounded on
`S²`); only the intrinsic frame-summand *difference* `Aᵢ − Dᵢ` is order-`≤ 2`, which is exactly the
content of the commutation identity.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces `rfns(remDiffFib g s S x i) = 0`
for every direction `i`, hence `remDiffFib g s S x i = 0`, hence the frame sum
`∑ᵢ remDiffFib g s S x i = (Curv S).toSection x` (`pointwiseTensorCurv_toSection_eq_frame_sum`) would
vanish for every `S` — false on a non-flat manifold. Already at `s = 0` the scalar commutator defect
`Curv f = Ric(∇f, ·)` integrated is nonzero for a non-harmonic `f` on a curved manifold
(`weitzenbock_integrated_covGrad_l2_normSq`), and `remDiffFib` genuinely uses `S` through its
`∇²_{Bᵢ, Bᵢ}(∇S)` top-order term. So `C` is genuinely positive. The body is `sorry` (the genuine
classical iterated-Ricci `∇³S`-cancellation content: the curvature-residue uniform fibre sups of the
commutation identity); consumers transitively depend on `sorryAx`. -/
theorem exists_remDiffFib_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (remDiffFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

/-- **Posited per-direction pure-Riemann curvature fibre order.** For a closed smooth Riemannian
manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every
covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and frame index `i`, the
intrinsic fibre norm of the per-direction pure-Riemann curvature fibre `remDiffGenuineFib g s S x i`
(`MovingFrameRemainderFrameSumBridge`) — the slot-`0` uncurry of the curvature-direction CLM
`v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, `Bᵢ := smoothOrthoFrame g x i` — is bounded by `(C s)²` times the **sum** of
the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(remDiffGenuineFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuinely-tensorial pure-Riemann `R(∇S)` contraction**, order-`1` in `S` (it contracts
the `1`-jet `∇_{Bᵢ} S` against the curvature `R(Bᵢ, ·)`, read off the bundled trilinear Riemann
operator `riemannOp`). Its frame sum is the concrete pure-Riemann genuine section `GcurvSection g s S`
(`remDiffGenuineFib_sum_eq_GcurvSection_toSection`, frame-free, tensorial), whose fibre norm is bounded
sorry-free by `‖R‖_∞ · rfns(∇S)` through the curvature-operator `g`-norm sup
(`riemannOp_covGrad_fiberNormSq_le_gen`, `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`,
`IntegratedOrder2WeitzenbockCurvature`); the per-direction fibre norm is the slot-`0` uncurry of the
same curvature-direction CLM (`remDiffGenuineDirCLM`), uniformly bounded over the frame index `i` and
the point `x` by the same compactness sup. The `∇²S` and `S` terms appear only to give the per-direction
bound the common order-`≤ 2` shape shared with the commutator leg (the bound is, in fact, of pure
`rfns(∇S)` order, which is `≤` the full sum since every fibre norm is nonnegative).

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian
fibre norm `rfns` of the single tensor `remDiffGenuineFib g s S x i` throughout — it never extracts a
per-direction `M → E` quantity; the curvature direction is read off the bundled `riemannOp`, genuinely
linear in `v`.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces
`rfns(remDiffGenuineFib g s S x i) = 0` for every direction `i`, hence the frame sum
`∑ᵢ remDiffGenuineFib g s S x i = (GcurvSection g s S).toSection x` would vanish for every `S`. For
`s ≥ 1` this is false on a non-flat manifold (the pure-Riemann trace `GcurvSection` is genuinely
nonzero, `pureRGenuineDiffOp0_eq_GcurvSection`). The `R(∇S)` contraction genuinely uses `S` through its
`∇_{Bᵢ} S` factor. So `C` is genuinely positive. The body is `sorry` (the per-direction curvature-CLM
fibre sup, the slot-`0` uncurry of the uniform `‖R‖_∞` bound); consumers transitively depend on
`sorryAx`. -/
theorem exists_remDiffGenuineFib_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (remDiffGenuineFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
