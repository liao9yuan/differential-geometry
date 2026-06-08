import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.SecondOrderCommutationResidueFiberBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Connection.LeviCivita.TwoJetVanishingExtension

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

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
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

/-- **Uniform-over-`M` rank-`s` proportional curvature-operator fibre bound.** The supremum over the
compact `M` of the continuous per-point proportional curvature envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`: a single nonnegative
constant `Csup` with, for every point `x`, tangent vectors `v, w`, and `(0, s)`-tensor `T`,
`rfns(R_x(v, w) T)(x) ≤ Csup · g(v, v) · g(w, w) · rfns(T)(x)`. It is the rank-`s` curvature
operator's base-point-uniform proportional fibre constant. -/
private lemma exists_uniform_riemannOp_tensorCov_proportional_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional (I := I) (M := M) g s
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww_nn : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
    mul_nonneg (mul_nonneg hvv_nn hww_nn)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x T)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x v w T)
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
          hCcurv_bound x v w T
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by ring

/-- **The bridge from the per-direction covariant derivative to the slot-`0` reading of the gradient.**
The directional covariant derivative `(tensorCov g 0 s).toFun (S.toSection) x v = ∇_v S(x)` is the
slot-`0` reading of the gradient `∇S = covGrad g 0 s S` along `v`:
```
(tensorCov g 0 s).toFun (S.toSection) x v =
  ((covGradBundleEquiv 0 s x).symm ((covGrad g 0 s S).toSection x)) v.
```
Both sides are `tensorRSCovariantDerivative I M 0 s (LeviCivita g) (S.toSection) x v`: the left by
definition of `tensorCov`, the right by the pointwise gradient formula `covGrad_toSection_apply` after
applying `(covGradBundleEquiv 0 s x).symm`. -/
private lemma tensorCov_toFun_eq_covGradBundleEquiv_symm_reading
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v =
      ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)) v := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **The slot-`0` curry of the unit-evaluated frame commutator is the second-order curvature residue
(sorry-free, the curry identity through the named difference).** For a smooth slot-`0` direction field
`w`, the slot-`0` curry at `w x` of the unit-evaluation of the frame commutator `remDiffFib g s S x i`
is the curvature residue `secondOrderResidue g s S x i w`. This is `secondOrderResidue_eq_curry_remDiffFib_unit`
(itself the rank-generic second-order leading-slot commutation, sorry-free) routed through the named
difference `remDiffFib = Aᵢ − Dᵢ`: the continuous-linear coercion of the subtraction distributes over the
unit evaluation (`ContinuousLinearMap.sub_apply`) and the slot-`0` curry (`map_sub`), recovering the
difference of the two curried unit-evaluated frame summands. -/
private lemma curry_remDiffFib_unit_eq_secondOrderResidue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          remDiffFib (I := I) (M := M) g s S x i)
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      secondOrderResidue (I := I) (M := M) g s S x i w := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        remDiffFib (I := I) (M := M) g s S x i) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 s x
          ((tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x)) from rfl]
  rw [ContinuousLinearMap.sub_apply, map_sub]
  exact secondOrderResidue_eq_curry_remDiffFib_unit (I := I) (M := M) g s S x i hw

/-- **Posited uniform fibre order of the second-order commutation curvature residue (the genuine
`∇R`-and-curvature content of the `∇³S`-cancellation).** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, frame index `i`, and **smooth
slot-`0` direction field `w` with vanishing covariant `1`- and `2`-jets at `x`** (a unit direction
`g(w x, w x) ≤ 1`, `∇_u w(x) = 0` for every `u`, and `∇_Y(∇_Y w)(x) = 0` for every smooth `Y`), the
intrinsic fibre norm of the `tensor0SAsRS`-wrapped second-order commutation curvature residue
`secondOrderResidue g s S x i w` (`SecondOrderCommutationResidueFiberBound`) is bounded by `C s` times
the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(tensor0SAsRS x (secondOrderResidue g s S x i w))(x)
  ≤ C s · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine order-`≤ 2` curvature content of the iterated-Ricci `∇³S`-cancellation.** With the
covariant-`2`-jet-vanishing reading direction `w`, the four covariant-derivative-of-`w` summands of the
residue `secondOrderResidue` — the `R(B, ∇_B w) V` curvature term, and the three Christoffel-residual
summands reading `∇_B(∇_B w)`, `∇_{[B, w]}(·)` and `∇_{∇_B w}(·)` — vanish at `x` through `∇w(x) = 0`,
`∇²w(x) = 0`; the surviving summands are the differentiated-curvature `(∇_B R)(B, w) V` class
(`nablaTensorCurvSec`, tensorial in the reading direction, contracting the `0`-jet of `V` against `∇R`)
and the curvature classes `R(∇_B B, w) V`, `R(B, w)(∇_B V)` (contracting the `≤ 1`-jet of `V` against
`R`). Each reads only the value `w x` (a unit direction) of the reading field, the tangent Christoffel
directions `∇_B B`, and the bracket value `[B, w] x`, contracted against the `≤ 2`-jet of the
unit-evaluated section `V := unitEvalSection g s S` (orders `0, 1, 2`, transported to `rfns(∇²S), rfns(∇S),
rfns(S)`); bounding the differentiated-curvature `‖∇R‖_∞` and the curvature `‖R‖_∞` uniformly over the
compact `M` and the frame indices `(i, a)` gives the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian fibre
norm `rfns` of the single tensor `tensor0SAsRS x (secondOrderResidue g s S x i w)` throughout — it never
extracts a per-direction `M → E` quantity. The reading direction `w` enters only through its value `w x`
and its (vanishing) covariant `1`- and `2`-jets at `x`, never through a chart-selection-unbounded
`smoothExtensionTangent` jet — the `2`-jet-vanishing hypotheses are exactly the intrinsic, chart-free
covariant-jet conditions, and the residue is genuinely a `(0, s)`-tensor of `w x`
(`secondOrderResidue_eq_curry_remDiffFib_unit`).

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces
`rfns(tensor0SAsRS x (secondOrderResidue g s S x i w)) = 0`, hence the residue
`secondOrderResidue g s S x i w = 0`, for every such direction `w` and every `S`. By the curry identity
`secondOrderResidue_eq_curry_remDiffFib_unit` this forces the slot-`0` curry of the unit-evaluated frame
commutator `remDiffFib g s S x i` to vanish, hence (Parseval) the frame summand `remDiffFib g s S x i`
itself, hence `∑ᵢ remDiffFib g s S x i = (Curv S).toSection x` would vanish for every `S` — false on a
non-flat manifold already at `s = 0` (`weitzenbock_integrated_covGrad_l2_normSq`). So `C` is genuinely
positive. The body is `sorry` (the uniform `‖∇R‖_∞` and `‖R‖_∞` envelope of the surviving curvature
classes over the `2`-jet-vanishing reading direction, with the unit-evaluation `≤ 2`-jet transports);
consumers transitively depend on its `sorryAx`. -/
theorem exists_secondOrderResidue_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        (w : Π b : M, TangentSpace I b),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w) →
        g.inner x (w x) (w x) ≤ 1 →
        (∀ u : TangentSpace I x, (LeviCivita (I := I) g).toFun w x u = 0) →
        (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
          (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y w) x (Y x) = 0) →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (secondOrderResidue (I := I) (M := M) g s S x i w)) ≤
          C s *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

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
`∇²_{Bᵢ, Bᵢ}(∇S)` top-order term. So `C` is genuinely positive.

**Proof (the intrinsic `∇³S`-cancellation, over the covariant-`2`-jet-vanishing extension).** The bound
is the single tensorial fibre-order statement of the iterated-Ricci `∇³S`-cancellation: the per-direction
frame summand `remDiffFib g s S x i` is intrinsically a *tensor* (its slot-`0` curry depends only on the
value of the reading direction, not its jet — `secondOrderResidue_eq_curry_remDiffFib_unit` exhibits it as
the order-`≤ 2` curvature residue `secondOrderResidue`). The `(0, s + 1)` fibre norm reconstructs as the
slot-`0` frame-sum of the slot-`s` fibre norms of the `tensor0SAsRS`-wrapped bare curries
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame`, in the `g_x`-orthonormal centre frame
`Bᵢ x`); each curry, read at the unit through the curry identity with the *covariant-`2`-jet-vanishing*
smooth extension `wₐ := exists_twoJetVanishing_tangentExtension g x (Bₐ x)` of the orthonormal direction
(`curry_remDiffFib_unit_eq_secondOrderResidue`, the curry is `w`-jet-independent so `wₐ x = Bₐ x` suffices),
is `secondOrderResidue g s S x i wₐ`. The four covariant-derivative-of-`wₐ` summands of the residue vanish
through `∇wₐ(x) = 0` and `∇²wₐ(x) = 0`, leaving the order-`≤ 2` curvature contractions bounded uniformly
over `(i, a, x)` by `exists_secondOrderResidue_fiberOrder_bound`; summing over the `finrank` slot-`0`
directions gives the single nonnegative valence-dependent `C s := √(finrank · C₀ s)`. A prior attempt to
prove this by a slot-`0` Parseval reconstruction over a *per-direction `secondOrderResidue` per-class* split
was found UNSOUND — the per-class split exposes a chart-selection-unbounded `smoothExtensionTangent` 1-jet
(read by an inner `covApply`) that cancels only in the full residue sum, never class-by-class — so the bound
is established here over the residue's *full* curvature fibre order, which is sound. -/
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
  classical
  obtain ⟨Csup, hCsup_nn, hCsup⟩ :=
    exists_secondOrderResidue_fiberOrder_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s),
    fun s => Real.sqrt_nonneg _, fun s S x i => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The `g_x`-orthonormal centre frame `Bₐ x` represents both fibre norms.
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with heC
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  -- Slot-`0` Parseval reconstruction of the `(0, s + 1)` fibre norm of `remDiffFib`.
  rw [riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame (I := I) (M := M) g s x
    (remDiffFib (I := I) (M := M) g s S x i) eC hnC horthC]
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Csup s := by
    rw [Real.sq_sqrt]; exact mul_nonneg (by positivity) (hCsup_nn s)
  rw [hCsq]
  -- Per-direction: realise each slot-`0` curry through the `2`-jet-vanishing extension of `Bₐ x`.
  have hper : ∀ a : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                remDiffFib (I := I) (M := M) g s S x i)
                (unitZeroSec (I := I) (M := M) x)) (eC a))) ≤ Csup s * (A + B + D) := by
    intro a
    obtain ⟨w, hw_sm, hw_x, hw_grad, hw_hess⟩ :=
      exists_twoJetVanishing_tangentExtension (I := I) (M := M) g x (eC a)
    have hrw : tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            remDiffFib (I := I) (M := M) g s S x i)
            (unitZeroSec (I := I) (M := M) x)) (eC a) =
        secondOrderResidue (I := I) (M := M) g s S x i w := by
      rw [← hw_x]
      exact curry_remDiffFib_unit_eq_secondOrderResidue (I := I) (M := M) g s S x i hw_sm
    rw [hrw]
    have hww : g.inner x (w x) (w x) ≤ 1 := by
      rw [hw_x]; have := horthC a a; rw [if_pos rfl] at this; rw [this]
    exact hCsup s S x i w hw_sm hww hw_grad hw_hess
  refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq; ring

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
  classical
  -- The uniform rank-`s` curvature sup family.
  choose Csup hCsup_nn hCsup using fun s =>
    exists_uniform_riemannOp_tensorCov_proportional_local (I := I) (M := M) g s
  refine ⟨fun s => Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s),
    fun s => Real.sqrt_nonneg _, fun s S x i => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  -- The per-direction genuine fibre is the slot-`0` uncurry of the curvature-direction CLM.
  have hfib : remDiffGenuineFib (I := I) (M := M) g s S x i =
      covGradBundleEquiv (I := I) (M := M) 0 s x
        (remDiffGenuineDirCLM (I := I) (M := M) g s S x i) := rfl
  rw [hfib]
  -- The squared constant.
  have hCsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) * Csup s)) ^ 2 =
      (Module.finrank ℝ E : ℝ) * Csup s := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (hCsup_nn s)
  rw [hCsq]
  -- Per-direction unit-direction fibre bound on the curvature contraction.
  have hbound : ∀ v : TangentSpace I x, g.inner x v v = 1 →
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (remDiffGenuineDirCLM (I := I) (M := M) g s S x i v) ≤ Csup s * B := by
    intro v hv
    -- Unfold the CLM to its curvature-contraction value.
    have hval : remDiffGenuineDirCLM (I := I) (M := M) g s S x i v =
        riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)
            (smoothOrthoFrame (I := I) g x i x)) := by
      rw [remDiffGenuineDirCLM, LinearMap.coe_toContinuousLinearMap', remDiffGenuineDirLM,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [show covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x =
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (smoothOrthoFrame (I := I) g x i x) from rfl,
        tensorCov_toFun_eq_covGradBundleEquiv_symm_reading (I := I) (M := M) g s S x
          (smoothOrthoFrame (I := I) g x i x)]
    rw [hval]
    -- The orthonormality scalars at the centre frame are `1`.
    have hgB : g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) = 1 := by
      have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i; rwa [if_pos rfl] at this
    -- The curvature sup bound on the contraction.
    have hcurv := hCsup s x (smoothOrthoFrame (I := I) g x i x) v
      ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x)
        (smoothOrthoFrame (I := I) g x i x))
    rw [hgB, hv, mul_one, mul_one] at hcurv
    refine le_trans hcurv ?_
    -- The slot-`0` reading of the gradient along the centre frame is dominated by `rfns(∇S) = B`.
    have hread : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)
          (smoothOrthoFrame (I := I) g x i x)) ≤ B := by
      rw [hB]
      exact riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le (I := I) (M := M) g s x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (smoothOrthoFrame (I := I) g x)
        (fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b) i
    exact mul_le_mul_of_nonneg_left hread (hCsup_nn s)
  -- Lift the per-direction bound to the full fibre norm via the frame-sum engine.
  refine le_trans
    (riemannianFiberNormSq_covGradBundleEquiv_le_card_mul (I := I) (M := M) g s x
      (remDiffGenuineDirCLM (I := I) (M := M) g s S x i) (Csup s * B) hbound) ?_
  -- `finrank · (Csup · B) = (finrank · Csup) · B ≤ (finrank · Csup) · (A + B + D)`.
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  calc (Module.finrank ℝ E : ℝ) * (Csup s * B)
      = (Module.finrank ℝ E : ℝ) * Csup s * B := by ring
    _ ≤ (Module.finrank ℝ E : ℝ) * Csup s * (A + B + D) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hfr_nn (hCsup_nn s))
        nlinarith [hA_nn, hD_nn]

end Connection
end Integral
end DifferentialGeometry

end
