import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.BareSlot0CurryParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# The second-order commutation curvature residue and its posited per-direction fibre order

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
**curvature residue** of the rank-generic second-order leading-slot commutation
`covGrad_covDeriv_leadingSlot_secondOrder_commutation`
(`MetricCompatibility/CovGradCovDerivSecondOrderCommutation`, sorry-free) — the right-hand side that
survives once the top-order `∇³S` term of the per-direction frame commutator `Aᵢ − Dᵢ` has cancelled
through the iterated Ricci identity:
```
secondOrderResidue g s S x i w
  = (∇_{Bᵢ} R)(Bᵢ, w) V                                                   -- the (∇R) S class
  + ( R(∇_{Bᵢ} Bᵢ, w) V + R(Bᵢ, ∇_{Bᵢ} w) V + 2 R(Bᵢ, w)(∇_{Bᵢ} V) )      -- the R(diff) class
  + ρ,                                                                     -- the Christoffel residual
```
with `V := unitEvalSection g s S`, `Bᵢ := smoothOrthoFrame g x i`, `R = riemannSec nab`,
`(∇R) = nablaTensorCurvSec`, `ρ = secondOrderChristoffelResidual`, and `nab` the abstract `(0, s)`-tensor
covariant derivative. By the commutation identity this residue is *exactly* the slot-`0` curry of the
unit-evaluated frame commutator `remDiffFib g s S x i` at the field `w`, so its `(0, s)` fibre norm,
frame-summed over the slot-`0` orthonormal directions `w := smoothExtensionTangent x (e a)`,
reconstructs the intrinsic `(0, s + 1)` fibre norm of `remDiffFib g s S x i`
(`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`).

## The posited per-direction frontier

Every right-hand-side summand is order-`≤ 2` in `S`: the `(∇R) S` and `R(diff) V` classes are curvature
contractions of `V` resp. `∇_{Bᵢ} V` (orders `0` and `1`), and the Christoffel residual `ρ` is a sum of
iterated `cov`-covariant derivatives of `V` along the tangent Christoffel directions of `Bᵢ, w` (each at
most a second covariant derivative of `V`, order `≤ 2`). Bounding each class by the intrinsic fibre
norms of `∇²S`, `∇S`, `S` — with the per-point curvature, differentiated-curvature, frame-jet and
`smoothExtensionTangent`-jet magnitudes made uniform over `M` and the finite frame `(i, a)` by
compactness — gives the per-direction frame-summed fibre order. This is the genuine classical
iterated-Ricci `∇³S`-cancellation content (the residue, NOT the un-cancelled commutator); it is posited
here as the precise strictly-smaller frontier the per-direction commutator fibre order
`exists_remDiffFib_fiberOrder_bound` (`RemDiffFibThirdOrderCancellation`) is assembled from through the
slot-`0` Parseval reconstruction and the sorry-free commutation identity.

## Main results

* `secondOrderResidue` — the curvature residue of the second-order leading-slot commutation, as a
  `(0, s)`-tensor-valued function of the slot-`0` direction field `w`.
* `secondOrderResidue_eq_curry_remDiffFib_unit` — the residue equals the slot-`0` curry of the
  unit-evaluated frame commutator `remDiffFib g s S x i` (sorry-free, by the commutation identity).
* `exists_secondOrderResidue_frameSum_fiberOrder_bound` — the **posited** per-direction frame-summed
  fibre order of the residue.

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

/-- **The curvature residue of the second-order leading-slot commutation.** At a point `x`, frame
index `i` (with `Bᵢ := smoothOrthoFrame g x i`) and slot-`0` direction field `w`, the right-hand side of
the rank-generic second-order leading-slot commutation
`covGrad_covDeriv_leadingSlot_secondOrder_commutation`: the differentiated-curvature `(∇R) S` class,
the curvature-applied-to-differentiated-arguments `R(diff) V` class, and the Christoffel-derivative
residual `ρ`, with `V := unitEvalSection g s S` and `nab` the abstract `(0, s)`-tensor covariant
derivative. This is the `(0, s)`-tensor that survives once the top-order `∇³S` term has cancelled. -/
def secondOrderResidue (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : Π b : M, TangentSpace I b) : Tensor0SSpace s I x :=
  nablaTensorCurvSec (I := I) g
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) w
      (unitEvalSection (I := I) (M := M) g s S) x
    + (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)) w
          (unitEvalSection (I := I) (M := M) g s S) x
        + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i)
          (covApply (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x i) w)
          (unitEvalSection (I := I) (M := M) g s S) x
        + (2 : ℝ) • riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) w
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i)
            (unitEvalSection (I := I) (M := M) g s S)) x)
    + secondOrderChristoffelResidual (I := I) g
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g x i) w
        (unitEvalSection (I := I) (M := M) g s S) x

/-- **The curvature residue is the slot-`0` curry of the unit-evaluated frame commutator (sorry-free).**
For a smooth slot-`0` direction field `w`, the slot-`0` curry at `w x` of the unit-evaluation of the
frame commutator `remDiffFib g s S x i = Aᵢ − Dᵢ` is the curvature residue `secondOrderResidue g s S x i
w`. This is exactly the rank-generic second-order leading-slot commutation identity
`covGrad_covDeriv_leadingSlot_secondOrder_commutation` (sorry-free): the curried-unit-evaluated
difference of the two frame summands equals the curvature residue once the top-order `∇³S` cancels. -/
theorem secondOrderResidue_eq_curry_remDiffFib_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (w x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      secondOrderResidue (I := I) (M := M) g s S x i w :=
  covGrad_covDeriv_leadingSlot_secondOrder_commutation (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x i) hw x

/-- **Posited per-direction frame-summed fibre order of the second-order commutation curvature
residue.** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `C : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor
`S`, point `x`, frame index `i`, and every `g_x`-orthonormal tangent frame `e` (with
`n = Module.finrank ℝ E` directions, in δ-form Gram), the slot-`0` frame-sum of the intrinsic `(0, s)`
fibre norms of the `tensor0SAsRS`-wrapped curvature residue `secondOrderResidue g s S x i
(smoothExtensionTangent x (e a))` is bounded by `(C s)²` times the **sum** of the intrinsic fibre norms
of `∇²S`, `∇S` and `S`:
```
∑ a, rfns(tensor0SAsRS x (secondOrderResidue g s S x i (smoothExtensionTangent x (e a))))(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine, irreducible classical iterated-Ricci `∇³S`-cancellation content (the residue,
not the un-cancelled commutator).** Every summand of `secondOrderResidue` is order-`≤ 2` in `S`: the
`(∇R) S` (`nablaTensorCurvSec`) and `R(diff) V` (three `riemannSec`) classes are curvature contractions
of `V := unitEvalSection g s S` resp. its first covariant derivative `∇_{Bᵢ} V` (orders `0` and `1`, by
`‖R‖_∞`/`‖∇R‖_∞` against `rfns(S)`/`rfns(∇S)`); the Christoffel residual `ρ`
(`secondOrderChristoffelResidual`) is a sum of `≤ 2`-fold covariant derivatives of `V` along the tangent
Christoffel directions of `Bᵢ, w` (order `≤ 2`, by `rfns(∇²S)`). The per-point curvature `‖R‖`,
differentiated-curvature `‖∇R‖`, frame-jet `‖∇ smoothOrthoFrame‖` and slot-`0`
`smoothExtensionTangent`-jet magnitudes are bounded uniformly over `M` and the finite frame `(i, a)` by
compactness, giving the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian fibre
norm `rfns` of the `(0, s)`-tensor `secondOrderResidue` (the slot-`0` curry of the intrinsic frame
commutator difference `remDiffFib`), frame-summed; the `smoothExtensionTangent x (e a)` direction only
appears as the slot-`0` reading direction (the `∇³S`-cancellation is false term-by-term through the
non-tensorial reading, but the intrinsic frame-summand difference, i.e. the residue, is order-`≤ 2`).

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces every frame-sum to vanish, hence
(through the Parseval reconstruction `riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry` and the
commutation identity `secondOrderResidue_eq_curry_remDiffFib_unit`) `rfns(remDiffFib g s S x i) = 0` for
every direction `i`, hence the frame sum `∑ᵢ remDiffFib g s S x i = (Curv S).toSection x` would vanish
for every `S` — false on a non-flat manifold (the scalar commutator defect `Curv f = Ric(∇f, ·)`
integrated is nonzero for a non-harmonic `f` on a curved manifold,
`weitzenbock_integrated_covGrad_l2_normSq`). So `C` is genuinely positive. The body is `sorry` (the
genuine classical iterated-Ricci `∇³S`-cancellation content: the curvature-residue uniform fibre sups);
consumers transitively depend on `sorryAx`. -/
theorem exists_secondOrderResidue_frameSum_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E))
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) →
        (∑ a : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensor0SAsRS (I := I) (M := M) x
                (secondOrderResidue (I := I) (M := M) g s S x i
                  (smoothExtensionTangent (I := I) x (e a))))) ≤
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
