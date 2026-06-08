import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation

/-!
# The second-order commutation curvature residue

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
unit-evaluated frame commutator `remDiffFib g s S x i` at the field `w` — a genuine `(0, s)`-tensor of
`w x`, even though no individual right-hand-side summand is tensorial in `w` (the `R(diff) V` and
Christoffel classes read the `1`-jet of `w` through `covApply (LeviCivita g) Bᵢ w`, which only cancels
across the full frame-summand *difference* `Aᵢ − Dᵢ`).

## Main results

* `secondOrderResidue` — the curvature residue of the second-order leading-slot commutation, as a
  `(0, s)`-tensor-valued function of the slot-`0` direction field `w`.
* `secondOrderResidue_eq_curry_remDiffFib_unit` — the residue equals the slot-`0` curry of the
  unit-evaluated frame commutator `remDiffFib g s S x i` (sorry-free, by the commutation identity).
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

end Connection
end Integral
end DifferentialGeometry

end
