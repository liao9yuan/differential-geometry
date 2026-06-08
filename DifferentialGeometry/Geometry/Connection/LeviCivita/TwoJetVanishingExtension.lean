import DifferentialGeometry.Geometry.Connection.LeviCivita.LinearExtensionTangent
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator

/-!
# A controlled smooth tangent extension with vanishing covariant `2`-jet at the basepoint

For a smooth Riemannian metric `g` on a closed manifold, a base point `x₀ : M`, and a fibre
vector `v : TangentSpace I x₀`, this file isolates the **covariant-`2`-jet-vanishing** smooth
tangent extension `W : Π b, TangentSpace I b` of `v`: a smooth section with

* `W x₀ = v` (it extends `v`);
* `∇_u W (x₀) = 0` for every direction `u` — the covariant `1`-jet vanishes; and
* `∇_Y(∇_Y W)(x₀) = 0` for every smooth field `Y` — the iterated covariant `2`-jet vanishes.

Such an extension is the geometric device that turns the genuine per-direction third-order
cancellation residue of `MovingFrameRemainderFrameSumBridge`/`SecondOrderCommutationResidueFiberBound`
into a *pure curvature* contraction reading only `v`: in the second-order leading-slot commutation
residue `secondOrderResidue g s S x i w` the four covariant-derivative-of-`w` summands —
`R(B, ∇_B w) V`, `∇_{[B, w]}(∇_B V)` (through `∇_B w`), `∇_B(∇_{∇_B w} V)`, and the iterated
`∇_B(∇_B w)`-direction term — all read the covariant `1`- or `2`-jet of `w` at `x`, which the
vanishing-`2`-jet extension kills, leaving only the order-`≤ 2` curvature contractions of `V` against
the `(∇R)` and `R` classes.

The construction is the **chart-coordinate quadratic correction** of the coordinate-constant linear
extension `linearExtensionTangent x₀ v` (`LinearExtensionTangent`): the linear extension already has a
vanishing chart-derivative near `x₀`, so its covariant `1`-jet at `x₀` is the pure metric Christoffel
correction (`covApply_linearExtensionTangent_basepoint_eq`) and its covariant `2`-jet is the chart
`∂Γ + Γ·Γ` contraction (`covApply_covApply_linearExtensionTangent_basepoint_eq`); subtracting the
degree-`1` and degree-`2` chart polynomials reproducing those corrections cancels the covariant
`1`- and `2`-jets without disturbing the basepoint value.

## Main results

* `covApply_covApply_linearExtensionTangent_basepoint_eq` — the basepoint chart formula for the
  iterated covariant derivative `∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` in terms of the chart
  Christoffel derivative `∂Γ` (`fderiv` of `chartChristoffel`), the quadratic `Γ·Γ` contraction, and
  the coordinate `tangentCoord x₀ w`. (Posited chart sub-node.)
* `exists_twoJetVanishing_tangentExtension` — the existence of a smooth covariant-`2`-jet-vanishing
  tangent extension of `v`. (Posited geometric construction.)
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The basepoint chart formula for the iterated covariant derivative of the linear extension
(`∂Γ`-sub-node, posited).** For the coordinate-constant linear extension `linearExtensionTangent x₀ w`
(`LinearExtensionTangent`), the iterated tangent covariant derivative
`∇_v(∇_v(linearExtensionTangent x₀ w))(x₀)` along a fixed direction `v` collapses, at the basepoint, to
the chart-coordinate second-order contraction of the model coordinate `tangentCoord x₀ w` against the
chart Christoffel derivative `∂Γ` (the `fderiv` of `chartChristoffel`) and the quadratic `Γ·Γ` term:
```
∇_v(∇_v W)(x₀) = trivFromE x₀ x₀ ( ∑ᵢⱼₖₗ (vᵏ vⁱ wʲ) · (∂ₖ Γᵐᵢⱼ)(φ x₀) · eₘ
                                     + ∑ᵢⱼₖₗₘ (vⁱ vᵏ wʲ) · Γᵐₖₗ(φ x₀) · Γˡᵢⱼ(φ x₀) · eₘ ),
```
with `W := linearExtensionTangent x₀ w`, `v`-coordinates and `w := tangentCoord x₀ w` taken in the
`chartModelBasis`, and `Γ = chartChristoffel g x₀`. The bump and the (vanishing near `x₀`) chart
derivative of the coordinate-constant field contribute nothing; only the once-differentiated and the
quadratic Christoffel corrections survive. This is the genuine missing chart formula, the second-order
companion of the `1`-jet basepoint reduction `covApply_linearExtensionTangent_basepoint_eq`.

**Posited** (body `sorry`): the chart computation of the iterated covariant derivative of the
coordinate-constant field — a second-order chart-coordinate expansion. Consumers transitively depend on
its `sorryAx`. -/
theorem covApply_covApply_linearExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) (w : TangentSpace I x₀)
    (v : TangentSpace I x₀) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (linearExtensionTangent (I := I) x₀ v)
          (linearExtensionTangent (I := I) x₀ w)) x₀
        (linearExtensionTangent (I := I) x₀ v x₀) =
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j) •
              ((fderiv ℝ (fun y : E => chartChristoffel (I := I) g x₀ i j m y)
                  (extChartAt I x₀ x₀)) ((chartModelBasis E) k) • (chartModelBasis E) m)) +
      trivFromE (I := I) x₀ x₀
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) i *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ v)) k *
                ((chartModelBasis E).repr (tangentCoord (I := I) x₀ w)) j *
                chartChristoffel (I := I) g x₀ k l m (extChartAt I x₀ x₀) *
                chartChristoffel (I := I) g x₀ i j l (extChartAt I x₀ x₀)) •
              (chartModelBasis E) m) := by
  sorry

/-- **The covariant-`2`-jet-vanishing smooth tangent extension (posited geometric construction).** For
a smooth Riemannian metric `g` on a closed manifold, a base point `x₀`, and a fibre vector
`v : TangentSpace I x₀`, there is a smooth tangent-bundle section `W : Π b, TangentSpace I b` that

* extends `v`: `W x₀ = v`;
* has vanishing covariant `1`-jet at `x₀`: `∇_u W(x₀) = (LeviCivita g).toFun W x₀ u = 0` for every
  direction `u`; and
* has vanishing iterated covariant `2`-jet at `x₀`: for every smooth field `Y`,
  `∇_Y(∇_Y W)(x₀) = (LeviCivita g).toFun (covApply (LeviCivita g) Y W) x₀ (Y x₀) = 0`.

The construction is the chart-coordinate quadratic correction of `linearExtensionTangent x₀ v`: the
degree-`1` chart polynomial cancelling the metric Christoffel `1`-jet correction
(`covApply_linearExtensionTangent_basepoint_eq`) and the degree-`2` chart polynomial cancelling the
`∂Γ + Γ·Γ` `2`-jet correction (`covApply_covApply_linearExtensionTangent_basepoint_eq`), both cut off by
the same bump, leave the basepoint value `v` untouched while zeroing the covariant `1`- and `2`-jets.

**Posited** (body `sorry`): the chart-polynomial correction construction over the chart `2`-jet formula.
Consumers transitively depend on its `sorryAx`. -/
theorem exists_twoJetVanishing_tangentExtension
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v : TangentSpace I x₀) :
    ∃ W : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) ∧
      W x₀ = v ∧
      (∀ u : TangentSpace I x₀, (LeviCivita (I := I) g).toFun W x₀ u = 0) ∧
      (∀ Y : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y W) x₀ (Y x₀) = 0) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
