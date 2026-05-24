import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.Integral.Connection.LeviCivita

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## The Cartan formula for the Lie derivative of a Riemannian metric

The Cartan formula
$$
  (\mathcal L_W g)(X, Y) = g(\nabla_X W, Y) + g(X, \nabla_Y W)
$$
expresses the Lie derivative of the metric `g` along a vector field `W` as the
symmetrized covariant derivative of `W`, where `∇` is the Levi-Civita connection of
`g`. Equivalently, the right-hand side is `2 · (sym ∇W)(X, Y)` — the *Killing
operator* of `W`. The identity uses the torsion-free property of `∇`
(so `[X, Y] = ∇_X Y - ∇_Y X`) and its metric-compatibility
(`X(g(Y, Z)) = g(∇_X Y, Z) + g(Y, ∇_X Z)`).

The bundled Lie derivative `lieDerivMetric g W` is defined by the explicit
chart-coordinate formula
$$
  (\mathcal L_W g)_{ij}
    = W^k\,\partial_k g_{ij} + g_{kj}\,\partial_i W^k + g_{ik}\,\partial_j W^k ;
$$
the present file connects that formula to the connection form on the right-hand
side, through three chart-coordinate steps:

* the Christoffel expansion of `∇W` in a coordinate chart,
  `(∇_X W)^i = X^j \partial_j W^i + X^j \Gamma^i_{jk} W^k`;
* the chart form of metric compatibility,
  `∂_k g_{ij} = g_{lj}\,\Gamma^l_{ik} + g_{il}\,\Gamma^l_{jk}`; and
* an algebraic recombination that turns the right-hand side of the Cartan formula
  into the left-hand side via these two identities.
-/

/-- **Cartan formula for the Lie derivative of a Riemannian metric.**

For a smooth Riemannian metric `g` on `M`, a smooth tangent vector field `W`, a
point `x : M`, and tangent vectors `v, w : T_x M`:
$$
  (\mathcal L_W g)(v, w) = g(\nabla_v W, w) + g(v, \nabla_w W),
$$
where `∇` is the Levi-Civita connection of `g` and the left-hand side is the
bundled Lie-derivative tensor `lieDerivMetric g W` evaluated at `(x, v, w)`.

This is the connection form of the Killing operator that drives the DeTurck
modification of the Ricci flow.

PROOF NOTE. The identity unwinds in coordinates through the chart-Christoffel
expansion of `∇W` (`chart_christoffel_expansion_of_nabla_on_vf`) and the
chart form of metric compatibility (`metric_compat_coord_identity`), recombined
algebraically (`cartan_formula_chart_algebra`). -/
theorem cartan_formula_for_lie_deriv_metric
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g W x v w =
      g.inner x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v) w
      + g.inner x v
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w) := by
  sorry

/-! ## Chart-coordinate helpers

The Levi-Civita connection has the well-known chart-coordinate expression
$$
  (\nabla_X W)^i
    = X^j \,\partial_j W^i + X^j\,\Gamma^i_{jk}\,W^k,
$$
where `X^j, W^k` are the components of `X, W` in the chart-`α` coordinate frame and
`Γ^i_{jk}` are the Christoffel symbols of `g` in that chart
(`chartChristoffel g α k j i`).  The chart form of metric compatibility is
$$
  \partial_k g_{ij}
    = g_{lj}\,\Gamma^l_{ik} + g_{il}\,\Gamma^l_{jk}.
$$
These two identities, recombined with the symmetry
`Γ^i_{jk} = Γ^i_{kj}` (the torsion-free property), yield the Cartan formula in chart
coordinates.
-/

/-- **Chart-Christoffel expansion of the covariant derivative of a vector field.**

In the chart at `α : M`, on the chart-Levi-Civita good set, the `i`-th component of
the Levi-Civita covariant derivative `∇_X W` in the chart-coordinate frame has the
classical expression
$$
  (\nabla_X W)^i
    = \sum_j X^j\,\partial_j W^i
      + \sum_{j, k} X^j\,\Gamma^i_{jk}\,W^k.
$$
This is the coordinate form that feeds the Cartan-formula derivation: the second
term is the lower-slot Christoffel correction acting on the upper index of `W`. -/
theorem chart_christoffel_expansion_of_nabla_on_vf
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (x : M) (v : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v)) i =
      (∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) j *
            partialDeriv (E := E) j (chartCoeffOnE (I := I) α W i)
              (extChartAt I α x))
      + (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) j *
              chartChristoffel (I := I) g α j k i (extChartAt I α x) *
              chartCoeff (I := I) α W k x) := by
  sorry

/-- **Chart form of metric compatibility.**

The chart-coordinate Gram matrix `g_{ij}(α, ·)` and the chart-Christoffel symbols
`Γ^l_{ik}` are related by
$$
  \partial_k g_{ij}
    = \sum_l \Gamma^l_{ki}\,g_{lj}
      + \sum_l \Gamma^l_{kj}\,g_{li}.
$$
This is the chart-coordinate translation of `g(∇_X Y, Z) + g(Y, ∇_X Z) = X(g(Y, Z))`
applied to the coordinate frame `{e_j}`: the `(i, j, k)` components recover the
Christoffel symbols against the Gram matrix, term by term. The hypothesis
`x ∈ chartLeviCivitaGoodSet α` ensures that the chart point `extChartAt I α x` lies
in the interior of the chart target, so that the defining `partialDeriv` of the
Gram matrix has the chart-Christoffel form supplied by
`partialDeriv_chartGramOnE_eq_chartChristoffel_sum`. -/
theorem metric_compat_coord_identity
    (g : SmoothRiemannianMetric I M)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (extChartAt I α x) =
      (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k i l (extChartAt I α x) *
            chartGramOnE (I := I) g α l j (extChartAt I α x))
      + (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k j l (extChartAt I α x) *
            chartGramOnE (I := I) g α l i (extChartAt I α x)) := by
  have hint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    (mem_chartLeviCivitaGoodSet_iff.mp hx).2.2
  exact
    partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k hint

/-- **Cartan formula in chart coordinates.**

Combining the chart-Christoffel expansion of `∇W`
(`chart_christoffel_expansion_of_nabla_on_vf`) and the chart form of metric
compatibility (`metric_compat_coord_identity`), the chart-`α` component
`(𝓛_W g)_{ij}` of the metric Lie derivative coincides with
$$
  g_{kj}\,(\nabla_{e_i} W)^k + g_{ik}\,(\nabla_{e_j} W)^k,
$$
the right-hand side of the Cartan formula evaluated on the chart-coordinate frame
vectors `(e_i, e_j)`. This is the algebraic recombination step that produces the
intrinsic Cartan formula from the two preceding identities. -/
theorem cartan_formula_chart_algebra
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieDerivMetricMatrix (I := I) g W α i j x =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x k j *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
                    (extChartAt I α x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α i l k (extChartAt I α x) *
                    chartCoeff (I := I) α W l x)))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i k *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k)
                    (extChartAt I α x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α j l k (extChartAt I α x) *
                    chartCoeff (I := I) α W l x))) := by
  sorry

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
