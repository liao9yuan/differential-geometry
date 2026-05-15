import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSecondOrder

/-!
# The principal-symbol / remainder split of the second-order DeTurck-correction part

The second-order-in-`h` part `chartDeTurckCorrSecondOrderPart` of the linearized
DeTurck-correction operator is the chart-derivative combination
$$[D(\mathcal L_W g)]^{(2)}_{ij}[h] =
    \sum_k g_{kj}\,\partial_i\bigl[(DW)^k_{\mathrm{principal}}[h]\bigr]
      + \sum_k g_{ik}\,\partial_j\bigl[(DW)^k_{\mathrm{principal}}[h]\bigr],$$
with `(DW)^k_{\mathrm{principal}}[h]` the principal part of the linearized DeTurck
vector field.  Expanding the outer chart derivative by the Leibniz product rule
(`partialDeriv_chartLinearizedDeTurckVFPrincipal`) and then expanding the principal
linearized Christoffel part it contains (`partialDeriv_chartLinearizedChristoffelPrincipal`),
the outer derivative `∂_d[(DW)^k_{\mathrm{principal}}]` splits into:

* a branch where `∂_d` lands on a derivative of a component field of `h` — this
  carries the **second** chart derivative of `h` and is the principal-symbol
  content;
* the complementary branches where `∂_d` lands on an inverse-Gram factor `G^{ab}`
  or `G^{kl}` — these carry only **one** chart derivative of `h` and are genuinely
  first order.

This file isolates the two pieces.

## Index-block abbreviations

Two per-direction, per-index abbreviations keep the nested sums shallow:

* `chartDeTurckCorrHessBlock g α h d a b k` is the `∂²h` block
  `½∑_l G^{kl}·(∂_d∂_a h_{lb} + ∂_d∂_b h_{la} − ∂_d∂_l h_{ab})` — the content of
  `∂_d[(DΓ)^k{}_{ab}[h]]` carrying a second chart derivative of `h`;
* `chartDeTurckCorrGramDerivBlock g α h d a b k` is the `(∂G)(∂h)` block
  `½∑_l(∂_d G^{kl})·(∂_a h_{lb} + ∂_b h_{la} − ∂_l h_{ab})` — the content of
  `∂_d[(DΓ)^k{}_{ab}[h]]` where the outer derivative lands on the internal
  inverse-Gram factor `G^{kl}`.

## Contents

* `chartDeTurckCorrPrincipalSymbolExpr` — the pure `∂²h` expression: the
  principal-symbol content of `chartDeTurckCorrSecondOrderPart`, with every
  inverse-Gram and Gram factor frozen as a coefficient.
* `chartDeTurckCorrFirstOrderRemainder` — the complementary terms, each carrying
  **exactly one** chart derivative of a component field of `h`.
* `chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder` — the rigorous
  split `chartDeTurckCorrSecondOrderPart = chartDeTurckCorrPrincipalSymbolExpr
  + chartDeTurckCorrFirstOrderRemainder`, valid at chart-interior points, and its
  chart-source wrapper
  `chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source`
  under `[I.Boundaryless]`.
* `chartDeTurckCorrFirstOrderRemainder_eq_first_order_sum` — the explicit exhibition
  of the remainder as a finite sum of terms each of the syntactic shape
  `(coefficient)·partialDeriv _ (h _ _) _`, making precise that it carries at most
  one chart derivative of `h`.
* `h`-linearity (`_add`, `_smul`, `_zero`) of `chartDeTurckCorrPrincipalSymbolExpr`
  and `chartDeTurckCorrFirstOrderRemainder`.
* `chartDeTurckCorrPrincipalSymbolExpr_symm` — the `(i, j)`-symmetry of the
  principal-symbol expression.

The `∂_a∂_b ↦ ξ_aξ_b` substitution applied to `chartDeTurckCorrPrincipalSymbolExpr`
recovers the principal symbol of the linearized DeTurck-correction operator; the
remainder, carrying only first derivatives of `h`, is invisible to that second-order
symbol.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Index-block abbreviations

The double Leibniz expansion of `∂_d[(DW)^k_{\mathrm{principal}}]` produces, for each
lower index pair `(a, b)`, three `l`-sum blocks.  We name the two of them that carry a
chart derivative of `h` directly under their own `∂`: the pure `∂²h` block and the
`(∂G)(∂h)` block.  Naming them keeps the nested-sum expressions of the
principal-symbol expression and the remainder shallow. -/

set_option linter.unusedVariables false in
/-- The **`∂²h` index block** of the double Leibniz expansion: for the outer
chart-derivative direction `d`, the lower index pair `(a, b)`, the upper index `k`,
$$[\sigma]^k{}_{ab}[h](d)(y) = \tfrac12\sum_l G^{kl}(y)\,
    \bigl(\partial_d\partial_a h_{lb} + \partial_d\partial_b h_{la}
        - \partial_d\partial_l h_{ab}\bigr)(y),$$
the content of `∂_d[(DΓ)^k{}_{ab}[h]]` carrying a second chart derivative of `h`,
with the internal inverse-Gram factor `G^{kl}` frozen.

The background-metric parameter `g'` is retained for signature uniformity with the
public objects; it does not appear in the body. -/
def chartDeTurckCorrHessBlock (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
       partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
       partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)

@[simp] lemma chartDeTurckCorrHessBlock_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y) := rfl

set_option linter.unusedVariables false in
/-- The **`(∂G)(∂h)` index block** of the double Leibniz expansion: for the outer
chart-derivative direction `d`, the lower index pair `(a, b)`, the upper index `k`,
$$[\rho]^k{}_{ab}[h](d)(y) = \tfrac12\sum_l(\partial_d G^{kl})(y)\,
    \bigl(\partial_a h_{lb} + \partial_b h_{la} - \partial_l h_{ab}\bigr)(y),$$
the content of `∂_d[(DΓ)^k{}_{ab}[h]]` where the outer derivative lands on the
internal inverse-Gram factor `G^{kl}`.  It carries exactly one chart derivative of a
component field of `h`.

The background-metric parameter `g'` is retained for signature uniformity with the
public objects; it does not appear in the body. -/
def chartDeTurckCorrGramDerivBlock (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
      (partialDeriv (E := E) a (h l b) y +
       partialDeriv (E := E) b (h l a) y -
       partialDeriv (E := E) l (h a b) y)

@[simp] lemma chartDeTurckCorrGramDerivBlock_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a (h l b) y +
           partialDeriv (E := E) b (h l a) y -
           partialDeriv (E := E) l (h a b) y) := rfl

/-! ## The pure `∂²h` principal-symbol expression

`chartDeTurckCorrPrincipalSymbolExpr` is the pure `∂²h` content of
`chartDeTurckCorrSecondOrderPart`.  It is obtained by Leibniz-expanding the outer
chart derivative `∂_d[(DW)^k_{\mathrm{principal}}]` twice and retaining only the
branch where both chart derivatives fall on a component field of `h`.  The principal
part of the linearized DeTurck vector field is
`(DW)^k_{\mathrm{principal}}[h](y) = ∑_{a,b} G^{ab}(y)·(DΓ)^k{}_{ab}[h](y)`; the pure
`∂²h` branch of `∂_d[(DW)^k_{\mathrm{principal}}]` is therefore
`∑_{a,b} G^{ab}·[σ]^k{}_{ab}[h](d)`, with `[σ]^k{}_{ab}[h](d)` the `∂²h` index block
`chartDeTurckCorrHessBlock`.  Contracting against the chart Gram factors of the two
deformation terms gives the principal-symbol expression. -/

/-- The **pure `∂²h` principal-symbol expression** of the second-order part of the
linearized DeTurck-correction operator, in the chart at `α`, in the perturbation
direction `h`, evaluated at the chart-coordinate point `y ∈ E`.

It is the content of `chartDeTurckCorrSecondOrderPart` carrying two chart derivatives
of a component field of `h`: every chart Gram factor `g_{kj}`, `g_{ik}`, every
inverse-Gram trace factor `G^{ab}`, and every internal inverse-Gram factor `G^{kl}`
of the principal linearized Christoffel part (inside the `∂²h` index block
`chartDeTurckCorrHessBlock`) is a frozen coefficient.  Concretely
$$[D(\mathcal L_W g)]^{\sigma}_{ij}[h](y) =
    \sum_k g_{kj}(y)\,\sum_{a,b} G^{ab}(y)\,[\sigma]^k{}_{ab}[h](i)(y)
  + \sum_k g_{ik}(y)\,\sum_{a,b} G^{ab}(y)\,[\sigma]^k{}_{ab}[h](j)(y),$$
where `[σ]^k{}_{ab}[h](d) = chartDeTurckCorrHessBlock g g' α h d a b k` is the `∂²h`
index block `½∑_l G^{kl}·(∂_d∂_a h_{lb} + ∂_d∂_b h_{la} − ∂_d∂_l h_{ab})`.

Substituting `∂_d∂_a ↦ ξ_dξ_a` here gives the principal symbol of the linearized
DeTurck-correction operator. -/
def chartDeTurckCorrPrincipalSymbolExpr (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y)

@[simp] lemma chartDeTurckCorrPrincipalSymbolExpr_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y) := rfl

/-- The fully explicit `∂²h` form of the principal-symbol expression, with the `∂²h`
index block `chartDeTurckCorrHessBlock` unfolded.  Every occurrence of `h` is under an
iterated `partialDeriv`, with all chart Gram and inverse-Gram factors as frozen
coefficients. -/
lemma chartDeTurckCorrPrincipalSymbolExpr_eq_explicit
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (partialDeriv (E := E) i (partialDeriv (E := E) a (h l b)) y +
                     partialDeriv (E := E) i (partialDeriv (E := E) b (h l a)) y -
                     partialDeriv (E := E) i (partialDeriv (E := E) l (h a b)) y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α k l y *
                    (partialDeriv (E := E) j (partialDeriv (E := E) a (h l b)) y +
                     partialDeriv (E := E) j (partialDeriv (E := E) b (h l a)) y -
                     partialDeriv (E := E) j (partialDeriv (E := E) l (h a b)) y))) := by
  rw [chartDeTurckCorrPrincipalSymbolExpr_def]
  simp only [chartDeTurckCorrHessBlock_def]

/-! ## The genuinely-first-order remainder

`chartDeTurckCorrFirstOrderRemainder` collects the complementary branches of the
double Leibniz expansion: those where the outer chart derivative `∂_d` lands on an
inverse-Gram factor.  There are two such branches per `k`:

* `∂_d` on the inverse-Gram trace factor `G^{ab}`: produces
  `∑_{a,b}(∂_d G^{ab})·(DΓ)^k{}_{ab}[h]`, where `(DΓ)^k{}_{ab}[h] =
  chartLinearizedChristoffelPrincipal g α h a b k` already carries exactly one chart
  derivative of `h`;
* `∂_d` on the internal inverse-Gram factor `G^{kl}` of the principal linearized
  Christoffel part: produces `∑_{a,b} G^{ab}·[ρ]^k{}_{ab}[h](d)`, where
  `[ρ]^k{}_{ab}[h](d) = chartDeTurckCorrGramDerivBlock g g' α h d a b k` is the
  `(∂G)(∂h)` index block, again carrying exactly one chart derivative of `h`. -/

/-- The **genuinely-first-order remainder** of the second-order part of the linearized
DeTurck-correction operator.  Once the pure `∂²h` principal-symbol expression
`chartDeTurckCorrPrincipalSymbolExpr` is extracted from
`chartDeTurckCorrSecondOrderPart`, the complementary terms are the inverse-Gram
branches of the double Leibniz expansion of `∂_d[(DW)^k_{\mathrm{principal}}]`.

In the chart at `α`, in the perturbation direction `h`, at the chart-coordinate point
`y ∈ E`:
$$[D(\mathcal L_W g)]^{\rho}_{ij}[h](y) =
    \sum_k g_{kj}(y)\,\Bigl[
      \sum_{a,b}(\partial_i G^{ab})(y)\,(D\Gamma)^k{}_{ab}[h](y)
        + \sum_{a,b} G^{ab}(y)\,[\rho]^k{}_{ab}[h](i)(y)\Bigr]
  + \sum_k g_{ik}(y)\,\Bigl[
      \sum_{a,b}(\partial_j G^{ab})(y)\,(D\Gamma)^k{}_{ab}[h](y)
        + \sum_{a,b} G^{ab}(y)\,[\rho]^k{}_{ab}[h](j)(y)\Bigr],$$
where `(DΓ)^k{}_{ab}[h] = chartLinearizedChristoffelPrincipal g α h a b k` is the
principal linearized Christoffel part and `[ρ]^k{}_{ab}[h](d) =
chartDeTurckCorrGramDerivBlock g g' α h d a b k` is the `(∂G)(∂h)` index block.

Each term carries exactly one chart derivative of a component field of `h` — this is
the content of `chartDeTurckCorrFirstOrderRemainder_eq_first_order_sum`, which
justifies the remainder being invisible to the second-order principal symbol. -/
def chartDeTurckCorrFirstOrderRemainder (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y)))

@[simp] lemma chartDeTurckCorrFirstOrderRemainder_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                  chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
              (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y))) := rfl

/-! ## The Leibniz expansion of the outer chart derivative

The technical lemma `partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded` expands
`∂_d[(DW)^k_{\mathrm{principal}}]` once for the inverse-Gram trace factor `G^{ab}` and
once for the principal linearized Christoffel part `(DΓ)^k{}_{ab}[h]` it contains.  The
result is sorted into the `∂²h` index block `chartDeTurckCorrHessBlock` and the two
inverse-Gram branches (one with `∂_d G^{ab}`, one packaged into the `(∂G)(∂h)` index
block `chartDeTurckCorrGramDerivBlock`). -/

/-- **The fully-expanded outer chart derivative of the principal part of the
linearized DeTurck vector field.**  Leibniz-expanding `∂_d[(DW)^k_{\mathrm{principal}}]`
across the metric-`g` trace and then across the principal linearized Christoffel part,
each `(a, b)` summand splits into the `(∂_d G^{ab})·(DΓ)^k{}_{ab}[h]` term, the
`G^{ab}·[ρ]^k{}_{ab}[h](d)` term (with `[ρ]` the `(∂G)(∂h)` index block), and the
`G^{ab}·[σ]^k{}_{ab}[h](d)` term (with `[σ]` the `∂²h` index block).  Valid at
chart-interior points. -/
lemma partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y) +
       (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y)) := by
  classical
  -- Leibniz-expand the outer derivative across the metric-`g` trace.
  rw [partialDeriv_chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k d hy]
  -- Each `(a, b)` summand is `(∂_d G^{ab})·(DΓ)^k{}_{ab} + G^{ab}·∂_d[(DΓ)^k{}_{ab}]`;
  -- split the double sum into the two corresponding double sums.
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y +
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]]
  congr 1
  -- Expand the principal linearized Christoffel part's outer derivative, then sort it
  -- into the `(∂G)(∂h)` index block and the `∂²h` index block.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h a b k d hy,
    chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrHessBlock_def]
  -- The bracketed `∂_d[(DΓ)^k{}_{ab}]` is `½∑_l[(∂_d G^{kl})·(∂h) + G^{kl}·(∂²h)]`;
  -- distribute `G^{ab}·½∑_l(·)` over the `l`-sum's `(A + B)` split.
  rw [show ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (partialDeriv (E := E) a (h l b) y +
               partialDeriv (E := E) b (h l a) y -
               partialDeriv (E := E) l (h a b) y) +
            chartInvGramOnE (I := I) g α k l y *
              (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
               partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
               partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y))) =
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
              (partialDeriv (E := E) a (h l b) y +
               partialDeriv (E := E) b (h l a) y -
               partialDeriv (E := E) l (h a b) y)) +
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
               partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
               partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)) from by
    rw [Finset.sum_add_distrib, mul_add]]
  ring

/-! ## The rigorous split

The deliverable identity: `chartDeTurckCorrSecondOrderPart`, the literal
chart-derivative combination, equals the pure `∂²h` principal-symbol expression
`chartDeTurckCorrPrincipalSymbolExpr` plus the genuinely-first-order remainder
`chartDeTurckCorrFirstOrderRemainder`.

The proof Leibniz-expands `∂_d[(DW)^k_{\mathrm{principal}}]` via
`partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded`; every resulting summand is
sorted into the `∂²h` block (which assembles into the principal-symbol expression) or
one of the two inverse-Gram branches (which assemble into the remainder).  The sorting
is purely the distributivity of `Finset.sum` over addition together with `ring`. -/

/-- **The principal-symbol / remainder split of the second-order DeTurck-correction
part.**  At chart-interior points, the literal chart-derivative combination
`chartDeTurckCorrSecondOrderPart` splits as the pure `∂²h` principal-symbol expression
`chartDeTurckCorrPrincipalSymbolExpr` plus the genuinely-first-order remainder
`chartDeTurckCorrFirstOrderRemainder`.

The principal-symbol expression collects the branch of the double Leibniz expansion
where both chart derivatives fall on a component field of `h`; the remainder collects
the two inverse-Gram branches.  Under `[I.Boundaryless]` the chart-interior hypothesis
is automatic for `y = extChartAt I α x` with `x` in the chart source — see
`chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source`. -/
theorem chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    chartDeTurckCorrFirstOrderRemainder_def]
  -- Expand each `k`-summand's outer derivative `∂_i[(DW)^k]` and `∂_j[(DW)^k]`.
  have hexp : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y) +
         (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y)) :=
    fun d k => partialDeriv_chartLinearizedDeTurckVFPrincipal_expanded
      (I := I) g g' α h k d hy
  -- Substitute the expansion into the first `k`-sum and split into the principal block
  -- and the remainder block.
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp i k]
    ring
  -- Likewise for the second `k`-sum.
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hexp j k]
    ring
  rw [hsum1, hsum2]
  ring

/-- **The principal-symbol / remainder split on the chart source under
`[I.Boundaryless]`.**  At chart-image points `y = extChartAt I α x` with `x` in the
chart source, the chart-interior hypothesis of
`chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder` is automatic. -/
theorem chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
    [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j (extChartAt I α x) =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j (extChartAt I α x) +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder
    (I := I) g g' α h i j hx_int

/-! ## First-order character of the remainder

The remainder `chartDeTurckCorrFirstOrderRemainder` carries **exactly one** chart
derivative of any component field of `h`.  We make this precise by exhibiting it as a
finite sum of terms each syntactically of the form `(coefficient)·partialDeriv _
(h _ _) _`, where the coefficient does not involve `h` at all.  The principal
linearized Christoffel part `chartLinearizedChristoffelPrincipal g α h a b k` that
appears in the inverse-Gram-trace branch is itself first order in `h`; we unfold it,
and the `(∂G)(∂h)` index block, to their explicit `½∑_l (·)·(∂h)` formulas so that
every occurrence of `h` is visibly under a single `partialDeriv`. -/

/-- **The first-order remainder, exhibited as a sum of first-order terms.**  The
remainder `chartDeTurckCorrFirstOrderRemainder` is a finite sum of terms, each a
product of a coefficient not involving `h` with a single `partialDeriv` of a component
field of `h`.

Each contribution is `g`- or `G`-weighted; the principal linearized Christoffel part
of the inverse-Gram-trace branch and the `(∂G)(∂h)` index block are unfolded to their
explicit `½∑_l (·)·(∂h)` formulas, so no term carries a second chart derivative of
`h`.  This is the formal content of "the remainder carries at most one chart
derivative of `h`". -/
theorem chartDeTurckCorrFirstOrderRemainder_eq_first_order_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) l (h a b) y)))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (partialDeriv (E := E) j
                      (chartInvGramOnE (I := I) g α a b) y *
                    chartInvGramOnE (I := I) g α k l y)) *
                    partialDeriv (E := E) l (h a b) y)) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                (((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) a (h l b) y +
                  ((1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) b (h l a) y +
                  (-(1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α a b y *
                    partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y)) *
                    partialDeriv (E := E) l (h a b) y)))) := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def]
  -- Match the two `k`-sums summand by summand.
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · -- Inverse-Gram-trace branch: unfold `chartLinearizedChristoffelPrincipal` to its
      -- explicit `½∑_l G^{kl}·(∂h)` formula, then push `(∂_i G^{ab})·` inside.
      refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · -- Internal-inverse-Gram branch: unfold the `(∂G)(∂h)` index block, push weights in.
      refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartLinearizedChristoffelPrincipal_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [chartDeTurckCorrGramDerivBlock_def, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

/-! ## Linearity of the index blocks in the perturbation direction

The `∂²h` index block and the `(∂G)(∂h)` index block are `ℝ`-linear in the
perturbation `h`: additive over a sum of perturbations, homogeneous under a real-scalar
multiple, and zero on the zero perturbation.  These are read off the explicit formulas
through the `partialDeriv` algebra; the principal-symbol expression and the remainder
inherit their linearity from these blocks. -/

section BlockLinearity

/-- An iterated partial derivative of a zero component field vanishes. -/
private lemma partialDeriv_partialDeriv_zero
    (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p
        (partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b)) y = 0 := by
  have hinner : partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b) =
      fun _ : E => (0 : ℝ) := by
    funext y'
    have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
    rw [hconst, partialDeriv_const]
  rw [hinner, partialDeriv_const]

/-- A first partial derivative of a zero component field vanishes. -/
private lemma partialDeriv_zero_apply
    (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((0 : ChartMetricPerturbation E) a b) y = 0 := by
  have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
  rw [hconst, partialDeriv_const]

/-- A perturbation component field of a pointwise sum splits the iterated partial
derivative additively. -/
private lemma partialDeriv_partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((h₁ + h₂) a b)) y =
      partialDeriv (E := E) p (partialDeriv (E := E) q (h₁ a b)) y +
        partialDeriv (E := E) p (partialDeriv (E := E) q (h₂ a b)) y := by
  have hinner : partialDeriv (E := E) q ((h₁ + h₂) a b) =
      fun y' => partialDeriv (E := E) q (h₁ a b) y' +
        partialDeriv (E := E) q (h₂ a b) y' := by
    funext y'
    have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
    rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
          (h₁.differentiableAt a b y') (h₂.differentiableAt a b y')]
  rw [hinner, partialDeriv_add (E := E)
        (partialDeriv (E := E) q (h₁ a b)) (partialDeriv (E := E) q (h₂ a b))
        (partialDeriv_perturbation_differentiableAt h₁ q a b y)
        (partialDeriv_perturbation_differentiableAt h₂ q a b y)]

/-- A perturbation component field of a pointwise sum splits the first partial
derivative additively. -/
private lemma partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((h₁ + h₂) a b) y =
      partialDeriv (E := E) p (h₁ a b) y + partialDeriv (E := E) p (h₂ a b) y := by
  have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
  rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
        (h₁.differentiableAt a b y) (h₂.differentiableAt a b y)]

/-- A perturbation component field of a scalar multiple scales the iterated partial
derivative. -/
private lemma partialDeriv_partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((c • h) a b)) y =
      c * partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y := by
  have hinner : partialDeriv (E := E) q ((c • h) a b) =
      fun y' => c • partialDeriv (E := E) q (h a b) y' := by
    funext y'
    have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
    rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y')]
  rw [hinner, partialDeriv_const_smul (E := E) c
        (partialDeriv (E := E) q (h a b))
        (partialDeriv_perturbation_differentiableAt h q a b y), smul_eq_mul]

/-- A perturbation component field of a scalar multiple scales the first partial
derivative. -/
private lemma partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p ((c • h) a b) y =
      c * partialDeriv (E := E) p (h a b) y := by
  have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
  rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y),
    smul_eq_mul]

/-- The `∂²h` index block vanishes on the zero perturbation. -/
@[simp] lemma chartDeTurckCorrHessBlock_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrHessBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) d
            (partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b)) y +
         partialDeriv (E := E) d
            (partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a)) y -
         partialDeriv (E := E) d
            (partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b)) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_zero d a l b y,
      partialDeriv_partialDeriv_zero d b l a y,
      partialDeriv_partialDeriv_zero d l a b y]
    ring
  rw [hzero, mul_zero]

/-- **Additivity** of the `∂²h` index block in the perturbation direction. -/
lemma chartDeTurckCorrHessBlock_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) d a b k y =
      chartDeTurckCorrHessBlock (I := I) g g' α h₁ d a b k y +
        chartDeTurckCorrHessBlock (I := I) g g' α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrHessBlock_def, chartDeTurckCorrHessBlock_def,
    chartDeTurckCorrHessBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_partialDeriv_add_apply h₁ h₂ d a l b y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d b l a y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ d l a b y]
  ring

/-- **Scalar homogeneity** of the `∂²h` index block in the perturbation direction. -/
lemma chartDeTurckCorrHessBlock_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrHessBlock (I := I) g g' α (c • h) d a b k y =
      c * chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y := by
  classical
  rw [chartDeTurckCorrHessBlock_def, chartDeTurckCorrHessBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a ((c • h) l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b ((c • h) l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l ((c • h) a b)) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
           partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
           partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_smul_apply c h d a l b y,
      partialDeriv_partialDeriv_smul_apply c h d b l a y,
      partialDeriv_partialDeriv_smul_apply c h d l a b y]
    ring]
  ring

/-- The `(∂G)(∂h)` index block vanishes on the zero perturbation. -/
@[simp] lemma chartDeTurckCorrGramDerivBlock_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α
      (0 : ChartMetricPerturbation E) d a b k y = 0 := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def]
  have hzero : (∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
        (partialDeriv (E := E) a ((0 : ChartMetricPerturbation E) l b) y +
         partialDeriv (E := E) b ((0 : ChartMetricPerturbation E) l a) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) a b) y)) = 0 := by
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [partialDeriv_zero_apply a l b y, partialDeriv_zero_apply b l a y,
      partialDeriv_zero_apply l a b y]
    ring
  rw [hzero, mul_zero]

/-- **Additivity** of the `(∂G)(∂h)` index block in the perturbation direction. -/
lemma chartDeTurckCorrGramDerivBlock_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) d a b k y =
      chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ d a b k y +
        chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ d a b k y := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrGramDerivBlock_def,
    chartDeTurckCorrGramDerivBlock_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_add_apply h₁ h₂ a l b y, partialDeriv_add_apply h₁ h₂ b l a y,
    partialDeriv_add_apply h₁ h₂ l a b y]
  ring

/-- **Scalar homogeneity** of the `(∂G)(∂h)` index block in the perturbation
direction. -/
lemma chartDeTurckCorrGramDerivBlock_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (d a b k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) d a b k y =
      c * chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y := by
  classical
  rw [chartDeTurckCorrGramDerivBlock_def, chartDeTurckCorrGramDerivBlock_def]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a ((c • h) l b) y +
           partialDeriv (E := E) b ((c • h) l a) y -
           partialDeriv (E := E) l ((c • h) a b) y)) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) d (chartInvGramOnE (I := I) g α k l) y *
          (partialDeriv (E := E) a (h l b) y +
           partialDeriv (E := E) b (h l a) y -
           partialDeriv (E := E) l (h a b) y) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_smul_apply c h a l b y, partialDeriv_smul_apply c h b l a y,
      partialDeriv_smul_apply c h l a b y]
    ring]
  ring

end BlockLinearity

/-! ## Linearity of the principal-symbol expression and the remainder

Both the pure `∂²h` principal-symbol expression and the first-order remainder are
`ℝ`-linear in the perturbation `h`.  Linearity is now immediate from the linearity of
the `∂²h` and `(∂G)(∂h)` index blocks proved above, pushed through the metric-`g`
trace and the deformation Gram factors. -/

/-! ### Linearity of the principal-symbol expression -/

/-- The pure `∂²h` principal-symbol expression vanishes on the zero perturbation. -/
@[simp] lemma chartDeTurckCorrPrincipalSymbolExpr_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def]
  have hzero : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hzero i k, mul_zero]),
    Finset.sum_eq_zero (fun k _ => by rw [hzero j k, mul_zero]), add_zero]

/-- **Additivity** of the pure `∂²h` principal-symbol expression in the perturbation
direction. -/
theorem chartDeTurckCorrPrincipalSymbolExpr_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h₁ i j y +
        chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    chartDeTurckCorrPrincipalSymbolExpr_def]
  have hsplit : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) i a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ i a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ i a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit i k, mul_add]]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (h₁ + h₂) j a b k y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₁ j a b k y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h₂ j a b k y) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsplit j k, mul_add]]
  ring

/-- **Scalar homogeneity** of the pure `∂²h` principal-symbol expression in the
perturbation direction. -/
theorem chartDeTurckCorrPrincipalSymbolExpr_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    smul_eq_mul]
  have hscale : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrHessBlock (I := I) g g' α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrHessBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (c • h) i a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h i a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α (c • h) j a b k y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h j a b k y from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hscale j k]; ring]
  ring

/-! ### Linearity of the first-order remainder -/

/-- The first-order remainder vanishes on the zero perturbation. -/
@[simp] lemma chartDeTurckCorrFirstOrderRemainder_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def]
  have hbranchA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α
              (0 : ChartMetricPerturbation E) a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_zero, mul_zero]
  have hbranchB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α
              (0 : ChartMetricPerturbation E) d a b k y) = 0 := by
    intro d k
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_zero, mul_zero]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hbranchA i k, hbranchB i k]; ring),
    Finset.sum_eq_zero (fun k _ => by rw [hbranchA j k, hbranchB j k]; ring), add_zero]

/-- **Additivity** of the first-order remainder in the perturbation direction. -/
theorem chartDeTurckCorrFirstOrderRemainder_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h₁ i j y +
        chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def, chartDeTurckCorrFirstOrderRemainder_def,
    chartDeTurckCorrFirstOrderRemainder_def]
  -- The inverse-Gram-trace branch splits additively.
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
              chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_add]
    ring
  -- The internal-inverse-Gram branch splits additively.
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) d a b k y) =
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ d a b k y) +
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ d a b k y) := by
    intro d k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_add]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) i a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ i a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ i a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (h₁ + h₂) j a b k y))) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₁ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₁ j a b k y))) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h₂ a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h₂ j a b k y))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

/-- **Scalar homogeneity** of the first-order remainder in the perturbation
direction. -/
theorem chartDeTurckCorrFirstOrderRemainder_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrFirstOrderRemainder (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrFirstOrderRemainder (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrFirstOrderRemainder_def, chartDeTurckCorrFirstOrderRemainder_def,
    smul_eq_mul]
  -- The inverse-Gram-trace branch scales by `c`.
  have hA : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartLinearizedChristoffelPrincipal_smul, smul_eq_mul]
    ring
  -- The internal-inverse-Gram branch scales by `c`.
  have hB : ∀ (d k : Fin (Module.finrank ℝ E)),
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) d a b k y) =
        c * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y *
            chartDeTurckCorrGramDerivBlock (I := I) g g' α h d a b k y := by
    intro d k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [chartDeTurckCorrGramDerivBlock_smul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) i a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h i a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA i k, hB i k]; ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α (c • h) a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α (c • h) j a b k y))) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (chartInvGramOnE (I := I) g α a b) y *
                chartLinearizedChristoffelPrincipal (I := I) g α h a b k y) +
            (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α a b y *
                chartDeTurckCorrGramDerivBlock (I := I) g g' α h j a b k y)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA j k, hB j k]; ring]
  ring

/-! ## Symmetry of the principal-symbol expression

The pure `∂²h` principal-symbol expression is symmetric in the index pair `(i, j)`.
This is the linearized analogue of the symmetry of the DeTurck-correction tensor.  The
symmetry is term-by-term clean: under `i ↔ j` the two big `k`-sums of
`chartDeTurckCorrPrincipalSymbolExpr` are interchanged, and the chart Gram factors
`g_{kj}`, `g_{ik}` match after the symmetry `g_{kj} = g_{jk}`, `g_{ik} = g_{ki}` of the
Gram matrix.  No Schwarz symmetry of the mixed partials is needed. -/

/-- **Symmetry of the pure `∂²h` principal-symbol expression** in the index pair
`(i, j)`.  Swapping `i ↔ j` interchanges the two `k`-sums of
`chartDeTurckCorrPrincipalSymbolExpr`; the chart Gram factors `g_{kj}`, `g_{ik}` agree
after `g_{kj} = g_{jk}`, `g_{ik} = g_{ki}` (`chartGramOnE_symm`), so the expression is
invariant. -/
theorem chartDeTurckCorrPrincipalSymbolExpr_symm
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i j y =
      chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h j i y := by
  classical
  rw [chartDeTurckCorrPrincipalSymbolExpr_def, chartDeTurckCorrPrincipalSymbolExpr_def]
  -- `Symbol(j, i)` has the same two `k`-sums as `Symbol(i, j)` with the order swapped;
  -- the Gram factors agree after `chartGramOnE_symm`.
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α i k y]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartGramOnE_symm (I := I) g α k j y]

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
