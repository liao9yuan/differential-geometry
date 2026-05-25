import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ChartVectorField
import DifferentialGeometry.Integral.Connection.ChartLeviCivitaParallelExtend

/-!
# Chart-coordinate decomposition of the bundled DeTurck vector field

For two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M`, the
bundled DeTurck vector field `deTurckVF g g'` (a smooth tangent-bundle section
defined as the metric-`g` trace of the connection-difference tensor
`connDiff g g' = ∇^{LC}(g) − ∇^{LC}(g')`) admits, in each chart `α` and at every
point `x` of the chart-`α` Levi-Civita good set, the explicit chart-coordinate
expansion

$$
  (\mathrm{deTurckVF}\,g\,g')\,x \;=\;
  \sum_{k} W^{k}(g, g', \alpha)(\varphi_\alpha x)\;e_k(x),
$$

where `W^{k}(g, g', \alpha)(y) = \sum_{a,b} G(g)^{ab}(y)
(\Gamma^{k}{}_{ab}(g)(y) - \Gamma^{k}{}_{ab}(g')(y))` is the chart-coordinate
DeTurck-VF component (`chartDeTurckVFComp` of
`DeTurckLinearization/ChartVectorField`) and
`e_k(x) = \mathrm{chartBasisVecFiber}\,\alpha\,k\,x` is the `k`-th chart-`α`
coordinate basis vector field.

This identity bridges the two parallel descriptions of the DeTurck vector field
that live elsewhere in the project: the **bundled** description via `connDiff`
(used to argue smoothness and chart-independence), and the **chart-formula**
description via `chartDeTurckVFComp` (used to argue continuity-in-the-metric of
its chart-coordinate components).  The two are forced to agree by the
chart-coordinate expansion of the Levi-Civita covariant derivative.

## Main results

* `deTurckChartLocal_eq_chartDeTurckVFComp_sum` — chart-`α` version: on the
  chart-`α` Levi-Civita good set,
  $\mathrm{deTurckChartLocal}\,g\,g'\,\alpha\,x =
  \sum_{k} W^{k}(g, g', \alpha)(\varphi_\alpha x) \cdot e_k(x)$.
* `deTurckFun_apply_eq_chartDeTurckVFComp_sum` — at every point `x`, taking the
  chart at `α := x`,
  $\mathrm{deTurckFun}\,g\,g'\,x = \sum_{k} W^{k}(g, g', x)(\varphi_x x)
  \cdot (\mathrm{chartModelBasis}\,E)_k$.
* `deTurckVF_apply_eq_chartDeTurckVFComp_sum` — the headline bridge: on the
  bundled section `deTurckVF g g'`, the same chart-coordinate sum identity
  holds.

## Strategy

The chart at `α = x` always contains `x` in its good set (`self_mem`), so
the chart-`α` form specialised to `α = x` covers the bundled identity.  In the
chart at `α`, the chart-local representative `deTurckChartLocal g g' α x` is the
double sum
$\sum_{j,k} G^{jk}(g, \alpha, x) \cdot \mathrm{connDiff}\,g\,g'\,x
(e_j(x), e_k(x))$.

For each pair `(j, k)` we expand `connDiff g g' x (e_j(x), e_k(x))` into a sum
of chart-basis vectors with chart-Christoffel coefficients:

* The section `b' ↦ \mathrm{chartBasisVecFiber}\,\alpha\,j\,b'` and the
  chart-parallel extension `\mathrm{chartParallelExtend}\,\alpha\,x
  (\mathrm{chartBasisVecFiber}\,\alpha\,j\,x)` agree on the trivialisation base
  set at `α` (both equal `\mathrm{trivFromE}\,\alpha\,b'\,(\mathrm{chartModelBasis}\,E)_j`),
  hence eventually agree near `x`.
* By `IsCovariantDerivativeOn.congr_of_eventuallyEq` applied to `LeviCivita g`
  on the chart-`α` good set, the two covariant derivatives at `x` along the two
  sections coincide.
* The `chartLeviCivita_chartParallelExtend_symm` identity reduces the
  covariant derivative of the chart-parallel extension to the chart-local
  Christoffel correction term `christoffelCorrection g α x · (e_k(x))`.
* `coord_christoffelCorrection_eq` (from
  `Analysis/Laplacian/TensorRegularity/CovDerivSlotCorrectionComponent`) gives
  the `p`-th model-basis coordinate of that Christoffel-correction term as a
  single sum over `chartChristoffel` evaluated at the chart image of `x`.

Combining for both `LeviCivita g` and `LeviCivita g'`, the difference yields the
chart-Christoffel difference `Γ^p_{kj}(g) − Γ^p_{kj}(g')(extChartAt α x)`, and a
`chartChristoffel_symm` swap converts `(k, j)` to `(j, k)` so the resulting
double sum matches `chartDeTurckVFComp` exactly.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Pointwise agreement between chart-basis section and chart-parallel extension -/

/-- The chart-`α` coordinate basis vector field at index `j`, viewed as a
section, agrees on the chart-`α` trivialisation base set with the chart-parallel
extension of its own value at any base-set point.

Both sides unfold to `trivFromE α b' (chartModelBasis E j)` on the base set:

* LHS `chartBasisVecFiber α j b' = trivFromE α b' (chartModelBasis E j)` directly.
* RHS `chartParallelExtend α b (chartBasisVecFiber α j b) b' =
  trivFromE α b' (trivToE α b (trivFromE α b (chartModelBasis E j)))
  = trivFromE α b' (chartModelBasis E j)` after collapsing `trivToE α b ∘
  trivFromE α b = id` on the base set. -/
lemma chartBasisVecFiber_eq_chartParallelExtend_on_baseSet
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (j : Fin (Module.finrank ℝ E)) :
    ∀ b' ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartBasisVecFiber (I := I) α j b' =
        chartParallelExtend (I := I) α b
          (chartBasisVecFiber (I := I) α j b) b' := by
  intro b' _hb'
  -- Both sides unfold to `trivFromE α b' (chartModelBasis E j)`.
  unfold chartParallelExtend
  -- RHS: `trivFromE α b' (trivToE α b (chartBasisVecFiber α j b))`.
  -- Substitute the definition of `chartBasisVecFiber α j b`.
  -- `chartBasisVecFiber α j b = trivFromE α b (chartModelBasis E j)` by `chartBasisVecFiber` def.
  change (trivializationAt E (TangentSpace I) α).symm b' ((chartModelBasis E) j) =
    trivFromE (I := I) α b'
      (trivToE (I := I) α b
        ((trivializationAt E (TangentSpace I) α).symm b ((chartModelBasis E) j)))
  -- `(triv α).symm b = trivFromE α b` on the base set (by definition); collapse
  -- the inner round-trip using `trivToE_trivFromE`.
  have hround : trivToE (I := I) α b
      ((trivializationAt E (TangentSpace I) α).symm b ((chartModelBasis E) j)) =
      (chartModelBasis E) j := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) j)) = (chartModelBasis E) j
    exact trivToE_trivFromE (I := I) α hb ((chartModelBasis E) j)
  rw [hround]
  rfl

/-- Eventually-equal form on a chart-`α` good-set point: the chart-basis section
agrees with the chart-parallel extension of its value at `b`, near `b`. -/
lemma chartBasisVecFiber_eventuallyEq_chartParallelExtend
    (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (j : Fin (Module.finrank ℝ E)) :
    (fun b' : M => chartBasisVecFiber (I := I) α j b') =ᶠ[𝓝 b]
      fun b' : M =>
        chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b' := by
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hbase_nhds : (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 b :=
    hopen.mem_nhds hb_base
  refine Filter.eventually_of_mem hbase_nhds ?_
  intro b' hb'
  exact chartBasisVecFiber_eq_chartParallelExtend_on_baseSet (I := I) α hb_base j b' hb'

/-! ## Manifold-differentiability of the chart-basis section at a good-set point -/

/-- The chart-`α` coordinate basis section is `MDifferentiableAt` at every point
of the chart-`α` trivialisation base set; in particular at every good-set point. -/
lemma chartBasisVecFiber_mdifferentiableAt
    (α : M) (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) b := by
  classical
  have hcontMDiff_on := chartBasisVec_contMDiffOn (I := I) α j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α j) b :=
    (hcontMDiff_on b hb).contMDiffAt (hopen.mem_nhds hb)
  exact hcontMDiff_at.mdifferentiableAt (by norm_num)

/-! ## The Levi-Civita bridge: from the chart-basis section to the parallel CLM

On the chart-`α` good set, the bundled Levi-Civita derivative of the chart-basis
section `chartBasisVecFiber α j`, evaluated at `b` along a direction `v`, agrees
with the chart-`α` parallel-CLM action.  This is the headline rewrite step from
the parallel-extension agreement lemma, lifted to the chart-basis section via
`IsCovariantDerivativeOn.congr_of_eventuallyEq`. -/

/-- **Chart-coordinate value of `LeviCivita g` on the chart-basis section.** On
the chart-`α` good set, the bundled Levi-Civita derivative of
`chartBasisVecFiber α j` at `b` along `v` equals
`trivFromE α b (christoffelCorrection g α b (chartModelBasis E j) v)`. -/
lemma LeviCivita_chartBasisVecFiber_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (j : Fin (Module.finrank ℝ E)) (v : TangentSpace I b) :
    (LeviCivita (I := I) g).toFun
        (fun b' : M => chartBasisVecFiber (I := I) α j b') b v =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b ((chartModelBasis E) j) v) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Manifold-differentiability of the chart-basis section at `b`.
  have hsection_diff : MDiffAt
      (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) b :=
    chartBasisVecFiber_mdifferentiableAt (I := I) α j
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hb)
  -- Manifold-differentiability of the chart-parallel extension at `b`.
  have hparallel_diff : MDiffAt
      (T% (fun b' : M => chartParallelExtend (I := I) α b
        (chartBasisVecFiber (I := I) α j b) b')) b :=
    chartParallelExtend_mdifferentiableAt (I := I) α hb
      (chartBasisVecFiber (I := I) α j b)
  -- Pointwise equality on the good-set neighbourhood.
  have heq : (fun b' : M => chartBasisVecFiber (I := I) α j b') =ᶠ[𝓝 b]
      fun b' : M =>
        chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b' :=
    chartBasisVecFiber_eventuallyEq_chartParallelExtend (I := I) α hb j
  -- The good set itself is open and contains `b`, hence is in 𝓝 b.
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hgood_nhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b :=
    hgood_open.mem_nhds hb
  -- Congruence of `LeviCivita g` along eventually-equal sections.
  have hcov_eq :
      (LeviCivita (I := I) g).toFun
          (fun b' : M => chartBasisVecFiber (I := I) α j b') b =
        (LeviCivita (I := I) g).toFun
          (fun b' : M =>
            chartParallelExtend (I := I) α b (chartBasisVecFiber (I := I) α j b) b') b := by
    have hLC := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv
    exact hLC.congr_of_eventuallyEq hsection_diff hparallel_diff
      (Filter.univ_mem) heq
  rw [show
        (LeviCivita (I := I) g).toFun
            (fun b' : M => chartBasisVecFiber (I := I) α j b') b v
          = (LeviCivita (I := I) g).toFun
              (fun b' : M =>
                chartParallelExtend (I := I) α b
                  (chartBasisVecFiber (I := I) α j b) b') b v from by
          rw [hcov_eq]]
  -- Now reduce the parallel-extension form using chart-overlap + parallel-CLM
  -- identity.  We package the "X b = v" trick via a constant section `fun _ => v`,
  -- but we just need the value at `b`, so pick `X b' := v` extended trivially.
  -- A `Π b' : M, TangentSpace I b'` constant-on-fibre extension is awkward, so
  -- use a smooth global section through `v`.
  -- Easier path: directly chain through the chart-overlap formula.
  -- Step 1: chart-overlap.
  rw [LeviCivita_chart_apply (I := I) g α hb hparallel_diff v]
  -- Step 2: chart-Levi-Civita on chart-parallel extension.
  have hcompute := chartLeviCivita_chartParallelExtend_symm (I := I) g α hb
    (chartBasisVecFiber (I := I) α j b) (fun _ : M => v)
  -- `hcompute : chartLeviCivita g α (chartParallelExtend α b (chartBasisVecFiber α j b)) b v =
  --              trivFromE α b (christoffelCorrection g α b
  --                (trivToE α b v) (chartBasisVecFiber α j b))`.
  -- We instead want the form with `(chartModelBasis E j)` as the `Y` slot and
  -- `v` as the directional slot.  Note `christoffelCorrection_symm_cancel` already
  -- swapped them inside `chartLeviCivita_chartParallelExtend_symm`.
  -- Reading `hcompute`: the LHS is `chartLeviCivita … b ((fun _ => v) b)` which
  -- definitionally reduces to `chartLeviCivita … b v`.
  -- The RHS is `trivFromE α b (christoffelCorrection g α b
  --   (trivToE α b ((fun _ => v) b)) (chartBasisVecFiber α j b))`
  -- which definitionally reduces to
  -- `trivFromE α b (christoffelCorrection g α b (trivToE α b v) (chartBasisVecFiber α j b))`.
  -- We want: `trivFromE α b (christoffelCorrection g α b (chartModelBasis E j) v)`.
  -- The slot order in the headline IS swapped from `hcompute`'s slot order; we'll
  -- handle this using `christoffelCorrection_symm_cancel` directly.
  rw [hcompute]
  -- Goal: `trivFromE α b (christoffelCorrection g α b (trivToE α b v) (chartBasisVecFiber α j b)) =
  --         trivFromE α b (christoffelCorrection g α b (chartModelBasis E j) v)`.
  congr 1
  -- Apply `christoffelCorrection_symm_cancel` to swap the slot order, then rewrite
  -- the `chartBasisVecFiber α j b` argument using `trivToE`.
  have hcancel := christoffelCorrection_symm_cancel (I := I) g α b
    (chartBasisVecFiber (I := I) α j b) v
  -- `hcancel : christoffelCorrection g α b (trivToE α b v) (chartBasisVecFiber α j b) =
  --              christoffelCorrection g α b
  --                (trivToE α b (chartBasisVecFiber α j b)) v`.
  rw [hcancel]
  -- Now identify `trivToE α b (chartBasisVecFiber α j b) = chartModelBasis E j`
  -- on the base set.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have htriv : trivToE (I := I) α b
      (chartBasisVecFiber (I := I) α j b) = (chartModelBasis E) j := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) j)) = (chartModelBasis E) j
    exact trivToE_trivFromE (I := I) α hb_base ((chartModelBasis E) j)
  rw [htriv]

/-! ## Chart-coordinate form of `connDiff` on chart-basis section pairs

For two metrics `g` and `g'`, the connection difference `connDiff g g' x` applied
to two chart-basis section values `(chartBasisVecFiber α j x, chartBasisVecFiber α k x)`
expands, on the chart-`α` good set, as the model-basis sum of chart-Christoffel
differences, transported back to the tangent space at `x` by `trivFromE α x`. -/

/-- **Chart-coordinate value of `connDiff g g'` on chart-basis fibre pair.**
On the chart-`α` good set,
$\mathrm{connDiff}\,g\,g'\,x\,
(\mathrm{chartBasisVecFiber}\,\alpha\,j\,x,
 \mathrm{chartBasisVecFiber}\,\alpha\,k\,x) =
\mathrm{trivFromE}\,\alpha\,x\,(\mathrm{christoffelCorrection}\,g\,\alpha\,x\,(e_j) -
\mathrm{christoffelCorrection}\,g'\,\alpha\,x\,(e_j))(e_k(x))$. -/
lemma connDiff_chartBasis_pair_eq
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      trivFromE (I := I) α x
        (christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) -
      trivFromE (I := I) α x
        (christoffelCorrection (I := I) g' α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) := by
  classical
  -- Manifold-differentiability of the chart-basis section at `x`.
  have hsection_diff : MDiffAt
      (T% (fun b' : M => chartBasisVecFiber (I := I) α j b')) x :=
    chartBasisVecFiber_mdifferentiableAt (I := I) α j
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)
  -- `connDiff_apply` with `σ := chartBasisVecFiber α j` and `v := chartBasisVecFiber α k x`.
  rw [connDiff_apply (I := I) g g' hsection_diff
        (chartBasisVecFiber (I := I) α k x)]
  -- Apply the Levi-Civita chart-basis identity to both terms.
  rw [LeviCivita_chartBasisVecFiber_eq (I := I) g α hx j
        (chartBasisVecFiber (I := I) α k x)]
  rw [LeviCivita_chartBasisVecFiber_eq (I := I) g' α hx j
        (chartBasisVecFiber (I := I) α k x)]

/-! ## Coordinate expansion of `christoffelCorrection` on chart-basis pair

Using `coord_christoffelCorrection_eq`-style expansion: the `p`-th model-basis
coordinate of `christoffelCorrection g α x (chartModelBasis E j) (chartBasisVecFiber α k x)`
is `chartChristoffel g α k j p (extChartAt I α x)`. -/

/-- **Coordinate expansion of `christoffelCorrection` on chart-basis pair.** On
the chart-`α` good set, the `p`-th model-basis coordinate of
$\mathrm{christoffelCorrection}\,g\,\alpha\,x\,(e_j)(e_k(x))$ equals the chart
Christoffel symbol $\Gamma^p{}_{k j}(g, \alpha)(\varphi_\alpha x)$. -/
lemma coord_christoffelCorrection_chartBasis_pair
    (g : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k p : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).coord p)
        (christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
          (chartBasisVecFiber (I := I) α k x)) =
      chartChristoffel (I := I) g α k j p (extChartAt I α x) := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  -- Apply `christoffelCorrection_apply` directly.
  rw [christoffelCorrection_apply (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α k x)]
  -- `trivToE α x (chartBasisVecFiber α k x) = chartModelBasis E k` on the base set.
  have htriv : trivToE (I := I) α x
      (chartBasisVecFiber (I := I) α k x) = (chartModelBasis E) k := by
    change trivToE (I := I) α x
        (trivFromE (I := I) α x ((chartModelBasis E) k)) = (chartModelBasis E) k
    exact trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) k)
  rw [htriv]
  -- The triple sum collapses to a single term at `(k, j)` via Kronecker deltas.
  -- We use `simp` with the basis-coordinate lemmas to handle the
  -- `(b.repr (b k)) i = δ_{k,i}` patterns uniformly.
  rw [map_sum]
  -- Collapse the outer `i` sum at `i = k`.
  rw [Finset.sum_eq_single k]
  · -- `i = k` case.
    rw [map_sum]
    rw [Finset.sum_eq_single j]
    · -- `j' = j` case.
      rw [map_sum]
      rw [Finset.sum_eq_single p]
      · -- `k' = p` case: collapse all three deltas.
        rw [LinearMap.map_smul, smul_eq_mul]
        simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply, ↓reduceIte]
        ring
      · -- `k' ≠ p` case: `(b.coord p) (b k') = 0`.
        intro k' _ hk'
        rw [LinearMap.map_smul, smul_eq_mul]
        simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply, if_neg hk', mul_zero]
      · intro h
        exact absurd (Finset.mem_univ p) h
    · -- `j' ≠ j` case.
      intro j' _ hj'
      rw [map_sum]
      refine Finset.sum_eq_zero (fun p' _ => ?_)
      rw [LinearMap.map_smul, smul_eq_mul]
      -- `(b.repr (b j)) j' = if j = j' then 1 else 0`, here `j' ≠ j`.
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg (Ne.symm hj')]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  · -- `i ≠ k` case: all three nested sums vanish.
    intro k' _ hk'
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun p' _ => ?_)
    rw [LinearMap.map_smul, smul_eq_mul]
    -- `(b.repr (b k)) k' = if k = k' then 1 else 0`, here `k' ≠ k`.
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hk')]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ## Sum expansion of `trivFromE` and `christoffelCorrection`

We now combine `connDiff_chartBasis_pair_eq` with the model-basis coordinate
expansion `coord_christoffelCorrection_chartBasis_pair` to express the
`connDiff`-on-chart-basis-pair as the explicit sum
`∑_p (Γ^p_{kj}(g) - Γ^p_{kj}(g')) • chartBasisVecFiber α p x`. -/

/-- A vector in `TangentSpace I x` (sitting at a chart-`α` base-set point) is
the sum, over `p`, of its model-basis coordinates after applying `trivToE α x`,
each multiplying `chartBasisVecFiber α p x`. -/
private lemma tangent_vector_eq_chartBasisVecFiber_sum
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I x) :
    w =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (trivToE (I := I) α x w)) p •
          chartBasisVecFiber (I := I) α p x := by
  classical
  -- `w = trivFromE α x (trivToE α x w)`, then expand `trivToE α x w` in the model basis.
  have hround : trivFromE (I := I) α x (trivToE (I := I) α x w) = w :=
    trivFromE_trivToE (I := I) α hx w
  conv_lhs => rw [← hround]
  -- Expand `trivToE α x w` in the model basis, then push `trivFromE` through.
  set u : E := trivToE (I := I) α x w with hu_def
  have hexp : u =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr u) p • (chartModelBasis E) p := by
    exact ((chartModelBasis E).sum_equivFun u).symm
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.map_smul]
  -- `trivFromE α x ((chartModelBasis E) p) = chartBasisVecFiber α p x`.
  rfl

/-- Apply `trivFromE α x` to a vector in `E` and expand the result as a sum of
`chartBasisVecFiber α p x` against the model-basis coordinates of the vector. -/
private lemma trivFromE_eq_chartBasisVecFiber_sum
    (α : M) (x : M) (y : E) :
    trivFromE (I := I) α x y =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr y) p •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hexp : y =
      ∑ p : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr y) p • (chartModelBasis E) p := by
    exact ((chartModelBasis E).sum_equivFun y).symm
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.map_smul]
  rfl

/-- **Sum-form of `connDiff g g'` on a chart-basis fibre pair.** On the chart-`α`
good set, the connection-difference value
$\mathrm{connDiff}\,g\,g'\,x\,(e_j(x), e_k(x))$ admits the chart-coordinate
expansion
$\sum_{p} (\Gamma^p{}_{kj}(g) - \Gamma^p{}_{kj}(g'))(\varphi_\alpha x)
\cdot e_p(x)$. -/
lemma connDiff_chartBasis_pair_eq_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
          chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  rw [connDiff_chartBasis_pair_eq (I := I) g g' α hx j k]
  -- Expand each `trivFromE α x (christoffelCorrection ...)` term as a sum of
  -- `chartBasisVecFiber α p x` against the `p`-th model-basis coordinate of
  -- `christoffelCorrection ...`, then subtract.
  set Cg : E := christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
    (chartBasisVecFiber (I := I) α k x) with hCg_def
  set Cg' : E := christoffelCorrection (I := I) g' α x ((chartModelBasis E) j)
    (chartBasisVecFiber (I := I) α k x) with hCg'_def
  -- Apply the sum-expansion of `trivFromE`.
  rw [trivFromE_eq_chartBasisVecFiber_sum (I := I) α x Cg]
  rw [trivFromE_eq_chartBasisVecFiber_sum (I := I) α x Cg']
  -- Combine the two sums into one with subtraction of coefficients.
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← sub_smul]
  congr 1
  -- Identify the `p`-th model-basis coordinates of `Cg` and `Cg'` with the
  -- chart Christoffel symbols using `coord_christoffelCorrection_chartBasis_pair`.
  -- `(chartModelBasis E).repr Cg p = (chartModelBasis E).coord p Cg`.
  have hcoord_g : ((chartModelBasis E).repr Cg) p =
      ((chartModelBasis E).coord p) Cg := rfl
  have hcoord_g' : ((chartModelBasis E).repr Cg') p =
      ((chartModelBasis E).coord p) Cg' := rfl
  rw [hcoord_g, hcoord_g']
  rw [hCg_def, hCg'_def]
  rw [coord_christoffelCorrection_chartBasis_pair (I := I) g α hx j k p]
  rw [coord_christoffelCorrection_chartBasis_pair (I := I) g' α hx j k p]

/-! ## The chart-bridge: chart-`α` form

Plugging the sum form of `connDiff g g' x (e_j(x), e_k(x))` into the chart-α
metric trace `deTurckChartLocal g g' α x`, swapping the order of summation, and
applying `chartChristoffel_symm` to relabel `(k, j)` as `(j, k)`, we identify the
result with `∑_p chartDeTurckVFComp g g' α p (extChartAt α x) • e_p(x)`. -/

/-- **Chart-`α` bridge for the DeTurck-VF chart-local representative.** On the
chart-`α` Levi-Civita good set, the chart-`α` representative of the DeTurck
vector field is the chart-`α` sum of `chartDeTurckVFComp` components against the
chart-`α` coordinate frame vectors:
$\mathrm{deTurckChartLocal}\,g\,g'\,\alpha\,x =
\sum_{p} \mathrm{chartDeTurckVFComp}\,g\,g'\,\alpha\,p\,(\varphi_\alpha x) \cdot
e_p(x)$. -/
theorem deTurckChartLocal_eq_chartDeTurckVFComp_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    deTurckChartLocal (I := I) g g' α x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' α p (extChartAt I α x) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  -- Unfold `deTurckChartLocal` and expand each inner `connDiff` term using the
  -- sum form proved above.
  rw [deTurckChartLocal_def]
  -- The expanded double sum becomes
  -- ∑_j ∑_k chartInvGramMatrix g α x j k •
  --   ∑_p (Γ^p_{kj}(g) - Γ^p_{kj}(g'))(φ x) • chartBasisVecFiber α p x.
  have hreplace :
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x) =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          ∑ p : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
              chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [connDiff_chartBasis_pair_eq_sum (I := I) g g' α hx j k]
  rw [hreplace]
  -- Push the scalar `chartInvGramMatrix g α x j k` inside the `p`-sum.
  have hpush :
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          ∑ p : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x)) •
              chartBasisVecFiber (I := I) α p x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g α x j k *
            (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
              chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
            chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
  rw [hpush]
  -- Reorder the sums: pull `p` to the outermost position via two `Finset.sum_comm`.
  -- Strategy: first move `p` past `k` (inner), then past `j` (outer).
  -- Apply `Finset.sum_comm` to swap inner `k` and `p`.
  have hcomm1 :
      ∀ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x =
        ∑ p : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x := by
    intro j
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl (fun j _ => hcomm1 j)]
  -- Now swap outer `j` and `p`.
  rw [Finset.sum_comm]
  -- The outer sum is now over `p`; each term involves a sum over `(j, k)`.
  refine Finset.sum_congr rfl ?_
  intro p _
  -- Pull `e_p` out of the inner `k` sum first, then out of the outer `j` sum.
  have hinner_pull :
      ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (chartInvGramMatrix (I := I) g α x j k *
              (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
              chartBasisVecFiber (I := I) α p x =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ k : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α x j k *
                (chartChristoffel (I := I) g α k j p (extChartAt I α x) -
                  chartChristoffel (I := I) g' α k j p (extChartAt I α x))) •
            chartBasisVecFiber (I := I) α p x := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_smul]
  rw [hinner_pull]
  -- Now pull out the outer `j` sum.
  rw [← Finset.sum_smul]
  -- Goal: `(∑ j ∑ k coef j k) • e_p = chartDeTurckVFComp g g' α p (extChartAt α x) • e_p`.
  congr 1
  -- Now match `∑ j ∑ k coef j k` to `chartDeTurckVFComp`.
  rw [DeTurckLinearization.chartDeTurckVFComp_def]
  -- chartDeTurckVFComp = ∑ a ∑ b chartInvGramOnE g α a b y * (Γ^p_{ab}(g)(y) - Γ^p_{ab}(g')(y)).
  -- Currently LHS has Γ^p_{k j}; symmetry swaps to Γ^p_{j k}; then relabel a:=j, b:=k.
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  -- `chartInvGramMatrix g α x a b = chartInvGramOnE g α a b (extChartAt α x)`.
  have hinv_eq : chartInvGramMatrix (I := I) g α x a b =
      chartInvGramOnE (I := I) g α a b (extChartAt I α x) := by
    rw [chartInvGramOnE_def]
    have hsrc : x ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
    have hinv : (extChartAt I α).symm ((extChartAt I α) x) = x :=
      (extChartAt I α).left_inv hsrc
    rw [hinv]
  rw [hinv_eq]
  congr 1
  -- We need: `Γ^p_{ba}(g) - Γ^p_{ba}(g') = Γ^p_{ab}(g) - Γ^p_{ab}(g')`.
  -- Apply `chartChristoffel_symm` to swap (b, a) to (a, b).
  rw [chartChristoffel_symm (I := I) g α b a p (extChartAt I α x)]
  rw [chartChristoffel_symm (I := I) g' α b a p (extChartAt I α x)]

/-! ## The chart-bridge: bundled form -/

/-- **Headline bridge: the bundled DeTurck vector field equals the
chart-coordinate sum.**  At every point `x : M` and every base point `α` whose
chart-Levi-Civita good set contains `x`, the bundled DeTurck vector field
`(deTurckVF g g') x` equals the chart-`α` coordinate sum
$\sum_{p} \mathrm{chartDeTurckVFComp}\,g\,g'\,\alpha\,p\,(\varphi_\alpha x) \cdot
\mathrm{chartBasisVecFiber}\,\alpha\,p\,x$. -/
theorem deTurckVF_apply_eq_chartDeTurckVFComp_sum
    (g g' : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (deTurckVF (I := I) g g' :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' α p (extChartAt I α x) •
          chartBasisVecFiber (I := I) α p x := by
  -- Reduce `(deTurckVF g g') x` to `deTurckFun g g' x` to `deTurckChartLocal g g' α x`
  -- via chart-independence, then apply the chart-`α` bridge.
  rw [deTurckVF_apply (I := I) g g' x]
  have hxα_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [← deTurckChartLocal_eq_deTurckFun (I := I) g g' α hxα_base]
  -- Apply the chart-α bridge.
  exact deTurckChartLocal_eq_chartDeTurckVFComp_sum (I := I) g g' α hx

/-- **Specialisation to the chart at `α := x`.**  Using
`self_mem_chartLeviCivitaGoodSet`, every point `x : M` lies in its own
chart-Levi-Civita good set, so the bridge applies with `α := x`:
$(\mathrm{deTurckVF}\,g\,g')\,x =
\sum_{p} \mathrm{chartDeTurckVFComp}\,g\,g'\,x\,p\,(\varphi_x x) \cdot
(\mathrm{chartModelBasis}\,E)_p$, using
$\mathrm{chartBasisVecFiber}\,x\,p\,x = (\mathrm{chartModelBasis}\,E)_p$. -/
theorem deTurckVF_apply_eq_chartDeTurckVFComp_sum_self
    (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ p : Fin (Module.finrank ℝ E),
        DeTurckLinearization.chartDeTurckVFComp (I := I) g g' x p (extChartAt I x x) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g' x
    (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  exact chartBasisVecFiber_self (I := I) x p

end DeTurck
end PDE
end DifferentialGeometry
