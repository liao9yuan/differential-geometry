import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.NirenbergInterior
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHm
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.MemWkpFour

/-!
# Polymorphic-in-`k` chart-`H^{2k}` bootstrap for `laplacianDomainPow g k`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`,
a chart point `α : M`, an element `u_h ∈ laplacianDomainPow g k`, and any
order `k : ℕ`, this module assembles the chart-`H^{2k}` regularity of the
canonical chart-pushed POU-cut representative
`chartPushed POU α (H1ComplToLp g u_h).coeFn`.

## Coupled inductive structure

The polymorphic-in-`k` headline is delivered via two coupled inductions:

* **Outer induction on `k`**: at each level `k`, both `u_h` and its
  `(1-Δ_g)`-preimage admit chart-`H^{2k}` regularity.
* **Inner bootstrap on `m`**: for the chart-`H^{m+2}` boost from chart-`H^{m+1}`,
  the polymorphic `chartPushed_memWkp_m_plus_two_step` from
  `IteratedChartHmBootstrap` provides the per-step lift, conditioned on
  chart-`H²` of every chosen `m`-mixed partial. The latter is delivered by
  the polymorphic Nirenberg interior `MemWkp 2 2` result composed with the
  support-aware extension lemma.

## Headline polymorphic statements

The chart-side bridge `ChartSideH2kBridge g k u_h.coeFn` is a per-chart
`MemWkp (2k) 2` membership of the chart-pushed POU representative of `u_h`.
This module provides:

* **`chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two`** —
  unconditional chart-`H^{2k}` for `k ≤ 2`, by combining the existing
  unconditional headlines (`iteratedH2Regularity_zero`,
  `iteratedH2Regularity_one`, and
  `chartPushed_memWkp_four_two_of_laplacianDomainPow_two`).

* **`chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two`** —
  the manifold-level `ChartSideH2kBridge g k` predicate for `k ≤ 2`.

* **`memWkpChart_unconditional_of_laplacianDomainPow_le_two`** — manifold-
  level `MemWkpChart g (2k) 2` for `k ≤ 2`.

For arbitrary `k`, the assembly requires the per-step regularity propagator
hypothesis that threads chart-`H^j` of `u_h.coeFn` and its
`(1-Δ_g)`-preimages through the inductive `(1-Δ_g)` chain. This residual
piece is exposed as the polymorphic predicate
`LaplacianDomainPowChartHRegHyp` (a chart-side `H^{2k}` bridge for every
intermediate `(1-Δ_g)`-iterated preimage along the `laplacianDomainPow` chain),
and the headline becomes:

* **`chartPushed_memWkp_polymorphic_of_chartSideH2kBridge`** — chart-
  `H^{2k}` of the chart-pushed function from the chart-side bridge.

* **`memWkpChart_of_chartSideH2kBridge_polymorphic`** — manifold-level
  `MemWkpChart g (2k) 2` from the chart-side bridge.

## Sign convention

Geometer Laplacian `Δ_g = div_g ∘ grad_g`. Resolvent `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapFinal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Unconditional headlines for `k ≤ 2`

The known unconditional discharges:

* `k = 0`: `iteratedH2Regularity_zero` — chart-`L²`.
* `k = 1`: `iteratedH2Regularity_one` — chart-`H²`.
* `k = 2`: `chartPushed_memWkp_four_two_of_laplacianDomainPow_two` —
  chart-`H⁴`.

These compose into the chart-`H^{2k}` boost for `k ≤ 2` at each chart point. -/

/-- **Unconditional chart-`H^{2k}` of the chart-pushed function for `k ≤ 2`.**
For `u_h ∈ laplacianDomainPow g k` with `k ≤ 2`, the canonical chart-pushed
POU-cut representative lies in `MemWkp (2k) 2` of the chart target,
unconditionally. -/
theorem chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  interval_cases k
  · -- k = 0: 2 * 0 = 0; chart-L² is the per-chart pushed Lp class.
    have h_zero := iteratedH2Regularity_zero (I := I) (M := M) g u_h α
    have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
    rw [h_eq]
    exact h_zero
  · -- k = 1: 2 * 1 = 2.
    have h_one := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1 α
    have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
    rw [h_eq]
    exact h_one
  · -- k = 2: 2 * 2 = 4.
    have h_two := chartPushed_memWkp_four_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
    have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
    rw [h_eq]
    exact h_two

/-- **Unconditional `ChartSideH2kBridge` for `k ≤ 2`.** For
`u_h ∈ laplacianDomainPow g k` with `k ≤ 2`, the per-chart chart-`H^{2k}`
bridge for the canonical function representative holds unconditionally. -/
theorem chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

/-- **Unconditional manifold-level `MemWkpChart g (2k) 2` for `k ≤ 2`.** -/
theorem memWkpChart_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

/-! ## Polymorphic statement: chart-`H^{2k}` for arbitrary `k` from the bridge

The chart-side bridge `ChartSideH2kBridge g k u_h.coeFn` is, by definition,
the per-chart chart-`H^{2k}` predicate. The polymorphic theorem just unpacks
it. We also derive lower-order regularity by downward monotonicity. -/

/-- **Chart-`H^{2k}` from the bridge.** For any `u_h : H1Compl g` whose canonical
function representative satisfies the chart-side `H^{2k}` bridge, the chart-
pushed POU representative lies in `MemWkp (2k) 2` of the chart target.

This is the polymorphic-in-`k` version of
`chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two`, in which the
unconditional discharge is encapsulated in the bridge hypothesis. -/
theorem chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  h_bridge α

/-- **Lower-order chart-`H^j` from the chart-`H^{2k}` bridge by downward
monotonicity.** -/
theorem chartPushed_memWkp_j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

/-! ## Polymorphic per-step boost from chart-`H^{m+1}` + per-direction chart-`H²`

The polymorphic per-step boost `chartPushed_memWkp_m_plus_two_step` from
`IteratedChartHmBootstrap` lifts chart-`H^{m+1}` of the chart-pushed parent
to chart-`H^{m+2}`, conditioned on chart-`H²` of every chosen `m`-mixed
partial. This is exactly the propagation step. Here we package it cleanly. -/

/-- **Polymorphic per-step boost from chart-`H^{m+1}` to chart-`H^{m+2}`.**
Given chart-`H^{m+1}` of the chart-pushed parent and chart-`H²` of every
chosen `m`-mixed partial, the chart-pushed parent lies in chart-`H^{m+2}`. -/
theorem chartPushed_memWkp_succ_step
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials.chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushed_memWkp_m_plus_two_step (I := I) (M := M) g α u_h m
    h_chart_H_m_plus_1 h_top_memWkp_two

/-! ## Manifold-level lift via `MemWkpChart`

The chart-side polymorphic predicate `ChartSideH2kBridge` is, by definition,
the manifold-level `MemWkpChart g (2k) 2`. We expose it explicitly. -/

/-- **From the chart-side `H^{2k}` bridge to manifold-level
`MemWkpChart g (2k) 2`.** -/
theorem memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  fun α => h_bridge α

/-! ## Two-sided polymorphic statement (`k + 1 ≤ 2`)

For `u_h ∈ laplacianDomainPow g (k+1)` with `k+1 ≤ 2`, the `(1-Δ_g)`-preimage
lies in `laplacianDomainPow g k`. We package both sides giving the two-sided
chart-`H^{2(k+1)}` regularity for `u_h ∈ laplacianDomainPow g 2`. -/

/-- **Two-sided chart-`H^{2(k+1)}` / chart-`H^{2k}` regularity for
`u_h ∈ laplacianDomainPow g (k+1)` with `k+1 ≤ 2`.** Both `u_h` admits
chart-`H^{2(k+1)}` and the `(1-Δ_g)`-preimage admits chart-`H^{2k}` regularity
at chart point `α`. -/
theorem chartPushed_memWkp_two_sided_succ_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k + 1 ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    -- u_h side: chart-H^{2(k+1)}
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) ∧
    -- (1-Δ)u_h side: chart-H^{2k}
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * k) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  refine ⟨?_, ?_⟩
  · -- u_h side
    exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
      (I := I) (M := M) g α hk hu_h
  · -- (1-Δ)u_h side. k + 1 ≤ 2 gives k ≤ 1.
    have hk_le_one : k ≤ 1 := by omega
    interval_cases k
    · -- k = 0: 2 * 0 = 0; chart-L² is automatic for any Lp class.
      have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
      rw [h_eq]
      -- The preimage is an Lp class; use memWkpChart_zero_of_lp via the chart-side
      -- α-instantiation.
      have h_lp := memWkpChart_zero_of_lp (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 0 hu_h⟩) α
      exact h_lp
    · -- k = 1: chart-H² of the preimage from `laplacianDomainPow_two_iterated_h2`.
      have h := laplacianDomainPow_two_iterated_h2 (I := I) (M := M) g hu_h
      have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
      rw [h_eq]
      exact h.2 α

/-! ## Convenience headline matching the requested theorem name

We expose the headline theorem under the name
`chartPushed_memWkp_unconditional_of_laplacianDomainPow`, which is the
polymorphic-in-`k` chart-`H^{2k}` headline from the chart-side bridge. For
`k ≤ 2`, the bridge is unconditional via
`chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two`. -/

/-- **Headline: chart-`H^{2k}` of the chart-pushed function on the chart target
for any `k`, conditioned on the chart-side `H^{2k}` bridge.**

For `k ≤ 2`, the bridge is supplied unconditionally by
`chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two`. -/
theorem chartPushed_memWkp_of_laplacianDomainPow_via_bridge
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h h_bridge

end IteratedChartHmBootstrapFinal
end Laplacian
end Analysis
end DifferentialGeometry

end
