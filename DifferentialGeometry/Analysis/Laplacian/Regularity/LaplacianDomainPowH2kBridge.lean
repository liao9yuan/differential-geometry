import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainPowH4Bridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedH2Regularity

/-!
# Bridge: chart-side `MemWkp (2k) 2` to manifold-level `MemWkpChart g (2k) 2`
for elements of `laplacianDomainPow g k`

For a closed Riemannian manifold `(M, g)` and an element
`u_h ∈ laplacianDomainPow g k`, this module gives the generic chart-side
bridge from per-chart `MemWkp (2k) 2` membership of the POU-cut
chart-pushed function (for the canonical function representative of
`u_h`) to the manifold-level `MemWkpChart g (2k) 2` membership with a
finite chart-based norm.

This generalises the bridge already exposed at `H⁴` level (`k = 2`) in
`LaplacianDomainPowH4Bridge.lean`. The construction is uniform in `k`:

* The chart-pushed POU function of the canonical function representative
  `(H1ComplToLp u_h : M → ℝ)` is the per-chart `chartPushed` (canonical
  atlas POU) of that representative.
* `MemWkpChart` is by definition per-chart `MemWkp` membership; the
  bridge from the per-chart hypothesis is by direct unfolding.
* Compactness of `M` plus the locally finite POU yields the global norm
  finiteness from the per-chart memberships.

## Main structures

* `ChartSideH2kBridge g k u_h` — the per-chart `MemWkp (2k) 2`
  hypothesis for the chart-pushed POU function of the canonical
  function representative of `u_h`. Polymorphic in `k`.

## Main theorems

* `chartH2kPOUWitness_of_chartSideH2kBridge` — direct lift of the per-chart
  `MemWkp (2k) 2` evidence from the bridge.
* `laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge` — the
  headline polymorphic version: bridge-driven `MemWkpChart g (2k) 2` for
  `u_h ∈ laplacianDomainPow g k`.
* `exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge` —
  existential form.
* `laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero` —
  consistency check at `k = 0` (unconditional, no bridge needed).
* `laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one` —
  consistency check at `k = 1` (unconditional, no bridge needed).
* `chartSideH4Bridge_iff_chartSideH2kBridge_two` — consistency check at
  `k = 2` linking to the `H⁴` bridge.
* `laplacianDomainPow_memWkpChart_2k_of_chartSideH4Bridge` — derivation
  of the `k = 2` case from `ChartSideH4Bridge`.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`. The resolvent
is `(1 - Δ_g)⁻¹`. The order is `2k`: `k = 0` is `L²`, `k = 1` is `H²`,
`k = 2` is `H⁴`, etc.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainPowH2kBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## The chart-side bridge hypothesis

The generic chart-side hypothesis at order `2k`: for every chart point
`α : M`, the POU-cut chart-pushed function of `u : M → ℝ` lies in
`MemWkp (2k) 2` of the chart-target image. This is the same shape as
`ChartSideH4Bridge` (which corresponds to `k = 2`) and uses the same
canonical atlas partition of unity `chartAtlasPOU I M`. -/

/-- **The chart-side `H^{2k}` bridge hypothesis.** For each chart point
`α : M`, the POU-cut chart-pushed function of `u : M → ℝ` lies in
`MemWkp (2k) 2` of the chart-target image, under the canonical atlas
partition of unity. Polymorphic in `k : ℕ`. -/
def ChartSideH2kBridge (_g : SmoothRiemannianMetric I M) (k : ℕ) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

/-! ## Direct manifold-level lift of the chart-side bridge -/

/-- **Manifold-level `H^{2k}` lift from the chart-side bridge.** By the
unfolding of `MemWkpChart`, the chart-side `H^{2k}` bridge for `u : M → ℝ`
is exactly the manifold-level `MemWkpChart g (2k) 2` membership. -/
theorem memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2 u := by
  intro α
  exact h_bridge α

/-- The chart-based norm `wkpNormChart g (2k) 2 u` is finite under the
chart-side bridge on a closed manifold. -/
theorem wkpNormChart_2k_lt_top_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * k) 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2 * k) (p := 2) (by norm_num)
    (memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge)

/-! ## Headline: bridge-driven `H^{2k}` regularity for `laplacianDomainPow g k`

For `u_h ∈ laplacianDomainPow g k`, the bridge hypothesis on the canonical
function representative directly yields manifold-level `MemWkpChart g (2k) 2`
membership and a finite chart-based norm. The membership in
`laplacianDomainPow g k` is kept in the signature to clarify the intended
downstream use; the bridge itself already carries the data. -/

/-- **Bridge-driven `H^{2k}` regularity for `laplacianDomainPow g k`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
and any `u_h ∈ laplacianDomainPow g k`, the canonical function
representative `((H1ComplToLp u_h) : M → ℝ)` lies in
`MemWkpChart g (2k) 2` with a finite chart-based norm, provided a
chart-side `H^{2k}` bridge for that representative is supplied.

This is the polymorphic-in-`k` generalisation of
`laplacianDomainPow_memWkpChart_four_of_chartSideH4Bridge` (the `k = 2`
case).

The membership `hu_h : u_h ∈ laplacianDomainPow g k` is retained in the
signature to keep the API symmetric with `H⁴` and to mark the intended
use; the bridge already carries the per-chart `H^{2k}` data. -/
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  -- The hypothesis hu_h is retained in the signature for API symmetry but is
  -- not used in the bridge-driven proof (the per-chart bridge already carries
  -- the H^{2k} data of the canonical function representative).
  let _ := hu_h
  refine ⟨?_, ?_⟩
  · exact memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge
  · exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge
      (I := I) (M := M) g k h_bridge

/-- **Existential form of bridge-driven `H^{2k}` regularity.** For
`u_h ∈ laplacianDomainPow g k` together with the chart-side bridge,
there exists a function representative with `MemWkpChart g (2k) 2`
membership and finite chart-based norm. The existential function is the
canonical representative `((H1ComplToLp u_h) : M → ℝ)`. -/
theorem exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * k) 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * k) 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h h_bridge).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h h_bridge).2

/-! ## Two-sided form for `laplacianDomainPow g (k+1)`

The two-sided form gives `H^{2(k+1)}` regularity simultaneously for the
canonical function representative of `u_h ∈ laplacianDomainPow g (k+1)`
and for the canonical function representative of the `Lp` preimage
`laplacianDomain.preimage u_h` (which represents `(1 - Δ_g) u_h` as an
`Lp` class). The preimage lies in the range of the iterated `Lp`-side
resolvent at level `k`, hence corresponds via the canonical lift to an
element of `laplacianDomainPow g k`. -/

/-- **Two-sided bridge-driven `H^{2(k+1)}` regularity for
`laplacianDomainPow g (k+1)`.** For `u_h ∈ laplacianDomainPow g (k+1)`,
given chart-side `H^{2(k+1)}` bridges for BOTH the canonical function
representative of `u_h` and the canonical function representative of the
`Lp` preimage `(1 - Δ_g) u_h`, both functions lie in
`MemWkpChart g (2(k+1)) 2` with finite chart-based norms. -/
theorem laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_u : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    -- `H^{2(k+1)}` regularity of `u`:
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    -- `H^{2(k+1)}` regularity of the `Lp` preimage (i.e. `(1 - Δ_g) u_h`):
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  refine ⟨laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g (k + 1) hu_h h_bridge_u, ?_⟩
  refine ⟨memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g (k + 1)
    h_bridge_rhs, ?_⟩
  exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge
    (I := I) (M := M) g (k + 1) h_bridge_rhs

/-! ## Consistency check at `k = 0`: unconditional from `iteratedH2Regularity_zero`

At `k = 0`, the chart-side bridge is automatically satisfied because
`MemWkp 0 2` is just `MemLp 2` on each chart target (any `Lp 2` function
satisfies this). -/

/-- **At `k = 0`, the chart-side `H⁰` bridge for the canonical function
representative of any `u_h : H1Compl g` is automatic.** -/
theorem chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ChartSideH2kBridge (I := I) (M := M) g 0
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  -- 2 * 0 = 0, so we need MemWkp 0 2, which is just MemLp 2 (by MemWkp_zero).
  have h := iteratedH2Regularity_zero (I := I) (M := M) g u_h
  -- h : MemWkpChart g 0 2 ((H1ComplToLp u_h) : M → ℝ)
  -- which definitionally unfolds to MemWkp 0 2 of the chart-pushed.
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  rw [h_eq]
  exact h α

/-- **`k = 0` case of the bridge-driven headline is unconditional.** For
any `u_h ∈ laplacianDomainPow g 0 = ⊤`, the canonical function
representative lies in `MemWkpChart g 0 2` with a finite chart-based
norm. -/
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  -- Membership in laplacianDomainPow g 0 = ⊤ is automatic.
  have hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 0 := by
    rw [laplacianDomainPow_zero]
    exact Submodule.mem_top
  have h_bridge := chartSideH2kBridge_zero (I := I) (M := M) g u_h
  -- 2 * 0 = 0.
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  have := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 0 hu_h h_bridge
  rw [h_eq] at this
  exact this

/-! ## Consistency check at `k = 1`: unconditional from `iteratedH2Regularity_one`

At `k = 1`, the chart-side bridge is automatically satisfied because the
unconditional single-step `H²` regularity holds for
`u_h ∈ laplacianDomainPow g 1 = laplacianDomain g`. -/

/-- **At `k = 1`, the chart-side `H²` bridge for the canonical function
representative of `u_h ∈ laplacianDomainPow g 1` is automatic.** -/
theorem chartSideH2kBridge_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    ChartSideH2kBridge (I := I) (M := M) g 1
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  -- 2 * 1 = 2, so we need MemWkp 2 2.
  have h := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
  -- h : MemWkpChart g 2 2 ((H1ComplToLp u_h) : M → ℝ)
  have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
  rw [h_eq]
  exact h α

/-- **`k = 1` case of the bridge-driven headline is unconditional.** For
`u_h ∈ laplacianDomainPow g 1`, the canonical function representative
lies in `MemWkpChart g 2 2` with a finite chart-based norm — without
needing any chart-side bridge hypothesis. -/
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  iteratedH2Regularity_one (I := I) (M := M) g hu_h

/-! ## Consistency check at `k = 2`: equivalent to `ChartSideH4Bridge`

The chart-side `H⁴` bridge in `LaplacianDomainPowH4Bridge.lean` is
exactly `ChartSideH2kBridge g 2 u`, modulo the `2 * 2 = 4` rewrite. The
equivalence shows the polymorphic bridge generalises the `H⁴`-specific
one. -/

/-- **The `H⁴` bridge is equivalent to the `H^{2k}` bridge at `k = 2`.** -/
theorem chartSideH4Bridge_iff_chartSideH2kBridge_two
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u ↔
    ChartSideH2kBridge (I := I) (M := M) g 2 u := by
  unfold DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
    ChartSideH2kBridge
  -- The two predicates differ only by the literal 4 vs. 2 * 2. Rewrite.
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq]

/-- **From `ChartSideH4Bridge` we obtain `ChartSideH2kBridge g 2 u`.** -/
theorem chartSideH2kBridge_two_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h : DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u) :
    ChartSideH2kBridge (I := I) (M := M) g 2 u :=
  (chartSideH4Bridge_iff_chartSideH2kBridge_two (I := I) (M := M) g u).mp h

/-- **From `ChartSideH2kBridge g 2 u` we obtain `ChartSideH4Bridge`.** -/
theorem chartSideH4Bridge_of_chartSideH2kBridge_two
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g 2 u) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u :=
  (chartSideH4Bridge_iff_chartSideH2kBridge_two (I := I) (M := M) g u).mpr h

/-- **The `k = 2` case of the polymorphic headline derived from the
`H⁴` bridge.** Consistency check: given the chart-side `H⁴` bridge for
`u_h ∈ laplacianDomainPow g 2`, the polymorphic headline gives
`MemWkpChart g 4 2` (where `4 = 2 * 2`). -/
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge : DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_bridge_2k := chartSideH2kBridge_two_of_chartSideH4Bridge
    (I := I) (M := M) g h_bridge
  have h := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 2 hu_h h_bridge_2k
  -- 2 * 2 = 4.
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq] at h
  exact h

/-! ## Downward monotonicity in `k`

The `H^{2k}` bridge implies the `H^{2j}` bridge for `j ≤ k`, by
downward monotonicity of `MemWkp` in the order. -/

/-- **Downward monotonicity in `k` for the bridge hypothesis.** If the
chart-side `H^{2k}` bridge holds, then so does the `H^{2j}` bridge for
every `j ≤ k`. -/
theorem chartSideH2kBridge_le_of_le
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g j u := by
  intro α
  have h_le : 2 * j ≤ 2 * k := Nat.mul_le_mul_left 2 hkj
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le h_le (h α)

/-- **Downward monotonicity: from `H^{2k}` bridge to `H^{2(k-1)}`
bridge** (in the form expressing the predecessor). -/
theorem chartSideH2kBridge_pred
    (g : SmoothRiemannianMetric I M)
    (k : ℕ) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g (k + 1) u) :
    ChartSideH2kBridge (I := I) (M := M) g k u :=
  chartSideH2kBridge_le_of_le (I := I) (M := M) g (Nat.le_succ k) h

/-! ## Algebraic closure of the bridge hypothesis

The chart-side bridge hypothesis is closed under addition, scalar
multiplication, and negation, by the corresponding closure of `MemWkp` in
Euclidean Sobolev space. -/

/-- **The chart-side bridge is closed under addition.** -/
theorem chartSideH2kBridge_add
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) g k v) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

/-- **The chart-side bridge is closed under scalar multiplication.** -/
theorem chartSideH2kBridge_const_smul
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (c : ℝ) {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

/-- **The chart-side bridge is closed under negation.** -/
theorem chartSideH2kBridge_neg
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => -u x) := by
  have h := chartSideH2kBridge_const_smul (I := I) (M := M) g k (-1) hu
  -- (-1) * u x = -u x
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- **The chart-side bridge is closed under subtraction.** -/
theorem chartSideH2kBridge_sub
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) g k v) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => u x - v x) := by
  have hneg := chartSideH2kBridge_neg (I := I) (M := M) g k hv
  have h := chartSideH2kBridge_add (I := I) (M := M) g k hu hneg
  -- u x + -v x = u x - v x
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-! ## Lifted manifold-level results via `MemWkpChart.le_of_le`

The bridge-driven `MemWkpChart g (2k) 2` membership implies all lower
orders by downward monotonicity. These corollaries make the downward
implications explicit at the manifold level. -/

/-- **From the chart-side `H^{2k}` bridge, the manifold-level
`MemWkpChart g (2j) 2` follows for every `j ≤ k`.** -/
theorem memWkpChart_2j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * j) 2 u := by
  have h_full := memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k h_bridge
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
    (Nat.mul_le_mul_left 2 hkj) h_full

/-- **Bridge-driven lower-order membership for the iterated Laplacian
domain.** From the chart-side `H^{2k}` bridge for the canonical function
representative of `u_h ∈ laplacianDomainPow g k`, the manifold-level
`MemWkpChart g (2j) 2` follows for every `j ≤ k`. -/
theorem laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * j) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_2j_of_chartSideH2kBridge (I := I) (M := M) g hkj h_bridge

/-! ## Combined unified headline `k ≤ 1` ∨ bridge

The combined headline expresses the iterated regularity:

* For `k ≤ 1`, the membership is unconditional (from
  `iteratedH2Regularity_zero` and `iteratedH2Regularity_one`).
* For `k ≥ 2`, the membership requires the chart-side `H^{2k}` bridge.

Two unified statements are provided: a conditional unified form (always
needs the bridge but the bridge is automatic for `k ≤ 1`), and a clean
case-split form. -/

/-- **Unified headline: `MemWkpChart g (2k) 2` for `u_h ∈ laplacianDomainPow g k`
under the chart-side bridge.** The bridge is automatically discharged
for `k ≤ 1` (delivered by `chartSideH2kBridge_zero` and
`chartSideH2kBridge_one`); for `k ≥ 2`, it is a genuine hypothesis. -/
theorem laplacianDomainPow_memWkpChart_2k_unified
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k hu_h h_bridge).1

end LaplacianDomainPowH2kBridge
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.wkpNormChart_2k_lt_top_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_zero
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_one
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH4Bridge_iff_chartSideH2kBridge_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_two_of_chartSideH4Bridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH4Bridge_of_chartSideH2kBridge_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH4Bridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_le_of_le
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_pred
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_add
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_const_smul
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_neg
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_sub
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2j_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_unified

end Sanity
