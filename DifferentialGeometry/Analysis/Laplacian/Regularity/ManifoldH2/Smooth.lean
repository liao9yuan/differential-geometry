import DifferentialGeometry.Analysis.Laplacian.Operator.ChartLocalLaplacian
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity

/-!
# Per-chart interior `H²` regularity for chart-pulled smooth weak solutions

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M` and a chart point `α : M`, the previous layer (`ChartLocalLaplacian`)
packages the chart-pulled-back smooth function `chartPullback I α u : EuclN → ℝ`
as a smooth weak solution of a `SmoothEllipticBilinearForm` on
`Set.univ : Set EuclN` (provided the chart-pulled bilinear identity is supplied).

This file glues that packaging to the Euclidean interior `H²` regularity
theorem `h2_loc_smooth_solution` from `NirenbergH2Regularity.lean`. The
end product is a per-chart statement that, on any precompact open subdomain
`Ω''` of the chart-target image, the chart-pulled smooth function admits weak
`(i, k)`-second partials in `L²(Ω'')`, with a quantitative bound in terms of
the `H¹` data on a slightly enlarged neighborhood.

The result is stated in **hypothesis-bearing form**: the caller provides
the `IsSmoothWeakSolution` witness for `(B, chartPullback I α u, F̃)`, plus the
`L²`-locality of the right-hand side `F̃`. These hypotheses are exactly the
output of `chart_pulled_smooth_weak_solution_of_chartIdentity` (from H3) and a
local boundedness check for `F̃` on compact subsets, both of which are
discharged downstream by the manifold-side Voss-Weyl + chart-pulled volume
identity.

## Setting

Closed (compact, boundaryless) smooth Riemannian manifold setting:
`[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`, `[CompactSpace M]`.
The model fibre `E` is a finite-dimensional real inner-product space with
positive dimension (`[NeZero (Module.finrank ℝ E)]`).

## Main results

* `h2_loc_chart_pulled` — the per-chart interior `H²` regularity statement for
  any smooth weak solution `(B, w, F̃)` and any precompact open subdomain
  `Ω''` of the chart-target image. Provides existence, for every pair
  `(i, k) : Fin n × Fin n`, of a weak `k`-partial `g_{i,k}` of the classical
  `i`-partial `∂_i w` on `Ω''`, with `g_{i,k} ∈ L²(Ω'')` and a quantitative
  bound on `∫_{Ω''} g_{i,k}²` in terms of the `H¹` seminorm and `L²` norms on
  a slightly enlarged compact-closure neighborhood.

* `h2_loc_chart_pulled_manifold` — the manifold-level wrapper that takes the
  manifold-side smooth function `u : M → ℝ` (with chart-source-supported
  closed support), the bilinear form `B`, the `IsSmoothWeakSolution` witness,
  and a precompact open subdomain. The conclusion is the Euclidean
  `h2_loc_chart_pulled` statement applied to `chartPullback I α u`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

/-! ## File-local Borel-space instances on `E` and `M`

Match the convention in surrounding files: install Borel σ-algebras locally
without leaking global instances. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Per-chart Euclidean interior `H²` regularity

The headline per-chart statement: for any smooth weak solution `(B, w, F̃)` of a
`SmoothEllipticBilinearForm` on `Set.univ ⊆ EuclN`, where `F̃` has the standard
locally-`L²` property, the function `w` admits weak second partials in `L²` on
any precompact open `Ω'' ⊆ EuclN`.

In our application, `B` is the bilinear form constructed from `g` by H1
(`exists_smooth_metric_extension`), `w = chartPullback I α u` is the
chart-pulled-back manifold function, and `F̃ = negDensityLaplacianPullback`
is the chart-pulled density-weighted negative Laplacian. The
`IsSmoothWeakSolution` witness is provided by H3
(`chart_pulled_smooth_weak_solution_of_chartIdentity`), once the chart-pulled
bilinear identity is supplied. The `L²`-locality of `F̃` follows from
continuity on the chart-target image plus the boundary indicator (extension
by `0`).

The Euclidean theorem `h2_loc_smooth_solution` does the heavy lifting:
* uniform-in-`h` Nirenberg estimate on the difference quotients,
* Fatou's lemma to pass to the classical limit `∂_k ∂_i w`,
* extraction of a precompact open `Ω' ⊇ closure Ω''` with the resulting
  bound on `∫_{Ω''} g²`.
-/

/-- **Per-chart interior `H²` regularity (Euclidean form).**

For a smooth elliptic bilinear form `B` on `Set.univ : Set EuclN`, a function
`w : EuclN → ℝ` that is a smooth weak solution of `B u = F̃` (in the sense
of `B.IsSmoothWeakSolution`), with `F̃` locally in `L²` on every
compact-closure open set, and a precompact open subdomain `Ω'' ⊆ EuclN`,
the function `w` admits, for every pair `(i, k) : Fin n × Fin n`, a weak
`k`-partial `g` of the classical `i`-partial `∂_i w` on `Ω''`. The function
`g` is in `L²(Ω'')`, and there is a slightly enlarged precompact open
neighborhood `Ω'` and a constant `C ≥ 0` such that
`∫_{Ω''} g² ≤ C · (∫_{Ω'} ∑_j (∂_j w)² + ∫_{Ω'} w² + ∫_{Ω'} F̃²)`.

This is the manifold-side packaging of `h2_loc_smooth_solution`: the only
input that is mathematically nontrivial is the smooth-weak-solution witness
`h_weak`, which in turn comes from H3. -/
theorem h2_loc_chart_pulled
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {w F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution w F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g : EuclN → ℝ,
      MemLp g 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g
        (fun y : EuclN => (fderiv ℝ w y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ w x) (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (w x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  -- Apply `h2_loc_smooth_solution` with `Ω := Set.univ`.
  -- The hypothesis `closure Ω'' ⊆ Set.univ` is trivial.
  -- The hypothesis `Metric.cthickening 2 (closure Ω'') ⊆ Set.univ` is trivial.
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  -- The engine produces a constant independent of the solution data;
  -- specialise it to `(w, F)` and the direction pair.
  obtain ⟨C, hC_nn, h_eng⟩ := h2_loc_smooth_solution
    (d := Module.finrank ℝ E)
    B hΩ'' hΩ''_compact_closure h_closure_in h_room
  intro i k
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hF_l2_loc i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

/-! ## `L²`-locality of the chart-pulled negative density-weighted Laplacian

We package the standard fact that a continuous function with compact support
on a metric space lies in `L²` on every compact-closure open set. This
underlies the `hF_l2_loc` hypothesis of `h2_loc_chart_pulled` in the
chart-pulled application: the function
`negDensityLaplacianPullback g hf α : EuclN → ℝ` is continuous on
`chartTargetEuclid α` and zero outside (by the indicator extension), and on
the chart-target image it equals the smooth product
`-densityOnEuclid g α · (Δ_g g hf) ∘ extChartAt^{-1} ∘ toEuclidean^{-1}`. To
keep this file independent of further chart-pulled smoothness lemmas, we
state the locality property as a hypothesis on the right-hand side; in
applications it is discharged by continuity + compact support arguments. -/

omit [NeZero (Module.finrank ℝ E)] in
/-- A continuous function with compact support on `EuclN` is in `L²` on
every measurable subset (in particular, on any precompact open subset). -/
theorem memLp_two_continuous_compactSupport_restrict
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
  -- A continuous compactly-supported function is in `L^p` for all `p` w.r.t.
  -- the ambient `volume`. Restriction to any subset preserves this.
  have h_global : MemLp f 2 (volume : Measure EuclN) :=
    hf_cont.memLp_of_hasCompactSupport (μ := volume) (p := 2) hf_cs
  exact h_global.restrict _

/-! ## Manifold-level wrapper

The user-facing per-chart H² regularity for a chart-pulled-back smooth
function on a closed Riemannian manifold. Inputs:

* a chart point `α : M`,
* a smooth `u : M → ℝ` with `tsupport u ⊆ (chartAt H α).source`,
* a smooth elliptic bilinear form `B` on `Set.univ : Set EuclN`,
* a smooth weak solution witness `B.IsSmoothWeakSolution (chartPullback I α u) F̃`,
* an `L²`-locality witness for `F̃` on compact-closure subsets,
* a precompact open subdomain `Ω''` of the chart-target image.

Output: existence, for every `(i, k) : Fin n × Fin n`, of a weak `k`-partial
of the classical `i`-partial `∂_i (chartPullback I α u)` on `Ω''`, in `L²(Ω'')`,
with the standard `H¹`-data quantitative bound on a slightly enlarged
neighborhood `Ω' ⊆ EuclN`. -/

/-- **Per-chart interior `H²` regularity for chart-pulled-back smooth
manifold functions.**

In the closed (compact, boundaryless) Riemannian manifold setting, the
chart-pulled-back smooth function `chartPullback I α u : EuclN → ℝ` (with
manifold-side smooth `u` and `tsupport u ⊆ chart source`) is `C^∞` on `EuclN`
by `chartPullback_contDiff` (from H3). Coupled with the smooth-weak-solution
hypothesis `B.IsSmoothWeakSolution (chartPullback I α u) F̃` produced by
`chart_pulled_smooth_weak_solution_of_chartIdentity` (from H3), and the
`L²`-locality of `F̃`, the standard Euclidean interior `H²` regularity
theorem `h2_loc_smooth_solution` gives the conclusion. -/
theorem h2_loc_chart_pulled_manifold
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_cs : HasCompactSupport u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution
      (chartPullback (I := I) α u) F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN => (fderiv ℝ (chartPullback (I := I) α u) y)
          (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ (chartPullback (I := I) α u) x)
                      (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (chartPullback (I := I) α u x)^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  -- Suppress unused-hypothesis warnings on the manifold-side smoothness data;
  -- they are recorded as part of the theorem statement to make the manifold-level
  -- hypothesis discipline explicit, but the per-chart Euclidean conclusion is
  -- proved by direct invocation of the Euclidean form.
  let _ := g
  let _ := hu_smooth
  let _ := hu_cs
  let _ := hu_supp
  exact h2_loc_chart_pulled (E := E)
    B h_weak hF_l2_loc hΩ'' hΩ''_compact_closure

end ManifoldH2
end Laplacian
end Analysis
end DifferentialGeometry
