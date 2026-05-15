import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedMixedPartials
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedH2Regularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedLaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainPowH2kBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushedMemWkpFourUnconditional
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

/-!
# Polymorphic-in-`m` chart-`H^{m+2}` bootstrap for the canonical chart-pushed
representative

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h : H1Compl g`, the canonical chart-pushed POU-cut representative
`chartPushed POU α (H1ComplToLp g u_h).coeFn` decomposes into chart-Sobolev
regularity layers via the iterated chosen mixed weak partials. This module
provides the polymorphic chart-`H^{m+2}` assembly:

```
chart-H^{m+2} of u_h.coeFn  ⇐  chart-H^{m+1} of u_h.coeFn AND
                                ∀ (idx : Fin m → Fin n),
                                chart-H² of (m-mixed partial in idx)
```

The assembly itself is purely structural: it iterates the elementary
`MemWkp_succ` decomposition. Combined with the base case from
`iteratedH2Regularity_one` (which gives chart-`H²` for
`u_h ∈ laplacianDomainPow g 1`), it produces chart-`H^{m+2}` of the canonical
function representative provided the chart-`H²` regularity of every `m`-mixed
chosen partial is supplied.

This module also provides a polymorphic cutoff-based support-aware extension
of `MemWkp k 2` from a precompact open subdomain to the full chart target,
generalising the bespoke `m = 2` version in `ChartPushedMemWkpFourUnconditional`.

## Main results

* `MemWkp_extend_via_cutoff_poly` — the polymorphic support-aware extension
  of `MemWkp k 2` from a precompact open subdomain to the full chart target.

* `chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two` — the polymorphic
  chart-`H^{m+2}` assembly: chart-`H^{m+2}` of the chart-pushed function from
  chart-`H¹` of the chart-pushed function and chart-`H^{k+1}` of every
  chosen `k`-mixed partial for every `k ≤ m`.

* `chartPushed_memWkp_two_of_laplacianDomainPow_one` — base case chart-`H²`
  for `u_h ∈ laplacianDomainPow g 1`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Polymorphic support-aware extension of `MemWkp k 2`

The polymorphic cutoff-based extension lemma below promotes a `MemWkp k 2`
membership on a precompact open subdomain `Ω' ⊆ Ω` to the entire ambient
open set `Ω`, provided the function vanishes a.e. on `Ω \ K` for some
compact `K ⊆ Ω'`. The cutoff `η` is smooth, equals `1` on a neighborhood
of `K`, and has pointwise topological support inside `Ω'`. This generalises
the bespoke `MemWkp_two_extend_via_cutoff_aux` used in the chart-`H⁴`
assembly to arbitrary order `k`. -/

/-- **Polymorphic cutoff-based extension of `MemWkp k 2` from a precompact
open subdomain.** A function in `MemWkp k 2` of an open precompact `Ω' ⊆ Ω`
that vanishes a.e. on `Ω \ K` (for some compact `K ⊆ Ω'`) lies in
`MemWkp k 2 Ω`. -/
theorem MemWkp_extend_via_cutoff_poly
    (k : ℕ)
    {Ω Ω' K : Set EuclN}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hΩ'_in_Ω : Ω' ⊆ Ω)
    (hK_compact : IsCompact K) (hK_in_Ω' : K ⊆ Ω')
    {u : EuclN → ℝ}
    (hu_local : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω')
    (hu_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ K)),
      u y = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact hΩ'_open hK_in_Ω'
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hη_smooth hη_compact_support k
  have h_eta_u_in_Ω' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω' :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    have hx_ne : η x * u x ≠ 0 := hx
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  have h_eta_u_in_Ω : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set U_K : Set EuclN := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict Ω] u := by
    have h_eq_on_U_K : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict U_K] u := by
      refine (ae_restrict_iff' hU_K_meas).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx_eta : η x = 1 := hη_one_on_cthick x hx
      change η x * u x = u x
      rw [hx_eta]; ring
    have h_diff_meas : MeasurableSet (Ω \ U_K) := hΩ_meas.diff hU_K_meas
    have h_K_in_U_K : Ω \ U_K ⊆ Ω \ K := by
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hK_in_U_K hxK)⟩
    have hu_ae_zero_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ U_K)),
        u y = 0 := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ U_K) ≪
          (volume : Measure EuclN).restrict (Ω \ K) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_K_in_U_K le_rfl)
      exact h_abs.ae_le hu_ae_zero
    have h_eq_on_diff : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict (Ω \ U_K)] u := by
      filter_upwards [hu_ae_zero_diff] with x hx
      rw [hx]; ring
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

/-! ## Polymorphic chart-`H^{m+2}` assembly from chart-`H²` of `m`-mixed
partials

The polymorphic `Nat.rec`-style assembly: for every level-`k ≤ m`, the
chosen `k`-mixed partial of the chart-pushed parent admits chart-`H^{?}`
regularity whose precise order decreases by `1` as we go from level `k` to
level `k+1`. Combined recursively via `MemWkp_succ` at each layer, this
produces chart-`H^{m+2}` of the chart-pushed parent. -/

/-- **Polymorphic chart-`H^{m+2}` assembly via iterated `MemWkp_succ`.**
For any `m, k : ℕ` and any `m`-direction multi-index `dirs`, if every chosen
`k`-mixed partial of the chart-pushed function (for arbitrary multi-index
`Fin k → Fin n`) is in `MemWkp 2 2` of the chart target, and every chosen
`j`-mixed partial for `j ≤ k` is in `MemW1p 2` of the chart target, then
the chosen `m`-mixed partial in directions `dirs` lies in
`MemWkp (k + 2 - m) 2` of the chart target — provided `m ≤ k`.

This is the structural engine. The headline `chartPushed_memWkp_m_plus_two`
specialises this at `m = 0`, where the chosen `0`-mixed partial is the
chart-pushed parent itself. -/
private theorem chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (n_succ : ℕ), -- We prove the statement by induction on `n_succ := k + 1 - m`.
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E)),
      -- chart-H^{m + n_succ + 1} of every (m + n_succ)-mixed partial via the
      -- top-level chart-H^{n_succ + 1} hypothesis on every (m+n_succ)-multi-index,
      -- AND chart-H¹ of every chosen-mixed-partial at intermediate levels.
      -- Hypothesis: chart-H^{n_succ + 1} of every chosen (m+n_succ-1)-mixed partial.
      -- Actually we take the simplest form: chart-H^{n_succ+1} at every direction.
      (∀ (idx_all : Fin m → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx_all)
          (chartTargetEuclid (I := I) (M := M) α)) →
      (∀ (idx_next : Fin (m + 1) → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (n_succ + 1) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) idx_next)
          (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (n_succ + 2) 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro n_succ m dirs h_w1p_m h_memWkp_succ
  -- Apply MemWkp_succ: chart-H^{n_succ+2} of (m-mixed partial in dirs) iff
  --   MemW1p 2 (m-mixed partial in dirs) AND
  --   for every direction `i`, chart-H^{n_succ+1} of the chosen weak partial
  --   `chosenWeakPartial' 2 i (m-mixed partial in dirs)` on chartTarget.
  -- The chosen weak partial in direction i is `chosenMthMixedPartialChartPushedU
  -- g α u_h (m + 1) (Fin.snoc dirs i)` — when we extend `dirs` by appending `i`
  -- (the outermost direction, since the inductive recursion uses Fin.last as the
  -- outermost direction).
  refine ⟨h_w1p_m dirs, ?_⟩
  intro i
  -- Need: chart-H^{n_succ+1} of chosenWeakPartial' 2 i (chosenMthMixed m dirs) chartTarget.
  -- By `chosenMthMixedPartialChartPushedU_succ` (definitionally, since
  -- the recursion of `chosenMthMixedPartialChartPushedU` at level `m+1` and
  -- multi-index `Fin.snoc dirs i` evaluates to `chosenWeakPartial' 2 i (chosenMthMixed m dirs) Ω`):
  --   chosenMthMixed (m+1) (Fin.snoc dirs i) =
  --     chosenWeakPartial' 2 ((Fin.snoc dirs i)(Fin.last m)) (chosenMthMixed m (Fin.init (Fin.snoc dirs i))) Ω
  --   = chosenWeakPartial' 2 i (chosenMthMixed m dirs) Ω.
  have h_snoc_last : (Fin.snoc dirs i : Fin (m + 1) →
      Fin (Module.finrank ℝ E)) (Fin.last m) = i := Fin.snoc_last _ _
  have h_init_snoc : (Fin.init (Fin.snoc dirs i : Fin (m + 1) →
      Fin (Module.finrank ℝ E)) : Fin m → Fin (Module.finrank ℝ E)) = dirs :=
    Fin.init_snoc _ _
  have h_succ_eq :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
        (Fin.snoc dirs i) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [chosenMthMixedPartialChartPushedU_succ, h_snoc_last, h_init_snoc]
  -- Apply the hypothesis at `idx_next := Fin.snoc dirs i`.
  have h_next := h_memWkp_succ (Fin.snoc dirs i)
  rw [h_succ_eq] at h_next
  exact h_next

/-- **Polymorphic chart-`H^{m+2}` assembly from chart-`H²` of every `m`-mixed
partial.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, an element
`u_h : H1Compl g`, an order `m : ℕ`, the chart-pushed POU-cut representative
`chartPushed POU α u_h.coeFn` lies in `MemWkp (m + 2) 2` of the chart target,
provided:

* `MemW1p 2` of every chosen `j`-mixed partial for every `j ≤ m`,
* `MemWkp 2 2` of every chosen `m`-mixed partial (the per-direction chart-`H²`
  regularity that the Nirenberg pipeline delivers).
-/
theorem chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  -- Apply repeated MemWkp_succ. We induct on m, treating the m-multi-index as
  -- arbitrary. At each step, MemWkp_succ peels off one direction, reducing the
  -- problem to MemWkp (m+1) 2 of (1-mixed partial in some direction). Continue.
  -- Strategy: prove the general statement
  --   ∀ k m, chart-H^{k + 2} of every (m - k)-mixed partial -- wait, that's confusing.
  -- Let's prove the simpler general lemma by Nat.rec on a "remaining order" parameter.
  -- We prove by induction on `r` (the order we want):
  --   For every j ≤ m and dirs : Fin j, chart-H^{m + 2 - j} of (j-mixed partial in dirs).
  -- For j = m: we have chart-H^2 of the m-mixed partial (h_top_memWkp_two).
  -- For j = m-1: chart-H^3 of the (m-1)-mixed via MemWkp_succ at order 3.
  -- ...
  -- For j = 0: chart-H^{m+2} of the chart-pushed parent (= 0-mixed partial).
  -- We use the auxiliary lemma above with n_succ varying.
  --
  -- Concretely: by induction on `s : ℕ` (= m - j), prove
  --   chart-H^{s + 2} of every (m - s)-mixed partial (for s ≤ m).
  -- We use a slightly different parametrisation: by `s := m - j`. At s = 0,
  -- j = m and we have the hypothesis. At s = s' + 1, j = m - s' - 1 and we
  -- apply the auxiliary lemma to step from chart-H^{s'+2} of (j+1)-mixed partials
  -- to chart-H^{s'+3} of j-mixed partials.
  --
  -- Define a strong predicate:
  --   P s ↔ s ≤ m ∧ ∀ (j : ℕ), j + s = m → ∀ (dirs : Fin j → ...),
  --     chart-H^{s + 2} of (j-mixed partial in dirs).
  -- We prove ∀ s ≤ m, P s by induction on s. Then specialise to s = m, j = 0.
  --
  -- Actually it's easier to prove the statement directly via Nat.rec on m.
  -- We prove the more general statement
  --   ∀ j (dirs : Fin j → Fin n), chart-H^{(m - j) + 2} of (j-mixed partial in dirs)
  -- but with j ranging from m downwards. This requires a strong induction.
  --
  -- Cleanest: introduce a helper that does the induction.
  suffices h : ∀ s : ℕ, ∀ (j : ℕ), s + j = m → ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (s + 2) 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j dirs)
        (chartTargetEuclid (I := I) (M := M) α) by
    have h_apply := h m 0 (by omega) (Fin.elim0)
    simpa [chosenMthMixedPartialChartPushedU_zero] using h_apply
  intro s
  induction s with
  | zero =>
      -- Base case s = 0: need chart-H^2 of every m-mixed partial (j = m).
      intro j hj dirs
      have hj_eq : j = m := by omega
      subst hj_eq
      exact h_top_memWkp_two dirs
  | succ s ih =>
      -- Step: chart-H^{(s+1) + 2} of every j-mixed partial with j + s + 1 = m.
      -- Apply the auxiliary lemma at level j with `n_succ := s + 1`:
      --   chart-H^{(s+1) + 2} of (j-mixed) ⇐ MemW1p of (j-mixed) AND
      --     chart-H^{(s+1) + 1} of every (j+1)-mixed.
      -- The chart-H^{s + 2} = chart-H^{(s+1) + 1} = chart-H^{s+2} of every
      -- (j+1)-mixed is exactly the inductive hypothesis at `s` and `j + 1`
      -- (where j + 1 + s = m).
      intro j hj dirs
      have hj_le_m : j ≤ m := by omega
      have hj_succ_in_m : s + (j + 1) = m := by omega
      have h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j dirs)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le_m dirs
      have h_next : ∀ (idx : Fin (j + 1) → Fin (Module.finrank ℝ E)),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (s + 2) 2
            (chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (j + 1) idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun idx => ih (j + 1) hj_succ_in_m idx
      -- Apply the auxiliary lemma. n_succ in the auxiliary lemma plays the role
      -- of `s + 1`, so n_succ + 1 = s + 2 and n_succ + 2 = s + 3.
      -- Wait: we want to conclude chart-H^{(s+1) + 2} = chart-H^{s + 3}.
      -- The auxiliary lemma at `n_succ := s + 1` concludes chart-H^{(s+1) + 2}.
      -- It needs:
      --   - h_w1p_m : MemW1p of every m-mixed (taking ALL idx — but it's only used at `dirs`).
      --     Actually the auxiliary takes `∀ idx_all : Fin m → ⋯, MemW1p (m-mixed in idx_all)`
      --     which is stronger than needed (it really needs only at `dirs`).
      -- That's a slight mismatch. Let's modify the auxiliary to take only at the specific dirs.
      -- Actually re-examine: the auxiliary takes a forall over idx_all because the
      -- conclusion `chosenWeakPartial_mem` step requires MemW1p of the parent in all
      -- multi-indices. But really, the auxiliary only USES h_w1p_m at the specific dirs.
      -- We could pass `(fun _ => h_w1p)`.
      have h_w1p_at_all : ∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
          DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
            (chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h j idx_all)
            (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le_m
      have h_aux := chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
        (I := I) (M := M) g α u_h (s + 1) j dirs h_w1p_at_all h_next
      -- h_aux : MemWkp ((s+1) + 2) 2 of (j-mixed in dirs) = MemWkp (s + 3) 2
      have h_eq : s + 1 + 2 = s + 1 + 2 := rfl
      exact h_aux

/-! ## Base case: chart-`H²` from `laplacianDomainPow g 1`

The base case of the bootstrap is `m = 0`: the chart-pushed POU-cut
representative lies in chart-`H²` of every chart target, provided
`u_h ∈ laplacianDomainPow g 1` (= `laplacianDomain g`). This follows from
`iteratedH2Regularity_one`. -/

/-- **Base case chart-`H²` of the chart-pushed function.** For
`u_h ∈ laplacianDomainPow g 1`, the canonical chart-pushed POU-cut
representative lies in `MemWkp 2 2` of the chart target. -/
theorem chartPushed_memWkp_two_of_laplacianDomainPow_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  -- `iteratedH2Regularity_one` gives MemWkpChart g 2 2 (canonical function).
  have h := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
  exact h α

/-! ## Headline iterated chart-`H^{m+2}` from chart-`H^{m+1}` plus chart-`H²`
of every chosen `m`-mixed partial

This is the per-step boost. Combined with the polymorphic Nirenberg pipeline
(applied to every `m`-mixed partial of the chart-pushed parent), it would
deliver chart-`H^{m+2}` of the chart-pushed parent. -/

/-- **Per-step chart-`H^{m+2}` boost.** For a closed Riemannian manifold
`(M, g)`, a chart point `α : M`, an element `u_h : H1Compl g`, and an order
`m : ℕ`, given:

* chart-`H^{m+1}` of the chart-pushed parent — equivalently, by the polymorphic
  regularity bridge, `MemW1p 2` of every chosen `j`-mixed partial for every
  `j ≤ m`;
* `MemWkp 2 2` of every chosen `m`-mixed partial of the chart-pushed parent
  (the per-direction chart-`H²` regularity that the polymorphic Nirenberg
  pipeline delivers on a precompact open subdomain, then extended to the
  full chart target via the support-aware extension lemma),

the chart-pushed parent lies in chart-`H^{m+2}`. -/
theorem chartPushed_memWkp_m_plus_two_step
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  -- chart-H^{m+1} of the parent ⇒ MemW1p 2 of every j-mixed partial for j ≤ m
  -- (via `chosenMthMixedPartialChartPushedU_memW1p_two` with the parent at order m+1).
  -- The intermediate W1p is needed for the polymorphic assembly.
  have h_intermediate_w1p : ∀ (j : ℕ), j ≤ m →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro j hj idx
    -- chart-H^{j+1} of the parent ⇒ MemW1p of every j-mixed partial.
    have h_parent_j_plus_1 :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (j + 1) 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      have h_le : j + 1 ≤ m + 1 := by omega
      exact h_chart_H_m_plus_1.le_of_le h_le
    exact chosenMthMixedPartialChartPushedU_memW1p_two
      (I := I) (M := M) g α u_h j h_parent_j_plus_1 idx
  exact chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two
    (I := I) (M := M) g α u_h m h_intermediate_w1p h_top_memWkp_two

/-! ## Connection to the chart-Sobolev manifold-level regularity

The chart-`H^{m+2}` of the chart-pushed parent corresponds to manifold-level
`MemWkpChart g (m + 2) 2` of the canonical function representative,
via the standard `ChartSideH2kBridge` framework when `m + 2 = 2k`. -/

/-- **Chart-side bridge promotion at order `m + 2`.** If chart-`H^{m+2}` of
the chart-pushed parent holds for every chart point `α`, then the manifold-
level `MemWkpChart g (m + 2) 2` membership holds for the canonical function
representative. -/
theorem memWkpChart_m_plus_two_of_chartPushed_memWkp_m_plus_two
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_chart_pushed_memWkp :
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 2) 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (m + 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact h_chart_pushed_memWkp α

end IteratedChartHmBootstrap
end Laplacian
end Analysis
end DifferentialGeometry

end
