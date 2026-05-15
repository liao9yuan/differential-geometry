import DifferentialGeometry.Analysis.Laplacian.Regularity.DerivedChartBilinearH1ComplDataUnconditional
import DifferentialGeometry.Analysis.Laplacian.Regularity.DerivedChartBilinearH2Interior
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushedMemWkpThreeTrulyUnconditional
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplH3
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Final unconditional chart-`H³` regularity of the chart-pushed function

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed
representative

`chartPushed POU α (H1ComplToLp g u_h).coeFn`

lies in `MemWkp 3 2 (chartTargetEuclid α)`, **unconditionally** — i.e. with
no extra Sobolev or smoothness hypothesis on `u_h.coeFn`.

## Strategy

By the structural unfolding `MemWkp_succ`, this regularity claim splits
into the conjunction

* `MemW1p 2 (chartPushed POU α u_h.coeFn) chartTargetEuclid`, and
* for every coordinate direction `i : Fin (Module.finrank ℝ E)`,
  `MemWkp 2 2 (chosenWeakPartial' 2 i (chartPushed POU α u_h.coeFn)
    chartTargetEuclid) chartTargetEuclid`.

The first conjunct is already unconditional via
`chartPushed_memW1p_two_of_laplacianDomainPow_two`.

For the second conjunct, fix a direction `i` and let

`D_eff := derivedChartBilinearH1ComplDataUnconditional g α i hu_h`.

By `derivedChartBilinear_memWkp_two_two_interior`, there is an open
precompact `Ω''_i ⊆ chartTargetEuclid α` containing the chart-pushed POU
support `K_α := chartImagePOUTsupport α` with

`MemWkp 2 2 D_eff.u_chart Ω''_i`.

Geometrically, `D_eff.u_chart` is `(base).weak_partial i` — the chart-pushed
weak `i`-partial coercion of `u_h`. It is **ae-zero** off `K_α` (witness:
`base_weak_partial_ae_zero_off_K_α`). We promote the `MemWkp 2 2`
membership from `Ω''_i` to the entire chart target by multiplying
`D_eff.u_chart` against a smooth cutoff `η_i` that equals `1` on a
neighborhood of `K_α` and is supported pointwise inside `Ω''_i`:

* `η_i · D_eff.u_chart` is `MemWkp 2 2 Ω''_i` by
  `MemWkp.smul_smooth_bounded`;
* `η_i · D_eff.u_chart` has compact pointwise topological support inside
  `Ω''_i`, so it extends by zero via `MemWkp.extend_zero` to the entire
  chart target;
* `η_i · D_eff.u_chart` agrees a.e. with `D_eff.u_chart` on
  `chartTargetEuclid α` (since `η_i = 1` on a neighborhood of `K_α` and
  `D_eff.u_chart = 0` a.e. on the complement of `K_α`), and
* `D_eff.u_chart` agrees a.e. with `chartPushedChosenFirstPartial g α u_h i`
  on the chart target via
  `chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget`.

Transferring via `MemWkp_congr_ae` gives
`MemWkp 2 2 (chosenWeakPartial' 2 i (chartPushed POU α u_h.coeFn)
chartTargetEuclid) chartTargetEuclid`.

## Main result

`chartPushed_memWkp_three_two_of_laplacianDomainPow_two` — for any chart
point `α : M`, the canonical chart-pushed POU-cut representative of
`H1ComplToLp g u_h` lies in `MemWkp 3 2 (chartTargetEuclid α)` for every
`u_h ∈ laplacianDomainPow g 2`.

This headline is **fully unconditional**: no extra Sobolev or smoothness
hypothesis on `u_h` is required.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpThreeUnconditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataUnconditional
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH2Interior
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThreeTrulyUnconditional
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Support-aware `MemWkp` extension from a precompact open subdomain

The core technical lemma: a function `u` that lies in `MemWkp k 2` of a
precompact open `Ω' ⊆ Ω` and that vanishes a.e. on the complement
`Ω \ K` for some compact `K ⊆ Ω'` can be promoted to `MemWkp k 2 Ω`. The
proof multiplies `u` by a smooth cutoff `η` that is `1` on a neighborhood
of `K` and has pointwise topological support inside `Ω'`, then applies
`MemWkp.extend_zero` to the product and transfers back via
`MemWkp_congr_ae`. -/

/-- Given a function `u : EuclN → ℝ` that lies in `MemWkp k 2` of an open
precompact `Ω' ⊆ Ω` (both open, `Ω' ⊆ Ω`, closure of `Ω'` inside `Ω`),
and that vanishes a.e. on `Ω \ K` for some compact `K ⊆ Ω'`, `u` lies in
`MemWkp k 2 Ω`. -/
private theorem MemWkp_two_extend_via_cutoff
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
  -- Pick a smooth cutoff η ≡ 1 on a neighborhood of K, tsupport η ⊆ Ω'.
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact hΩ'_open hK_in_Ω'
  -- Uniform bound on the iterated derivatives of η, up to order k.
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hη_smooth hη_compact_support k
  -- The product `η · u` is in `MemWkp k 2 Ω'`.
  have h_eta_u_in_Ω' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω' :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  -- The pointwise tsupport of `η · u` is inside `tsupport η ⊆ Ω'`.
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    -- hx : x ∈ support (η · u), i.e. (η x) * (u x) ≠ 0.
    have hx_ne : η x * u x ≠ 0 := hx
    -- Show x ∈ support η, i.e. η x ≠ 0.
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  -- Extend `η · u` from `Ω'` to `Ω`.
  have h_eta_u_in_Ω : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  -- Show `η · u =ᵃᵉ u` on `volume.restrict Ω`.
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  -- Inner cthickening: η ≡ 1 on cthickening δ K.
  set U_K : Set EuclN := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  -- The ae-equality argument.
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict Ω] u := by
    -- Split Ω as U_K ∪ (Ω \ U_K).
    -- On U_K: η x = 1, so η x * u x = u x.
    -- On Ω \ U_K ⊆ Ω \ K: u x = 0 ae, so η x * u x = 0 = u x ae.
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
    -- Cover Ω = U_K ∪ (Ω \ U_K).
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have h_U_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    -- Goal is now `(fun x ↦ η x * u x) =ᵐ[μ_U_K + μ_diff] u`. Split via
    -- `ae_add_measure_iff` after unfolding `Filter.EventuallyEq`.
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  -- Transfer `MemWkp k 2 (η · u) Ω` to `MemWkp k 2 u Ω` via ae-equality.
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

/-! ## Per-direction chart-`H²` regularity of the chart-pushed chosen first
weak partial

For each coordinate direction `i`, the chosen first weak partial
`chosenWeakPartial' 2 i (chartPushed POU α u_h.coeFn) chartTargetEuclid`
lies in `MemWkp 2 2 (chartTargetEuclid α)`, unconditionally for
`u_h ∈ laplacianDomainPow g 2`. -/

/-- For every coordinate direction `i`, the canonical chosen first weak
partial `chartPushedChosenFirstPartial g α u_h i` lies in
`MemWkp 2 2 (chartTargetEuclid α)` unconditionally for
`u_h ∈ laplacianDomainPow g 2`.

The proof uses the chart-bilinear "interior" `MemWkp 2 2` regularity of
the once-differentiated chart-bilinear data on a precompact open
neighborhood `Ω''_i ⊆ chartTargetEuclid α` of the POU-cut support
`chartImagePOUTsupport α`, combined with the ae-zero support of the
chart-pushed weak partial coercion outside the POU-cut support, plus the
unconditional ae-equality of the chart-pushed weak partial coercion and
the chosen first weak partial on the chart target. -/
theorem chartPushed_chosenFirstPartial_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Set up the derived data for direction `i`.
  set D : ChartBilinearH1ComplData (I := I) (M := M) g α :=
    derivedChartBilinearH1ComplDataUnconditional (I := I) (M := M) g α i hu_h
    with hD_def
  -- Interior MemWkp 2 2 regularity of D.u_chart on a precompact open `Ω''`.
  obtain ⟨Ω'', hΩ''_open, hΩ''_compact_closure, hΩ''_in_chart, hK_in_Ω'',
    h_D_uChart_memWkp22_Ω''⟩ :=
    derivedChartBilinear_memWkp_two_two_interior (I := I) (M := M) g α i hu_h
  -- The compact POU support `K_α := chartImagePOUTsupport α`.
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  -- The full chart target is open.
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hΩ''_in_chart' : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    subset_trans subset_closure hΩ''_in_chart
  -- `D.u_chart` is ae zero on `chartTargetEuclid α \ K_α`. This follows from
  -- the fact that `D.u_chart = (base).weak_partial i`, where `(base)` is the
  -- chart-bilinear data attached to `laplacianDomain`. The base's weak
  -- partial is ae zero on the complement of `K_α` (from
  -- `base_weak_partial_ae_zero_off_K_α`).
  have h_D_uChart_eq_base : D.u_chart =
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1
          hu_h)).weak_partial i := by
    -- D.u_chart = derivedChartBilinearH1ComplDataUnconditional.u_chart =
    -- derivedChartBilinearH1ComplData.u_chart = derived_u_chart g α i hu_h =
    -- (chartBilinearH1ComplData_of_laplacianDomain ...).weak_partial i
    rfl
  -- Apply `base_weak_partial_ae_zero_off_K_α` for direction `i`.
  have h_D_uChart_ae_zero_off_K_α :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α)),
        D.u_chart y = 0 := by
    rw [h_D_uChart_eq_base]
    exact base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i
  -- Promote `MemWkp 2 2 D.u_chart Ω''` to the full chart target via the
  -- support-aware extension lemma.
  have h_D_uChart_memWkp22_chart :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_two_extend_via_cutoff (E := E) 2
      h_chart_open hΩ''_open hΩ''_in_chart' hK_α_compact hK_in_Ω''
      h_D_uChart_memWkp22_Ω'' h_D_uChart_ae_zero_off_K_α
  -- `D.u_chart` agrees ae with `chartPushedChosenFirstPartial g α u_h i` on
  -- the chart target.
  have h_D_uChart_ae_eq_chosen :
      D.u_chart =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
    -- D.u_chart unfolds to chartPushedWeakPartialLp.coeFn. The ae-equality is
    -- the existing σ-compact-exhaustion bridge.
    have h_eq : D.u_chart = (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) := by
      rw [h_D_uChart_eq_base]
      -- (base).weak_partial i = chartPushedWeakPartialLp ... .coeFn.
      exact DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartBilinearH1ComplData_of_laplacianDomain_weak_partial_def
        (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h) i
    rw [h_eq]
    exact chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
      (I := I) (M := M) g α hu_h i
  -- Transfer `MemWkp 2 2` from `D.u_chart` to
  -- `chartPushedChosenFirstPartial g α u_h i` via ae-equality.
  have h_chosenFirst_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
        (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
      h_D_uChart_ae_eq_chosen).mp h_D_uChart_memWkp22_chart
  -- Unfold `chartPushedChosenFirstPartial` to the explicit chosen partial.
  -- The definitions coincide by `rfl`.
  exact h_chosenFirst_memWkp22

/-! ## Final unconditional chart-`H³` regularity

The headline of this module: for any chart point `α : M`, the canonical
chart-pushed POU-cut representative `chartPushed POU α u_h.coeFn` lies in
`MemWkp 3 2 (chartTargetEuclid α)`, unconditionally for any element
`u_h ∈ laplacianDomainPow g 2` on a closed Riemannian manifold. -/

/-- **Final chart-`H³` regularity of the canonical chart-pushed function,
unconditional for `u_h ∈ laplacianDomainPow g 2`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
and any element `u_h ∈ laplacianDomainPow g 2`, the canonical chart-pushed
POU-cut representative `chartPushed POU α u_h.coeFn` lies in
`MemWkp 3 2 (chartTargetEuclid α)`, unconditionally. -/
theorem chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  -- Use the assembly form: combine the unconditional `MemW1p 2` of the
  -- chart-pushed function with the per-direction `MemWkp 2 2` of the chosen
  -- first weak partials.
  refine chartPushed_memWkp_three_two_of_chosen_partials_memWkp_two_two
    (I := I) (M := M) g α hu_h ?_
  intro i
  exact chartPushed_chosenFirstPartial_memWkp_two_two
    (I := I) (M := M) g α hu_h i

/-! ## Headline statement, exposed at the requested name -/

/-- **Headline (renamed for compatibility): chart-`H³` of the canonical
chart-pushed function, unconditional for `u_h ∈ laplacianDomainPow g 2`.**

This is the precise statement required to discharge the residual
hypothesis `h_chartPushed_memWkp32` in downstream consumers; the headline
re-states `chartPushed_memWkp_three_two_of_laplacianDomainPow_two` in the
canonical form. -/
theorem chartPushed_memWkp_three_two_of_laplacianDomainPow_two'
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h

end ChartPushedMemWkpThreeUnconditional
end Laplacian
end Analysis
end DifferentialGeometry

end
