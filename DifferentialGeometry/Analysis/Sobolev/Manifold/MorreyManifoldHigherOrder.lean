import DifferentialGeometry.Analysis.Sobolev.Euclidean.MorreyHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity

/-!
# Higher-order manifold Morrey bound on closed Riemannian manifolds

For a closed Riemannian manifold `M` of dimension `n` modelled on a
finite-dimensional real inner-product space `E`, and for `p > n`, every smooth
`v : M → ℝ` satisfies, for each chart `α : M` and each point `y : EuclN`, a
sup bound on the `m`-th iterated derivative of the chart-pulled smooth
extension `chartSmoothExt α (ρ_α · v)`:

  `‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · v)) y‖
       ≤ C_α · (wkpNormChart g (m+1) p v).toReal`

with a constant `C_α ≥ 0` depending on the metric `g`, the chart `α`, the
exponent `p`, and `m`.

The proof reduces to the Euclidean order-`m` Morrey theorem
`smooth_morrey_iteratedFDeriv_bound_uniform`, applied to the chart-pulled
extension on the Euclidean ball `B(0, R_α)` whose half-radius interior
contains `chartCarrier α`. Off that half-ball, the extension is identically
zero, so all iterated derivatives vanish there too, making the bound trivial
on the complement.

The Euclidean Sobolev norms appearing on the right-hand side are then
related to `wkpNormChart g (m+1) p v` via a chain that mirrors the order-1
construction in `MorreyManifold.lean`:

1. `eLpNorm (‖iteratedFDeriv ℝ j (chartSmoothExt α (ρ_α v))‖) p (vol.restrict (B(0, R_α)))`
    `= eLpNorm ... (vol.restrict Ω_α)` (support inside chartCarrier ⊆ Ω_α);
2. `∑_{j ≤ m+1} eLpNorm (‖iteratedFDeriv ℝ j ...‖) p ≤ wkpNorm (m+1) p (chartSmoothExt) Ω_α`
    (`eLpNorm_iteratedFDeriv_le_wkpNorm`);
3. `wkpNorm (m+1) p (chartSmoothExt α (ρ_α v)) Ω_α
    = wkpNorm (m+1) p (chartPushed α v) Ω_α` (a.e. equality on `Ω_α`);
4. `wkpNorm (m+1) p (chartPushed α v) Ω_α ≤ wkpNormChart g (m+1) p v`
    (it is a summand in the `tsum`).

Finiteness of `wkpNormChart g (m+1) p v` for smooth `v` follows from
`MemWkp_of_smooth_compactSupport_pub` applied to `chartSmoothExt α (ρ_α v)`,
combined with the a.e. equality on `Ω_α`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-! ## Pointwise vanishing of iterated derivatives off the support -/

/-- For any smooth scalar function `h : EuclN → ℝ` and any `y` not in its
`tsupport`, every iterated derivative of order ≥ 0 vanishes at `y`. -/
private lemma iteratedFDeriv_eq_zero_of_notMem_tsupport
    {h : EuclN → ℝ} {y : EuclN} (hy : y ∉ tsupport h) (m : ℕ) :
    iteratedFDeriv ℝ m h y = 0 := by
  have hy_off : y ∉ Function.support (iteratedFDeriv ℝ m h) := by
    intro hy_in
    exact hy ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := m)) hy_in)
  exact Function.notMem_support.mp hy_off

/-- The chart-pulled smooth extension `chartSmoothExt α (ρ_α · u)` has all
iterated derivatives equal to zero off `chartCarrier α`. -/
private lemma iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ chartCarrier (I := I) (M := M) α) (m : ℕ) :
    iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) y = 0 := by
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  have hy_off : y ∉ tsupport h := fun hy_in =>
    hy (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
      (I := I) (M := M) α u hy_in)
  exact iteratedFDeriv_eq_zero_of_notMem_tsupport hy_off m

/-- Iterated derivatives of `chartSmoothExt α (ρ_α · u)` vanish off the
half-ball `B(0, R_α/2)`, since the function has tsupport in `chartCarrier α`
which is contained in that half-ball. -/
private lemma iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2))
    (m : ℕ) :
    iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) y = 0 := by
  have hy_off_carrier : y ∉ chartCarrier (I := I) (M := M) α := fun hin =>
    hy (chartCarrier_subset_half_ball (I := I) (M := M) α hin)
  exact iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
    (I := I) (M := M) α u hy_off_carrier m

/-! ## Indicator-style equality for the `eLpNorm` of `‖iteratedFDeriv m h‖`

For `h = chartSmoothExt α (ρ_α · u)`, the iterated derivative of order `j`
vanishes outside `chartCarrier α`, which sits inside both `B(0, R_α)` and
`chartTargetEuclid α`. Hence the `eLpNorm` is preserved when restricting
the measure to either set. -/

/-- For `h = chartSmoothExt α (ρ_α · u)` and any order `j`, the `eLpNorm` of
`‖iteratedFDeriv ℝ j h‖` on the ball `B(0, R_α)` equals its `eLpNorm` on
`chartTargetEuclid α`. Both equal the full-space `eLpNorm`. -/
private lemma eLpNorm_norm_iteratedFDeriv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) (j : ℕ) :
    eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) =
      eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuclN := chartCarrier (I := I) (M := M) α with hK_def
  set BR : Set EuclN := Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)
    with hBR_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_BR : K ⊆ BR := chartCarrier_subset_full_ball (I := I) (M := M) α
  have hK_Ω : K ⊆ Ω := chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  set fnNorm : EuclN → ℝ := fun z : EuclN => ‖iteratedFDeriv ℝ j h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_iter_zero : iteratedFDeriv ℝ j h y = 0 :=
        iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
          (I := I) (M := M) α u hyK j
      change ‖iteratedFDeriv ℝ j h y‖ = 0
      rw [h_iter_zero, norm_zero]
  have h_eq_Ω : fnNorm = Ω.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_Ω h2)
      have h_iter_zero : iteratedFDeriv ℝ j h y = 0 :=
        iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_carrier
          (I := I) (M := M) α u hyK j
      change ‖iteratedFDeriv ℝ j h y‖ = 0
      rw [h_iter_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]
    _ = eLpNorm (Ω.indicator fnNorm) q volume := by rw [← h_eq_Ω]
    _ = eLpNorm fnNorm q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

/-! ## Bound on the sum of `eLpNorm (‖iteratedFDeriv j h‖)` by `wkpNorm`

Apply `eLpNorm_iteratedFDeriv_le_wkpNorm` to `h = chartSmoothExt α (ρ_α u)`,
using that `h` is smooth, has compact support, and `tsupport h ⊆ Ω_α`. -/

/-- For smooth `u : M → ℝ`, the sum `∑_{j ≤ k} eLpNorm (‖iteratedFDeriv ℝ j h‖)`
on the chart target is bounded by `wkpNorm k p h Ω_α`, where
`h = chartSmoothExt α (ρ_α u)`. -/
private lemma sum_eLpNorm_norm_iteratedFDeriv_chartSmoothExt_le_wkpNorm
    [NeZero (Module.finrank ℝ E)]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) p
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hh_smooth : ContDiff ℝ ∞ h := by
    rw [hh_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) hu
  have hh_smooth_top : ContDiff ℝ (⊤ : ℕ∞) h := hh_smooth
  have hh_compact : HasCompactSupport h := by
    rw [hh_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) u
  have hh_supp : tsupport h ⊆ Ω := by
    rw [hh_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iteratedFDeriv_le_wkpNorm
    (d := Module.finrank ℝ E) hΩ_open hp_one k hh_smooth_top hh_compact hh_supp

/-! ## Bound on the Euclidean `wkpNorm` of `chartSmoothExt α (ρ_α u)` by
`wkpNormChart g k p u`

This generalises the order-1 case in `MorreyManifold.lean`. The proof:
1. `chartSmoothExt α (ρ_α u) =ᵃᵉ chartPushed ρ α u` on `vol.restrict Ω_α`;
2. `wkpNorm_congr_ae` gives `wkpNorm k p (chartSmoothExt) Ω_α = wkpNorm k p (chartPushed) Ω_α`;
3. `wkpNormChart` is the `tsum` of `wkpNorm k p (chartPushed β u) Ω_β` over `β`, so
    the single-`α` term is bounded by the `tsum` via `ENNReal.le_tsum`.
-/

/-- The Euclidean `wkpNorm` of `chartPushed ρ α u` at chart `α` is bounded
by `wkpNormChart u` at order `k`. -/
private lemma wkpNorm_chartPushed_target_le_wkpNormChart_k
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {q : ℝ≥0∞} (k : ℕ) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k q
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) g k q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-- The Euclidean `wkpNorm` of `chartSmoothExt α (ρ_α u)` on `Ω_α` equals
that of `chartPushed ρ α u` on `Ω_α`. -/
private lemma wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target_k
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (k : ℕ) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k q
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k q
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hq_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u)

/-- The Euclidean `wkpNorm` of `chartSmoothExt α (ρ_α u)` on `Ω_α` is bounded
by `wkpNormChart g k q u`. -/
private lemma wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart_k
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (k : ℕ) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k q
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) g k q u := by
  classical
  rw [wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target_k
    (I := I) (M := M) hq_one k α u]
  exact wkpNorm_chartPushed_target_le_wkpNormChart_k
    (I := I) (M := M) g k α u

/-! ## Smooth → `MemWkpChart g k p` for arbitrary order `k`

The order-1 bridge `MemWkpChart_of_contMDiff` lives in
`Intrinsic/Equivalence.lean`. For higher orders the proof becomes simpler in
the chart-pushed setting: `chartSmoothExt α (ρ_α u)` is smooth and compactly
supported, so `MemWkp_of_smooth_compactSupport_pub` gives membership at any
order; this transfers to `chartPushed ρ α u` by a.e. equality on `Ω_α`. -/

/-- The chart-pulled smooth extension `chartSmoothExt α (ρ_α u)` belongs to
`MemWkp k p` of `Ω_α`, for every smooth `u : M → ℝ` and every `k`. -/
private lemma memWkp_chartSmoothExt_pou_mul
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hh_smooth : ContDiff ℝ ∞ h := by
    rw [hh_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) hu
  have hh_smooth_top : ContDiff ℝ (⊤ : ℕ∞) h := hh_smooth
  have hh_compact : HasCompactSupport h := by
    rw [hh_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) u
  have hh_supp : tsupport h ⊆ Ω := by
    rw [hh_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
    (d := Module.finrank ℝ E) hΩ_open hh_smooth_top hh_compact hh_supp hp_one k

/-- The chart-pushed `chartPushed ρ α u` belongs to `MemWkp k p` of `Ω_α`
for every smooth `u : M → ℝ` and every `k`. -/
private lemma memWkp_chartPushed_of_contMDiff
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hExt := memWkp_chartSmoothExt_pou_mul (I := I) (M := M) α hu hp_one k
  -- chartSmoothExt α (ρ_α u) =ᵃᵉ chartPushed ρ α u on vol.restrict Ω_α.
  have h_ae := chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u
  -- Use MemWkp's a.e. invariance (via `wkpNorm_congr_ae` and a structural
  -- argument). The cleanest way: every iterated weak partial is a.e.
  -- preserved, hence finite Lp norms transfer. Since MemWkp is a `Prop`
  -- preserved under a.e. equality on open sets, we directly use the
  -- a.e.-congruence lemma.
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Use MemWkp.congr_ae (the predicate is preserved under a.e. equality).
  refine (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one hΩ_open h_ae).mp hExt

/-- Every smooth function on a closed Riemannian manifold lies in the
chart-based `W^{k,p}` space, for every order `k`. -/
theorem memWkpChart_of_contMDiff_k
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) g k p u := by
  intro α
  exact memWkp_chartPushed_of_contMDiff (I := I) (M := M) α hu hp_one k

/-- For smooth `u : M → ℝ` on a closed manifold, `wkpNormChart g k p u` is
finite at every order `k`. -/
private lemma wkpNormChart_lt_top_of_contMDiff_k
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    wkpNormChart (I := I) (M := M) g k p u < (⊤ : ℝ≥0∞) :=
  wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one
    (memWkpChart_of_contMDiff_k (I := I) (M := M) g hp_one k hu)

/-! ## Per-chart Morrey bound on `iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α u))`

Apply `smooth_morrey_iteratedFDeriv_bound_uniform` to `chartSmoothExt α (ρ_α u)`
on the Euclidean ball `B(0, R_α)`. -/

/-- For each chart `α` and each order `m`, smooth `u : M → ℝ`, and `p > n`,
there is a uniform constant `C_α ≥ 0` (independent of `u`) such that for ALL
`y : EuclN`:
`‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · u)) y‖ ≤ C_α · ∑_{j ≤ m+1} eLpNorm (‖iteratedFDeriv ℝ j (chartSmoothExt α (ρ_α · u))‖) p (vol.restrict B(0, R_α))`. -/
private lemma chartSmoothExt_morrey_iteratedFDeriv_sup_uniform
    (α : M) {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤ C *
          ((Finset.range (m + 2)).sum fun j =>
            (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j (chartSmoothExt
                (I := I) (M := M) α
                (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuclN) (chartRadius
                (I := I) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (I := I) (M := M) α :=
    chartRadius_pos (I := I) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      (d := Module.finrank ℝ E) hp
      (x₀ := (0 : EuclN)) (R := chartRadius (I := I) (M := M) α) hR_pos m
  refine ⟨C, hC_nn, ?_⟩
  intro u hu y
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) hu
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  by_cases hy_half : y ∈ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · -- iteratedFDeriv ℝ m f y = 0, so LHS = 0.
    have hf_iter_zero : iteratedFDeriv ℝ m f y = 0 := by
      rw [hf_def]
      exact iteratedFDeriv_chartSmoothExt_pou_mul_eq_zero_off_half_ball
        (I := I) (M := M) α u hy_half m
    rw [hf_iter_zero, norm_zero]
    -- RHS ≥ 0.
    apply mul_nonneg hC_nn
    exact Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)

/-! ## Per-chart Morrey bound on `iteratedFDeriv ℝ m` by `wkpNormChart`

Combine the chart-local Morrey bound with the conversion of Euclidean Sobolev
norms to `wkpNormChart`. -/

/-- For each chart `α`, smooth `u : M → ℝ`, `p > n`, and order `m`, there is
a constant `C_α ≥ 0` such that, for every smooth `u`:
`‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · u)) y‖ ≤ C_α · (wkpNormChart g (m+1) p u).toReal`
holds for ALL `y : EuclN`. -/
private lemma per_chart_smooth_iteratedFDeriv_sup_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤ C *
          (wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast NeZero.pos (Module.finrank ℝ E)
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_iteratedFDeriv_sup_uniform (I := I) (M := M) α hp m
  refine ⟨Cmorrey, hCmorrey_nn, ?_⟩
  intro u hu y
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hbound_y := hbound hu y
  -- Now show that ∑_{j ≤ m+1} eLpNorm (‖iteratedFDeriv ℝ j f‖)_{p, BR} ≤ (wkpNormChart g (m+1) p u).toReal.
  set total_eLpNorm : ℝ :=
    (Finset.range (m + 2)).sum fun j =>
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal
    with htotal_def
  set N : ℝ := (wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u).toReal
    with hN_def
  -- Step 1: bound each `eLpNorm BR` by the same `eLpNorm` on Ω_α.
  have h_step_BR_eq_Ω : ∀ j : ℕ,
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN)
          (chartRadius (I := I) (M := M) α)))) =
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α))) := by
    intro j
    rw [hf_def]
    exact eLpNorm_norm_iteratedFDeriv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
      (I := I) (M := M) α u (ENNReal.ofReal p) j
  -- Set the .toReal version.
  set total_Ω : ℝ :=
    (Finset.range (m + 2)).sum fun j =>
      (eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α))).toReal
    with htotalΩ_def
  have h_total_eq : total_eLpNorm = total_Ω := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_step_BR_eq_Ω j]
  -- Step 2: ∑ eLpNorm on Ω_α is bounded by wkpNorm (m+1) p f Ω_α.
  -- We need the `.toReal` inequality.
  -- First, the ENNReal inequality.
  have h_sum_eLpNorm_le_wkpNorm :
      ∑ j ∈ Finset.range (m + 2),
        eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
          (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p) f
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hf_def]
    -- The general lemma uses k+1 = m+2 (range up to k+1), so we apply with k = m+1.
    have := sum_eLpNorm_norm_iteratedFDeriv_chartSmoothExt_le_wkpNorm
      (I := I) (M := M) α hu hp_enn_one (m + 1)
    -- The LHS has range (k+1) = range (m+2), matches our sum.
    exact this
  -- Step 3: wkpNorm (m+1) p f Ω_α ≤ wkpNormChart g (m+1) p u.
  have h_wkpNorm_le_wkpNormChart :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p) f
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u := by
    rw [hf_def]
    exact wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart_k
      (I := I) (M := M) g hp_enn_one (m + 1) α u
  have h_wkp_chain :
      ∑ j ∈ Finset.range (m + 2),
        eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
          (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u :=
    h_sum_eLpNorm_le_wkpNorm.trans h_wkpNorm_le_wkpNormChart
  -- Step 4: take `.toReal` of `h_wkp_chain`.
  have hwkp_ne_top : wkpNormChart (I := I) (M := M) g (m + 1)
      (ENNReal.ofReal p) u ≠ ⊤ :=
    (wkpNormChart_lt_top_of_contMDiff_k (I := I) (M := M) g hp_enn_one (m + 1) hu).ne
  have h_sum_le_N : total_Ω ≤ N := by
    have h_sum_eq :
        (∑ j ∈ Finset.range (m + 2),
          eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α))).toReal =
        total_Ω := by
      rw [htotalΩ_def, ENNReal.toReal_sum]
      intro j hj
      -- Each summand has finite eLpNorm because it ≤ wkpNormChart.
      have h_sum_j_le :
          eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j f z‖) (ENNReal.ofReal p)
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u := by
        refine le_trans ?_ h_wkpNorm_le_wkpNormChart
        refine le_trans ?_ h_sum_eLpNorm_le_wkpNorm
        exact Finset.single_le_sum
          (f := fun j' : ℕ =>
            eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ j' f z‖) (ENNReal.ofReal p)
              (volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
          (fun _ _ => zero_le _) hj
      exact lt_of_le_of_lt h_sum_j_le
        (wkpNormChart_lt_top_of_contMDiff_k (I := I) (M := M) g hp_enn_one (m + 1) hu) |>.ne
    rw [← h_sum_eq]
    exact ENNReal.toReal_mono hwkp_ne_top h_wkp_chain
  -- Combine.
  have h_total_le_N : total_eLpNorm ≤ N := by
    rw [h_total_eq]; exact h_sum_le_N
  -- Final bound.
  have h_bound_chain :
      ‖iteratedFDeriv ℝ m f y‖ ≤ Cmorrey * total_eLpNorm := by
    rw [hf_def]; exact hbound_y
  have h_final : Cmorrey * total_eLpNorm ≤ Cmorrey * N :=
    mul_le_mul_of_nonneg_left h_total_le_N hCmorrey_nn
  exact le_trans h_bound_chain h_final

/-! ## Per-chart Morrey constants (packaged as a function `M → ℝ`) -/

/-- Per-chart constant from `per_chart_smooth_iteratedFDeriv_sup_bound`,
packaged as a function `M → ℝ`. -/
private noncomputable def perChartMorreyIteratedConst
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_iteratedFDeriv_sup_bound
    (I := I) (M := M) g hp m α)

private lemma perChartMorreyIteratedConst_nn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    0 ≤ perChartMorreyIteratedConst (I := I) (M := M) g hp m α :=
  (Classical.choose_spec
    (per_chart_smooth_iteratedFDeriv_sup_bound
      (I := I) (M := M) g hp m α)).1

private lemma perChartMorreyIteratedConst_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ)
    [NeZero (Module.finrank ℝ E)] (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (y : EuclN) :
    ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) y‖ ≤
      perChartMorreyIteratedConst (I := I) (M := M) g hp m α *
        (wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_iteratedFDeriv_sup_bound
      (I := I) (M := M) g hp m α)).2 hu y

/-! ## Public theorem: per-chart higher-order manifold Morrey bound

Statement: for each chart `α : M`, there is a uniform constant `C_α ≥ 0`
such that for every smooth `v : M → ℝ` and every `y : EuclN`,
`‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · v)) y‖ ≤ C_α · (wkpNormChart g (m+1) p v).toReal`.

The constant `C_α` is uniform in `v`. -/

/-- **Higher-order per-chart manifold Morrey bound** (uniform in `v`). For a
closed Riemannian manifold and `p > n = dim ℝ E`, every chart `α : M` and
every order `m`, there is a uniform constant `C_α ≥ 0` (depending on `g`, `p`,
`m`, the chart `α`, and the canonical chart-atlas POU) such that for every
smooth `v : M → ℝ` and every `y : EuclN`:

  `‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · v)) y‖ ≤ C_α · (wkpNormChart g (m+1) p v).toReal`.

For `m = 0`, this is a per-chart variant of `smooth_manifold_morrey_sup_bound_uniform`.
For `m ≥ 1`, the bound on iterated derivatives of the chart-pulled extension is
exactly what downstream chains (chart-Sobolev → `C^∞`) require. -/
theorem smooth_manifold_morrey_iteratedFDeriv_bound_uniform_perChart
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x)) y‖ ≤ C *
            (wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) v).toReal :=
  per_chart_smooth_iteratedFDeriv_sup_bound (I := I) (M := M) g hp m α

/-- **Higher-order manifold Morrey bound** (atlas-quantified form, uniform in
`v`). For a closed Riemannian manifold and `p > n = dim ℝ E`, every order `m`,
and every chart `α : M`, there is a uniform constant `C_α ≥ 0` such that for
every smooth `v : M → ℝ` and every `y : EuclN`:

  `‖iteratedFDeriv ℝ m (chartSmoothExt α (ρ_α · v)) y‖ ≤ C_α · (wkpNormChart g (m+1) p v).toReal`.

The constant `C_α` is the per-chart Morrey constant from the Euclidean
order-`m` Morrey theorem applied to the chart-pulled extension; it depends on
`α`. This is the canonical per-chart formulation used in the chart-Sobolev to
`C^∞` chain: downstream users instantiate it per-chart and combine via the
partition of unity. -/
theorem smooth_manifold_morrey_iteratedFDeriv_bound_uniform
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) (m : ℕ) :
    ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
        ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ m (chartSmoothExt (I := I) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x)) y‖ ≤ C *
            (wkpNormChart (I := I) (M := M) g (m + 1) (ENNReal.ofReal p) v).toReal :=
  fun α => per_chart_smooth_iteratedFDeriv_sup_bound (I := I) (M := M) g hp m α

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
