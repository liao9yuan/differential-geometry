import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# Explicit-norm `eLpNorm` bound for the differentiated chart-RHS numerator

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the level-`(m+1)`
differentiated chart-RHS numerator `eigenvectorChartRHSDiffNumerator` is the
explicit five-layer Leibniz combination `A + B − C + D + E` produced by one more
integration by parts in the new direction `lₙ := l (Fin.last m)`.

The qualitative companion `eigenvectorChartRHSDiffNumerator_memLp_volume_compact`
records that the numerator is `MemLp 2` of the plain Lebesgue volume restricted
to the compact partition-of-unity kernel `chartPouKernel α`, by splitting the
five layers and proving each `MemLp 2`.

This file records the quantitative twin: there is a nonnegative constant `C`
with

```
eLpNorm (eigenvectorChartRHSDiffNumerator … m l fChartEffPrev) 2 μ
  ≤ ENNReal.ofReal C * <AGGREGATE>,
```

where `μ = volume.restrict (chartPouKernel α)` and `<AGGREGATE>` is the honest
finite sum

* `∑ₐ wkpNorm 2 2 (eigenvectorChartIteratedPartial … (m+1) (Fin.cons a (Fin.init
  l))) (chartTargetEuclid α)` — the iterated weak partials feeding layers `A`,
  `B`;
* `wkpNorm 2 2 (eigenvectorChartIteratedPartial … m (Fin.init l))
  (chartTargetEuclid α)` — the iterated weak partial feeding layer `C`;
* `wkpNorm 1 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer `E` via
  the chosen weak partial;
* `eLpNorm fChartEffPrev 2 μ` — controlling layer `D`.

## Strategy

The numerator is a five-layer `+`/`-` combination of functions `EuclN → ℝ`.
Iterated Minkowski (`eLpNorm_add_le` / `eLpNorm_sub_le`) bounds its `eLpNorm` by
the sum of the five layer `eLpNorm`s. Each layer is a finite sum of
`(smooth coefficient) · atom` summands:

* layers `A`, `B`, `C` have a `C^∞`-on-the-chart-target coefficient
  (`weightedInvGramDerivOnEuclid`-and-`fderiv` thereof, or `densityDerivOnEuclid`)
  and an iterated-weak-partial atom — directly the `(m+1)`-fold mixed weak
  partial, its chosen weak partial, or the `m`-fold mixed weak partial;
* layers `D`, `E` have the smooth coefficient `densityDerivOnEuclid`,
  respectively `densityOnEuclid`, and the `fChartEffPrev` atom — directly, or
  its chosen weak partial.

Per summand the `C^∞`-coefficient bound (the plain-`volume.restrict` analogue of
`eLpNorm_weighted_contDiffOn_mul_le`, established here by a few-line pointwise
norm domination on the compact kernel) gives `eLpNorm (coeff · atom) 2 μ ≤
ENNReal.ofReal Cᵢ * eLpNorm atom 2 μ`. The atom `eLpNorm` is then bounded:

* an iterated weak partial atom by `eLpNorm_le_wkpNorm`, then `wkpNorm 0 2 ≤
  wkpNorm 2 2`;
* a chosen weak partial of an iterated partial by `wkpNorm_chosenWeakPartial_le`
  (which drops one Sobolev order), then `eLpNorm_le_wkpNorm` and the order
  monotonicity `wkpNorm 1 2 ≤ wkpNorm 2 2`;
* the `fChartEffPrev` atom by `eLpNorm_le_wkpNorm` of the restricted measure;
* the chosen weak partial of `fChartEffPrev` by `wkpNorm_chosenWeakPartial_le`
  then `eLpNorm_le_wkpNorm`.

Every per-summand quantity is dominated by the full aggregate (the norms are
nonnegative `ℝ≥0∞` quantities), so all per-summand constants and finite-sum
multiplicities fold into a single nonnegative constant `C`.

## Main result

* `eigenvectorChartRHSDiffNumerator_eLpNorm_le` — the explicit-norm `eLpNorm`
  bound for the differentiated chart-RHS numerator.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## A plain-`volume.restrict` explicit-norm bound for a `C^∞`-coefficient product

The quantitative coefficient lemma `eLpNorm_weighted_contDiffOn_mul_le` records,
for the *chart-pulled weighted* measure, that a `C^∞`-on-the-chart-target
coefficient `c` multiplied by an `L²` function `w` has `eLpNorm` bounded by an
explicit constant — the sup of `‖c‖` over the compact support set — times the
`eLpNorm` of `w`.

The differentiated chart-RHS numerator is `MemLp 2` (and is `eLpNorm`-bounded
here) for the **plain Lebesgue volume restricted to the compact kernel**
`chartPouKernel α`, the measure of the qualitative companion
`eigenvectorChartRHSDiffNumerator_memLp_volume_compact`. The plain-`volume`
analogue is recorded here: on a compact `K`, all of which carries the restricted
measure, the pointwise bound `‖c y‖ ≤ C` for `y ∈ K` gives `‖c y * w y‖ ≤
‖C • w y‖` everywhere on the support; monotonicity and homogeneity of `eLpNorm`
finish. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- **Plain-`volume.restrict` explicit-norm bound for a `C^∞`-coefficient
product.** Let `c : EuclN → ℝ` be `C^∞` on the open chart target, let
`K ⊆ chartTargetEuclid α` be compact, and let `w : EuclN → ℝ` be arbitrary. Then
there is a nonnegative constant `C` — the sup of `‖c‖` over `K` — with

```
eLpNorm (fun y => c y * w y) 2 (volume.restrict K)
  ≤ ENNReal.ofReal C * eLpNorm w 2 (volume.restrict K).
```

The restricted measure `volume.restrict K` is supported in `K`, so the pointwise
bound `‖c y‖ ≤ C` for `y ∈ K` upgrades — almost everywhere for the restricted
measure — to `‖c y * w y‖ ≤ ‖C • w y‖`. Monotonicity of `eLpNorm` under that
norm domination, the homogeneity `eLpNorm (C • w) 2 μ = ‖C‖ₑ * eLpNorm w 2 μ`,
and the conversion `‖C‖ₑ = ENNReal.ofReal C` for `C ≥ 0` give the estimate.

This is the plain-`volume.restrict` companion of the weighted-measure lemma
`eLpNorm_weighted_contDiffOn_mul_le`. -/
private lemma eLpNorm_volume_restrict_contDiffOn_mul_le
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (w : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  -- The `C^∞` coefficient is bounded on the compact `K` by a nonnegative `C`.
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  -- Pointwise almost-everywhere norm domination `‖c · w‖ ≤ ‖C • w‖`. The
  -- restricted measure is supported in `K`, where `‖c y‖ ≤ C` holds.
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  -- Monotonicity of `eLpNorm` under the a.e. norm domination.
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  -- Homogeneity of `eLpNorm` under scalar multiplication, with `‖C‖ₑ` rewritten
  -- to `ENNReal.ofReal C` (valid since `C ≥ 0`).
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * eLpNorm w 2 μ := by
    have h := eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μ
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μ := h_smul

/-! ## A finite-sum aggregation lemma

A finite indexed family of summands `F j`, each with `eLpNorm` bounded by
`ENNReal.ofReal Cⱼ` times one *fixed* aggregate `ℝ≥0∞`-quantity `A`, has its
summed `eLpNorm` bounded by `ENNReal.ofReal` of an explicit constant times `A`.
The explicit constant is the sum of the per-summand constants times the
cardinality of the index type; the triangle inequality `eLpNorm_sum_le` and the
monotonicity of `ENNReal.ofReal` assemble it. -/

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- A finite indexed family of `MemLp` summands, each `eLpNorm`-bounded by
`ENNReal.ofReal Cⱼ` times a fixed aggregate quantity `A`, has its summed
`eLpNorm` bounded by `ENNReal.ofReal` of an explicit nonnegative constant times
`A`. -/
private lemma eLpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {μ : Measure EuclN} (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemLp (F j) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ eLpNorm (F j) 2 μ ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ j : ι, F j y) 2 μ ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, eLpNorm (F j) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

/-! ## The differentiated-numerator aggregate

`diffNumeratorAggregate` packages the honest finite sum of source norms
controlling the differentiated chart-RHS numerator. It aggregates: the
`wkpNorm 2 2` of the `(m+1)`-fold iterated weak partials feeding layers `A`, `B`;
the `wkpNorm 2 2` of the `m`-fold iterated weak partial feeding layer `C`; the
`wkpNorm 1 2` of `fChartEffPrev` controlling layer `E`; and the `eLpNorm` of
`fChartEffPrev` against the restricted volume controlling layer `D`. -/

/-- The finite aggregate of source norms controlling the differentiated
chart-RHS numerator: the `wkpNorm 2 2` of the iterated weak partials feeding
layers `A`, `B`, `C`, together with the `wkpNorm 1 2` and the restricted-volume
`eLpNorm` of the previous-level right-hand side `fChartEffPrev`. -/
def diffNumeratorAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
    + wkpNorm (d := Module.finrank ℝ E) 1 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)
    + eLpNorm fChartEffPrev 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))

/-! ## Per-layer atom `eLpNorm` bounds

Each of the four kinds of atom appearing in the five layers has its `eLpNorm`
against `volume.restrict (chartPouKernel α)` bounded by a sub-aggregate of
`diffNumeratorAggregate`. Each sub-aggregate is `≤ diffNumeratorAggregate` (all
summands are nonnegative `ℝ≥0∞` quantities). -/

section AtomBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
/-- The `(m+1)`-fold iterated weak partial atom (layer `A`) has restricted-volume
`eLpNorm` bounded by its `wkpNorm 2 2` on the chart target. The restricted volume
on the compact kernel is the chart-target restricted volume re-restricted to the
kernel; `eLpNorm` is monotone in the domain, and `eLpNorm_le_wkpNorm` controls it
by `wkpNorm 2 2`. -/
private lemma eLpNorm_iteratedPartial_succ_le
    (a : Fin (Module.finrank ℝ E)) :
    eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The restricted volume on the kernel is the chart-target volume re-restricted.
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _
    (Measure.restrict_le_self)) ?_
  exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 2 2
    (chartTargetEuclid (I := I) (M := M) α) _

omit [CompleteSpace E] in
/-- The `m`-fold iterated weak partial atom (layer `C`) has restricted-volume
`eLpNorm` bounded by its `wkpNorm 2 2` on the chart target. -/
private lemma eLpNorm_iteratedPartial_le :
    eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l)) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _
    (Measure.restrict_le_self)) ?_
  exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 2 2
    (chartTargetEuclid (I := I) (M := M) α) _

omit [CompleteSpace E] in
/-- The chosen weak `b`-partial of the `(m+1)`-fold iterated weak partial atom
(layer `B`) has restricted-volume `eLpNorm` bounded by the `wkpNorm 2 2` of the
`(m+1)`-fold iterated weak partial. A chosen weak partial drops one Sobolev order
(`wkpNorm_chosenWeakPartial_le`); `eLpNorm_le_wkpNorm` then controls the chosen
weak partial's `eLpNorm` by its `wkpNorm 1 2`, which `wkpNorm_mono_order` bounds
by `wkpNorm 2 2` of the parent. -/
private lemma eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
    (a b : Fin (Module.finrank ℝ E)) :
    eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  -- The chosen weak partial's `eLpNorm` is `≤` its `wkpNorm 0 2`.
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 1 2 Ω _) ?_
  -- `wkpNorm 1 2 (∂_b P) Ω ≤ wkpNorm 2 2 P Ω` — a chosen weak partial drops one
  -- order, and the order-`2` norm dominates the order-`2` norm of the parent.
  exact wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 1 hΩ_open _ b

end AtomBounds

/-! ## Per-layer `eLpNorm` bounds

Each of the five layers of `eigenvectorChartRHSDiffNumerator` is a finite sum of
`(C^∞ coefficient) · atom` summands; this section bounds the `eLpNorm` of every
layer by an explicit constant times `diffNumeratorAggregate`. -/

section LayerBounds

/-! ### Layer A

`A = ∑ₐ ∑_b (∂_b weightedInvGramDerivOnEuclid g α a b lₙ) ·
(eigenvectorChartIteratedPartial … (m+1) (Fin.cons a (Fin.init l)))`. -/

omit [CompleteSpace E] in
/-- **`eLpNorm` bound for layer `A`.** Each summand is a `C^∞` coefficient — the
`fderiv`-evaluation of `weightedInvGramDerivOnEuclid` — times the `(m+1)`-fold
iterated weak partial; the plain-`volume` coefficient bound and the iterated
weak partial `eLpNorm` bound combine, and `eLpNorm_sum_le_const_mul_aggregate`
aggregates the double sum. -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The `C^∞` coefficient `∂_b (weightedInvGramDerivOnEuclid · · ·)`.
  have h_coeff : ∀ a b : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro a b
    have h_diffOn : ContDiffOn ℝ ∞
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ ∞
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  -- The iterated weak partial atom is `MemLp 2 μ`.
  have h_atom_mem : ∀ a : Fin (Module.finrank ℝ E),
      MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
    intro a
    have h0 := (h_iter a).le_of_le (Nat.zero_le 2)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict
          (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  -- The single iterated weak partial atom is `≤ A` (it is one summand of `A`).
  have h_atom_le : ∀ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    intro a
    rw [hA_def, diffNumeratorAggregate]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- The double-sum aggregation: bound the inner sum over `b`, then over `a`.
  refine eLpNorm_sum_le_const_mul_aggregate
    (μ := μ)
    (fun a => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) A ?_ ?_
  · -- Each inner sum over `b` is `MemLp 2 μ`.
    intro a
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem a)
  · -- Each inner sum over `b` is `eLpNorm`-bounded by an explicit constant * A.
    intro a
    refine eLpNorm_sum_le_const_mul_aggregate
      (μ := μ)
      (fun b => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) A ?_ ?_
    · intro b
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem a)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
        (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
      gcongr
      exact le_trans (eLpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s h_atlas i α P₀ m l a) (h_atom_le a)

/-! ### Layer B

`B = ∑ₐ ∑_b weightedInvGramDerivOnEuclid g α a b lₙ ·
(∂_b-weak-partial of eigenvectorChartIteratedPartial … (m+1) (Fin.cons a
(Fin.init l)))`. -/

omit [CompleteSpace E] in
/-- **`eLpNorm` bound for layer `B`.** Each summand is the `C^∞` coefficient
`weightedInvGramDerivOnEuclid` times the chosen weak `b`-partial of the
`(m+1)`-fold iterated weak partial; the plain-`volume` coefficient bound and the
chosen-weak-partial `eLpNorm` bound combine. -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The iterated weak partial atom is `≤ A` (it is one summand of `A`).
  have h_atom_le : ∀ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω ≤ A := by
    intro a
    rw [hA_def, diffNumeratorAggregate, ← hΩ_def]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- The chosen weak partial is `MemLp 2 μ`: from `MemWkp 2 2` of the iterated
  -- partial, `MemWkp.chosenWeakPartial_mem` gives `MemWkp 1 2`, hence `MemLp`.
  have h_chosen_mem : ∀ a b : Fin (Module.finrank ℝ E),
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) 2 μ := by
    intro a b
    have h1 : MemWkp (d := Module.finrank ℝ E) 1 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) Ω :=
      (h_iter a).chosenWeakPartial_mem b
    have h0 := h1.le_of_le (Nat.zero_le 1)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  refine eLpNorm_sum_le_const_mul_aggregate
    (μ := μ)
    (fun a => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y) A ?_ ?_
  · intro a
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in (h_chosen_mem a b)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate
      (μ := μ)
      (fun b => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y) A ?_ ?_
    · intro b
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in (h_chosen_mem a b)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
        (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
      gcongr
      exact le_trans (eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
        (I := I) (M := M) g r s h_atlas i α P₀ m l a b) (h_atom_le a)

/-! ### Layer C

`C = densityDerivOnEuclid g α lₙ · (eigenvectorChartIteratedPartial … m
(Fin.init l))`. -/

omit [CompleteSpace E] in
/-- **`eLpNorm` bound for layer `C`.** The single summand is the `C^∞`
coefficient `densityDerivOnEuclid` times the `m`-fold iterated weak partial; the
plain-`volume` coefficient bound and the iterated weak partial `eLpNorm` bound
combine. -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The `m`-fold iterated weak partial atom is `≤ A` (it is the second summand).
  have h_atom_le : wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    rw [hA_def, diffNumeratorAggregate]
    exact le_trans le_add_self (le_trans le_self_add le_self_add)
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
    (eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s h_atlas i α P₀ m (Fin.init l))
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  exact le_trans (eLpNorm_iteratedPartial_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l) h_atom_le

/-! ### Layer D

`D = densityDerivOnEuclid g α lₙ · fChartEffPrev`. -/

omit [CompleteSpace E] in
/-- **`eLpNorm` bound for layer `D`.** The single summand is the `C^∞`
coefficient `densityDerivOnEuclid` times `fChartEffPrev`; the plain-`volume`
coefficient bound applies, and `eLpNorm fChartEffPrev 2 μ` is a summand of the
aggregate. -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            fChartEffPrev y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `eLpNorm fChartEffPrev 2 μ` is the fourth summand of `A`.
  have h_atom_le : eLpNorm fChartEffPrev 2 μ ≤ A := by
    rw [hA_def, diffNumeratorAggregate, ← hμ_def]
    exact le_add_self
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in fChartEffPrev
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr

/-! ### Layer E

`E = densityOnEuclid g α · (∂_{lₙ}-weak-partial of fChartEffPrev)`. -/

omit [CompleteSpace E] in
/-- **`eLpNorm` bound for layer `E`.** The single summand is the `C^∞`
coefficient `densityOnEuclid` times the chosen weak `lₙ`-partial of
`fChartEffPrev`; the plain-`volume` coefficient bound applies, and the chosen
weak partial's `eLpNorm` is bounded by `wkpNorm 1 2 fChartEffPrev`, a summand of
the aggregate. -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
              fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `wkpNorm 1 2 fChartEffPrev Ω` is the third summand of `A`.
  have h_atom_le : wkpNorm (d := Module.finrank ℝ E) 1 2 fChartEffPrev Ω ≤ A := by
    rw [hA_def, diffNumeratorAggregate, ← hΩ_def]
    exact le_trans le_add_self le_self_add
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    hK_compact hK_meas hK_in
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
      fChartEffPrev Ω)
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  -- The chosen weak partial's `eLpNorm` is `≤ wkpNorm 0 2 ≤ wkpNorm 1 2 (fPrev)`.
  have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
      (chartPouKernel (I := I) (M := M) α) := by
    rw [hμ_def, Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 0 2 Ω _) ?_
  exact le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 0
    hΩ_open _ (l (Fin.last m))) h_atom_le

end LayerBounds

/-! ## The headline explicit-norm `eLpNorm` bound -/

section MainBound

-- The headline carries the support hypothesis `h_prev_zero` — the previous-level
-- right-hand side `fChartEffPrev` vanishes almost everywhere off the compact
-- partition-of-unity kernel — as part of the shared API contract: the iterated
-- divergence-form scaffold consuming this bound supplies it for every level, and
-- the qualitative companion's input contract carries it likewise. The `eLpNorm`
-- estimate is against `volume.restrict (chartPouKernel α)`, whose support is the
-- kernel, so the off-kernel behavior of `fChartEffPrev` does not enter the proof
-- term; the hypothesis is kept for that parity.
set_option linter.unusedVariables false in
/-- **The explicit-norm `eLpNorm` bound for the differentiated chart-RHS
numerator.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, a
direction multi-index `l : Fin (m+1) → Fin n`, and a previous-level right-hand
side `fChartEffPrev : EuclN → ℝ`, there is a nonnegative constant `C` such that
the `eLpNorm` of the level-`(m+1)` differentiated chart-RHS numerator
`eigenvectorChartRHSDiffNumerator g r s h_atlas i α P₀ m l fChartEffPrev`
against the plain Lebesgue volume restricted to the compact partition-of-unity
kernel `chartPouKernel α` is bounded by `ENNReal.ofReal C` times the finite
aggregate `diffNumeratorAggregate` of the source norms:

* `∑ₐ wkpNorm 2 2 (eigenvectorChartIteratedPartial … (m+1) (Fin.cons a (Fin.init
  l))) (chartTargetEuclid α)` — the iterated weak partials feeding layers `A`,
  `B`;
* `wkpNorm 2 2 (eigenvectorChartIteratedPartial … m (Fin.init l))
  (chartTargetEuclid α)` — the iterated weak partial feeding layer `C`;
* `wkpNorm 1 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer `E`;
* `eLpNorm fChartEffPrev 2 (volume.restrict (chartPouKernel α))` — controlling
  layer `D`.

The hypotheses are: every `(m+1)`-fold and `m`-fold iterated weak partial of the
eigenvector chart component appearing in the numerator lies in
`W^{2,2}(chartTargetEuclid α)` (passed as the genuine regularity hypothesis
`h_iter`), and the previous-level right-hand side `fChartEffPrev` lies in
`W^{1,2}(chartTargetEuclid α)` and vanishes almost everywhere off the compact
kernel `chartPouKernel α` (the genuine hypotheses `h_prev`, `h_prev_zero`).

`eigenvectorChartRHSDiffNumerator` is the five-layer `+`/`-` combination
`A + B − C + D + E`; iterated Minkowski (`eLpNorm_add_le` / `eLpNorm_sub_le`)
bounds its `eLpNorm` by the sum of the five layer `eLpNorm`s. The per-layer
bounds — each layer being a finite sum of a `C^∞`-coefficient product whose atom
is an iterated weak partial, a chosen weak partial thereof, or `fChartEffPrev`
(directly or via a chosen weak partial) — control every layer by an explicit
constant times the aggregate; the five per-layer constants fold into the single
nonnegative `C`. -/
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) 1 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α → fChartEffPrev y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s h_atlas i α P₀ m l fChartEffPrev y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hA_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The five layers, as functions `EuclN → ℝ`.
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  -- The numerator is, pointwise, `layerA + layerB - layerC + layerD + layerE`.
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l fChartEffPrev y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  -- `MemLp` of each layer, for the iterated-triangle-inequality measurability.
  -- Layer A.
  have hA_mem : MemLp layerA 2 μ := by
    rw [hlayerA_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
      have h0 := (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le
        (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in h_atom_mem
  -- Layer B.
  have hB_mem : MemLp layerB 2 μ := by
    rw [hlayerB_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := ((h_iter (m + 1) (Fin.cons a (Fin.init l)))).chosenWeakPartial_mem b
      have h0 := h1.le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in h_chosen_mem
  -- Layer C.
  have hC_mem : MemLp layerC 2 μ := by
    rw [hlayerC_def]
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l)) 2 μ := by
      have h0 := (h_iter m (Fin.init l)).le_of_le (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_atom_mem
  -- Layer D.
  have hD_mem : MemLp layerD 2 μ := by
    rw [hlayerD_def]
    have h_prev_mem : MemLp fChartEffPrev 2 μ := by
      have h0 := h_prev.le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_prev_mem
  -- Layer E.
  have hE_mem : MemLp layerE 2 μ := by
    rw [hlayerE_def]
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2
        (l (Fin.last m)) fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := h_prev.chosenWeakPartial_mem (l (Fin.last m))
      rw [MemWkp_zero] at h1
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h1.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α)
      hK_compact hK_meas hK_in h_chosen_mem
  -- The five per-layer `eLpNorm` bounds.
  obtain ⟨CA, hCA_nn, hCA⟩ := eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l fChartEffPrev
    (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CB, hCB_nn, hCB⟩ := eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l fChartEffPrev
    (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CC, hCC_nn, hCC⟩ := eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l fChartEffPrev
  obtain ⟨CD, hCD_nn, hCD⟩ := eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l fChartEffPrev
  obtain ⟨CE, hCE_nn, hCE⟩ := eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l fChartEffPrev
  rw [← hμ_def, ← hA_def] at hCA hCB hCC hCD hCE
  -- The headline constant: the sum of the five per-layer constants.
  refine ⟨CA + CB + CC + CD + CE, by positivity, ?_⟩
  rw [h_num_eq]
  -- Iterated Minkowski over the five layers `A + B - C + D + E`.
  have h_tri :
      eLpNorm (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) 2 μ
        ≤ eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
          + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ := by
    -- Express the pointwise combination via `Pi`-algebra so Minkowski applies.
    have h_pi : (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
        = layerA + layerB - layerC + layerD + layerE := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_pi]
    have hAB_mem : MemLp (layerA + layerB) 2 μ := hA_mem.add hB_mem
    have hABC_mem : MemLp (layerA + layerB - layerC) 2 μ := hAB_mem.sub hC_mem
    have hABCD_mem : MemLp (layerA + layerB - layerC + layerD) 2 μ :=
      hABC_mem.add hD_mem
    -- Peel `+ E`, then `+ D`, then `- C`, then `+ B`.
    refine le_trans (eLpNorm_add_le hABCD_mem.aestronglyMeasurable
      hE_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hABC_mem.aestronglyMeasurable
      hD_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hAB_mem.aestronglyMeasurable
      hC_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_add_le hA_mem.aestronglyMeasurable
      hB_mem.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  -- Each of the five per-layer `eLpNorm`s is `≤ ofReal Cⱼ * A`.
  have h_five :
      eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
        + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA hCB) hCC) hCD) hCE
  refine le_trans h_five ?_
  -- Collect the five `ofReal Cⱼ * A` terms into `ofReal (∑ Cⱼ) * A`.
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBound

/-! ## The uniform-constant explicit-norm `eLpNorm` bound

The headline `eigenvectorChartRHSDiffNumerator_eLpNorm_le` produces, per
eigenbasis index `i`, a nonnegative constant `C`. A downstream bounded-operator
argument over the whole eigenbasis needs the constant *uniform* — one `C`
serving every `i`. The five per-layer constants are geometric — sup-norms of the
`C^∞` chart-target coefficients (`weightedInvGramDerivOnEuclid` and its `fderiv`,
`densityDerivOnEuclid`, `densityOnEuclid`) over the compact partition-of-unity
kernel — and do not depend on `i`. The eigenbasis index enters only through the
iterated-weak-partial *atoms* and the regularity hypotheses, never the constant.

The eigenvector index `i` is **not** a section variable here, so each restatement
carries its own `∀ i`. A `_uniform` statement cannot be derived from its per-`i`
original (one cannot get `∃ C, ∀ i` from `∀ i, ∃ C`); each carries its own proof
— the per-`i` proof with the constant hoisted before the `∀ i`. The genuine
regularity hypotheses `h_iter`, `h_prev`, `h_prev_zero` move to top-level
`∀ i`-uniform hypotheses. -/

section MainBoundUniform

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Uniform-constant plain-`volume.restrict` `C^∞`-coefficient product bound.**
The constant-uniform form of `eLpNorm_volume_restrict_contDiffOn_mul_le`: the
constant — the sup of `‖c‖` over the compact `K` — depends only on the
coefficient `c` and the set `K`, not on the function being multiplied, so a
single nonnegative `C` serves *every* `w : EuclN → ℝ`. -/
private lemma eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclN → ℝ,
      eLpNorm (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  -- The `C^∞` coefficient is bounded on the compact `K` by a nonnegative `C`.
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w => ?_⟩
  -- Pointwise almost-everywhere norm domination `‖c · w‖ ≤ ‖C • w‖`.
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  -- Monotonicity of `eLpNorm` under the a.e. norm domination.
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  -- Homogeneity of `eLpNorm` under scalar multiplication.
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * eLpNorm w 2 μ := by
    have h := eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μ
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μ := h_smul

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- **Uniform-constant finite-sum aggregation.** The constant-uniform form of
`eLpNorm_sum_le_const_mul_aggregate`: a finite indexed family of summands
`F j n`, each `MemLp` and each — *with an `n`-uniform constant* — having its
`eLpNorm` bounded by `ENNReal.ofReal Cⱼ` times an aggregate `A n`, has its summed
`eLpNorm` bounded by `ENNReal.ofReal` of a single nonnegative constant — *the
same for every `n`* — times `A n`. -/
private lemma eLpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {ν : Type*} {μ : Measure EuclN}
    (F : ι → ν → EuclN → ℝ) (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), MemLp (F j n) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, eLpNorm (F j n) 2 μ ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν,
        eLpNorm (fun y => ∑ j : ι, F j n y) 2 μ ≤ ENNReal.ofReal C * A n := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, eLpNorm (F j n) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j n) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j n) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

/-! ## Uniform-constant per-layer `eLpNorm` bounds

The constant-uniform twins of the five per-layer bounds. Each carries its
genuine regularity hypothesis as a top-level `∀ i`-uniform hypothesis and
concludes `∃ C, 0 ≤ C ∧ ∀ i, <layer bound>`; the geometric constant is hoisted
before the `∀ i`. -/

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for layer `A`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The `C^∞` coefficient `∂_b (weightedInvGramDerivOnEuclid · · ·)`.
  have h_coeff : ∀ a b : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro a b
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_diffOn : ContDiffOn ℝ ∞
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ ∞
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  -- The iterated weak partial atom is `MemLp 2 μ`, for every `i`.
  have h_atom_mem : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
    intro i a
    have h0 := (h_iter i a).le_of_le (Nat.zero_le 2)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict
          (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  -- The single iterated weak partial atom is `≤ A i` (one summand of `A i`).
  have h_atom_le : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
    intro i a
    rw [diffNumeratorAggregate]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- The double-sum aggregation, hoisting the geometric constant: index `ι` over
  -- `b`, parameter `ν` over `(i, a)` for the inner sum, then over `i` outermost.
  refine eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μ) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun i => diffNumeratorAggregate (I := I) (M := M)
      g r s h_atlas i α P₀ m l (fChartEffPrev i)) ?_ ?_
  · -- Each inner sum over `b` is `MemLp 2 μ`.
    intro a i
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem i a)
  · -- Each inner sum over `b` is `eLpNorm`-bounded by an `i`-uniform constant.
    intro a
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun i => diffNumeratorAggregate (I := I) (M := M)
        g r s h_atlas i α P₀ m l (fChartEffPrev i)) ?_ ?_
    · intro b i
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in (h_atom_mem i a)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
        eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
          (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
      gcongr
      exact le_trans (eLpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s h_atlas i α P₀ m l a) (h_atom_le i a)

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for layer `B`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The iterated weak partial atom is `≤ A i` (one summand of `A i`).
  have h_atom_le : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a : Fin (Module.finrank ℝ E)),
      wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
    intro i a
    rw [diffNumeratorAggregate, ← hΩ_def]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω)
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- The chosen weak partial is `MemLp 2 μ`, for every `i`.
  have h_chosen_mem : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (a b : Fin (Module.finrank ℝ E)),
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) 2 μ := by
    intro i a b
    have h1 : MemWkp (d := Module.finrank ℝ E) 1 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω) Ω :=
      (h_iter i a).chosenWeakPartial_mem b
    have h0 := h1.le_of_le (Nat.zero_le 1)
    rw [MemWkp_zero] at h0
    have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
      rw [hμ_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
    rw [h_eq]
    exact h0.restrict _
  refine eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μ) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y)
    (fun i => diffNumeratorAggregate (I := I) (M := M)
      g r s h_atlas i α P₀ m l (fChartEffPrev i)) ?_ ?_
  · intro a i
    refine memLp_finset_sum _ (fun b _ => ?_)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in (h_chosen_mem i a b)
  · intro a
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) Ω y)
      (fun i => diffNumeratorAggregate (I := I) (M := M)
        g r s h_atlas i α P₀ m l (fChartEffPrev i)) ?_ ?_
    · intro b i
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m)))
        hK_compact hK_meas hK_in (h_chosen_mem i a b)
    · intro b
      obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
        eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
          (I := I) (M := M) α
          (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
            (l (Fin.last m)))
          hK_compact hK_meas hK_in
      rw [← hμ_def] at hC₀
      refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
      gcongr
      exact le_trans (eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
        (I := I) (M := M) g r s h_atlas i α P₀ m l a b) (h_atom_le i a)

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for layer `C`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The `m`-fold iterated weak partial atom is `≤ A i` (the second summand).
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wkpNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate]
    exact le_trans le_add_self (le_trans le_self_add le_self_add)
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  exact le_trans (eLpNorm_iteratedPartial_le
    (I := I) (M := M) g r s h_atlas i α P₀ m l) (h_atom_le i)

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for layer `D`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `eLpNorm (fChartEffPrev i) 2 μ` is the fourth summand of `A i`.
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (fChartEffPrev i) 2 μ ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate, ← hμ_def]
    exact le_add_self
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  exact h_atom_le i

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for layer `E`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `wkpNorm 1 2 (fChartEffPrev i) Ω` is the third summand of `A i`.
  have h_atom_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wkpNorm (d := Module.finrank ℝ E) 1 2 (fChartEffPrev i) Ω ≤
        diffNumeratorAggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
    intro i
    rw [diffNumeratorAggregate, ← hΩ_def]
    exact le_trans le_add_self le_self_add
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α) hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
  gcongr
  -- The chosen weak partial's `eLpNorm` is `≤ wkpNorm 0 2 ≤ wkpNorm 1 2 (fPrev)`.
  have h_eq : μ = ((volume : Measure EuclN).restrict Ω).restrict
      (chartPouKernel (I := I) (M := M) α) := by
    rw [hμ_def, Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 0 2 Ω _) ?_
  exact le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 0
    hΩ_open _ (l (Fin.last m))) (h_atom_le i)

set_option linter.unusedVariables false in
/-- **The uniform-constant explicit-norm `eLpNorm` bound for the differentiated
chart-RHS numerator.**

The constant-uniform form of `eigenvectorChartRHSDiffNumerator_eLpNorm_le`: a
single nonnegative constant `C` — geometric, the combined sup-norms of the
`C^∞` chart-target coefficients over the compact partition-of-unity kernel,
independent of the eigenbasis index — serves *every* eigenbasis index `i`. For
each `i`, the `eLpNorm` of the level-`(m+1)` differentiated chart-RHS numerator
against the plain Lebesgue volume restricted to the compact kernel
`chartPouKernel α` is bounded by `ENNReal.ofReal C` times the finite aggregate
`diffNumeratorAggregate` of that `i`.

The genuine regularity hypotheses are uniform over `i`: every `(m+1)`-fold and
`m`-fold iterated weak partial of every eigenvector chart component lies in
`W^{2,2}(chartTargetEuclid α)` (`h_iter`); each previous-level right-hand side
`fChartEffPrev i` lies in `W^{1,2}(chartTargetEuclid α)` (`h_prev`) and vanishes
almost everywhere off the compact kernel (`h_prev_zero`).

A `_uniform` statement cannot be derived from its per-`i` original; this carries
its own proof — the per-`i` proof of `eigenvectorChartRHSDiffNumerator_eLpNorm_le`
with the five per-layer geometric constants hoisted before the `∀ i` via the
constant-uniform per-layer bounds. -/
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) 1 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α → fChartEffPrev i y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s h_atlas i α P₀ m l (fChartEffPrev i) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i) := by
  classical
  -- The five `i`-uniform per-layer constants — hoisted before the `∀ i`.
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev
  -- The headline constant: the sum of the five per-layer constants.
  refine ⟨CA + CB + CC + CD + CE, by positivity, fun i => ?_⟩
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  set A := diffNumeratorAggregate (I := I) (M := M)
    g r s h_atlas i α P₀ m l (fChartEffPrev i) with hA_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The five layers, as functions `EuclN → ℝ`.
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  -- The numerator is, pointwise, `layerA + layerB - layerC + layerD + layerE`.
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l (fChartEffPrev i) y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  -- `MemLp` of each layer, for the iterated-triangle-inequality measurability.
  -- Layer A.
  have hA_mem : MemLp layerA 2 μ := by
    rw [hlayerA_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2 μ := by
      have h0 := (h_iter i (m + 1) (Fin.cons a (Fin.init l))).le_of_le
        (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in h_atom_mem
  -- Layer B.
  have hB_mem : MemLp layerB 2 μ := by
    rw [hlayerB_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := ((h_iter i (m + 1)
        (Fin.cons a (Fin.init l)))).chosenWeakPartial_mem b
      have h0 := h1.le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in h_chosen_mem
  -- Layer C.
  have hC_mem : MemLp layerC 2 μ := by
    rw [hlayerC_def]
    have h_atom_mem : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l)) 2 μ := by
      have h0 := (h_iter i m (Fin.init l)).le_of_le (Nat.zero_le 2)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_atom_mem
  -- Layer D.
  have hD_mem : MemLp layerD 2 μ := by
    rw [hlayerD_def]
    have h_prev_mem : MemLp (fChartEffPrev i) 2 μ := by
      have h0 := (h_prev i).le_of_le (Nat.zero_le 1)
      rw [MemWkp_zero] at h0
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h0.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_prev_mem
  -- Layer E.
  have hE_mem : MemLp layerE 2 μ := by
    rw [hlayerE_def]
    have h_chosen_mem : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2
        (l (Fin.last m)) (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α)) 2 μ := by
      have h1 := (h_prev i).chosenWeakPartial_mem (l (Fin.last m))
      rw [MemWkp_zero] at h1
      have h_eq : μ = ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K := by
        rw [hμ_def, hK_def, Measure.restrict_restrict hK_meas,
          Set.inter_eq_self_of_subset_left hK_in]
      rw [h_eq]
      exact h1.restrict _
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α)
      hK_compact hK_meas hK_in h_chosen_mem
  -- The five per-layer `eLpNorm` bounds, specialised to this `i`.
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  rw [← hA_def] at hCA_i hCB_i hCC_i hCD_i hCE_i
  rw [h_num_eq]
  -- Iterated Minkowski over the five layers `A + B - C + D + E`.
  have h_tri :
      eLpNorm (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) 2 μ
        ≤ eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
          + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ := by
    have h_pi : (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
        = layerA + layerB - layerC + layerD + layerE := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_pi]
    have hAB_mem : MemLp (layerA + layerB) 2 μ := hA_mem.add hB_mem
    have hABC_mem : MemLp (layerA + layerB - layerC) 2 μ := hAB_mem.sub hC_mem
    have hABCD_mem : MemLp (layerA + layerB - layerC + layerD) 2 μ :=
      hABC_mem.add hD_mem
    refine le_trans (eLpNorm_add_le hABCD_mem.aestronglyMeasurable
      hE_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hABC_mem.aestronglyMeasurable
      hD_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hAB_mem.aestronglyMeasurable
      hC_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_add_le hA_mem.aestronglyMeasurable
      hB_mem.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  -- Each of the five per-layer `eLpNorm`s is `≤ ofReal Cⱼ * A`.
  have h_five :
      eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
        + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_i hCB_i) hCC_i) hCD_i)
      hCE_i
  refine le_trans h_five ?_
  -- Collect the five `ofReal Cⱼ * A` terms into `ofReal (∑ Cⱼ) * A`.
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUniform

/-! ## Sharp per-layer `eLpNorm` bounds with direct atom hypotheses

The five `_le_uniform` per-layer bounds (`…_layerA_eLpNorm_le_uniform`, …)
take qualitative `MemWkp` hypotheses on the iterated weak partials of the
eigenvector chart components and conclude an `eLpNorm` bound of each layer by
an explicit constant times `diffNumeratorAggregate`, the finite aggregate
containing `wkpNorm 2 2` of the `(m+1)`- and `m`-fold iterated weak partials.

The following sharp variants take, instead, *direct quantitative `eLpNorm`
bounds* on each layer's atom (the `(m+1)`-fold iterated weak partial for
layers `A`, `C`; the chosen weak partial of the `(m+1)`-fold iterated weak
partial for layer `B`; `fChartEffPrev` for layer `D`; the chosen weak partial
of `fChartEffPrev` for layer `E`) of the form `eLpNorm atom ≤
ENNReal.ofReal (C_atom · μ⁻¹^e_atom) · ‖vec‖`, where `μ = i.fst.val` is the
eigenvalue and `‖vec‖ = ‖tensorResolventEigenbasisVec h_atlas i‖`. They
conclude with the same multiplicative shape: an `i`-uniform `C` times
`ofReal (C_atom · μ⁻¹^e_atom) · ‖vec‖`.

The proof structure mirrors the corresponding `_le_uniform` variant: the
geometric coefficient sup-norm is hoisted to an `i`-uniform constant via
`eLpNorm_volume_restrict_contDiffOn_mul_le_uniform`, and the per-summand
`gcongr` step routes through the direct `hAtom*_bd` hypothesis instead of the
`atom-`wkpNorm`-into-aggregate` chain. The geometric constant — exactly the
same one as in the corresponding `_le_uniform` variant — multiplies through
the inner-sum cardinality bookkeeping to give the final `i`-uniform `C`.

The sharp variants are intended as inputs to a recursive `eLpNorm` bound at
order `m+1` whose atom hypotheses are produced from a single chart-`W^{m+1,2}`
hypothesis on the eigenvector chart component (the `MemWkp (k + (m+1)) 2`
chart-pou wrapper) via the polymorphic chart-cpt-to-iterated-partial bridge.
This avoids the circular dependency in which the bound at order `m+1` would
otherwise require chart `wkpNorm (m+3) 2`. -/

section SharpAtomBounds

/-! ### Unconditional `MemLp` helpers

The sharp variants require, per summand, the `MemLp 2` of layer atoms
(iterated weak partials and chosen weak partials thereof) for the
restricted-volume measure on a compact subset of the chart target. The
iterated weak partial is unconditionally `MemLp 2` of the chart-target
restricted volume (`eigenvectorChartIteratedPartial_memLp_volume`); the
chosen weak partial of an arbitrary function is unconditionally `MemLp 2`
by the `DeGiorgi.MemW1p` case split. -/

omit [CompleteSpace E] in
/-- The `m`-fold mixed weak partial of the eigenvector chart component is
`MemLp 2` of the volume restricted to any measurable subset of the chart
target. -/
private lemma iter_memLp_volume_restrict
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m l) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := eigenvectorChartIteratedPartial_memLp_volume
    (I := I) (M := M) g r s h_atlas i α P₀ m l
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    exact congrArg _ (Set.inter_eq_self_of_subset_left hK_in)
  exact h_eq ▸ h_global.restrict K

omit [CompleteSpace E] in
/-- The canonical chosen weak partial `chosenWeakPartial' 2 b w Ω` of an
arbitrary function is `MemLp 2` of the volume restricted to any measurable
subset of `Ω`: by case split on `DeGiorgi.MemW1p 2 w Ω`, the chosen weak
partial is either the genuine `L²` weak partial of a `W^{1,2}` element or
the zero function. -/
private lemma chosenWp_memLp_volume_restrict
    (b : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) {Ω K : Set EuclN}
    (hK_meas : MeasurableSet K) (hK_in : K ⊆ Ω) :
    MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b w Ω) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have h_global : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b w Ω)
      2 ((volume : Measure EuclN).restrict Ω) := by
    by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
    · exact chosenWeakPartial'_memLp_of_mem hw b
    · rw [chosenWeakPartial'_of_not_mem hw b]
      exact MemLp.zero
  have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    exact congrArg _ (Set.inter_eq_self_of_subset_left hK_in)
  exact h_eq ▸ h_global.restrict K

/-! ### Per-layer sharp `eLpNorm` bounds

Each sharp variant takes a *direct quantitative `eLpNorm` bound* on its
layer's atom, of the form `eLpNorm atom 2 μ ≤ ofReal (CatomX · (μᵢ)⁻¹^eAtomX)
· ofReal ‖vec_i‖`, where `μᵢ = i.fst.val` is the eigenvalue and `vec_i =
tensorResolventEigenbasisVec h_atlas i`. The conclusion has the same
multiplicative shape, with an `i`-uniform geometric constant `C` (the
sup-norm of the smooth coefficient on the compact kernel) absorbed into the
prefactor:
`eLpNorm (layer X) 2 μ ≤ ofReal (C · CatomX · (μᵢ)⁻¹^eAtomX) · ofReal ‖vec_i‖`.

The proof structure mirrors the corresponding `_le_uniform` variant: the
geometric coefficient sup-norm is hoisted before the `∀ i` via
`eLpNorm_volume_restrict_contDiffOn_mul_le_uniform`, and the per-summand
`gcongr` step routes through `hAtom*_bd` directly instead of the
`atom-wkpNorm-into-diffNumeratorAggregate` chain. -/

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for layer `A`** with a direct quantitative
`eLpNorm` hypothesis on the layer-`A` atom (the `(m+1)`-fold iterated weak
partial). The geometric constant is hoisted before the `∀ i`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomA : ℝ) (eAtomA : ℕ) (_hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The `C^∞` coefficient `∂_b (weightedInvGramDerivOnEuclid · · ·)`.
  have h_coeff : ∀ a b : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro a b
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_diffOn : ContDiffOn ℝ ∞
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ ∞
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  -- The double-sum aggregation, hoisting the geometric constant. The
  -- aggregate `A i` is `ofReal (CatomA · (i.fst.val)⁻¹^eAtomA) · ofReal ‖vec_i‖`.
  -- The double `?_` placeholders are filled later: first MemLp, then the bound.
  have h_main : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2 μ
          ≤ ENNReal.ofReal C *
              (ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (F := fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (A := fun i => ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ?_ ?_
    · -- Each inner sum over `b` is `MemLp 2 μ`.
      intro a i
      refine memLp_finset_sum _ (fun b _ => ?_)
      have h_atom_mem := iter_memLp_volume_restrict
        (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)) hK_meas hK_in
      rw [← hμ_def] at h_atom_mem
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (h_coeff a b) hK_compact hK_meas hK_in h_atom_mem
    · -- Each inner sum over `b` is `eLpNorm`-bounded by an `i`-uniform constant.
      intro a
      refine eLpNorm_sum_le_const_mul_aggregate_uniform
        (μ := μ) (ι := Fin (Module.finrank ℝ E))
        (ν := TensorEigenIdx (I := I) (M := M) g r s)
        (F := fun b => fun i => fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (A := fun i => ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ?_ ?_
      · intro b i
        have h_atom_mem := iter_memLp_volume_restrict
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)) hK_meas hK_in
        rw [← hμ_def] at h_atom_mem
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (h_coeff a b) hK_compact hK_meas hK_in h_atom_mem
      · intro b
        obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
          eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
            (I := I) (M := M) α (h_coeff a b) hK_compact hK_meas hK_in
        rw [← hμ_def] at hC₀
        refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
        gcongr
        exact hAtomA_bd i a
  -- Repack `ofReal C * (ofReal (CatomA · …) * ofReal ‖·‖) = ofReal (C · CatomA · …) · ofReal ‖·‖`.
  obtain ⟨C, hC_nn, hC⟩ := h_main
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC i) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_assoc C CatomA]

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for layer `B`** with a direct quantitative
`eLpNorm` hypothesis on the layer-`B` atom (the chosen weak `b`-partial of
the `(m+1)`-fold iterated weak partial). -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomB : ℝ) (eAtomB : ℕ) (_hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_main : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y) 2 μ
          ≤ ENNReal.ofReal C *
              (ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
    refine eLpNorm_sum_le_const_mul_aggregate_uniform
      (μ := μ) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (F := fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (A := fun i => ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ?_ ?_
    · intro a i
      refine memLp_finset_sum _ (fun b _ => ?_)
      have h_chosen_mem := chosenWp_memLp_volume_restrict b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ω := chartTargetEuclid (I := I) (M := M) α)
        hK_meas hK_in
      rw [← hμ_def] at h_chosen_mem
      exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
        hK_compact hK_meas hK_in h_chosen_mem
    · intro a
      refine eLpNorm_sum_le_const_mul_aggregate_uniform
        (μ := μ) (ι := Fin (Module.finrank ℝ E))
        (ν := TensorEigenIdx (I := I) (M := M) g r s)
        (F := fun b => fun i => fun y =>
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
        (A := fun i => ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ?_ ?_
      · intro b i
        have h_chosen_mem := chosenWp_memLp_volume_restrict b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ω := chartTargetEuclid (I := I) (M := M) α)
          hK_meas hK_in
        rw [← hμ_def] at h_chosen_mem
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
            (l (Fin.last m)))
          hK_compact hK_meas hK_in h_chosen_mem
      · intro b
        obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
          eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
            (I := I) (M := M) α
            (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
              (l (Fin.last m)))
            hK_compact hK_meas hK_in
        rw [← hμ_def] at hC₀
        refine ⟨C₀, hC₀_nn, fun i => le_trans (hC₀ _) ?_⟩
        gcongr
        exact hAtomB_bd i a b
  obtain ⟨C, hC_nn, hC⟩ := h_main
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine le_trans (hC i) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_assoc C CatomB]

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for layer `C`** with a direct quantitative
`eLpNorm` hypothesis on the layer-`C` atom (the `m`-fold iterated weak
partial). -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomC : ℝ) (eAtomC : ℕ) (_hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  -- `ofReal C₀ · eLpNorm atom ≤ ofReal C₀ · (ofReal (CatomC · μ⁻¹^e) · ofReal ‖·‖)`,
  -- then collect: `ofReal C₀ · ofReal (CatomC · μ⁻¹^e) = ofReal (C₀ · CatomC · μ⁻¹^e)`.
  calc
    ENNReal.ofReal C₀ * eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l)) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
          gcongr
          exact hAtomC_bd i
    _ = ENNReal.ofReal (C₀ * CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomC]

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for layer `D`** with a direct quantitative
`eLpNorm` hypothesis on `fChartEffPrev`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomD : ℝ) (eAtomD : ℕ) (_hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (fChartEffPrev i) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  calc
    ENNReal.ofReal C₀ * eLpNorm (fChartEffPrev i) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
          gcongr
          exact hAtomD_bd i
    _ = ENNReal.ofReal (C₀ * CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomD]

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for layer `E`** with a direct quantitative
`eLpNorm` hypothesis on the chosen weak `lₙ`-partial of `fChartEffPrev`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomE : ℝ) (eAtomE : ℕ) (_hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict
    (chartPouKernel (I := I) (M := M) α) with hμ_def
  have hK_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (I := I) (M := M) α
    (densityOnEuclid_contDiffOn (I := I) g α)
    hK_compact hK_meas hK_in
  rw [← hμ_def] at hC₀
  refine ⟨C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans (hC₀ _) ?_
  calc
    ENNReal.ofReal C₀ * eLpNorm
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)) 2 μ
        ≤ ENNReal.ofReal C₀ *
          (ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
          gcongr
          exact hAtomE_bd i
    _ = ENNReal.ofReal (C₀ * CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, mul_assoc C₀ CatomE]

end SharpAtomBounds

/-! ## Sharp `eLpNorm` bound for the differentiated chart-RHS numerator

The sharp companion of `eigenvectorChartRHSDiffNumerator_eLpNorm_le_uniform`:
takes a *direct quantitative `eLpNorm` bound* on each of the five layer atoms
of the differentiated chart-RHS numerator (one per layer) and concludes a sharp
`eLpNorm` bound on the numerator itself, of the form

```
eLpNorm (numerator) 2 μ
  ≤ ENNReal.ofReal (C · (i.fst.val)⁻¹^e) ·
      ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖,
```

where `μ = volume.restrict (chartPouKernel α)`, `e := max(eAtomA, eAtomB,
eAtomC, eAtomD, eAtomE)`, and `C` is the appropriate geometric combination of
the per-layer constants and the per-layer input atom constants. NO
`diffNumeratorAggregate` appears on the right.

The proof composes the five sharp per-layer bounds
`eigenvectorChartRHSDiffNumerator_layerX_eLpNorm_le_chartcpt` via iterated
Minkowski (`eLpNorm_add_le` / `eLpNorm_sub_le`); the per-layer `μ⁻¹^eAtomX`
exponents are uniformly promoted to `μ⁻¹^e` via `pow_le_pow_right₀` (the
resolvent eigenvalue is in `(0, 1]`, so `μ⁻¹ ≥ 1`). -/

section SharpMainBound

omit [CompleteSpace E] in
/-- The resolvent eigenvalue lies in the unit interval `(0, 1]`; this is the
quantitative spectrum statement used to compare the per-layer
`(i.fst.val)⁻¹^eAtomX` factors via `pow_le_pow_right₀`. -/
private lemma eigen_inv_one_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    1 ≤ (i.fst.val)⁻¹ := by
  have h_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s) h_atlas).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  exact (one_le_inv₀ hμ_pos).mpr hμ_le_one

omit [CompleteSpace E] in
/-- A per-layer `(i.fst.val)⁻¹^k` factor is dominated by `(i.fst.val)⁻¹^e`
when `k ≤ e`, since the resolvent eigenvalue lies in `(0, 1]` (so `μ⁻¹ ≥ 1`)
and `pow` is monotone in the exponent for bases `≥ 1`. -/
private lemma pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {k e : ℕ} (hke : k ≤ e) :
    (i.fst.val)⁻¹ ^ k ≤ (i.fst.val)⁻¹ ^ e := by
  exact pow_le_pow_right₀
    (eigen_inv_one_le (I := I) (M := M) g r s h_atlas i) hke

omit [CompleteSpace E] in
/-- For a nonnegative `C` and `k ≤ e`, `ofReal (C · μ⁻¹^k) ≤ ofReal (C ·
μ⁻¹^e)`, where `μ = i.fst.val` is the resolvent eigenvalue. The exponent
unification step used to homogenise the five per-layer `μ⁻¹^eAtomX` factors. -/
private lemma ofReal_const_pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {C : ℝ} (hC_nn : 0 ≤ C) {k e : ℕ} (hke : k ≤ e) :
    ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ k) ≤
      ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) := by
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_left
    (pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i hke) hC_nn

omit [CompleteSpace E] in
/-- **Sharp `eLpNorm` bound for the differentiated chart-RHS numerator.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis-uniform
chart-effective-previous-level data `fChartEffPrev`, a chart center `α : M`, a
component multi-index `P₀`, a level `m`, a direction multi-index
`l : Fin (m + 1) → Fin n`, and *five direct quantitative `eLpNorm`
hypotheses* — one per layer — bounding each layer's atom in the form
`eLpNorm atom 2 μ ≤ ofReal (CatomX · μ⁻¹^eAtomX) · ofReal ‖vec_i‖`, where
`μ = volume.restrict (chartPouKernel α)`, `μ⁻¹ = (i.fst.val)⁻¹`, and
`vec_i = tensorResolventEigenbasisVec h_atlas i`, there is a nonnegative
constant `C` and an exponent `e : ℕ` — `C` geometric (the combined sup-norms of
the `C^∞` chart-target coefficients, times the per-layer atom constants
`CatomA · … · CatomE`), `e` the maximum of the five per-layer exponents — such
that for *every* eigenbasis index `i`,

```
eLpNorm (numerator) 2 (volume.restrict (chartPouKernel α))
  ≤ ENNReal.ofReal (C · (i.fst.val)⁻¹^e) · ofReal ‖vec_i‖.
```

The output `(C, e)` carries no `diffNumeratorAggregate` factor on the
right-hand side: every input hypothesis already pegs each atom's `eLpNorm` to
the eigenvalue / eigenvector data directly, so the assembled bound is sharp.

The proof structure mirrors `eigenvectorChartRHSDiffNumerator_eLpNorm_le_uniform`:
the five layers are bounded individually via the five sharp per-layer bounds
`eigenvectorChartRHSDiffNumerator_layerX_eLpNorm_le_chartcpt`; their exponents
are unified to `e := max(eAtomA, eAtomB, eAtomC, eAtomD, eAtomE)` via
`pow_le_pow_right₀` (using `μ⁻¹ ≥ 1`, which holds because `μ ∈ (0, 1]`); the
iterated triangle inequality on `+ B - C + D + E` over the five layers gives
the assembled bound. -/
theorem eigenvectorChartRHSDiffNumerator_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    -- Genuine measurability of the previous-level data — needed for the iterated
    -- Minkowski combination of the five layers.
    (h_prev_aesm : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      AEStronglyMeasurable (fChartEffPrev i)
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α)))
    -- Layer A atom: eLpNorm of (m+1)-fold partial.
    (CatomA : ℝ) (eAtomA : ℕ) (hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    -- Layer B atom: eLpNorm of chosenWeakPartial b ((m+1)-fold).
    (CatomB : ℝ) (eAtomB : ℕ) (hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    -- Layer C atom: eLpNorm of m-fold partial.
    (CatomC : ℝ) (eAtomC : ℕ) (hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    -- Layer D atom: eLpNorm of fChartEffPrev i.
    (CatomD : ℝ) (eAtomD : ℕ) (hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (fChartEffPrev i) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    -- Layer E atom: eLpNorm of chosen_weak_partial of fChartEffPrev.
    (CatomE : ℝ) (eAtomE : ℕ) (hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i)
            (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s h_atlas i α P₀ m l (fChartEffPrev i) y) 2
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The five sharp per-layer bounds, hoisting the geometric constants before `∀ i`.
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_eLpNorm_le_chartcpt
      (I := I) (M := M) g r s h_atlas α P₀ m l CatomA eAtomA hCatomA_nn hAtomA_bd
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_eLpNorm_le_chartcpt
      (I := I) (M := M) g r s h_atlas α P₀ m l CatomB eAtomB hCatomB_nn hAtomB_bd
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_eLpNorm_le_chartcpt
      (I := I) (M := M) g r s h_atlas α P₀ m l CatomC eAtomC hCatomC_nn hAtomC_bd
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_eLpNorm_le_chartcpt
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev CatomD eAtomD
      hCatomD_nn hAtomD_bd
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_eLpNorm_le_chartcpt
      (I := I) (M := M) g r s h_atlas α P₀ m l fChartEffPrev CatomE eAtomE
      hCatomE_nn hAtomE_bd
  -- The headline exponent: the maximum of the five per-layer exponents.
  set e : ℕ := max (max eAtomA (max eAtomB eAtomC)) (max eAtomD eAtomE)
    with he_def
  have heA : eAtomA ≤ e := le_max_of_le_left (le_max_left _ _)
  have heB : eAtomB ≤ e := le_max_of_le_left (le_trans (le_max_left _ _)
    (le_max_right _ _))
  have heC : eAtomC ≤ e := le_max_of_le_left (le_trans (le_max_right _ _)
    (le_max_right _ _))
  have heD : eAtomD ≤ e := le_max_of_le_right (le_max_left _ _)
  have heE : eAtomE ≤ e := le_max_of_le_right (le_max_right _ _)
  -- Per-layer nonneg products.
  have hCA_prod_nn : 0 ≤ CA * CatomA := mul_nonneg hCA_nn hCatomA_nn
  have hCB_prod_nn : 0 ≤ CB * CatomB := mul_nonneg hCB_nn hCatomB_nn
  have hCC_prod_nn : 0 ≤ CC * CatomC := mul_nonneg hCC_nn hCatomC_nn
  have hCD_prod_nn : 0 ≤ CD * CatomD := mul_nonneg hCD_nn hCatomD_nn
  have hCE_prod_nn : 0 ≤ CE * CatomE := mul_nonneg hCE_nn hCatomE_nn
  -- The headline constant: the sum of the five per-layer products.
  refine ⟨CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD + CE * CatomE,
    e, by positivity, fun i => ?_⟩
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The five layers, as functions `EuclN → ℝ`.
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  -- The numerator is, pointwise, `layerA + layerB - layerC + layerD + layerE`.
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l (fChartEffPrev i) y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  -- `MemLp` of each layer (for the iterated-triangle-inequality measurability).
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  -- Layer A: `MemLp 2 μ`.
  have hA_mem : MemLp layerA 2 μ := by
    rw [hlayerA_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    have h_atom_mem := iter_memLp_volume_restrict
      (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
      (Fin.cons a (Fin.init l)) hK_meas hK_in
    rw [← hμ_def] at h_atom_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in h_atom_mem
  -- Layer B: `MemLp 2 μ`.
  have hB_mem : MemLp layerB 2 μ := by
    rw [hlayerB_def]
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_chosen_mem := chosenWp_memLp_volume_restrict b
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ω := chartTargetEuclid (I := I) (M := M) α)
      hK_meas hK_in
    rw [← hμ_def] at h_chosen_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in h_chosen_mem
  -- Layer C: `MemLp 2 μ`.
  have hC_mem : MemLp layerC 2 μ := by
    rw [hlayerC_def]
    have h_atom_mem := iter_memLp_volume_restrict
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l) hK_meas hK_in
    rw [← hμ_def] at h_atom_mem
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_atom_mem
  -- Layer D and E will use the layer-D and layer-E `_le_chartcpt` MemLp side,
  -- which we get from the per-layer bound itself. But we need `MemLp` to invoke
  -- iterated triangle inequality on `+ B - C + D + E`. We exhibit `MemLp 2 μ`
  -- for layers `D` and `E` directly via `memLp_volume_compact_contDiffOn_mul`.
  -- For layer `D` we need `MemLp (fChartEffPrev i) 2 μ`; from `hAtomD_bd` we
  -- have `eLpNorm (fChartEffPrev i) 2 μ < ⊤` (since the RHS is `< ⊤`).
  -- However, an `eLpNorm` bound alone doesn't immediately give `MemLp` (the
  -- aestronglyMeasurable side is missing). To stay self-contained we ask: does
  -- the hypothesis `hAtomD_bd` give `aestronglyMeasurable`? No — only the
  -- `eLpNorm` bound. We therefore need to bound by triangle inequality the
  -- combined `+B - C + D + E` directly: `eLpNorm_add_le` and `eLpNorm_sub_le`
  -- only need `aestronglyMeasurable` of each side, not full `MemLp`. The
  -- layers `A, B, C` have full `MemLp`; for `D, E` we use the
  -- `aestronglyMeasurable` of the layer functions themselves, which holds
  -- since `densityDerivOnEuclid` and `densityOnEuclid` are continuous (hence
  -- `AEStronglyMeasurable`) and the chosen weak partial is `AEStronglyMeasurable`
  -- by `chosenWp_memLp_volume_restrict`. We package these as `AEStronglyMeasurable`
  -- of the layer functions.
  have h_aesm_D : AEStronglyMeasurable layerD μ := by
    rw [hlayerD_def]
    have h_dens_cts : ContinuousOn (densityDerivOnEuclid (I := I) g α
        (l (Fin.last m))) (chartTargetEuclid (I := I) (M := M) α) :=
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m))).continuousOn
    have h_dens_aesm : AEStronglyMeasurable
        (densityDerivOnEuclid (I := I) g α (l (Fin.last m))) μ := by
      have h_K : AEStronglyMeasurable
          (densityDerivOnEuclid (I := I) g α (l (Fin.last m)))
          ((volume : Measure EuclN).restrict K) :=
        (h_dens_cts.mono hK_in).aestronglyMeasurable hK_meas
      simpa [hμ_def, hK_def] using h_K
    exact h_dens_aesm.mul (h_prev_aesm i)
  have h_aesm_E : AEStronglyMeasurable layerE μ := by
    rw [hlayerE_def]
    have h_dens_cts : ContinuousOn (densityOnEuclid (I := I) g α)
        (chartTargetEuclid (I := I) (M := M) α) :=
      (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
    have h_dens_aesm : AEStronglyMeasurable
        (densityOnEuclid (I := I) g α) μ := by
      have h_K : AEStronglyMeasurable
          (densityOnEuclid (I := I) g α)
          ((volume : Measure EuclN).restrict K) :=
        (h_dens_cts.mono hK_in).aestronglyMeasurable hK_meas
      simpa [hμ_def, hK_def] using h_K
    have h_chosen_mem := chosenWp_memLp_volume_restrict (l (Fin.last m))
      (fChartEffPrev i) (Ω := chartTargetEuclid (I := I) (M := M) α)
      hK_meas hK_in
    rw [← hμ_def] at h_chosen_mem
    exact h_dens_aesm.mul h_chosen_mem.aestronglyMeasurable
  -- The five per-layer `eLpNorm` bounds at `i`. Since `μ := volume.restrict K`
  -- and `Rhs := ofReal ‖vec_i‖` are `set`-bindings, they are definitionally
  -- equal to the explicit expressions in the per-layer bounds; we keep them
  -- abbreviated `μ` and `Rhs` here for readability.
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  -- Promote per-layer exponents to `e` via `pow_le_pow_right₀` (uses `μ⁻¹ ≥ 1`).
  have hCA_e : eLpNorm layerA 2 μ ≤
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCA_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i
      hCA_prod_nn heA
  have hCB_e : eLpNorm layerB 2 μ ≤
      ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCB_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i
      hCB_prod_nn heB
  have hCC_e : eLpNorm layerC 2 μ ≤
      ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCC_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i
      hCC_prod_nn heC
  have hCD_e : eLpNorm layerD 2 μ ≤
      ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCD_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i
      hCD_prod_nn heD
  have hCE_e : eLpNorm layerE 2 μ ≤
      ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans hCE_i (mul_le_mul' ?_ (le_refl _))
    exact ofReal_const_pow_eigen_inv_le (I := I) (M := M) g r s h_atlas i
      hCE_prod_nn heE
  rw [h_num_eq]
  -- Iterated Minkowski over the five layers `A + B - C + D + E`.
  have h_tri :
      eLpNorm (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) 2 μ
        ≤ eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
          + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ := by
    have h_pi : (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
        = layerA + layerB - layerC + layerD + layerE := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_pi]
    have hAB_aesm : AEStronglyMeasurable (layerA + layerB) μ :=
      hA_mem.aestronglyMeasurable.add hB_mem.aestronglyMeasurable
    have hABC_aesm : AEStronglyMeasurable (layerA + layerB - layerC) μ :=
      hAB_aesm.sub hC_mem.aestronglyMeasurable
    have hABCD_aesm : AEStronglyMeasurable
        (layerA + layerB - layerC + layerD) μ :=
      hABC_aesm.add h_aesm_D
    refine le_trans (eLpNorm_add_le hABCD_aesm h_aesm_E (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hABC_aesm h_aesm_D (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hAB_aesm
      hC_mem.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_add_le hA_mem.aestronglyMeasurable
      hB_mem.aestronglyMeasurable (by norm_num)
  refine le_trans h_tri ?_
  -- Each of the five per-layer `eLpNorm`s is `≤ ofReal (CX * CatomX * μ⁻¹^e) * Rhs`.
  have h_five :
      eLpNorm layerA 2 μ + eLpNorm layerB 2 μ + eLpNorm layerC 2 μ
        + eLpNorm layerD 2 μ + eLpNorm layerE 2 μ
      ≤ ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_e hCB_e) hCC_e) hCD_e)
      hCE_e
  refine le_trans h_five ?_
  -- Collect the five `ofReal (CX * CatomX * μ⁻¹^e) * Rhs` terms into a single
  -- `ofReal ((CA·CatomA + … + CE·CatomE) * μ⁻¹^e) * Rhs`.
  set μi : ℝ := (i.fst.val)⁻¹ ^ e with hμi_def
  have hμi_nn : 0 ≤ μi := by
    rw [hμi_def]
    have h1 : 1 ≤ (i.fst.val)⁻¹ :=
      eigen_inv_one_le (I := I) (M := M) g r s h_atlas i
    have : 0 ≤ (i.fst.val)⁻¹ := le_trans zero_le_one h1
    exact pow_nonneg this _
  -- Rewrite `CX * CatomX * μ⁻¹^e = (CX * CatomX) * μi`.
  have h_pull :
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
            CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
    -- Repeatedly use `ofReal_add` to combine and `add_mul`.
    have hp1 : 0 ≤ CA * CatomA + CB * CatomB := add_nonneg hCA_prod_nn hCB_prod_nn
    have hp2 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC :=
      add_nonneg hp1 hCC_prod_nn
    have hp3 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD :=
      add_nonneg hp2 hCD_prod_nn
    -- Combine the five `ENNReal.ofReal` terms.
    have h_sum_ofReal :
        ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)
          = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) := by
      rw [add_mul, add_mul, add_mul, add_mul,
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCE_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCD_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCC_prod_nn hμi_nn),
        ENNReal.ofReal_add (mul_nonneg hCA_prod_nn hμi_nn)
          (mul_nonneg hCB_prod_nn hμi_nn)]
    calc ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = (ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)) * Rhs := by
          rw [add_mul, add_mul, add_mul, add_mul]
      _ = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
          rw [h_sum_ofReal]
  rw [h_pull]

end SharpMainBound

/-! ## Sanity test -/

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) 1 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α → fChartEffPrev y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s h_atlas i α P₀ m l fChartEffPrev y) 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev :=
  eigenvectorChartRHSDiffNumerator_eLpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev h_iter h_prev h_prev_zero

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
