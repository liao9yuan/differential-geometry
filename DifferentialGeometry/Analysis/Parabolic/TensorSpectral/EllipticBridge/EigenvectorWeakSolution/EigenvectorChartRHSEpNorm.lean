import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRotationENormBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderENormBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDivENormBound

/-!
# The explicit-norm `eLpNorm` bound for the eigenvector chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, and a
component multi-index `P₀`, the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s h_atlas i α P₀` of the eigenvector weak-solution
assembly is the explicit `densityOnEuclid`-and-`C^∞`-coefficient-weighted
seven-term bracket combination scaled overall by `μ⁻¹`.

This file records the quantitative twin of the qualitative weighted-`L²`
membership `eigenvectorChartRHS_memLp_weighted`: there is a nonnegative constant
`C` with

```
eLpNorm (eigenvectorChartRHS g r s h_atlas i α P₀) 2 μw
  ≤ ENNReal.ofReal (μ⁻¹ * C) * <AGGREGATE>,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` and
`<AGGREGATE>` is the honest finite sum of the weighted `eLpNorm`s of the source
quantities of the bracket:

* the canonical eigenvector chart component `eigenvectorChartComponentFun`;
* the cross-left limit objects `crossLeftLimitComponent` (summed over the
  rank-`(r, s + 1)` component multi-indices);
* the cross-right limit objects `crossRightLimitComponent` (summed over the
  rank-`(r, s)` component multi-indices);
* the chart-partial atoms `partialLpLimit` (summed over component multi-index
  and chart direction);
* the chart-component atoms `componentLpLimit` (summed over the component
  multi-indices);
* the cutoff chart-partial atoms `cutoffPartialLpLimit` (summed over component
  multi-index and chart direction).

## Strategy

The bracket is the `μ⁻¹`-scalar multiple of a seven-term `+`/`-` combination of
functions `EuclN → ℝ`. By the homogeneity `eLpNorm (c • f) = ‖c‖ₑ · eLpNorm f`
the overall `eLpNorm` is `‖μ⁻¹‖ₑ` times the `eLpNorm` of the bracket, and
`‖μ⁻¹‖ₑ = ENNReal.ofReal μ⁻¹` since the resolvent eigenvalue lies in `(0, 1]`.

Iterated Minkowski (`eLpNorm_add_le` / `eLpNorm_sub_le`) bounds the `eLpNorm` of
the seven-term bracket by the sum of the `eLpNorm`s of the seven terms. Each
term is then bounded by a constant times a sub-aggregate of the source
quantities:

* the canonical eigenvector chart-component term is the source quantity itself;
* the two cross-Leibniz double-sum terms have, per summand, a `C^∞` coefficient
  product (`covChartMetricGram · crossLeftTestCoeff`, respectively
  `covChartMetricGram · crossRightTestValueCoeff`) and an `L²` cross-limit atom
  that vanishes almost everywhere off the compact cutoff chart kernel; the
  explicit-norm coefficient bound `eLpNorm_weighted_contDiffOn_mul_le` and the
  triangle inequality control them;
* the two lower-order coefficient-limit terms are bounded directly by the
  companion lemmas `eLpNorm_covPrincipalRotationCoeffLimit_le` and
  `eLpNorm_covLowerOrderRotationValueCoeffLimit_le`;
* the two divergence-limit terms are products of the `C^∞` reciprocal chart
  density `1 / densityOnEuclid g α` with a divergence limit; the explicit-norm
  coefficient bound and the companion lemmas
  `eLpNorm_weightedGradCoeffDivLimit_le` and
  `eLpNorm_crossRightGradCoeffDivLimit_le` control them.

Every sub-aggregate is dominated by the full aggregate (the weighted `eLpNorm`s
are nonnegative `ℝ≥0∞` quantities), so the seven per-term constants and the
finite-sum multiplicities fold into a single nonnegative constant `C`.

## Main result

* `eigenvectorChartRHS_eLpNorm_le` — the explicit-norm `eLpNorm` bound for the
  eigenvector chart right-hand side.

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## A finite-sum aggregation lemma

A finite indexed family of summands `F j`, each weighted-`MemLp` and each having
its `eLpNorm` bounded by `ENNReal.ofReal Cⱼ` times one *fixed* aggregate
`ℝ≥0∞`-quantity `A`, has its summed `eLpNorm` bounded by `ENNReal.ofReal` of an
explicit constant times `A`. The explicit constant is the sum of all the
per-summand constants times the cardinality of the index type; the triangle
inequality `eLpNorm_sum_le` and the monotonicity of `ENNReal.ofReal` assemble it.
-/

section Aggregation

-- The aggregation step is established purely from the triangle inequality and
-- arithmetic of `ℝ≥0∞`; the finite-dimensionality, manifold-completeness and
-- closed-manifold instances enter only through the type of the chart-pulled
-- weighted measure and play no role in the proof term.
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- A finite indexed family of weighted-`MemLp` summands, each `eLpNorm`-bounded
by `ENNReal.ofReal Cⱼ` times a fixed aggregate quantity `A`, has its summed
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
  -- Extract a per-summand nonnegative constant and bound.
  choose Cf hCf_nn hCf using hbd
  -- The headline constant: the sum of the per-summand constants times the
  -- cardinality of the (finite) index type.
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  -- The function `fun y => ∑ j, F j y` is the `Finset.sum` of the `F j`.
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  -- The triangle inequality `eLpNorm_sum_le`.
  have h_tri : eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, eLpNorm (F j) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  -- Each per-summand `eLpNorm` is `≤ ENNReal.ofReal (∑ Cf) * A`: bound the
  -- per-summand constant `Cf j` by the whole nonnegative sum `∑ Cf`.
  have h_step : ∑ j : ι, eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  -- The constant sum is `card • (ENNReal.ofReal (∑ Cf) * A)`.
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Reassociate `card * ENNReal.ofReal (∑ Cf)` into a single `ENNReal.ofReal`.
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

end Aggregation

/-- The conversion `ENNReal.ofReal 2 = (2 : ℝ≥0∞)`, recorded once for reuse in
the constant-folding of the two-piece aggregate bounds. -/
private lemma ofReal_two : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
  norm_num

/-! ## The seven bracket terms as functions `EuclN → ℝ`

The bracket of `eigenvectorChartRHS` is, term by term, a function `EuclN → ℝ`.
We name the seven terms so the `eLpNorm` triangle inequality and the
per-term bounds can be stated cleanly. -/

section BracketTerms

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

/-- Bracket term 1: the canonical eigenvector chart `P₀`-component. -/
private def rhsTerm1 : EuclN → ℝ :=
  eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀

/-- Bracket term 2: the cross-left limit double-sum contribution. -/
private def rhsTerm2 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
    ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

/-- Bracket term 3: the cross-right value-coefficient double-sum contribution. -/
private def rhsTerm3 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r s,
    ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

/-- Bracket term 4: the principal rotation coefficient limit. -/
private def rhsTerm4 : EuclN → ℝ :=
  covPrincipalRotationCoeffLimit (I := I) (M := M) g r s h_atlas i α P₀

/-- Bracket term 5: the lower-order rotation value coefficient limit. -/
private def rhsTerm5 : EuclN → ℝ :=
  covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s h_atlas i α P₀

/-- Bracket term 6: the chart-density-weighted lower-order gradient divergence
limit. -/
private def rhsTerm6 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M) g r s h_atlas i α P₀ l y)

/-- Bracket term 7: the chart-density-weighted cross-right gradient divergence
limit. -/
private def rhsTerm7 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    crossRightGradCoeffDivLimit (I := I) (M := M) g r s h_atlas i α P₀ y

/-- The seven-term bracket of `eigenvectorChartRHS`, as a function `EuclN → ℝ`
built from `Pi`-algebra operations on the seven terms. -/
private def rhsBracket : EuclN → ℝ :=
  rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀ -
      rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀ +
      rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀ -
      rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀ -
      rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀ +
      rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀ -
      rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀

omit [CompleteSpace E] in
/-- `eigenvectorChartRHS` is the `μ⁻¹`-scalar multiple of the seven-term bracket
`rhsBracket`. -/
private lemma eigenvectorChartRHS_eq_smul_bracket :
    eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀
      = (i.fst.val)⁻¹ • rhsBracket (I := I) (M := M) g r s h_atlas i α P₀ := by
  funext y
  simp only [eigenvectorChartRHS, rhsBracket, rhsTerm1, rhsTerm2, rhsTerm3,
    rhsTerm4, rhsTerm5, rhsTerm6, rhsTerm7, eigenvectorChartComponentFun,
    Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]

end BracketTerms

/-! ## Weighted-`L²` membership of the seven bracket terms

Each of the seven bracket terms is weighted-`MemLp`; this is the term-by-term
content of the proof of `eigenvectorChartRHS_memLp_weighted`. The membership is
needed both to feed the `eLpNorm` triangle inequality (via almost-everywhere
strong measurability) and, for the divergence-term coefficient bounds, to feed
the explicit-norm coefficient lemma `eLpNorm_weighted_contDiffOn_mul_le`. -/

section TermMemLp

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target. -/
private lemma one_div_densityOnEuclid_contDiffOn :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-- Weighted-`L²` membership of bracket term 1. -/
private lemma rhsTerm1_memLp :
    MemLp (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm1 eigenvectorChartComponentFun
  exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀

/-- Weighted-`L²` membership of each cross-left double-sum summand. -/
private lemma rhsTerm2_summand_memLp
    (P Q : TensorCompIdx (E := E) r (s + 1)) :
    MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The cross-left limit vanishes almost everywhere off the compact cutoff
  -- chart kernel.
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossLeftLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
      (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P)
    h_aezero

/-- Weighted-`L²` membership of bracket term 2. -/
private lemma rhsTerm2_memLp :
    MemLp (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold rhsTerm2
  exact memLp_finset_sum _
    (fun P _ => memLp_finset_sum _
      (fun Q _ => rhsTerm2_summand_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ P Q))

/-- Weighted-`L²` membership of each cross-right double-sum summand. -/
private lemma rhsTerm3_summand_memLp
    (P Q : TensorCompIdx (E := E) r s) :
    MemLp
      (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The cross-right limit vanishes almost everywhere off the compact cutoff
  -- chart kernel.
  have h_aezero :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    rw [crossRightLimitComponent]
    exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
      (I := I) (M := M) g r s
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P)
    h_aezero

/-- Weighted-`L²` membership of bracket term 3. -/
private lemma rhsTerm3_memLp :
    MemLp (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold rhsTerm3
  exact memLp_finset_sum _
    (fun P _ => memLp_finset_sum _
      (fun Q _ => rhsTerm3_summand_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ P Q))

/-- Weighted-`L²` membership of bracket term 4. -/
private lemma rhsTerm4_memLp :
    MemLp (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [rhsTerm4]
  exact covPrincipalRotationCoeffLimit_memLp_weighted (I := I) (M := M)
    g r s h_atlas i α P₀

/-- Weighted-`L²` membership of bracket term 5. -/
private lemma rhsTerm5_memLp :
    MemLp (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [rhsTerm5]
  exact covLowerOrderRotationValueCoeffLimit_memLp_weighted (I := I) (M := M)
    g r s h_atlas i α P₀

/-- The finite sum over chart directions of the lower-order gradient-divergence
limit is weighted-`MemLp`. -/
private lemma weightedGradCoeffDivLimit_sum_memLp :
    MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ l y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  exact memLp_finset_sum _
    (fun l _ => weightedGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P₀ l)

/-- The finite sum over chart directions of the lower-order gradient-divergence
limit vanishes almost everywhere off the compact partition-of-unity kernel. -/
private lemma weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y) = 0 :=
  Filter.Eventually.of_forall (fun _y hy =>
    Finset.sum_eq_zero (fun l _ =>
      weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ l hy))

/-- Weighted-`L²` membership of bracket term 6. -/
private lemma rhsTerm6_memLp :
    MemLp (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm6
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (weightedGradCoeffDivLimit_sum_memLp (I := I) (M := M)
      g r s h_atlas i α P₀)
    (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s h_atlas i α P₀)

/-- The cross-right gradient-divergence limit is weighted-`MemLp`: it is
`MemLp 2` of the plain restricted volume and vanishes pointwise off the compact
partition-of-unity kernel. -/
private lemma crossRightGradCoeffDivLimit_memLp_weighted :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s h_atlas i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M) g r s h_atlas i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ hy))
    h_plain

/-- Weighted-`L²` membership of bracket term 7. -/
private lemma rhsTerm7_memLp :
    MemLp (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold rhsTerm7
  exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P₀)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ hy))

end TermMemLp

/-! ## The source-quantity aggregate

The aggregate against which the chart right-hand side `eLpNorm` is bounded is
the finite sum of the weighted `eLpNorm`s of the six source-quantity families
plus the canonical eigenvector chart component. -/

section Aggregate

/-- The weighted `eLpNorm` of the canonical eigenvector chart component. The
component index `P₀` is a genuine parameter. -/
private def aggrUchart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
      g r s h_atlas i α P₀) 2
    ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α))

/-- The summed weighted `eLpNorm`s of the cross-left limit objects. The
component index `_P₀` is carried for uniform aggregate API but the cross-left
limit objects do not depend on it. -/
private def aggrCrossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r (s + 1),
    eLpNorm ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

/-- The summed weighted `eLpNorm`s of the cross-right limit objects. The
component index `_P₀` is carried for uniform aggregate API. -/
private def aggrCrossRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    eLpNorm ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

/-- The summed weighted `eLpNorm`s of the chart-partial atoms. The component
index `_P₀` is carried for uniform aggregate API. -/
private def aggrPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      eLpNorm ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

/-- The summed weighted `eLpNorm`s of the chart-component atoms. The component
index `_P₀` is carried for uniform aggregate API. -/
private def aggrComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    eLpNorm ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

/-- The summed weighted `eLpNorm`s of the cutoff chart-partial atoms. The
component index `_P₀` is carried for uniform aggregate API. -/
private def aggrCutoffPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M) g r s h_atlas i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))

/-- The full source-quantity aggregate of the chart right-hand side: the sum of
the weighted `eLpNorm`s of the canonical eigenvector chart component and the six
source-quantity families. -/
private def rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  aggrUchart (I := I) (M := M) g r s h_atlas i α P₀ +
    aggrCrossLeft (I := I) (M := M) g r s h_atlas i α P₀ +
    aggrCrossRight (I := I) (M := M) g r s h_atlas i α P₀ +
    aggrPartial (I := I) (M := M) g r s h_atlas i α P₀ +
    aggrComponent (I := I) (M := M) g r s h_atlas i α P₀ +
    aggrCutoffPartial (I := I) (M := M) g r s h_atlas i α P₀

/-- Each of the six summands of a six-fold `ℝ≥0∞` sum is dominated by the sum.
This pure-arithmetic lemma over abstract `ℝ≥0∞` atoms keeps the six aggregate
domination lemmas free of any unification over the (large) `aggr*` terms. -/
private lemma le_sixSum (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
  · exact le_add_self

omit [CompleteSpace E] in
/-- The canonical eigenvector chart-component aggregate piece is dominated by
the full aggregate. -/
private lemma aggrUchart_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrUchart (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).1

omit [CompleteSpace E] in
/-- The cross-left aggregate piece is dominated by the full aggregate. -/
private lemma aggrCrossLeft_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCrossLeft (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).2.1

omit [CompleteSpace E] in
/-- The cross-right aggregate piece is dominated by the full aggregate. -/
private lemma aggrCrossRight_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCrossRight (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).2.2.1

omit [CompleteSpace E] in
/-- The chart-partial aggregate piece is dominated by the full aggregate. -/
private lemma aggrPartial_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrPartial (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.1

omit [CompleteSpace E] in
/-- The chart-component aggregate piece is dominated by the full aggregate. -/
private lemma aggrComponent_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrComponent (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.1

omit [CompleteSpace E] in
/-- The cutoff chart-partial aggregate piece is dominated by the full
aggregate. -/
private lemma aggrCutoffPartial_le_rhsAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    aggrCutoffPartial (I := I) (M := M) g r s h_atlas i α P₀
      ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  rw [rhsAggregate]
  exact (le_sixSum _ _ _ _ _ _).2.2.2.2.2

end Aggregate

/-! ## The per-term explicit-norm bounds

Each of the seven bracket terms is bounded by an explicit nonnegative constant
times the full source-quantity aggregate. -/

section TermBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
/-- Bracket term 1 is the canonical eigenvector chart component, so its
`eLpNorm` is exactly the first aggregate piece — bounded by the full
aggregate with constant `1`. -/
private lemma rhsTerm1_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  refine ⟨1, by norm_num, ?_⟩
  rw [rhsTerm1, ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)

/-- Bracket term 2 is bounded by an explicit constant times the full aggregate.
Each cross-left double-sum summand has a `C^∞` coefficient product and a
cross-left limit atom; the explicit-norm coefficient bound controls the summand
by a constant times the atom's `eLpNorm`, the atom's `eLpNorm` is dominated by
the cross-left aggregate piece, and the aggregation lemma sums it up. -/
private lemma rhsTerm2_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The cross-left double-sum summand, indexed by the pair `(P, Q)`.
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  -- Per summand: weighted-`MemLp` and an explicit-norm bound by the aggregate.
  have h_data : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1),
      MemLp (F x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (F x) 2 μw
            ≤ ENNReal.ofReal C *
              rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro x
    refine ⟨?_, ?_⟩
    · rw [hμw_def, hF_def]
      exact rhsTerm2_summand_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ x.1 x.2
    -- The cross-left limit vanishes a.e. off the compact cutoff chart kernel.
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α x.1
    -- The explicit-norm coefficient bound.
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1)
      h_aezero
    refine ⟨C, hC_nn, ?_⟩
    -- The atom's `eLpNorm` is dominated by the cross-left aggregate piece.
    have h_atom_le :
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      refine le_trans ?_
        (aggrCrossLeft_le_rhsAggregate (I := I) (M := M)
          g r s h_atlas i α P₀)
      rw [hμw_def, aggrCrossLeft]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans hC_bd ?_
    gcongr
  -- The aggregation lemma assembles the double sum.
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate
    (μ := μw) F (rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  -- Identify the single-product sum with the nested double sum.
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), F x y)
      = rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀ := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd

/-- Bracket term 3 is bounded by an explicit constant times the full aggregate.
The argument mirrors that of term 2 with the cross-right limit objects. -/
private lemma rhsTerm3_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The cross-right double-sum summand, indexed by the pair `(P, Q)`.
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s,
      MemLp (F x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (F x) 2 μw
            ≤ ENNReal.ofReal C *
              rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro x
    refine ⟨?_, ?_⟩
    · rw [hμw_def, hF_def]
      exact rhsTerm3_summand_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ x.1 x.2
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α x.1
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1)
      h_aezero
    refine ⟨C, hC_nn, ?_⟩
    have h_atom_le :
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      refine le_trans ?_
        (aggrCrossRight_le_rhsAggregate (I := I) (M := M)
          g r s h_atlas i α P₀)
      rw [hμw_def, aggrCrossRight]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans hC_bd ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate
    (μ := μw) F (rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, F x y)
      = rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀ := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd

/-- Bracket term 4 is bounded by an explicit constant times the full aggregate:
the companion lemma `eLpNorm_covPrincipalRotationCoeffLimit_le` bounds it by a
constant times the chart-partial aggregate piece, which is dominated by the full
aggregate. -/
private lemma rhsTerm4_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_covPrincipalRotationCoeffLimit_le
    (I := I) (M := M) g r s h_atlas i α P₀
  refine ⟨C, hC_nn, ?_⟩
  rw [rhsTerm4]
  refine le_trans hC_bd ?_
  gcongr
  -- The chart-partial aggregate piece is exactly the companion lemma's RHS sum.
  exact aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀

/-- Bracket term 5 is bounded by an explicit constant times the full aggregate:
the companion lemma `eLpNorm_covLowerOrderRotationValueCoeffLimit_le` bounds it
by a constant times the sum of the chart-partial and chart-component aggregate
pieces. Each piece is dominated by the full aggregate, so the two-piece sum is
bounded by twice it; doubling the companion constant absorbs the factor. -/
private lemma rhsTerm5_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_covLowerOrderRotationValueCoeffLimit_le
    (I := I) (M := M) g r s h_atlas i α P₀
  -- The headline constant for this term is `2 * C`.
  refine ⟨2 * C, by positivity, ?_⟩
  rw [rhsTerm5]
  -- Bound the companion lemma's two-piece RHS sum by twice the full aggregate.
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
      (aggrComponent_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
  -- Assemble: `eLpNorm ≤ ofReal C * (2-piece sum) ≤ ofReal (2 * C) * aggregate`.
  refine le_trans hC_bd ?_
  calc
    ENNReal.ofReal C *
        ((∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))))
        ≤ ENNReal.ofReal C *
            (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
          mul_comm C 2]

/-- The finite sum over chart directions of the lower-order gradient-divergence
limit is bounded by an explicit constant times the full aggregate. The companion
lemma `eLpNorm_weightedGradCoeffDivLimit_le` bounds each chart-direction summand
by a constant times the sum of the chart-component and chart-partial aggregate
pieces, which is dominated by twice the full aggregate; the aggregation lemma
assembles the chart-direction sum. -/
private lemma weightedGradCoeffDivLimit_sum_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          (fun y => ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Per chart direction `l`: weighted-`MemLp` and an explicit-norm bound by the
  -- full aggregate (the companion lemma's two-piece sum is `≤ 2 * aggregate`).
  have h_data : ∀ l : Fin (Module.finrank ℝ E),
      MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ l) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l) 2 μw
            ≤ ENNReal.ofReal C *
              rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro l
    refine ⟨?_, ?_⟩
    · rw [hμw_def]
      exact weightedGradCoeffDivLimit_memLp_weighted
        (I := I) (M := M) g r s h_atlas i α P₀ l
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weightedGradCoeffDivLimit_le
      (I := I) (M := M) g r s h_atlas i α P₀ l
    -- The companion constant doubled absorbs the two-piece aggregate sum.
    refine ⟨2 * C, by positivity, ?_⟩
    rw [hμw_def]
    refine le_trans hC_bd ?_
    -- The companion lemma's RHS sum is `aggrComponent + aggrPartial`.
    have h_sum_le :
        (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              ∑ l' : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
        ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
        (aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    calc
      ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α))))
          ≤ ENNReal.ofReal C *
              (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  -- The aggregation lemma assembles the chart-direction sum.
  exact eLpNorm_sum_le_const_mul_aggregate
    (μ := μw)
    (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s h_atlas i α P₀ l)
    (rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    (fun l => (h_data l).1) (fun l => (h_data l).2)

/-- Bracket term 6 is bounded by an explicit constant times the full aggregate.
It is the product of the `C^∞` reciprocal chart density with the lower-order
gradient-divergence chart-direction sum; the explicit-norm coefficient bound
`eLpNorm_weighted_contDiffOn_mul_le` and the chart-direction-sum bound combine. -/
private lemma rhsTerm6_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- The explicit-norm coefficient bound for the `1 / densityOnEuclid` factor.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (weightedGradCoeffDivLimit_sum_memLp (I := I) (M := M)
      g r s h_atlas i α P₀)
    (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s h_atlas i α P₀)
  -- The chart-direction-sum bound.
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ := weightedGradCoeffDivLimit_sum_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  -- The headline constant for this term is `C₁ * C₂`.
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  unfold rhsTerm6
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l y)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s h_atlas i α P₀ l y) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
        gcongr
    _ = ENNReal.ofReal (C₁ * C₂) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

/-- Bracket term 7 is bounded by an explicit constant times the full aggregate.
It is the product of the `C^∞` reciprocal chart density with the cross-right
gradient-divergence limit; the explicit-norm coefficient bound and the companion
lemma `eLpNorm_crossRightGradCoeffDivLimit_le` combine. -/
private lemma rhsTerm7_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- The explicit-norm coefficient bound for the `1 / densityOnEuclid` factor.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P₀)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ hy))
  -- The companion lemma for the cross-right gradient-divergence limit.
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ := eLpNorm_crossRightGradCoeffDivLimit_le
    (I := I) (M := M) g r s h_atlas i α P₀
  -- The headline constant for this term is `C₁ * (2 * C₂)`.
  refine ⟨C₁ * (2 * C₂), by positivity, ?_⟩
  unfold rhsTerm7
  -- The companion lemma's RHS sum is `aggrCrossRight + aggrCutoffPartial`.
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          eLpNorm ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ l : Fin (Module.finrank ℝ E),
              eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRight_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
      (aggrCutoffPartial_le_rhsAggregate (I := I) (M := M)
        g r s h_atlas i α P₀)
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)) := by
        gcongr
        exact le_trans hC₂_bd (by gcongr)
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end TermBounds

/-! ## The `eLpNorm` of the seven-term bracket

Iterated Minkowski (`eLpNorm_sub_le` / `eLpNorm_add_le`) bounds the `eLpNorm` of
the seven-term bracket by the sum of the `eLpNorm`s of the seven terms; each is
then bounded by an explicit constant times the full aggregate, and the seven
constants fold into one. -/

section BracketBound

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

/-- **The seven-term bracket `eLpNorm` bound.** The `eLpNorm` of the bracket
`rhsBracket` is bounded by an explicit nonnegative constant times the full
source-quantity aggregate. -/
private lemma rhsBracket_eLpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The seven per-term weighted-`MemLp` memberships.
  have hM1 := rhsTerm1_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM2 := rhsTerm2_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM3 := rhsTerm3_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM4 := rhsTerm4_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM5 := rhsTerm5_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM6 := rhsTerm6_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM7 := rhsTerm7_memLp (I := I) (M := M) g r s h_atlas i α P₀
  rw [← hμw_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  -- The partial-bracket weighted-`MemLp` memberships, built term by term.
  have hB12 := hM1.sub hM2
  have hB123 := hB12.add hM3
  have hB1234 := hB123.sub hM4
  have hB12345 := hB1234.sub hM5
  have hB123456 := hB12345.add hM6
  -- The seven per-term explicit-norm bounds.
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  rw [← hμw_def] at hD1 hD2 hD3 hD4 hD5 hD6 hD7
  -- The headline constant: the sum of the seven per-term constants.
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, ?_⟩
  -- Iterated Minkowski over the seven-term bracket.
  have h_tri :
      eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        ≤ eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw := by
    rw [rhsBracket]
    -- Peel `- T7`, then `+ T6`, then `- T5`, `- T4`, `+ T3`, `- T2`.
    refine le_trans (eLpNorm_sub_le hB123456.aestronglyMeasurable
      hM7.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12345.aestronglyMeasurable
      hM6.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB1234.aestronglyMeasurable
      hM5.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB123.aestronglyMeasurable
      hM4.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12.aestronglyMeasurable
      hM3.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_sub_le hM1.aestronglyMeasurable
      hM2.aestronglyMeasurable (by norm_num)
  -- Each of the seven per-term `eLpNorm`s is `≤ ofReal Dⱼ * aggregate`; the
  -- seven-fold sum is `≤ ofReal (∑ Dⱼ) * aggregate`.
  refine le_trans h_tri ?_
  have h_seven :
      eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
      ≤ ENNReal.ofReal D1 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D2 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D3 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D4 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D5 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D6 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D7 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hD1 hD2) hD3) hD4) hD5) hD6) hD7
  refine le_trans h_seven ?_
  -- Collect the seven `ofReal Dⱼ * aggregate` terms into `ofReal (∑ Dⱼ) *
  -- aggregate` by right-distributivity of `*` over `+` in `ℝ≥0∞`.
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end BracketBound

/-! ## The explicit-norm `eLpNorm` bound for the eigenvector chart right-hand
side -/

section MainBound

omit [CompleteSpace E] in
/-- The resolvent eigenvalue `μ := i.fst.val` is strictly positive: the
eigenspace at `μ` is non-trivial, so it contains a non-zero eigenvector, and the
resolvent eigenvalues lie in the unit interval `(0, 1]`. -/
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  -- Extract a non-zero eigenvector witness from the eigenvalue subtype.
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

/-- **The explicit-norm `eLpNorm` bound for the eigenvector chart right-hand
side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, and a
component multi-index `P₀`, there is a nonnegative constant `C` such that the
weighted `eLpNorm` of the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s h_atlas i α P₀` against the chart-pulled weighted
measure `(chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` is
bounded by `ENNReal.ofReal (μ⁻¹ * C)` times the finite aggregate of the weighted
`eLpNorm`s of the source quantities of the chart right-hand side: the canonical
eigenvector chart component `eigenvectorChartComponentFun`, the cross-left limit
objects `crossLeftLimitComponent`, the cross-right limit objects
`crossRightLimitComponent`, the chart-partial atoms `partialLpLimit`, the
chart-component atoms `componentLpLimit`, and the cutoff chart-partial atoms
`cutoffPartialLpLimit`.

`eigenvectorChartRHS` is the `μ⁻¹`-scalar multiple of the seven-term bracket; by
the homogeneity of `eLpNorm` under scalar multiplication and the positivity of
the resolvent eigenvalue, the overall `eLpNorm` is `ENNReal.ofReal μ⁻¹` times the
`eLpNorm` of the bracket. The seven-term bracket bound `rhsBracket_eLpNorm_le`
controls the latter by an explicit constant times the aggregate; folding the
`μ⁻¹` factor produces the stated estimate. -/
theorem eigenvectorChartRHS_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          (eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r (s + 1),
                eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                      g r s h_atlas i α P l :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The resolvent eigenvalue is strictly positive.
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  -- The seven-term bracket bound.
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_eLpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀
  rw [← hμw_def] at hC_bd
  refine ⟨C, hC_nn, ?_⟩
  -- `eigenvectorChartRHS = μ⁻¹ • rhsBracket`; the `eLpNorm` factors out `‖μ⁻¹‖ₑ`.
  have h_smul_eq :
      eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s h_atlas i α P₀]
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (i.fst.val)⁻¹
      (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀)
    rw [Real.enorm_of_nonneg hμ_inv_nn] at h
    exact h
  -- Assemble: `ofReal μ⁻¹ * eLpNorm bracket ≤ ofReal μ⁻¹ * (ofReal C * aggr)`.
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  -- The aggregate `rhsAggregate` is, by definition, this theorem's RHS sum.
  exact h_step

end MainBound

/-! ## Uniform-constant restatements

The headline bound `eigenvectorChartRHS_eLpNorm_le` produces, per eigenbasis
index `i`, a nonnegative constant `C`. A downstream bounded-operator argument
over the whole eigenbasis needs the constant *uniform* — one `C` serving every
`i`. The seven per-term constants are geometric (chart-transition / density /
dimension / operator-norm data) and do not depend on `i`, so the uniform
restatement is provable: the witness construction is hoisted before the `∀ i`.

The eigenvector index `i` is **not** a section variable here, so each restatement
carries its own `∀ i`. A `_uniform` statement cannot be derived from its per-`i`
original (one cannot get `∃ C, ∀ i` from `∀ i, ∃ C`); each carries its own proof
— the per-`i` proof with the constant hoisted before the `∀ i`. -/

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Uniform-constant finite-sum aggregation.** The constant-uniform form of
`eLpNorm_sum_le_const_mul_aggregate`: a finite indexed family of summands
`F j i`, each weighted-`MemLp` and each — *with an `i`-uniform constant* — having
its `eLpNorm` bounded by `ENNReal.ofReal Cⱼ` times an aggregate `A i`, has its
summed `eLpNorm` bounded by `ENNReal.ofReal` of a single nonnegative constant —
*the same for every `i`* — times `A i`. The per-summand constants are themselves
`i`-uniform, so their sum (times the index cardinality) is an `i`-uniform
headline constant. -/
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
  -- Extract the `i`-uniform per-summand nonnegative constant and bound.
  choose Cf hCf_nn hCf using hbd
  -- The headline constant: the sum of the per-summand constants times the
  -- cardinality of the (finite) index type — manifestly `i`-free.
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  -- The function `fun y => ∑ j, F j n y` is the `Finset.sum` of the `F j n`.
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  -- The triangle inequality `eLpNorm_sum_le`.
  have h_tri : eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, eLpNorm (F j n) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  -- Each per-summand `eLpNorm` is `≤ ENNReal.ofReal (∑ Cf) * A n`: bound the
  -- per-summand constant `Cf j` by the whole nonnegative sum `∑ Cf`.
  have h_step : ∑ j : ι, eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  -- The constant sum is `card • (ENNReal.ofReal (∑ Cf) * A n)`.
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Reassociate `card * ENNReal.ofReal (∑ Cf)` into a single `ENNReal.ofReal`.
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

section TermBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

omit [CompleteSpace E] in
/-- **Uniform-constant `eLpNorm` bound for bracket term 1.** The constant-uniform
form of `rhsTerm1_eLpNorm_le`: the constant is the literal `1`, manifestly
`i`-free. -/
private lemma rhsTerm1_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  refine ⟨1, by norm_num, fun i => ?_⟩
  rw [rhsTerm1, ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)

/-- **Uniform-constant `eLpNorm` bound for bracket term 2.** The constant-uniform
form of `rhsTerm2_eLpNorm_le`: the per-`i` constant is the `eLpNorm`-coefficient
bound of the `i`-free `C^∞` product `covChartMetricGram · crossLeftTestCoeff`
over the compact cutoff chart kernel, summed over the cross-left double-index;
the uniform coefficient lemma `eLpNorm_weighted_contDiffOn_mul_le_uniform`
exhibits each summand's constant once, before the `∀ i`, and the uniform
aggregation lemma assembles the double sum. -/
private lemma rhsTerm2_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The cross-left double-sum summand, indexed by the pair `(P, Q)` and `i`.
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  -- Per-summand weighted-`MemLp`, for every `i`.
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact rhsTerm2_summand_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ x.1 x.2
  -- Per-summand `i`-uniform explicit-norm bound by the full aggregate.
  have hF_bd : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro x
    -- The uniform coefficient bound for the `i`-free `C^∞` product. It is
    -- `∀ w`-quantified; the cross-left limit atom — `i`-dependent — is one such
    -- `w`, so the same constant serves every `i`.
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    -- The cross-left limit vanishes a.e. off the compact cutoff chart kernel.
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α x.1
    -- The atom's `eLpNorm` is dominated by the cross-left aggregate piece.
    have h_atom_le :
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      refine le_trans ?_
        (aggrCrossLeft_le_rhsAggregate (I := I) (M := M)
          g r s h_atlas i α P₀)
      rw [hμw_def, aggrCrossLeft]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1) h_aezero) ?_
    gcongr
  -- The uniform aggregation lemma assembles the double sum.
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- Identify the single-product sum with the nested double sum.
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1), F x i y)
      = rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀ := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

/-- **Uniform-constant `eLpNorm` bound for bracket term 3.** The constant-uniform
form of `rhsTerm3_eLpNorm_le`; the argument mirrors that of term 2 with the
cross-right limit objects. -/
private lemma rhsTerm3_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The cross-right double-sum summand, indexed by the pair `(P, Q)` and `i`.
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have hF_memLp : ∀ (x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s)
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F x i) 2 μw := by
    intro x i
    rw [hμw_def, hF_def]
    exact rhsTerm3_summand_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ x.1 x.2
  have hF_bd : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F x i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro x
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
      (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    refine ⟨C, hC_nn, fun i => ?_⟩
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α x.1 :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact
        tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
          (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α x.1
    have h_atom_le :
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
          ≤ rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      refine le_trans ?_
        (aggrCrossRight_le_rhsAggregate (I := I) (M := M)
          g r s h_atlas i α P₀)
      rw [hμw_def, aggrCrossRight]
      exact Finset.single_le_sum
        (f := fun P => eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        (fun P _ => zero_le _) (Finset.mem_univ x.1)
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd _
      (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1) h_aezero) ?_
    gcongr
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s, F x i y)
      = rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀ := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [← h_eq, hμw_def]
  exact hC_bd i

/-- **Uniform-constant `eLpNorm` bound for bracket term 4.** The constant-uniform
form of `rhsTerm4_eLpNorm_le`: the uniform companion lemma
`eLpNorm_covPrincipalRotationCoeffLimit_le_uniform` bounds it, with one constant
for every `i`, by a constant times the chart-partial aggregate piece, which is
dominated by the full aggregate. -/
private lemma rhsTerm4_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_covPrincipalRotationCoeffLimit_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [rhsTerm4]
  refine le_trans (hC_bd i) ?_
  gcongr
  exact aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀

/-- **Uniform-constant `eLpNorm` bound for bracket term 5.** The constant-uniform
form of `rhsTerm5_eLpNorm_le`: the uniform companion lemma
`eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform` bounds it, with one
constant for every `i`, by a constant times the sum of the chart-partial and
chart-component aggregate pieces; each piece is dominated by the full aggregate,
so doubling the companion constant absorbs the factor. -/
private lemma rhsTerm5_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀
  -- The uniform headline constant for this term is `2 * C`.
  refine ⟨2 * C, by positivity, fun i => ?_⟩
  rw [rhsTerm5]
  -- Bound the companion lemma's two-piece RHS sum by twice the full aggregate.
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
      (aggrComponent_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
  refine le_trans (hC_bd i) ?_
  calc
    ENNReal.ofReal C *
        ((∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))))
        ≤ ENNReal.ofReal C *
            (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
          mul_comm C 2]

/-- **Uniform-constant `eLpNorm` bound for the lower-order gradient-divergence
chart-direction sum.** The constant-uniform form of
`weightedGradCoeffDivLimit_sum_eLpNorm_le`: the uniform companion lemma
`eLpNorm_weightedGradCoeffDivLimit_le_uniform` bounds each chart-direction
summand, with one constant for every `i`, by a constant times the sum of the
chart-component and chart-partial aggregate pieces — `≤ 2 *` the full aggregate;
the uniform aggregation lemma assembles the chart-direction sum. -/
private lemma weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm
            (fun y => ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The chart-direction summand, indexed by `l` and `i`.
  set F : Fin (Module.finrank ℝ E) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun l i => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s h_atlas i α P₀ l with hF_def
  have hF_memLp : ∀ (l : Fin (Module.finrank ℝ E))
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      MemLp (F l i) 2 μw := by
    intro l i
    rw [hμw_def, hF_def]
    exact weightedGradCoeffDivLimit_memLp_weighted
      (I := I) (M := M) g r s h_atlas i α P₀ l
  -- Per chart direction `l`: an `i`-uniform explicit-norm bound by the full
  -- aggregate (the companion lemma's two-piece sum is `≤ 2 * aggregate`).
  have hF_bd : ∀ l : Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (F l i) 2 μw
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    intro l
    obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weightedGradCoeffDivLimit_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ l
    -- The companion constant doubled absorbs the two-piece aggregate sum.
    refine ⟨2 * C, by positivity, fun i => ?_⟩
    rw [hμw_def, hF_def]
    refine le_trans (hC_bd i) ?_
    -- The companion lemma's RHS sum is `aggrComponent + aggrPartial`.
    have h_sum_le :
        (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)))
          + (∑ p : TensorCompIdx (E := E) r s,
              ∑ l' : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
        ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
        (aggrPartial_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    calc
      ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α))))
          ≤ ENNReal.ofReal C *
              (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  -- The uniform aggregation lemma assembles the chart-direction sum.
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_sum_le_const_mul_aggregate_uniform
    (μ := μw) F
    (fun i => rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
    hF_memLp hF_bd
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [hμw_def] at hC_bd
  exact hC_bd i

/-- **Uniform-constant `eLpNorm` bound for bracket term 6.** The constant-uniform
form of `rhsTerm6_eLpNorm_le`: bracket term 6 is the product of the `i`-free
`C^∞` reciprocal chart density with the lower-order gradient-divergence
chart-direction sum; the uniform coefficient bound
`eLpNorm_weighted_contDiffOn_mul_le_uniform` and the uniform chart-direction-sum
bound `weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform` combine into one
constant for every `i`. -/
private lemma rhsTerm6_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- The uniform coefficient bound for the `i`-free `1 / densityOnEuclid` factor.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The uniform chart-direction-sum bound.
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ := weightedGradCoeffDivLimit_sum_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  -- The uniform headline constant for this term is `C₁ * C₂`.
  refine ⟨C₁ * C₂, by positivity, fun i => ?_⟩
  unfold rhsTerm6
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l y)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s h_atlas i α P₀ l y) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (weightedGradCoeffDivLimit_sum_memLp (I := I) (M := M)
              g r s h_atlas i α P₀)
            (weightedGradCoeffDivLimit_sum_ae_zero_off_chartPouKernel
              (I := I) (M := M) g r s h_atlas i α P₀)
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀) := by
        gcongr
        exact hC₂_bd i
    _ = ENNReal.ofReal (C₁ * C₂) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

/-- **Uniform-constant `eLpNorm` bound for bracket term 7.** The constant-uniform
form of `rhsTerm7_eLpNorm_le`: bracket term 7 is the product of the `i`-free
`C^∞` reciprocal chart density with the cross-right gradient-divergence limit;
the uniform coefficient bound `eLpNorm_weighted_contDiffOn_mul_le_uniform` and
the uniform companion lemma `eLpNorm_crossRightGradCoeffDivLimit_le_uniform`
combine into one constant for every `i`. -/
private lemma rhsTerm7_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- The uniform coefficient bound for the `i`-free `1 / densityOnEuclid` factor.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The uniform companion lemma for the cross-right gradient-divergence limit.
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ := eLpNorm_crossRightGradCoeffDivLimit_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  -- The uniform headline constant for this term is `C₁ * (2 * C₂)`.
  refine ⟨C₁ * (2 * C₂), by positivity, fun i => ?_⟩
  unfold rhsTerm7
  -- The companion lemma's RHS sum is `aggrCrossRight + aggrCutoffPartial`.
  have h_sum_le :
      (∑ P : TensorCompIdx (E := E) r s,
          eLpNorm ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)))
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ l : Fin (Module.finrank ℝ E),
              eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
      ≤ 2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRight_le_rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)
      (aggrCutoffPartial_le_rhsAggregate (I := I) (M := M)
        g r s h_atlas i α P₀)
  calc
    eLpNorm
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
          hC₁_bd _
            (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
              g r s h_atlas i α P₀)
            (Filter.Eventually.of_forall (fun y hy =>
              crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s h_atlas i α P₀ hy))
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀)) := by
        gcongr
        exact le_trans (hC₂_bd i) (by gcongr)
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end TermBoundsUniform

section BracketBoundUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

/-- **Uniform-constant seven-term bracket `eLpNorm` bound.** The constant-uniform
form of `rhsBracket_eLpNorm_le`: a single nonnegative constant `C` — the sum of
the seven `i`-uniform per-term constants — serves every eigenbasis index `i`.
Each per-term `_uniform` lemma supplies its `i`-free constant; iterated Minkowski
over the seven-term bracket and the right-distributivity of `*` over `+` in
`ℝ≥0∞` assemble them. -/
private lemma rhsBracket_eLpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
  classical
  -- The seven `i`-uniform per-term explicit-norm bounds.
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  -- The uniform headline constant: the sum of the seven per-term constants.
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The seven per-term weighted-`MemLp` memberships, for this `i`.
  have hM1 := rhsTerm1_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM2 := rhsTerm2_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM3 := rhsTerm3_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM4 := rhsTerm4_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM5 := rhsTerm5_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM6 := rhsTerm6_memLp (I := I) (M := M) g r s h_atlas i α P₀
  have hM7 := rhsTerm7_memLp (I := I) (M := M) g r s h_atlas i α P₀
  rw [← hμw_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  -- The partial-bracket weighted-`MemLp` memberships, built term by term.
  have hB12 := hM1.sub hM2
  have hB123 := hB12.add hM3
  have hB1234 := hB123.sub hM4
  have hB12345 := hB1234.sub hM5
  have hB123456 := hB12345.add hM6
  -- Iterated Minkowski over the seven-term bracket.
  have h_tri :
      eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        ≤ eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
          + eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw := by
    rw [rhsBracket]
    -- Peel `- T7`, then `+ T6`, then `- T5`, `- T4`, `+ T3`, `- T2`.
    refine le_trans (eLpNorm_sub_le hB123456.aestronglyMeasurable
      hM7.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12345.aestronglyMeasurable
      hM6.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB1234.aestronglyMeasurable
      hM5.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_sub_le hB123.aestronglyMeasurable
      hM4.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (eLpNorm_add_le hB12.aestronglyMeasurable
      hM3.aestronglyMeasurable (by norm_num)) ?_
    refine add_le_add ?_ (le_refl _)
    exact eLpNorm_sub_le hM1.aestronglyMeasurable
      hM2.aestronglyMeasurable (by norm_num)
  -- Each of the seven per-term `eLpNorm`s is `≤ ofReal Dⱼ * aggregate`; the
  -- seven-fold sum is `≤ ofReal (∑ Dⱼ) * aggregate`.
  refine le_trans h_tri ?_
  have h_seven :
      eLpNorm (rhsTerm1 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm2 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm3 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm4 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm5 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm6 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        + eLpNorm (rhsTerm7 (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
      ≤ ENNReal.ofReal D1 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D2 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D3 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D4 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D5 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D6 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀
          + ENNReal.ofReal D7 *
            rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (hD1 i) (hD2 i)) (hD3 i)) (hD4 i)) (hD5 i)) (hD6 i)) (hD7 i)
  refine le_trans h_seven ?_
  -- Collect the seven `ofReal Dⱼ * aggregate` terms into `ofReal (∑ Dⱼ) *
  -- aggregate` by right-distributivity of `*` over `+` in `ℝ≥0∞`.
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end BracketBoundUniform

section MainBoundUniform

/-- **Uniform-constant explicit-norm `eLpNorm` bound for the eigenvector chart
right-hand side.**

The constant-uniform form of `eigenvectorChartRHS_eLpNorm_le`: a single
nonnegative constant `C` — geometric (chart-transition / density / dimension /
operator-norm data), independent of the eigenbasis index — serves *every*
eigenbasis index `i`. For each `i`, with resolvent eigenvalue `μ := i.fst.val`,
the weighted `eLpNorm` of `eigenvectorChartRHS g r s h_atlas i α P₀` is bounded
by `ENNReal.ofReal (μ⁻¹ * C)` times the finite source-quantity aggregate of that
`i`.

The explicit eigenvalue factor `μ⁻¹` stays *inside* the `∀ i` — it is a genuine
per-`i` quantity, not part of the uniform constant. Only the geometric constant
`C` is hoisted before the `∀ i`. The proof exhibits the `i`-uniform witness of
the seven-term bracket bound `rhsBracket_eLpNorm_le_uniform`, then for each `i`
runs the per-`i` headline argument: `eigenvectorChartRHS` is the `μ⁻¹`-scalar
multiple of the seven-term bracket, and the homogeneity of `eLpNorm` factors out
`ENNReal.ofReal μ⁻¹`. -/
theorem eigenvectorChartRHS_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
                  g r s h_atlas i α P₀) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r (s + 1),
                  eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ k : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit (I := I) (M := M)
                        g r s h_atlas i α P k :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit (I := I) (M := M)
                      g r s h_atlas i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s h_atlas i α P l :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  -- The `i`-uniform seven-term bracket bound — the constant is hoisted before
  -- the `∀ i`.
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_eLpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- The resolvent eigenvalue is strictly positive.
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hC_bd_i := hC_bd i
  -- `eigenvectorChartRHS = μ⁻¹ • rhsBracket`; the `eLpNorm` factors out `‖μ⁻¹‖ₑ`.
  have h_smul_eq :
      eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s h_atlas i α P₀]
    have h := eLpNorm_const_smul (μ := μw) (p := 2) (i.fst.val)⁻¹
      (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀)
    rw [Real.enorm_of_nonneg hμ_inv_nn] at h
    exact h
  -- Assemble: `ofReal μ⁻¹ * eLpNorm bracket ≤ ofReal μ⁻¹ * (ofReal C * aggr)`.
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          eLpNorm (rhsBracket (I := I) (M := M) g r s h_atlas i α P₀) 2 μw
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsAggregate (I := I) (M := M) g r s h_atlas i α P₀ := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  -- The aggregate `rhsAggregate` is, by definition, this theorem's RHS sum.
  exact h_step

end MainBoundUniform

/-! ## Sanity test -/

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

example :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          (eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r (s + 1),
                eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                      g r s h_atlas i α P l :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))) :=
  eigenvectorChartRHS_eLpNorm_le (I := I) (M := M) g r s h_atlas i α P₀

example :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
                  g r s h_atlas i α P₀) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r (s + 1),
                  eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ k : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit (I := I) (M := M)
                        g r s h_atlas i α P k :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit (I := I) (M := M)
                      g r s h_atlas i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s h_atlas i α P l :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) :=
  eigenvectorChartRHS_eLpNorm_le_uniform (I := I) (M := M) g r s h_atlas α P₀

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
