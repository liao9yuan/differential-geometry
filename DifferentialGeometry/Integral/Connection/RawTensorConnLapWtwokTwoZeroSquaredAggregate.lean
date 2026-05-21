import DifferentialGeometry.Integral.Connection.RawTensorConnLapL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorSectionL2WtwokTwoZeroBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

/-!
# Squared chart-Sobolev-zero aggregate for the raw tensor connection Laplacian

For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, this file bounds the **square
of the chart-component aggregate** of `rawTensorConnLapSmooth g r s T`, taken
over the canonical finite cover and the finite component-index set, by a
constant times `(wtwokTwoNorm g 1 T) ^ 2`. Concretely:

```
(∑_α ∈ chartAtlasPOU_finset, ∑_Idx, ∑_Jdx,
    eLpNorm (tensorChartComp g r s (rawTensorConnLapSmooth g r s T) α Idx Jdx)
      2 (volume.restrict (chartTargetEuclid α))) ^ 2
  ≤ ENNReal.ofReal C · (wtwokTwoNorm g 1 T) ^ 2
```

The bound composes the existing chart-Sobolev raw-norm POU aggregate bound
`chartSobolevRawNormPou_le_wtwokTwoNorm_sq` with a per-chart, per-multi-index
pointwise op-norm comparison driven by
`chartRSTwistInv_pointwise_opNorm_isBounded_on_compact` on the
partition-of-unity tsupport, plus an `ENNReal` Cauchy–Schwarz step to pass from
the finset sum of `eLpNorm`s to its square.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Per-α chart twist-inverse op-norm bound on the POU tsupport -/

/-- For each chart base point `α`, there is a non-negative constant `C_α` such
that the inverse chart-`(α, b)`-twist operator norm is uniformly bounded by
`C_α` on the (compact) tsupport of the chart-`α` partition-of-unity weight.

Direct consequence of
`chartRSTwistInv_pointwise_opNorm_isBounded_on_compact` applied with
`K := tsupport (chartAtlasPOU I M α)`, using
`pouTsupport_isCompact` and `chartAtlasPOU_isSubordinate`. -/
private lemma exists_chartRSTwistInv_norm_bound_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (_g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : M), b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ (T : TensorRSModel r s ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s T‖ ≤ C * ‖T‖ := by
  classical
  set K : Set M := tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  obtain ⟨C, hC_pos, hC_le⟩ :=
    chartRSTwistInv_pointwise_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub r s
  refine ⟨C, le_of_lt hC_pos, ?_⟩
  intro b hb T
  -- Unfold K to refer to it by name.
  change b ∈ K at hb
  exact hC_le b hb T

/-! ## Per-α, per-IJ pointwise squared bound on `tensorChartComp` -/

/-- For each chart base point `α` and ranks `(r, s)`, there is a non-negative
constant `K_α` such that for every smooth compactly-supported `(r, s)`-tensor
section `S` (we will instantiate with `S := rawTensorConnLapSmooth g r s T`),
every multi-index pair `(Idx, Jdx)`, and every chart-target point `y`, the
squared chart component is bounded by

  `(tensorChartComp g r s S α Idx Jdx y) ^ 2 ≤
     K_α · ρ_α(symm y) ^ 2 · ‖S.toSection (symm y)‖ ^ 2`

uniformly in `S, Idx, Jdx, y`. The constant `K_α` depends only on `g`, the
chart at `α`, the ranks, and the model space.

Proof: on the chart target, `tensorChartComp α IJ S y = ρ_α(b) ·
tensorChartComponentRaw α IJ b` where `b = (extChartAt I α).symm
(toEuclidean.symm y)`. On `tsupport ρ_α`, `tensorTrivProj α S b =
chartRSTwistInv α b r s (toModel S b)` has norm `≤ C_α · ‖S b‖`, and each
multi-index projection `tensorChartComponentProjection IJ` has uniform
operator norm `≤ C_proj`. Off `tsupport ρ_α`, `ρ_α(b) = 0`, so the bound is
trivial. Off the chart target, `tensorChartComp α IJ S y = 0`. -/
private lemma tensorChartComp_sq_le_constMul_pou_sq_mul_pushedNormSq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN),
        (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2 ≤
          K *
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M => S.toSection b) y) := by
  classical
  obtain ⟨C_α, hC_α_nn, hC_α_le⟩ :=
    exists_chartRSTwistInv_norm_bound_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * C_α ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro S Idx Jdx y
  -- Notation.
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b with hρ_def
  set N_sq : ℝ := tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') y with hN_sq_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α b
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hN_sq_nn : 0 ≤ N_sq :=
    tensorTrivProjPushedNormSq_nonneg (I := I) (M := M) g r s α _ y
  -- Case split on `y ∈ chartTargetEuclid α`.
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- On chart target.
    -- `tensorChartComp α IJ S y = ρ · tensorChartComponentRaw α IJ b`.
    have h_lhs_eq :
        tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y =
          ρ * tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
      rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
      unfold tensorChartComponentPou
      rfl
    -- `N_sq = ‖toModel (S.toSection b)‖² = ‖S.toSection b‖²`.
    have hN_sq_eq :
        N_sq = ‖S.toSection b‖ ^ 2 := by
      rw [hN_sq_def, tensorTrivProjPushedNormSq_apply_of_mem
        (I := I) (M := M) g r s α (fun b' : M => S.toSection b') hy]
      rfl
    -- Case on whether `ρ = 0`.
    by_cases hρ_zero : ρ = 0
    · -- `ρ = 0` ⇒ both sides are zero (LHS) or non-negative (RHS).
      have h_lhs_zero :
          tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
        rw [h_lhs_eq, hρ_zero, zero_mul]
      rw [h_lhs_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      have h_K_nn : 0 ≤ C_proj ^ 2 * C_α ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_nonneg h_K_nn (mul_nonneg hρ_sq_nn hN_sq_nn)
    · -- `ρ ≠ 0` ⇒ `b ∈ tsupport ρ_α`.
      have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ_nn (Ne.symm hρ_zero)
      have hb_supp : b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ (Function.mem_support.mpr hρ_zero)
      have hb_chart : b ∈ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate (I := I) (M := M) α hb_supp
      -- The forward chart twist `tensorTrivProj α S b` equals
      -- `chartRSTwistInv α b r s (toModel(S.toSection b))`.
      have h_triv :
          tensorTrivProj (I := I) (M := M) g r s S α b =
            chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel (𝕜 := ℝ) (S.toSection b)) := by
        unfold tensorTrivProj
        exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
          (I := I) (M := M) r s α hb_chart (S.toSection b)
      -- `‖tensorTrivProj α S b‖ ≤ C_α · ‖S.toSection b‖`.
      have h_triv_norm :
          ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ ≤
            C_α * ‖S.toSection b‖ := by
        rw [h_triv]
        have := hC_α_le b hb_supp (TensorRSSpace.toModel (𝕜 := ℝ) (S.toSection b))
        -- `‖toModel X‖ = ‖X‖`.
        have hnorm_eq : ‖TensorRSSpace.toModel (𝕜 := ℝ) (S.toSection b)‖ =
            ‖S.toSection b‖ := rfl
        rw [hnorm_eq] at this
        exact this
      -- `|tensorChartComponentRaw α IJ b| ≤ C_proj · ‖tensorTrivProj α S b‖`.
      have h_raw_le :
          |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| ≤
            C_proj * ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ := by
        have h_proj_bound :
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤ C_proj :=
          tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx
        have h_le_op := (tensorChartComponentProjection (E := E) r s Idx Jdx).le_opNorm
          (tensorTrivProj (I := I) (M := M) g r s S α b)
        have h_norm_real :
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx
                (tensorTrivProj (I := I) (M := M) g r s S α b)‖ =
              |tensorChartComponentProjection (E := E) r s Idx Jdx
                (tensorTrivProj (I := I) (M := M) g r s S α b)| := by
          rw [Real.norm_eq_abs]
        rw [h_norm_real] at h_le_op
        have h_proj_step :
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ *
              ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ ≤
              C_proj * ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ :=
          mul_le_mul_of_nonneg_right h_proj_bound (norm_nonneg _)
        have hraw_eq :
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b =
              tensorChartComponentProjection (E := E) r s Idx Jdx
                (tensorTrivProj (I := I) (M := M) g r s S α b) := rfl
        rw [hraw_eq]
        exact le_trans h_le_op h_proj_step
      -- Chain: `|raw α IJ b| ≤ C_proj · C_α · ‖S.toSection b‖`.
      have h_chain :
          |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| ≤
            (C_proj * C_α) * ‖S.toSection b‖ := by
        have h_step :
            C_proj * ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ ≤
              C_proj * (C_α * ‖S.toSection b‖) :=
          mul_le_mul_of_nonneg_left h_triv_norm hC_proj_nn
        have h_arith : C_proj * (C_α * ‖S.toSection b‖) =
            (C_proj * C_α) * ‖S.toSection b‖ := by ring
        rw [← h_arith]
        exact le_trans h_raw_le h_step
      -- Square both sides.
      have h_chain_nn : 0 ≤ (C_proj * C_α) * ‖S.toSection b‖ :=
        mul_nonneg (mul_nonneg hC_proj_nn hC_α_nn) (norm_nonneg _)
      have h_raw_sq_le :
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 ≤
            (C_proj * C_α) ^ 2 * ‖S.toSection b‖ ^ 2 := by
        have h_abs_sq :
            |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| ^ 2 =
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 :=
          sq_abs _
        rw [← h_abs_sq]
        have h_sq := mul_self_le_mul_self (abs_nonneg _) h_chain
        have h_rearr :
            ((C_proj * C_α) * ‖S.toSection b‖) *
              ((C_proj * C_α) * ‖S.toSection b‖) =
                (C_proj * C_α) ^ 2 * ‖S.toSection b‖ ^ 2 := by ring
        have h_lhs :
            |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| *
              |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| =
                |tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b| ^ 2 :=
          by rw [sq]
        rw [h_lhs] at h_sq
        rw [h_rearr] at h_sq
        exact h_sq
      -- LHS expansion: `(ρ · raw)² = ρ² · raw²`.
      have h_lhs_sq_eq :
          (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2 =
            ρ ^ 2 *
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 := by
        rw [h_lhs_eq, mul_pow]
      rw [h_lhs_sq_eq]
      -- Plug in the squared bound and N_sq.
      have h_step :
          ρ ^ 2 *
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 ≤
            ρ ^ 2 *
              ((C_proj * C_α) ^ 2 * ‖S.toSection b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_raw_sq_le hρ_sq_nn
      refine h_step.trans ?_
      -- Rearrange to match the RHS.
      have h_arith :
          ρ ^ 2 *
              ((C_proj * C_α) ^ 2 * ‖S.toSection b‖ ^ 2) =
            (C_proj * C_α) ^ 2 *
              (ρ ^ 2 * ‖S.toSection b‖ ^ 2) := by ring
      rw [h_arith]
      have h_K_eq : C_proj ^ 2 * C_α ^ 2 = (C_proj * C_α) ^ 2 := by ring
      rw [h_K_eq]
      -- Now: `(C_proj * C_α)² · (ρ² · ‖S.b‖²) ≤ (C_proj * C_α)² · (ρ² · N_sq)`.
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [hN_sq_eq]
  · -- Off chart target: `tensorChartComp = 0`.
    have h_lhs_zero :
        tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y = 0 :=
      tensorChartComp_apply_of_notMem (I := I) (M := M) g r s S α Idx Jdx hy
    rw [h_lhs_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have h_K_nn : 0 ≤ C_proj ^ 2 * C_α ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg h_K_nn (mul_nonneg hρ_sq_nn hN_sq_nn)

/-! ## `eLpNorm` squared rewrite as a lintegral of `ENNReal.ofReal` of the square -/

/-- For a real-valued function `f` (Borel-measurable square) and a measure `μ`,
the square of `eLpNorm f 2 μ` equals the lintegral of `ENNReal.ofReal (f x ^ 2)`. -/
private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  -- Use the existing `sq_eLpNorm_two_eq_lintegral_enorm_sq`-style argument.
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  -- Reduce the integrand's rpow to a natural pow.
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
    rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by
      rw [Real.norm_eq_abs, sq_abs]]
    rw [← ofReal_norm_eq_enorm]
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
  -- Show `(I ^ (1/2)) ^ 2 = I` via `ENNReal.rpow_natCast`, `ENNReal.rpow_mul`.
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

/-! ## ENNReal Cauchy–Schwarz: `(∑ aᵢ)² ≤ N · ∑ aᵢ²` over a finset -/

/-- Cauchy–Schwarz in `ℝ≥0∞` for a finset sum:
`(∑ i ∈ s, f i) ^ 2 ≤ s.card · ∑ i ∈ s, (f i) ^ 2`.

Proof: split into the case where some summand is `⊤` (LHS and RHS both `⊤`)
and the case where all summands are finite (lift to `ℝ` via `toReal`). -/
private lemma ennreal_sq_finset_sum_le_card_mul_finset_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  by_cases h_top : ∃ j ∈ s, f j = ⊤
  · -- Some `f j = ⊤`. Then `∑ f i ≥ ⊤`, so LHS = `⊤²`. Also `∑ (f i)² ≥ ⊤² = ⊤`.
    obtain ⟨j, hj, hj_top⟩ := h_top
    have h_sum_top : ∑ i ∈ s, f i = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨j, hj, hj_top⟩
    rw [h_sum_top]
    rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by
      rw [sq]; exact ENNReal.top_mul_top]
    by_cases hs : s.card = 0
    · -- s = ∅, contradicting `j ∈ s`.
      rw [Finset.card_eq_zero] at hs
      subst hs
      simp at hj
    · -- s.card > 0, so RHS = ⊤.
      have h_card_pos : 0 < s.card := Nat.pos_of_ne_zero hs
      have h_card_ne : ((s.card : ℝ≥0∞)) ≠ 0 := by
        rw [Ne, Nat.cast_eq_zero]; exact hs
      have h_sum_sq_top : ∑ i ∈ s, (f i) ^ 2 = ⊤ := by
        rw [ENNReal.sum_eq_top]
        refine ⟨j, hj, ?_⟩
        rw [hj_top]
        rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by rw [sq]; exact ENNReal.top_mul_top]
      rw [h_sum_sq_top]
      rw [ENNReal.mul_top h_card_ne]
  · -- All `f i ≠ ⊤`. Lift to reals.
    -- Convert `h_top` from `¬∃ ...` to `∀ ..., ¬...`.
    have hf_ne_top : ∀ i ∈ s, f i ≠ ⊤ := by
      intro i hi h_eq_top
      exact h_top ⟨i, hi, h_eq_top⟩
    -- The sum is finite.
    have h_sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ := by
      intro h_sum_top
      rw [ENNReal.sum_eq_top] at h_sum_top
      obtain ⟨i, hi, h_eq_top⟩ := h_sum_top
      exact hf_ne_top i hi h_eq_top
    -- The sum-of-squares is also finite.
    have hf_sq_ne_top : ∀ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro i hi
      rw [sq]
      exact ENNReal.mul_ne_top (hf_ne_top i hi) (hf_ne_top i hi)
    have h_sum_sq_ne_top : ∑ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro h_eq_top
      rw [ENNReal.sum_eq_top] at h_eq_top
      obtain ⟨i, hi, h_top⟩ := h_eq_top
      exact hf_sq_ne_top i hi h_top
    -- Convert to reals.
    set a : ι → ℝ := fun i => (f i).toReal with ha_def
    have ha_nn : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    have hfi_eq : ∀ i ∈ s, f i = ENNReal.ofReal (a i) := by
      intro i hi
      rw [ha_def]
      exact (ENNReal.ofReal_toReal (hf_ne_top i hi)).symm
    -- Sum.
    have h_sum_eq : ∑ i ∈ s, f i = ENNReal.ofReal (∑ i ∈ s, a i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha_nn i)]
      exact Finset.sum_congr rfl hfi_eq
    -- (f i)² = ENNReal.ofReal ((a i)²).
    have hfsq_eq : ∀ i ∈ s, (f i) ^ 2 = ENNReal.ofReal ((a i) ^ 2) := by
      intro i hi
      rw [hfi_eq i hi]
      rw [← ENNReal.ofReal_pow (ha_nn i) 2]
    -- Sum of squares.
    have h_sumsq_eq : ∑ i ∈ s, (f i) ^ 2 = ENNReal.ofReal (∑ i ∈ s, (a i) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      exact Finset.sum_congr rfl hfsq_eq
    -- LHS = ofReal((Σ a)²).
    rw [h_sum_eq]
    rw [← ENNReal.ofReal_pow (Finset.sum_nonneg (fun i _ => ha_nn i)) 2]
    rw [h_sumsq_eq]
    -- Move RHS into ofReal.
    have h_card_eq :
        (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    rw [h_card_eq]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    -- Now: ofReal((Σ a)²) ≤ ofReal(card · Σ a²).
    apply ENNReal.ofReal_le_ofReal
    -- Real-valued CS: `(Σ aᵢ)² ≤ card · Σ aᵢ²`. Prove inline.
    have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
        2 * ((s.card : ℝ) * (∑ i ∈ s, (a i) ^ 2) -
              (∑ i ∈ s, a i) ^ 2) := by
      classical
      set S₀ : ℝ := ∑ i ∈ s, a i with hS₀_def
      set Q₀ : ℝ := ∑ i ∈ s, (a i) ^ 2 with hQ₀_def
      have h_inner : ∀ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
          (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
        intro i _
        have hexp : ∀ j, (a i - a j) ^ 2 =
            (a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2 := by
          intro j; ring
        calc ∑ j ∈ s, (a i - a j) ^ 2
            = ∑ j ∈ s, ((a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2) :=
              Finset.sum_congr rfl (fun j _ => hexp j)
          _ = (∑ _j ∈ s, (a i) ^ 2) - (∑ j ∈ s, 2 * (a i) * (a j))
              + (∑ j ∈ s, (a j) ^ 2) := by
                rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          _ = (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
                rw [Finset.sum_const]
                rw [show (∑ j ∈ s, 2 * (a i) * (a j)) = 2 * (a i) * S₀ from by
                  rw [show (fun j => 2 * (a i) * (a j)) =
                    (fun j => (2 * (a i)) * (a j)) from by funext j; ring]
                  rw [← Finset.mul_sum, ← hS₀_def]]
                rw [← hQ₀_def, nsmul_eq_mul]
      calc ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2
          = ∑ i ∈ s, ((s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀) :=
            Finset.sum_congr rfl h_inner
        _ = (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2)
            - (∑ i ∈ s, 2 * (a i) * S₀) + (∑ i ∈ s, Q₀) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = (s.card : ℝ) * Q₀ - 2 * S₀ * S₀ + (s.card : ℝ) * Q₀ := by
              rw [show (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2) =
                  (s.card : ℝ) * Q₀ from by
                rw [← Finset.mul_sum, ← hQ₀_def]]
              rw [show (∑ i ∈ s, 2 * (a i) * S₀) = 2 * S₀ * S₀ from by
                rw [show (fun i => 2 * (a i) * S₀) =
                  (fun i => (2 * S₀) * (a i)) from by funext i; ring]
                rw [← Finset.mul_sum, ← hS₀_def]]
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((s.card : ℝ) * Q₀ - S₀ ^ 2) := by ring
    have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [h_double_sum] at h_nn
    nlinarith

/-! ## Per-α per-IJ L² integral bound -/

/-- For each `α`, there is a non-negative constant `K_α` such that for every
smooth compactly-supported `(r, s)`-tensor section `S`, every multi-index pair
`(Idx, Jdx)`, the squared `eLpNorm`'s sum over `(Idx, Jdx)` of
`tensorChartComp g r s S α Idx Jdx` over `chartTargetEuclid α` is bounded by

  `K_α · ∫_{chart target} ENNReal.ofReal(ρ_α(symm y)² · pushedNormSq y) dvol`.

This is the integration of `tensorChartComp_sq_le_constMul_pou_sq_mul_pushedNormSq`
summed over the multi-indices. -/
private lemma sum_IJ_sq_eLpNorm_two_tensorChartComp_le_lintegral_pou_sq_pushedNormSq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (S : SmoothCcTensor g r s),
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (eLpNorm
              (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α))) ^ 2) ≤
          ENNReal.ofReal K *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b' : M => S.toSection b') y)
              ∂(volume : Measure EuclN) := by
  classical
  obtain ⟨K_pt, hK_pt_nn, hK_pt_bound⟩ :=
    tensorChartComp_sq_le_constMul_pou_sq_mul_pushedNormSq
      (I := I) (M := M) h_atlas g r s α
  set Idx_card_nat : ℕ := (Finset.univ : Finset
      (Fin r → Fin (Module.finrank ℝ E))).card with hIdx_card_nat_def
  set Jdx_card_nat : ℕ := (Finset.univ : Finset
      (Fin s → Fin (Module.finrank ℝ E))).card with hJdx_card_nat_def
  refine ⟨K_pt * (Idx_card_nat * Jdx_card_nat : ℝ),
    mul_nonneg hK_pt_nn
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), ?_⟩
  intro S
  -- Set notation.
  set ν : Measure EuclN := (volume : Measure EuclN).restrict
    (chartTargetEuclid (I := I) (M := M) α) with hν_def
  set RHS_int : ℝ≥0∞ :=
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b' : M => S.toSection b') y)
      ∂(volume : Measure EuclN) with hRHS_def
  -- Step 1: rewrite each `(eLpNorm ...) ^ 2 = ∫⁻ ofReal(comp²) dν`.
  have h_step1 :
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm
            (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) 2 ν) ^ 2 =
          ∫⁻ y, ENNReal.ofReal
            ((tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2) ∂ν := by
    intro Idx Jdx
    exact sq_eLpNorm_two_eq_lintegral_ofReal_sq
      (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) ν
  -- Step 2: pointwise bound:
  -- `ofReal(comp²) ≤ K_pt · ofReal(ρ² · N_sq)` on chart target.
  have h_pt :
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN),
        ENNReal.ofReal
            ((tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2) ≤
          ENNReal.ofReal K_pt *
            (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b' : M => S.toSection b') y)) := by
    intro Idx Jdx y
    have h_ineq := hK_pt_bound S Idx Jdx y
    -- Real inequality `comp² ≤ K_pt · (ρ² · N_sq)`. Lift via ofReal.
    have hρ_sq_nn : 0 ≤ ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 := sq_nonneg _
    have hN_sq_nn : 0 ≤ tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b' : M => S.toSection b') y :=
      tensorTrivProjPushedNormSq_nonneg (I := I) (M := M) g r s α _ y
    have hRHS_real_nn :
        0 ≤ K_pt *
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b' : M => S.toSection b') y) :=
      mul_nonneg hK_pt_nn (mul_nonneg hρ_sq_nn hN_sq_nn)
    refine (ENNReal.ofReal_le_ofReal h_ineq).trans ?_
    rw [ENNReal.ofReal_mul hK_pt_nn]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    rw [ENNReal.ofReal_mul hρ_sq_nn]
  -- Step 3: integrate the pointwise bound. We get per-(Idx, Jdx):
  -- `∫ ofReal(comp²) ≤ K_pt · ∫ ofReal(ρ²) · ofReal(N_sq)`.
  have h_int :
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∫⁻ y, ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2) ∂ν ≤
        ENNReal.ofReal K_pt * RHS_int := by
    intro Idx Jdx
    have h_mono :
        ∫⁻ y, ENNReal.ofReal
              ((tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2)
            ∂ν ≤
          ∫⁻ y,
            ENNReal.ofReal K_pt *
              (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm
                        ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b' : M => S.toSection b') y))
            ∂ν :=
      MeasureTheory.lintegral_mono (fun y => h_pt Idx Jdx y)
    refine h_mono.trans ?_
    -- Pull out `ENNReal.ofReal K_pt`.
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Step 4: sum over IJ.
  rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      (eLpNorm
        (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) 2 ν) ^ 2) =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ∫⁻ y, ENNReal.ofReal
            ((tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y) ^ 2) ∂ν from by
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact h_step1 Idx Jdx]
  -- Each summand ≤ ofReal K_pt · RHS_int. Sum over IJ.
  refine (Finset.sum_le_sum (fun Idx _ =>
      Finset.sum_le_sum (fun Jdx _ => h_int Idx Jdx))).trans ?_
  -- Inner: `Σ_Jdx ofReal K_pt · RHS_int = Jdx_card_nat · ofReal K_pt · RHS_int`.
  have hinner : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ENNReal.ofReal K_pt * RHS_int) =
        (Jdx_card_nat : ℝ≥0∞) * (ENNReal.ofReal K_pt * RHS_int) := by
    intro Idx
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      ENNReal.ofReal K_pt * RHS_int) =
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        (Jdx_card_nat : ℝ≥0∞) * (ENNReal.ofReal K_pt * RHS_int)) from
    Finset.sum_congr rfl (fun Idx _ => hinner Idx)]
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Now: Idx_card_nat · (Jdx_card_nat · (ofReal K_pt · RHS_int))
  --    ≤ ofReal(K_pt · (Idx_card · Jdx_card)) · RHS_int.
  have hIdx_ofReal : (Idx_card_nat : ℝ≥0∞) = ENNReal.ofReal (Idx_card_nat : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have hJdx_ofReal : (Jdx_card_nat : ℝ≥0∞) = ENNReal.ofReal (Jdx_card_nat : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have hKK_nn : 0 ≤ K_pt * (Idx_card_nat * Jdx_card_nat : ℝ) :=
    mul_nonneg hK_pt_nn
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hI_nn : (0 : ℝ) ≤ (Idx_card_nat : ℝ) := Nat.cast_nonneg _
  have hJ_nn : (0 : ℝ) ≤ (Jdx_card_nat : ℝ) := Nat.cast_nonneg _
  rw [hIdx_ofReal, hJdx_ofReal]
  -- LHS = ofReal Idx_card · (ofReal Jdx_card · (ofReal K_pt · RHS_int))
  -- = ofReal(Idx_card · Jdx_card · K_pt) · RHS_int
  -- = ofReal(K_pt · (Idx_card · Jdx_card)) · RHS_int.
  rw [show ENNReal.ofReal (Idx_card_nat : ℝ) *
      (ENNReal.ofReal (Jdx_card_nat : ℝ) *
        (ENNReal.ofReal K_pt * RHS_int)) =
        (ENNReal.ofReal (Idx_card_nat : ℝ) *
          (ENNReal.ofReal (Jdx_card_nat : ℝ) *
            ENNReal.ofReal K_pt)) * RHS_int from by ring]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul hJ_nn]
  rw [← ENNReal.ofReal_mul hI_nn]
  refine le_of_eq ?_
  apply congr_arg ENNReal.ofReal
  ring

/-! ## Sum over `α` of the per-α per-IJ L² aggregate -/

/-- Summed over `α ∈ chartAtlasPOU_finset`, the squared `eLpNorm` aggregate is
bounded by a constant times `chartSobolevRawNormPou g r s T`.

This is the chart-aggregating step: each per-α summand is bounded as in
`sum_IJ_sq_eLpNorm_two_tensorChartComp_le_lintegral_pou_sq_pushedNormSq`, and the
sum of the chart-target `∫ ρ² · pushedNormSq` over `α` is exactly
`chartSobolevRawNormPou g r s T` when `S = rawTensorConnLapSmooth g r s T`. -/
private lemma finset_sum_sum_IJ_sq_eLpNorm_two_tensorChartComp_raw_le
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (eLpNorm
                (tensorChartComp (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) ^ 2) ≤
          ENNReal.ofReal C *
            chartSobolevRawNormPou (I := I) (M := M) g r s T := by
  classical
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  -- Per-α constants via `Classical.choose`.
  set Kα : M → ℝ := fun α => Classical.choose
    (sum_IJ_sq_eLpNorm_two_tensorChartComp_le_lintegral_pou_sq_pushedNormSq
      (I := I) (M := M) h_atlas g r s α) with hKα_def
  have hKα_spec : ∀ α : M, 0 ≤ Kα α ∧
      ∀ (S : SmoothCcTensor g r s),
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (eLpNorm
              (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α))) ^ 2) ≤
          ENNReal.ofReal (Kα α) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm
                        ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b' : M => S.toSection b') y)
              ∂(volume : Measure EuclN) := fun α =>
    Classical.choose_spec
      (sum_IJ_sq_eLpNorm_two_tensorChartComp_le_lintegral_pou_sq_pushedNormSq
        (I := I) (M := M) h_atlas g r s α)
  -- Take the maximum constant via summation.
  set C : ℝ := ∑ α ∈ Sfin, Kα α with hC_def
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun α _ => (hKα_spec α).1)
  refine ⟨C, hC_nn, ?_⟩
  intro T
  set Spou : ℝ≥0∞ := chartSobolevRawNormPou (I := I) (M := M) g r s T with hSpou_def
  -- Apply the per-α bound to `S := rawTensorConnLapSmooth g r s T`.
  set S : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s T with hS_def
  -- The α-summand of `chartSobolevRawNormPou g r s T` is exactly the per-α
  -- lintegral involving `S.toSection = rawTensorConnLap T.toSection` (via the
  -- definitional equality from `rawTensorConnLapSmooth_toSection_apply`).
  have h_section_eq : ∀ b : M,
      S.toSection b = rawTensorConnLap (I := I) g r s
        (fun z : M => T.toSection z) b := by
    intro b
    rw [hS_def]
    exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T b
  -- For each α: the per-α α-summand of `chartSobolevRawNormPou g r s T` equals
  -- the per-α `RHS_int` (with the section being `S.toSection`).
  have h_alpha_RHS_eq : ∀ α : M,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b' : M => S.toSection b') y)
          ∂(volume : Measure EuclN) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b' : M =>
                rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) b') y)
          ∂(volume : Measure EuclN) := by
    intro α
    refine lintegral_congr ?_
    intro y
    have h_pushNormSq_eq :
        tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b' : M => S.toSection b') y =
        tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b' : M =>
            rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) b') y := by
      unfold tensorTrivProjPushedNormSq
      split_ifs with hy
      · simp only
        rw [h_section_eq ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))]
      · rfl
    rw [h_pushNormSq_eq]
  -- Per-α bound applied to S.
  have hα_le : ∀ α ∈ Sfin,
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (eLpNorm
            (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2) ≤
        ENNReal.ofReal (Kα α) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b' : M =>
                    rawTensorConnLap (I := I) g r s
                      (fun z : M => T.toSection z) b') y)
            ∂(volume : Measure EuclN) := by
    intro α _
    have h := (hKα_spec α).2 S
    rw [h_alpha_RHS_eq α] at h
    exact h
  -- Sum over α.
  refine (Finset.sum_le_sum hα_le).trans ?_
  -- RHS = Σ_α ofReal(Kα α) · α-summand of `chartSobolevRawNormPou g r s T`.
  -- And `Σ_α (ofReal C_α) · X_α ≤ (Σ_α ofReal C_α) · max X_α`... actually let me use
  -- a cleaner bound: bound by (sup_α Kα α) · Spou. We use Σ Kα = C as our constant.
  -- The bound: Σ_α ofReal(Kα α) · X_α ≤ ofReal(C) · (Σ_α X_α) = ofReal(C) · Spou
  -- iff each ofReal(Kα α) ≤ ofReal(C). Since Kα ≥ 0 and C = Σ_β Kβ ≥ Kα, we have
  -- ofReal Kα ≤ ofReal C. So:
  -- Σ_α (ofReal Kα · X_α) ≤ Σ_α (ofReal C · X_α) = ofReal C · Σ_α X_α.
  have h_Kα_le_C : ∀ α ∈ Sfin, Kα α ≤ C := by
    intro α hα
    rw [hC_def]
    exact Finset.single_le_sum (f := fun α : M => Kα α)
      (fun α _ => (hKα_spec α).1) hα
  have h_ofReal_Kα_le_C : ∀ α ∈ Sfin,
      ENNReal.ofReal (Kα α) ≤ ENNReal.ofReal C := by
    intro α hα
    exact ENNReal.ofReal_le_ofReal (h_Kα_le_C α hα)
  -- Σ ofReal(Kα) · X_α ≤ Σ ofReal(C) · X_α = ofReal(C) · Σ X_α = ofReal(C) · Spou.
  calc (∑ α ∈ Sfin,
            ENNReal.ofReal (Kα α) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm
                          ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b' : M =>
                        rawTensorConnLap (I := I) g r s
                          (fun z : M => T.toSection z) b') y)
                ∂(volume : Measure EuclN))
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm
                          ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b' : M =>
                        rawTensorConnLap (I := I) g r s
                          (fun z : M => T.toSection z) b') y)
                ∂(volume : Measure EuclN) := by
            refine Finset.sum_le_sum ?_
            intro α hα
            exact mul_le_mul_of_nonneg_right (h_ofReal_Kα_le_C α hα) (zero_le _)
      _ = ENNReal.ofReal C * ∑ α ∈ Sfin,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm
                        ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b' : M =>
                      rawTensorConnLap (I := I) g r s
                        (fun z : M => T.toSection z) b') y)
              ∂(volume : Measure EuclN) := by
            rw [Finset.mul_sum]
      _ = ENNReal.ofReal C * Spou := by
            rw [hSpou_def]
            rw [chartSobolevRawNormPou_def (I := I) (M := M) g r s T]

/-! ## Headline -/

/-- **Squared chart-Sobolev-zero aggregate for the raw tensor connection
Laplacian, bounded by the order-1 tensor Sobolev norm squared.**

For a closed smooth Riemannian manifold `(M, g)` and ranks `(r, s)`, there is
a non-negative constant `C` such that for every smooth compactly-supported
`(r, s)`-tensor section `T`, the **square** of the chart-component aggregate
of `rawTensorConnLapSmooth g r s T`, summed over the canonical finite cover
and the finite component-index set, is bounded by `C · (wtwokTwoNorm g 1 T) ^ 2`.

Strategy:

1. The aggregate is `∑_α ∑_IJ eLpNorm (tensorChartComp ... (raw T) α IJ) 2 ν_α`.
   By the ENNReal Cauchy–Schwarz `(∑ aᵢ)^2 ≤ N · ∑ aᵢ²`, the **square** of the
   aggregate is bounded by the cardinality of the index set times the sum of
   squares.

2. The sum of squared `eLpNorm`s is bounded, per α, by a constant times the
   `chartSobolevRawNormPou` α-summand. This uses
   `chartRSTwistInv_pointwise_opNorm_isBounded_on_compact` to bound the chart
   twist on the partition-of-unity tsupport, plus the uniform multi-index
   projection operator-norm bound.

3. The full `chartSobolevRawNormPou` is bounded by a constant times
   `(wtwokTwoNorm g 1 T)^2`, via the existing
   `chartSobolevRawNormPou_le_wtwokTwoNorm_sq` headline.
-/
theorem sq_finset_sum_eLpNorm_two_tensorChartComp_le_wtwokTwoNorm_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              eLpNorm
                (tensorChartComp (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
        ENNReal.ofReal C *
          (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set Idx_card_nat : ℕ := (Finset.univ : Finset
      (Fin r → Fin (Module.finrank ℝ E))).card with hIdx_card_nat_def
  set Jdx_card_nat : ℕ := (Finset.univ : Finset
      (Fin s → Fin (Module.finrank ℝ E))).card with hJdx_card_nat_def
  -- Cauchy–Schwarz step: the total cardinality is `Sfin.card · Idx_card · Jdx_card`.
  -- We use the chart-component bridge constant and the
  -- `chartSobolevRawNormPou_le_wtwokTwoNorm_sq` constant.
  obtain ⟨C_aggr, hC_aggr_nn, hC_aggr_bound⟩ :=
    finset_sum_sum_IJ_sq_eLpNorm_two_tensorChartComp_raw_le
      (I := I) (M := M) h_atlas g r s
  obtain ⟨C_pou, hC_pou_nn, hC_pou_bound⟩ :=
    chartSobolevRawNormPou_le_wtwokTwoNorm_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s
  -- The total cardinality `N := Sfin.card · Idx_card_nat · Jdx_card_nat`.
  set N_nat : ℕ := Sfin.card * Idx_card_nat * Jdx_card_nat with hN_nat_def
  refine ⟨(N_nat : ℝ) * (C_aggr * C_pou),
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hC_aggr_nn hC_pou_nn), ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  -- Step 1: Cauchy–Schwarz on the triple finset sum.
  -- Recast LHS as a sum over the product type.
  set f : ((M × (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)))) → ℝ≥0∞ :=
    fun p =>
      eLpNorm (tensorChartComp (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) p.1 p.2.1 p.2.2) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) p.1)) with hf_def
  -- We define the product finset.
  set FProd : Finset (M × (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))) :=
    Sfin ×ˢ Finset.univ ×ˢ Finset.univ with hFProd_def
  -- LHS = Σ_{p ∈ FProd} f p.
  have h_lhs_sum :
      (∑ α ∈ Sfin,
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
              (tensorChartComp (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α))) =
      ∑ p ∈ FProd, f p := by
    rw [hFProd_def]
    rw [Finset.sum_product
      (f := fun p : M × (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) => f p)]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
        f (α, p.1, p.2))]
  rw [h_lhs_sum]
  -- Σ_{p ∈ FProd} (f p)² is the squared aggregate.
  have h_sq_sum :
      (∑ p ∈ FProd, f p) ^ 2 ≤ (FProd.card : ℝ≥0∞) * ∑ p ∈ FProd, (f p) ^ 2 :=
    ennreal_sq_finset_sum_le_card_mul_finset_sum_sq FProd f
  refine h_sq_sum.trans ?_
  -- Compute `FProd.card = N_nat`.
  have h_card : (FProd.card : ℝ≥0∞) = (N_nat : ℝ≥0∞) := by
    rw [hFProd_def, hN_nat_def]
    rw [Finset.card_product, Finset.card_product]
    -- (s ×ˢ t).card = s.card * t.card
    push_cast
    ring
  rw [h_card]
  -- Convert Σ_{p ∈ FProd} (f p)² back to nested sums.
  have h_sq_sum_eq :
      ∑ p ∈ FProd, (f p) ^ 2 =
        ∑ α ∈ Sfin,
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (eLpNorm
                (tensorChartComp (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) ^ 2 := by
    rw [hFProd_def]
    rw [Finset.sum_product
      (f := fun p : M × (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) => (f p) ^ 2)]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
        (f (α, p.1, p.2)) ^ 2)]
  rw [h_sq_sum_eq]
  -- Step 2: bound nested sum by aggregate.
  have h_step2 := hC_aggr_bound T
  -- `h_step2 : Σ_α Σ_IJ (eLpNorm)² ≤ ofReal C_aggr · Spou(T)`.
  refine (mul_le_mul_of_nonneg_left h_step2 (zero_le _)).trans ?_
  -- Step 3: Spou(T) ≤ ofReal C_pou · W.
  have h_step3 := hC_pou_bound T
  -- We want: N_nat · (ofReal C_aggr · ofReal C_pou · W) ≤ ofReal(N · C_aggr · C_pou) · W.
  refine (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h_step3 (zero_le _)) (zero_le _)).trans ?_
  -- Now: (N_nat : ℝ≥0∞) · (ofReal C_aggr · (ofReal C_pou · W))
  --    = ofReal(N · C_aggr · C_pou) · W.
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- (N_nat : ℝ≥0∞) · ofReal C_aggr · ofReal C_pou = ofReal(N · C_aggr · C_pou).
  have hN_ofReal : (N_nat : ℝ≥0∞) = ENNReal.ofReal (N_nat : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  rw [hN_ofReal]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hC_aggr_nn)]
  refine le_of_eq ?_
  congr 1
  ring

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.sq_finset_sum_eLpNorm_two_tensorChartComp_le_wtwokTwoNorm_sq
end Sanity
