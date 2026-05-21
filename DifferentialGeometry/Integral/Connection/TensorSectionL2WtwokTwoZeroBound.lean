import DifferentialGeometry.Integral.Connection.RawTensorConnLapL2WtwokTwoBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound

/-!
# Manifold L² bound for a smooth compactly-supported tensor section by the
# order-zero chart-Sobolev norm

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, and a
smooth compactly-supported `(r, s)`-tensor section `T : SmoothCcTensor g r s`,
this file ships the bound

  `∫⁻ x, ‖T.toSection x‖ₑ ^ 2 ∂μ_g ≤ ENNReal.ofReal C · (wtwokTwoNorm g 0 T) ^ 2`

with `C` non-negative and independent of `T`. The right-hand side is the
square of the order-zero tensor chart-Sobolev norm, which decomposes as the
unweighted Lebesgue L² norms of the chart-frame scalar components summed over
the chart atlas and the finite component-index sets.

## Strategy

The proof composes two bridges:

* **Manifold L² to POU aggregate.** Define a chart-target POU-weighted
  aggregate `chartSobolevSectionNormPou g r s T`, the finite sum over the
  chart-atlas partition-of-unity support set of the chart-target Lebesgue
  integrals of `ρ_α(symm y)² · ‖T.toSection (symm y)‖²`. A pointwise
  Cauchy–Schwarz step `(Σ ρ_α · a)² ≤ N · Σ ρ_α² · a²` with `Σ ρ_α = 1` and
  the chart-pushforward of each per-α manifold integral give

  `∫⁻ ‖T.toSection x‖ₑ ^ 2 ∂μ_g ≤
        ENNReal.ofReal C_bridge · chartSobolevSectionNormPou g r s T`.

* **POU aggregate to order-zero chart-Sobolev norm.** Using the chart
  twist op-norm bound (`chartRSTwist_pointwise_opNorm_isBounded_on_compact`),
  one bounds `‖T.toSection b‖² ≤ C_twist · ‖tensorRSChartE_section_repr T.toSection b‖²`
  on `tsupport ρ_α`, then applies the existing order-zero per-α bound
  `chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq` to obtain

  `chartSobolevSectionNormPou g r s T ≤
        ENNReal.ofReal C₀ · (wtwokTwoNorm g 0 T) ^ 2`.

The composition produces the headline.
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

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## POU-weighted chart-target aggregate for the underlying tensor section

We package the right-hand side of the POU-weighted manifold L²-bound into a
single manifold-defined non-negative `ℝ≥0∞`-valued aggregate, mirroring
`chartSobolevRawNormPou` but with `T.toSection` in place of
`rawTensorConnLap T.toSection`. -/

/-- **POU-weighted chart-target aggregate for the tensor section.** For a
smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and a smooth
compactly-supported `(r, s)`-tensor section `T : SmoothCcTensor g r s`, the
chart-target POU-weighted aggregate is the finite sum, over the chart-atlas
partition-of-unity support set `chartAtlasPOU_finset I M`, of the chart-target
Lebesgue integrals of `ENNReal.ofReal` of
`ρ_α((extChartAt I α).symm (toEuclidean.symm y))² · (chart-pushed squared
model-fiber norm of `T.toSection`)(y)`. -/
noncomputable def chartSobolevSectionNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M => T.toSection b) y)
      ∂(volume : Measure EuclN)

/-- Unfolding lemma for `chartSobolevSectionNormPou`. -/
@[simp] lemma chartSobolevSectionNormPou_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevSectionNormPou (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M => T.toSection b) y)
          ∂(volume : Measure EuclN) := rfl

/-! ## Cauchy–Schwarz: pointwise bound on `‖T.toSection b‖²`

For each point `b : M`, the squared model-fibre norm of `T.toSection b` is
bounded above by `(card chartAtlasPOU_finset) · Σ_α ρ_α(b)² · ‖T.toSection b‖²`.
This follows from `Σ_α ρ_α(b) = 1` and the elementary finset Cauchy–Schwarz
inequality `(Σ_α a_α)² ≤ N · Σ_α a_α²`. -/

private lemma normSq_section_le_card_mul_sum_pou_sq_mul_normSq
    {r s : ℕ} (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    (‖T x‖ ^ 2 : ℝ) ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖T x‖ ^ 2 := by
  classical
  set v : ℝ := ‖T x‖ with hv_def
  set sset : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hs_def
  have hv_nn : 0 ≤ v := norm_nonneg _
  have hv_sq_nn : 0 ≤ v ^ 2 := sq_nonneg _
  -- POU sum equals one at `x`.
  have h_sum :=
    chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  -- `v² = (Σ ρ_α · v)²` since `Σ ρ_α = 1`.
  have hv_sq_eq :
      v ^ 2 = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := by
    have heq : ∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v = v := by
      rw [← Finset.sum_mul, h_sum, one_mul]
    rw [heq]
  -- Apply finset Cauchy–Schwarz: `(Σ a_α)² ≤ N · Σ a_α²` with `a_α = ρ_α · v`.
  -- The lemma `sum_finset_sq_le_card_mul_sum_sq` lives in the bridge file but
  -- we restate it inline via `Finset.sum_mul_sq_le_sq_mul_sq` for clarity.
  have hCS : (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 ≤
      (sset.card : ℝ) *
        ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq sset
      (fun _ : M => (1 : ℝ))
      (fun α : M => (chartAtlasPOU I M α : M → ℝ) x * v)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _α ∈ sset, (1 : ℝ)) = (sset.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    convert hbase using 1
  -- Rewrite each `(ρ_α · v)² = ρ_α² · v²`.
  have h_factor_eq : ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 =
      ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 :=
    Finset.sum_congr rfl (fun α _ => by ring)
  rw [h_factor_eq] at hCS
  -- Combine: `v² = (Σ ρ_α · v)² ≤ N · Σ ρ_α² · v²`.
  calc (‖T x‖ ^ 2 : ℝ)
      = v ^ 2 := rfl
    _ = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := hv_sq_eq
    _ ≤ (sset.card : ℝ) *
          ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 := hCS

/-! ## Per-α chart-pushforward of `∫_M ρ_α² · ‖T.toSection‖² dμ_g`

For each `α ∈ chartAtlasPOU_finset I M`, the manifold integral of
`ρ_α² · ‖T.toSection‖²` against `μ_g` equals the chart-target integral against
`volume`, weighted by `chartDensity g α` and the Haar factor `c_E`. -/

private lemma manifold_lintegral_pou_sq_section_normSq_eq_chartTarget
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g r s)
    (hsec_meas :
      Measurable (fun x : M => ‖T.toSection x‖ ^ 2))
    (α : M) :
    ∫⁻ x,
        ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖T.toSection x‖ ^ 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) := by
  classical
  set F : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖T.toSection x‖ ^ 2) with hF_def
  have hρ_cont : Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    ((chartAtlasPOU I M α)).contMDiff.continuous
  have hρ_meas : Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    hρ_cont.measurable
  have hρ_sq_meas : Measurable (fun x : M => ((chartAtlasPOU I M α : M → ℝ) x) ^ 2) :=
    hρ_meas.pow_const 2
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact ENNReal.measurable_ofReal.comp (hρ_sq_meas.mul hsec_meas)
  -- `F` is supported in `(chartAt H α).source`.
  have hF_supp : ∀ x : M, x ∉ (chartAt H α).source → F x = 0 := by
    intro x hx
    have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
      have hsub : tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate (I := I) (M := M) α
      have hx_notsupp : x ∉ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun hc => hx (hsub hc)
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖T.toSection x‖ ^ 2) = 0
    rw [hρ_zero]
    simp
  rw [show riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) from rfl]
  rw [riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp]
  rw [chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas]

/-! ## Bridge to `pushedNormSq` for `T.toSection`

On the chart-target image, `‖T.toSection (symm.symm y)‖²` equals
`tensorTrivProjPushedNormSq g r s α (fun b => T.toSection b) y`. -/

private lemma section_normSq_apply_eq_pushedNormSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g r s)
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2
        : ℝ) =
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M => T.toSection b) y := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem
      (I := I) (M := M) g r s α
      (fun b : M => T.toSection b) hy]
  -- `‖TensorRSSpace.toModel X‖ = ‖X‖` by the induced norm.
  rfl

/-! ## Per-α density × POU² uniform bound (reused argument)

We reuse the density bound `density_pou_sq_le` from the existing raw bridge
file inline (the proof is identical to that of the raw analog, replacing the
raw connection Laplacian by `T.toSection`). The bound is symbolic: it does
not depend on which scalar `‖·‖² function` is multiplied — it only bounds
`chartDensity g α (symm.symm y) · ρ_α(symm.symm y)²` by
`(chartDensitySupPou g α + 1) · ρ_α(symm.symm y)²` on the chart target. -/

private lemma density_pou_sq_le_section
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartDensity g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) ≤
      (chartDensitySupPou (I := I) (M := M) g α + 1) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) x with hρ_def
  set dens : ℝ := chartDensity g α x with hdens_def
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α x
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  by_cases hρ_zero : ρ = 0
  · rw [show ρ ^ 2 = 0 from by rw [hρ_zero]; ring]
    simp
  · have hx_supp : x ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ_zero)
    have hy_image : (toEuclidean (E := E)).symm y ∈
        (extChartAt I α) '' (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
      refine ⟨x, hx_supp, ?_⟩
      rw [hx_def]
      exact (extChartAt I α).right_inv hy_target
    have hdens_le : dens ≤ chartDensitySupPou (I := I) (M := M) g α := by
      rw [hdens_def, hx_def]
      exact chartDensitySupPou_le (I := I) (M := M) g α h_supp_ne hy_image
    have hbound : dens ≤ chartDensitySupPou (I := I) (M := M) g α + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right hbound hρ_sq_nn

/-! ## Bridge 1: manifold L² ≤ Const · POU section aggregate

Following the proof of `rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou`,
we bound the manifold L² of `‖T.toSection‖²` by a constant multiple of the
POU-weighted chart-target aggregate `chartSobolevSectionNormPou`. -/

theorem tensorSection_L2NormSq_le_chartSobolevSectionNormPou
    (_h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable (fun x : M => ‖T.toSection x‖ ^ 2) →
          ∫⁻ x, (‖T.toSection x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g) *
              chartSobolevSectionNormPou (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g,
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hsec_meas
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set N : ℕ := Sfin.card with hN_def
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set Mα : M → ℝ := fun α => chartDensitySupPou (I := I) (M := M) g α with hMα_def
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartDensitySupPou_nonneg (I := I) (M := M) g α
  set C : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g with hC_def
  -- `enorm² = ofReal ‖·‖²` rewrite.
  have henorm_sq :
      (fun x : M => (‖T.toSection x‖ₑ : ℝ≥0∞) ^ 2) =
        (fun x : M => ENNReal.ofReal (‖T.toSection x‖ ^ 2)) := by
    funext x
    have hen : ‖T.toSection x‖ₑ = ENNReal.ofReal ‖T.toSection x‖ :=
      (ofReal_norm _).symm
    rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [henorm_sq]
  -- Step 1: pointwise Cauchy–Schwarz bound.
  have h_pointwise : ∀ x : M,
      ENNReal.ofReal (‖T.toSection x‖ ^ 2) ≤
        ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖T.toSection x‖ ^ 2) := by
    intro x
    have hle := normSq_section_le_card_mul_sum_pou_sq_mul_normSq
      (I := I) (M := M) (r := r) (s := s) (fun b => T.toSection b) x
    refine ENNReal.ofReal_le_ofReal hle
  -- Step 2: integrate.
  have h_int_le :
      ∫⁻ x, ENNReal.ofReal (‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
            ∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.lintegral_mono h_pointwise
  -- Step 3: split the RHS.
  have h_nn_each : ∀ x : M, ∀ α ∈ Sfin,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2 := by
    intro x α _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_nn_sum : ∀ x : M,
      0 ≤ ∑ α ∈ Sfin,
        ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2 := by
    intro x; exact Finset.sum_nonneg (h_nn_each x)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h_ofReal_factor : ∀ x : M,
      ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) =
        ENNReal.ofReal (N : ℝ) *
          ENNReal.ofReal (∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) := fun x =>
    ENNReal.ofReal_mul hN_nn
  have h_ofReal_sum : ∀ x : M,
      ENNReal.ofReal (∑ α ∈ Sfin,
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) =
        ∑ α ∈ Sfin, ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (h_nn_each x)]
  have h_int_le' :
      ∫⁻ x, ENNReal.ofReal (‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          ∑ α ∈ Sfin,
            ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
              ∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_int_le
      _ = ∫⁻ x, ENNReal.ofReal (N : ℝ) *
              ENNReal.ofReal (∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            refine lintegral_congr ?_
            intro x; exact h_ofReal_factor x
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ENNReal.ofReal (∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            rw [MeasureTheory.lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ∑ α ∈ Sfin, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            refine lintegral_congr ?_
            intro x; exact h_ofReal_sum x
      _ = ENNReal.ofReal (N : ℝ) *
            ∑ α ∈ Sfin,
              ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            exact lintegral_finset_sum _ (fun α _ => by
              have hρ_cont :
                  Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                ((chartAtlasPOU I M α)).contMDiff.continuous
              have hρ_meas :
                  Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                hρ_cont.measurable
              exact ENNReal.measurable_ofReal.comp
                ((hρ_meas.pow_const 2).mul hsec_meas))
  -- Step 4: per-α push-forward bound.
  have h_per_alpha : ∀ α ∈ Sfin,
      ∫⁻ x, ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    have h_supp_ne : (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty := by
      rw [chartAtlasPOU_finset_mem] at hα_mem
      exact hα_mem.mono (subset_tsupport _)
    rw [manifold_lintegral_pou_sq_section_normSq_eq_chartTarget
      (I := I) (M := M) g T hsec_meas α]
    -- Pointwise bound on `chartTargetEuclid α`.
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖T.toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ≤ ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)) := by
      intro y hy
      have hdens_pou_sq_le := density_pou_sq_le_section
        (I := I) (M := M) g α h_supp_ne hy
      have hdens_nn : 0 ≤ chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
        Real.sqrt_nonneg _
      have hρ_sq_nn :
          0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        sq_nonneg _
      have hnormSq_nn :
          0 ≤ ‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 :=
        sq_nonneg _
      have h_pushed := section_normSq_apply_eq_pushedNormSq
        (I := I) (M := M) (r := r) (s := s) g T α hy
      have h_dens_pou_sq_nn : 0 ≤
          chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        mul_nonneg hdens_nn hρ_sq_nn
      have h_ofReal_inner : ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
            ‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖T.toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) :=
        ENNReal.ofReal_mul hρ_sq_nn
      rw [h_ofReal_inner]
      have hkey :
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ≤ ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
        have h_Mα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
        rw [← ENNReal.ofReal_mul hdens_nn,
            ← ENNReal.ofReal_mul h_Mα1_nn]
        exact ENNReal.ofReal_le_ofReal hdens_pou_sq_le
      have h_pushed_eq :
          ENNReal.ofReal
            (‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M => T.toSection b) y) := by
        rw [h_pushed]
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            ring
        _ ≤ (ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (‖T.toSection
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
            ring
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)) := by
            rw [h_pushed_eq]
    have hset_int_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y))
              ∂(volume : Measure EuclN) :=
      MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt_bound)
    have hpull :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (Mα α + 1) *
            (ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y))
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    calc (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                    ‖T.toSection
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
              ∂(volume : Measure EuclN)
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y))
              ∂(volume : Measure EuclN) :=
        mul_le_mul_right hset_int_le _
      _ = (euclideanHaarFactor E : ℝ≥0∞) *
            (ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN)) := by rw [hpull]
      _ = ((euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN) := by ring
      _ = ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN) := by
            congr 1
            rw [hcE_def]
            have hMα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
            rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
            congr 1
            rw [ENNReal.ofReal_coe_nnreal]
  -- Step 5: combine.
  set Sum_pou : Finset M → ℝ := fun s =>
    ∑ β ∈ s, (Mα β + 1) with hSum_pou_def
  set C_inner : ℝ := cE * Sum_pou Sfin with hC_inner_def
  have hC_inner_nn : 0 ≤ C_inner := by
    refine mul_nonneg hcE_nn ?_
    refine Finset.sum_nonneg ?_
    intro β _; have := hMα_nn β; linarith
  have hC_eq : C = (N : ℝ) * C_inner := by
    rw [hC_def, hN_def, hSfin_def, hC_inner_def, hSum_pou_def, hMα_def, hcE_def]
    rfl
  have hper_term_le : ∀ α ∈ Sfin,
      cE * (Mα α + 1) ≤ C_inner := by
    intro α hα_mem
    have h_term_le : (Mα α + 1) ≤ Sum_pou Sfin := by
      have hsum_nn : ∀ β ∈ Sfin, 0 ≤ Mα β + 1 := by
        intro β _; have := hMα_nn β; linarith
      exact Finset.single_le_sum (f := fun β => Mα β + 1) hsum_nn hα_mem
    rw [hC_inner_def]
    exact mul_le_mul_of_nonneg_left h_term_le hcE_nn
  have hper_alpha_C_inner : ∀ α ∈ Sfin,
      ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal C_inner *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    refine mul_le_mul_left ?_ _
    exact ENNReal.ofReal_le_ofReal (hper_term_le α hα_mem)
  have hsum_per_alpha_le :
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖T.toSection x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
    refine Finset.sum_le_sum ?_
    intro α hα_mem
    exact le_trans (h_per_alpha α hα_mem) (hper_alpha_C_inner α hα_mem)
  have hpull_sum :
      ∑ α ∈ Sfin,
          ENNReal.ofReal C_inner *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN)
        = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
    rw [← Finset.mul_sum]
  have h_combined :
      ENNReal.ofReal (N : ℝ) *
        ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          (ENNReal.ofReal C_inner *
            chartSobolevSectionNormPou (I := I) (M := M) g r s T) := by
    refine mul_le_mul_right ?_ _
    rw [chartSobolevSectionNormPou_def]
    calc
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := hsum_per_alpha_le
      _ = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := hpull_sum
  have h_NC_eq : ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C_inner =
      ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hN_nn, ← hC_eq]
  have h_final_eq :
      ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal C_inner *
          chartSobolevSectionNormPou (I := I) (M := M) g r s T) =
        ENNReal.ofReal C *
          chartSobolevSectionNormPou (I := I) (M := M) g r s T := by
    rw [← mul_assoc, h_NC_eq]
  exact le_trans h_int_le' (le_trans h_combined (le_of_eq h_final_eq))

/-! ## Per-α uniform twist bound: `‖T.toSection b‖² ≤ K_α · ‖repr T.toSection b‖²`

On `tsupport ρ_α`, the manifold-fibre norm of `T.toSection b` is bounded by a
uniform constant `K_α` times the chart-`α`-trivialised representation norm. The
bound is `‖toModel X‖ ≤ ‖chartRSTwist α b‖_op · ‖triv.continuousLinearMapAt b X‖`,
using the round-trip identity `chartRSTwist ∘ chartRSTwistInv = id` on the
trivialisation base set. -/

private lemma section_normSq_le_twist_repr_normSq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s) (b : M),
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        (‖T.toSection b‖ ^ 2 : ℝ) ≤
          K * ‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) b‖ ^ 2 := by
  classical
  -- Compact tsupport set inside the chart-α source.
  set K_set : Set M := tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  obtain ⟨C₁, hC₁_pos, hC₁_le⟩ :=
    chartRSTwist_pointwise_opNorm_isBounded_on_compact
      (I := I) (M := M) h_atlas α hK_compact hK_sub r s
  refine ⟨C₁ ^ 2, by positivity, ?_⟩
  intro T b hb
  -- `b ∈ chart source`.
  have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
  have hb_baseSet : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb_chart
  -- Bridge: `repr T.toSection b = chartRSTwistInv α b r s (toModel(T.toSection b))`.
  have h_bridge :
      tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z) b =
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel (𝕜 := ℝ) (T.toSection b)) := by
    unfold tensorRSChartE_section_repr
    exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α hb_chart (T.toSection b)
  -- Round-trip: `toModel(T.toSection b) = chartRSTwist α b r s (repr T.toSection b)`.
  have h_round :
      TensorRSSpace.toModel (𝕜 := ℝ) (T.toSection b) =
        chartRSTwist (I := I) (M := M) α b r s
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) b) := by
    rw [h_bridge]
    rw [chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_baseSet r s _]
  -- Norm bound.
  have h_norm_eq :
      ‖T.toSection b‖ = ‖TensorRSSpace.toModel (𝕜 := ℝ) (T.toSection b)‖ := rfl
  rw [h_norm_eq, h_round]
  -- Apply the uniform op-norm bound for chartRSTwist.
  have h_op_bound :=
    hC₁_le b hb (tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b)
  -- Square both sides.
  have h_C₁_nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁_pos
  have h_lhs_nn : 0 ≤ ‖chartRSTwist (I := I) (M := M) α b r s
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) b)‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ C₁ * ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b‖ :=
    mul_nonneg h_C₁_nn (norm_nonneg _)
  have h_sq :
      ‖chartRSTwist (I := I) (M := M) α b r s
        (tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z) b)‖ ^ 2 ≤
      (C₁ * ‖tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) b‖) ^ 2 := by
    have := mul_le_mul h_op_bound h_op_bound h_lhs_nn h_rhs_nn
    simpa [sq] using this
  refine le_trans h_sq ?_
  ring_nf
  apply le_of_eq
  ring

/-! ## Per-α bound: chartSobolevSectionNormPou summand ≤ K_α · (wtwokTwoNorm g 0 T)²

The proof composes the twist bound with the existing
`chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq` and a
monotonicity bound on `wkpNorm 0 2 ≤ wtwokTwoNorm g 0 T`. -/

private lemma per_alpha_section_summand_le_wtwokTwoNorm_zero_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (_h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  obtain ⟨K_twist, hK_twist_nn, hK_twist_bound⟩ :=
    section_normSq_le_twist_repr_normSq
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨K_repr, hK_repr_nn, hK_repr_bound⟩ :=
    chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
      (I := I) (M := M) g r s α
  set Idx_card_nat : ℕ := (Finset.univ : Finset
      (Fin r → Fin (Module.finrank ℝ E))).card with hIdx_card_nat_def
  set Jdx_card_nat : ℕ := (Finset.univ : Finset
      (Fin s → Fin (Module.finrank ℝ E))).card with hJdx_card_nat_def
  set Idx_card : ℝ := (Idx_card_nat : ℝ) with hIdx_card_def
  set Jdx_card : ℝ := (Jdx_card_nat : ℝ) with hJdx_card_def
  have hIdx_nn : 0 ≤ Idx_card := Nat.cast_nonneg _
  have hJdx_nn : 0 ≤ Jdx_card := Nat.cast_nonneg _
  refine ⟨K_twist * K_repr * (Idx_card * Jdx_card),
    mul_nonneg (mul_nonneg hK_twist_nn hK_repr_nn)
      (mul_nonneg hIdx_nn hJdx_nn), ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 with hW_def
  -- Step 1: bound the section integrand by K_twist · repr integrand.
  -- Pointwise: ofReal(ρ² · pushedNormSq) ≤ K_twist · ofReal(ρ² · ‖repr‖²) on chart target.
  have h_pt : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M => T.toSection b) y) ≤
      ENNReal.ofReal K_twist *
        (ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (‖tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
    intro y hy
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b
    set P : ℝ := tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M => T.toSection b) y
    set R : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) b‖ ^ 2
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α b
    have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
    have hP_nn : 0 ≤ P :=
      tensorTrivProjPushedNormSq_nonneg (I := I) (M := M) g r s α _ y
    have hR_nn : 0 ≤ R := sq_nonneg _
    -- Bridge: P = ‖T.toSection b‖² on chart target.
    have hP_eq_sec_normSq :
        P = ‖T.toSection b‖ ^ 2 := by
      symm
      exact section_normSq_apply_eq_pushedNormSq
        (I := I) (M := M) (r := r) (s := s) g T α hy
    -- Case split on ρ = 0.
    by_cases hρ_zero : ρ = 0
    · -- ρ = 0 → both sides vanish.
      rw [show ρ ^ 2 = 0 from by rw [hρ_zero]; ring]
      simp
    · -- ρ ≠ 0 → b ∈ tsupport ρ_α, so the twist bound applies.
      have hb_supp : b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ (Function.mem_support.mpr hρ_zero)
      have h_twist := hK_twist_bound T b hb_supp
      -- `P = ‖T.toSection b‖² ≤ K_twist · R`.
      have h_PR : P ≤ K_twist * R := by
        rw [hP_eq_sec_normSq]
        exact h_twist
      -- Multiply by ρ² (≥ 0).
      have h_scaled : ρ ^ 2 * P ≤ ρ ^ 2 * (K_twist * R) :=
        mul_le_mul_of_nonneg_left h_PR hρ_sq_nn
      -- ofReal monotonicity.
      have h_lhs_eq :
          ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal P = ENNReal.ofReal (ρ ^ 2 * P) :=
        (ENNReal.ofReal_mul hρ_sq_nn).symm
      rw [h_lhs_eq]
      have h_rhs_factor :
          ρ ^ 2 * (K_twist * R) = K_twist * (ρ ^ 2 * R) := by ring
      rw [h_rhs_factor] at h_scaled
      refine (ENNReal.ofReal_le_ofReal h_scaled).trans ?_
      rw [ENNReal.ofReal_mul hK_twist_nn]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
      rw [ENNReal.ofReal_mul hρ_sq_nn]
  -- Step 2: integrate.
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M => T.toSection b) y)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal K_twist *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (‖tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  -- Pull out K_twist.
  rw [show (fun y : EuclN =>
      ENNReal.ofReal K_twist *
        (ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (‖tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))) =
      (fun y : EuclN =>
        ENNReal.ofReal K_twist *
          (ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))) from rfl] at h_int_mono
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_int_mono
  -- Apply the existing per-α repr bound.
  have h_repr_bound := hK_repr_bound T
  -- Chain: lhs ≤ ofReal K_twist · (ofReal K_repr · Σ Σ (wkpNorm 0 2)²)
  --           = ofReal (K_twist · K_repr) · Σ Σ (wkpNorm 0 2)²
  --       ≤ ofReal (K_twist · K_repr) · (Idx_card · Jdx_card · W).
  refine h_int_mono.trans ?_
  -- Step 3: bound the chart-component sum by Idx_card · Jdx_card · W.
  -- First, each summand: (wkpNorm 0 2 (tensorChartComp α IJ))² ≤ W.
  have hwkpNorm_le_W : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W := by
    intro Idx Jdx
    -- `wkpNorm (2 * 0) 2 = wkpNorm 0 2`.
    have h_term : wkpNorm (d := Module.finrank ℝ E) 0 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        wtwokTwoNorm (I := I) (M := M) g 0 T := by
      unfold wtwokTwoNorm
      -- Convert `wkpNorm 0 2 = wkpNorm (2*0) 2`.
      have h_zero_eq : wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) =
        wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := by
        norm_num
      rw [h_zero_eq]
      have h_inner : wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ≤
          ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                (chartTargetEuclid (I := I) (M := M) α) := by
        calc wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)
            ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
              Finset.single_le_sum
                (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                  wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
                (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
          _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α) :=
              Finset.single_le_sum
                (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                  ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                    wkpNorm (d := Module.finrank ℝ E) (2 * 0) 2
                      (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                      (chartTargetEuclid (I := I) (M := M) α))
                (fun _ _ => zero_le _) (Finset.mem_univ Idx)
      refine h_inner.trans ?_
      exact ENNReal.le_tsum α
    exact pow_le_pow_left' h_term 2
  -- Bound the double sum.
  have hsum_le_card : ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (Idx_card_nat : ℝ≥0∞) * (Jdx_card_nat : ℝ≥0∞) * W := by
    have h_step1 :
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (wkpNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
          ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
      refine Finset.sum_le_sum (fun Idx _ => ?_)
      refine Finset.sum_le_sum (fun Jdx _ => ?_)
      exact hwkpNorm_le_W Idx Jdx
    refine h_step1.trans ?_
    have h_inner_eq :
        (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
          (Idx_card_nat : ℝ≥0∞) * ((Jdx_card_nat : ℝ≥0∞) * W) := by
      have h_inner :
          (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
          ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            (Jdx_card_nat : ℝ≥0∞) * W := by
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h_inner, Finset.sum_const, nsmul_eq_mul]
    rw [h_inner_eq]
    rw [mul_assoc]
  -- Chain.
  calc ENNReal.ofReal K_twist *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN)
      ≤ ENNReal.ofReal K_twist *
          (ENNReal.ofReal K_repr *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (wkpNorm (d := Module.finrank ℝ E) 0 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2) :=
          mul_le_mul_of_nonneg_left h_repr_bound (zero_le _)
    _ = ENNReal.ofReal (K_twist * K_repr) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (wkpNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
          rw [ENNReal.ofReal_mul hK_twist_nn, mul_assoc]
    _ ≤ ENNReal.ofReal (K_twist * K_repr) *
          ((Idx_card_nat : ℝ≥0∞) * (Jdx_card_nat : ℝ≥0∞) * W) :=
          mul_le_mul_of_nonneg_left hsum_le_card (zero_le _)
    _ = ENNReal.ofReal (K_twist * K_repr * (Idx_card * Jdx_card)) * W := by
          have hKK_nn : 0 ≤ K_twist * K_repr := mul_nonneg hK_twist_nn hK_repr_nn
          have hIdx_ofReal : ENNReal.ofReal Idx_card = (Idx_card_nat : ℝ≥0∞) := by
            rw [hIdx_card_def]
            exact ENNReal.ofReal_natCast _
          have hJdx_ofReal : ENNReal.ofReal Jdx_card = (Jdx_card_nat : ℝ≥0∞) := by
            rw [hJdx_card_def]
            exact ENNReal.ofReal_natCast _
          have h_eq : ENNReal.ofReal (K_twist * K_repr * (Idx_card * Jdx_card)) =
              ENNReal.ofReal (K_twist * K_repr) *
                ((Idx_card_nat : ℝ≥0∞) * (Jdx_card_nat : ℝ≥0∞)) := by
            rw [ENNReal.ofReal_mul hKK_nn, ENNReal.ofReal_mul hIdx_nn]
            rw [hIdx_ofReal, hJdx_ofReal]
          rw [h_eq]
          ring

/-! ## Bridge 2: chartSobolevSectionNormPou ≤ Const · (wtwokTwoNorm g 0 T)² -/

theorem chartSobolevSectionNormPou_le_wtwokTwoNorm_zero_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        chartSobolevSectionNormPou (I := I) (M := M) g r s T ≤
          ENNReal.ofReal C *
            (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set Kα : M → ℝ := fun α => Classical.choose
    (per_alpha_section_summand_le_wtwokTwoNorm_zero_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s α) with hKα_def
  have hKα_spec : ∀ α : M, 0 ≤ Kα α ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal (Kα α) *
            (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := fun α =>
    Classical.choose_spec
      (per_alpha_section_summand_le_wtwokTwoNorm_zero_sq
        (I := I) (M := M) h_atlas h_atlas_strong g r s α)
  set C : ℝ := ∑ α ∈ Sfin, Kα α with hC_def
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun α _ => (hKα_spec α).1)
  refine ⟨C, hC_nn, ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 with hW_def
  rw [chartSobolevSectionNormPou_def]
  refine (Finset.sum_le_sum (s := Sfin) (fun α _ => (hKα_spec α).2 T)).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [hC_def]
  rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => (hKα_spec α).1)]

/-! ## Headline -/

/-- **Manifold L² of a smooth compactly-supported tensor section bounded by the
order-zero chart-Sobolev norm.** For a smooth closed Riemannian manifold
`(M, g)` and ranks `(r, s)`, there is a non-negative constant `C` such that for
every smooth compactly-supported `(r, s)`-tensor section `T` with Borel-
measurable squared pointwise norm, the `L²` norm of `T.toSection` (taken with
respect to the Riemannian volume measure on `M`) is bounded by `C` times the
square of the order-zero tensor chart-Sobolev norm `wtwokTwoNorm g 0 T`. -/
theorem tensorSection_L2NormSq_le_wtwokTwoNorm_zero_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        (letI : MeasurableSpace M := borel M
         haveI : BorelSpace M := ⟨rfl⟩
         Measurable (fun x : M => ‖T.toSection x‖ ^ 2)) →
        ∫⁻ x, (‖T.toSection x‖ₑ : ℝ≥0∞) ^ 2
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set C_bridge : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g
    with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge :=
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g
  obtain ⟨C_B3, hC_B3_nn, hC_B3_bound⟩ :=
    chartSobolevSectionNormPou_le_wtwokTwoNorm_zero_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s
  refine ⟨C_bridge * C_B3, mul_nonneg hC_bridge_nn hC_B3_nn, ?_⟩
  intro T hsec_meas
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 with hW_def
  obtain ⟨_C_bridge', _hC_bridge'_nn, hC_bridge_bound⟩ :=
    tensorSection_L2NormSq_le_chartSobolevSectionNormPou
      (I := I) (M := M) h_atlas g r s
  have h1 := hC_bridge_bound T hsec_meas
  refine h1.trans ?_
  have h2 := hC_B3_bound T
  refine (mul_le_mul_of_nonneg_left h2 (zero_le _)).trans ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul hC_bridge_nn]

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.tensorSection_L2NormSq_le_chartSobolevSectionNormPou
#print axioms
  DifferentialGeometry.Integral.Connection.chartSobolevSectionNormPou_le_wtwokTwoNorm_zero_sq
#print axioms
  DifferentialGeometry.Integral.Connection.tensorSection_L2NormSq_le_wtwokTwoNorm_zero_sq
end Sanity
