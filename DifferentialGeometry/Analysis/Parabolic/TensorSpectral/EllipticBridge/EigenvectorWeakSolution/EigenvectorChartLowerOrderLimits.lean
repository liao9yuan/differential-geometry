import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionGlobal
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.PouComponentBridge
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# The `n → ∞` `L²`-limits of the three lower-order coefficient terms

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
and a component multi-index `P₀`, the per-approximant chart bilinear identity of
the connection Laplacian carries three lower-order coefficient terms on its
right-hand side, evaluated at the partition-of-unity-weighted smooth approximant
`Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s h_atlas i n)`:

* the principal rotation coefficient `covPrincipalRotationCoeff g r s Tₙ α P₀`;
* the lower-order rotation value coefficient
  `covLowerOrderRotationValueCoeff g r s Tₙ α P₀`;
* the chart-density-weighted lower-order gradient coefficient
  `weightedGradCoeff g r s Tₙ α P₀ l`, together with its chart-Euclidean
  divergence `euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)`.

This file produces, for each of these, the `n → ∞` `L²`-limit in
`Lp ℝ 2 (chartL2Measure α)`.

## The tracing identity

With `wₙ := eigenvectorSmoothApprox g r s h_atlas i n` and
`Tₙ := pouSmul g r s α wₙ.toCcTensor`, the raw chart component of `Tₙ` is the
partition-of-unity-weighted chart component of `wₙ.toCcTensor`
(`tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou`), whose Euclidean
push-forward is the canonical Euclidean chart component
`tensorChartComponent g r s wₙ.toCcTensor α P`. Consequently each of the three
coefficients, evaluated at `Tₙ` and restricted to the chart target, is a finite
`C^∞`-coefficient-weighted sum of the two `T`-dependent atoms

* `tensorChartComponent g r s wₙ.toCcTensor α P` (the bare chart component);
* `euclidPartial k (tensorChartComponent g r s wₙ.toCcTensor α P)` (its
  chart-Euclidean partial).

The `L²`-limits of those two atoms are supplied by the companion files:
`eigenvectorChartComponentL2_tendsto` (chart component) and
`eigenvectorChartPartialLp_tendsto` (chart partial). Multiplication by a `C^∞`
coefficient — bounded on the compact partition-of-unity kernel, off which every
atom vanishes — preserves `L²`-convergence, and a finite sum of `L²`-convergent
sequences converges.

## Main definitions

* `covPrincipalRotationCoeffLimit g r s h_atlas i α P₀` — the explicit
  `L²`-limit function of `covPrincipalRotationCoeff g r s Tₙ α P₀`.
* `covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀` — the explicit
  `L²`-limit function of `covLowerOrderRotationValueCoeff g r s Tₙ α P₀`.
* `weightedGradCoeffLimit g r s h_atlas i α P₀ l` — the explicit `L²`-limit
  function of `weightedGradCoeff g r s Tₙ α P₀ l`.
* `weightedGradCoeffDivLimit g r s h_atlas i α P₀ l` — the explicit `L²`-limit
  function of `euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)`.

## Main results

* `covPrincipalRotationCoeff_tendsto`, `covLowerOrderRotationValueCoeff_tendsto`,
  `weightedGradCoeff_tendsto`, `weightedGradCoeffDiv_tendsto` — the four
  `n → ∞` `L²`-convergence headlines.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The compact partition-of-unity kernel of the chart

Every Euclidean chart component of a smooth section is the chart push-forward of
the partition-of-unity-weighted chart-frame scalar `tensorChartComponentScalar`,
whose closed support sits inside the closed support of the chart-atlas
partition-of-unity weight. The Euclidean image of that closed support is a
single compact set — the `kernel` of the chart — inside which **every** chart
component (and hence its chart-Euclidean partial) of **every** smooth section is
supported. -/

/-- The compact partition-of-unity kernel of the chart at `α`, transferred to
the Euclidean model space: the `toEuclidean`-image of the chart image of the
closed support of the chart-atlas partition-of-unity weight. -/
def chartPouKernel (α : M) : Set EuclN :=
  toEuclidean '' ((extChartAt I α) ''
    (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))

/-- The partition-of-unity kernel is compact. -/
lemma chartPouKernel_isCompact (α : M) :
    IsCompact (chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_isCompact
    (I := I) (M := M) α).image (toEuclidean (E := E)).continuous

/-- The partition-of-unity kernel is a measurable set. -/
lemma chartPouKernel_measurableSet (α : M) :
    MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
  (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.measurableSet

/-- The partition-of-unity kernel is contained in the Euclidean chart target. -/
lemma chartPouKernel_subset_chartTargetEuclid (α : M) :
    chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rw [chartPouKernel, chartTargetEuclid]
  refine Set.image_mono ?_
  exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_subset_target
    (I := I) (M := M) α

/-- If a Euclidean point lies outside the partition-of-unity kernel, then its
chart-Euclidean preimage lies outside the closed support of the chart-atlas
partition-of-unity weight. -/
private lemma notMem_pouTsupport_of_notMem_chartPouKernel
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hker : y ∉ chartPouKernel (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
  classical
  intro hb
  apply hker
  refine ⟨(toEuclidean (E := E)).symm y, ⟨_, hb, ?_⟩, ?_⟩
  · -- `extChartAt I α` recovers `toEuclidean.symm y` from its chart preimage.
    have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
    exact (extChartAt I α).right_inv hmem
  · exact toEuclidean.apply_symm_apply y

/-! ## Vanishing of the chart component off the partition-of-unity kernel

The Euclidean chart component `tensorChartComponent g r s S α Idx Jdx` of a
smooth section is the chart push-forward of `tensorChartComponentScalar`, the
chart-atlas partition-of-unity weight times the raw chart-frame component. It
therefore vanishes off the chart target and, on the chart target, off the
partition-of-unity kernel. -/

/-- The Euclidean chart component vanishes outside the partition-of-unity
kernel. -/
lemma tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- On the chart target the component is the pushed scalar; the scalar
    -- vanishes off the closed support of the partition-of-unity weight.
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) htar]
    have hb := notMem_pouTsupport_of_notMem_chartPouKernel
      (I := I) (M := M) α htar hy
    have hb_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        Function.support
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      fun hc => hb (subset_tsupport _ hc)
    have hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      by_contra hc; exact hb_supp hc
    change tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0
    unfold tensorChartComponentPou
    rw [hρ, zero_mul]
  · -- Off the chart target the push-forward is zero outright.
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ htar]

/-- The chart-Euclidean partial of the Euclidean chart component vanishes
outside the partition-of-unity kernel. -/
lemma euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y = 0 := by
  classical
  -- The chart component is supported in the compact kernel, hence vanishes on
  -- an open neighbourhood of `y`; so does its Fréchet derivative.
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  have htsupp : tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α :=
    (closure_minimal hsupp
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed)
  have hy_compl : y ∈ (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    fun hc => hy (htsupp hc)
  have hopen : IsOpen (tsupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have hevt : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy_compl) (fun z hz => ?_)
    exact image_eq_zero_of_notMem_tsupport hz
  rw [euclidPartial_def, hevt.fderiv_eq]
  simp

/-! ## Boundedness of a `C^∞` factor on the partition-of-unity kernel

Every `T`-independent factor occurring in a lower-order coefficient is `C^∞` on
the open Euclidean chart target, hence continuous there. Its restriction to the
compact partition-of-unity kernel is therefore bounded. The indicator of the
kernel times the factor is consequently a globally bounded measurable
function. -/

/-- A `C^∞`-on-the-chart-target function is bounded on the compact
partition-of-unity kernel: there is a non-negative constant `C` with
`‖c y‖ ≤ C` for every `y` in the kernel. -/
lemma exists_bound_on_chartPouKernel
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ chartPouKernel (I := I) (M := M) α, ‖c y‖ ≤ C := by
  classical
  have hcont : ContinuousOn (fun y => ‖c y‖)
      (chartPouKernel (I := I) (M := M) α) :=
    (hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).norm
  obtain ⟨C, hC⟩ := (chartPouKernel_isCompact (I := I) (M := M) α).bddAbove_image
    hcont
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  exact (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)

/-- The indicator of the partition-of-unity kernel times a `C^∞`-on-the-chart-
target function is `AEStronglyMeasurable` with respect to the chart `L²`
measure. -/
lemma aestronglyMeasurable_indicator_mul
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    AEStronglyMeasurable
      (Set.indicator (chartPouKernel (I := I) (M := M) α) c)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcont : ContinuousOn c (chartPouKernel (I := I) (M := M) α) :=
    hc.continuousOn.mono
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hmeas : AEStronglyMeasurable c
      ((chartL2Measure (I := I) (M := M) α).restrict
        (chartPouKernel (I := I) (M := M) α)) :=
    hcont.aestronglyMeasurable
      (chartPouKernel_measurableSet (I := I) (M := M) α)
  exact (aestronglyMeasurable_indicator_iff
    (chartPouKernel_measurableSet (I := I) (M := M) α)).mpr hmeas

/-! ## Multiplication by a bounded measurable factor preserves `L²`-convergence

For a globally bounded `AEStronglyMeasurable` function `c`, multiplication by
`c` sends an `L²`-function to an `L²`-function, with `L²` norm controlled by the
sup bound. Consequently, if a sequence of `L²` classes converges, so does the
sequence of products by `c`. -/

/-- The product of a bounded `AEStronglyMeasurable` function with an `L²`
function is `L²`, with the `L²` norm of the product controlled by the bound. -/
lemma memLp_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {f : EuclN → ℝ}
    (hf : MemLp f 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine ⟨hc_meas.mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  have hmono := eLpNorm_mono (μ := chartL2Measure (I := I) (M := M) α)
    (p := 2) hpt
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) := hmono
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hf.2

/-- The `L²` norm of the product of a bounded `AEStronglyMeasurable` function
`c` with an `L²` function is bounded by the sup bound times the `L²` norm. -/
lemma eLpNorm_bdd_mul_le
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (f : EuclN → ℝ) :
    eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_mono hpt
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ = ENNReal.ofReal C *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [Real.enorm_eq_ofReal hC]

/-- **Multiplication by a bounded measurable factor preserves `L²`-convergence.**
If a sequence `Fₙ` of `Lp` classes converges to `F` in `Lp ℝ 2 (chartL2Measure α)`,
and `c` is a globally bounded `AEStronglyMeasurable` function, then the sequence
of `L²` classes of `c · Fₙ` converges to the `L²` class of `c · F`. -/
lemma tendsto_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {F : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    {Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    (hF : Filter.Tendsto F atTop (𝓝 Flim)) :
    Filter.Tendsto
      (fun n => (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
      atTop
      (𝓝 ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y))) := by
  classical
  -- Convergence in distance: the distance of the products is bounded by `C`
  -- times the distance of `Fₙ` and `Flim`, which tends to `0`.
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  -- The distance of the `Fₙ` to `Flim` is eventually `< ε / (C + 1)`.
  have hCpos : (0 : ℝ) < C + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hF (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  -- Compute the distance of the two `L²` products.
  have hdist_eq :
      dist
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y)) =
      (eLpNorm
        (fun y => c y * (F n : EuclN → ℝ) y -
          c y * (Flim : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [Lp.dist_def]
    refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC
        hc_bd hc_meas (Lp.memLp (F n))),
      MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim))] with y hy₁ hy₂
    rw [Pi.sub_apply, hy₁, hy₂]
  rw [hdist_eq]
  -- The product difference is `c` times the difference of representatives.
  have hsub_eq :
      (fun y => c y * (F n : EuclN → ℝ) y - c y * (Flim : EuclN → ℝ) y) =
        (fun y => c y * ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) := by
    funext y; ring
  rw [hsub_eq]
  -- Bound the `L²` norm of the product difference.
  have hle := eLpNorm_bdd_mul_le (I := I) (M := M) α hC hc_bd
    (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
  -- The `eLpNorm` of the representative difference is the `Lp` distance.
  have hsub_ae :
      (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ) :=
    (Lp.coeFn_sub (F n) Flim).symm
  have hdist_F :
      eLpNorm (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y) 2
          (chartL2Measure (I := I) (M := M) α) =
        ENNReal.ofReal (dist (F n) Flim) := by
    have hfin : eLpNorm
        (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) ≠ ⊤ :=
      (Lp.memLp ((F n) - Flim)).2.ne
    rw [eLpNorm_congr_ae hsub_ae, Lp.dist_def,
      ENNReal.ofReal_toReal ((eLpNorm_congr_ae hsub_ae) ▸ hfin)]
    exact (eLpNorm_congr_ae hsub_ae).symm
  rw [hdist_F] at hle
  -- Pass to real numbers and finish.
  have hfin : (ENNReal.ofReal C * ENNReal.ofReal (dist (F n) Flim)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have hreal :
      (eLpNorm (fun y => c y *
          ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        C * dist (F n) Flim := by
    refine (ENNReal.toReal_mono hfin hle).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal dist_nonneg]
  refine lt_of_le_of_lt hreal ?_
  -- `C · dist < ε`.
  have hd : dist (F n) Flim < ε / (C + 1) := hN n hn
  calc C * dist (F n) Flim
      ≤ (C + 1) * dist (F n) Flim :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left hd hCpos
    _ = ε := by field_simp

/-! ## The two `T`-dependent atoms and their `L²`-limits

With `wₙ := eigenvectorSmoothApprox g r s h_atlas i n`, the two atoms through
which the lower-order coefficients depend on `Tₙ := pouSmul g r s α wₙ.toCcTensor`
are the bare chart component `tensorChartComponent g r s wₙ.toCcTensor α P` and
its chart-Euclidean partial. Their `L²` classes are the rescaled images of the
limit objects of `EigenvectorChartComponentL2.lean` and
`EigenvectorChartPartialL2.lean`. -/

/-- The `L²` class of the bare Euclidean chart component of the `n`-th smooth
approximant. -/
def approxComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    α P.1 P.2).toLp
    (tensorChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_atlas i n).toCcTensor α P.1 P.2)

/-- The `L²` limit of `approxComponentLp`: `μ` times the canonical chart
component of the eigenvector. -/
def componentLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  i.fst.val •
    tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P

/-- The `n`-th approximant chart component `L²` class converges to
`componentLpLimit`. -/
lemma approxComponentLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => approxComponentLp (I := I) (M := M) g r s h_atlas i α P n)
      atTop
      (𝓝 (componentLpLimit (I := I) (M := M) g r s h_atlas i α P)) := by
  classical
  -- Rescale the headline `eigenvectorChartComponentL2_tendsto` by `μ • ·`.
  have h_tendsto :=
    (eigenvectorChartComponentL2_tendsto (I := I) (M := M)
      g r s h_atlas i α P).const_smul i.fst.val
  -- Identify the `n`-th rescaled term with `approxComponentLp`.
  have h_term : ∀ n : ℕ,
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P =
        approxComponentLp (I := I) (M := M) g r s h_atlas i α P n := by
    intro n
    rw [eigenvectorChartComponentL2_approx_eq (I := I) (M := M)
      g r s h_atlas i α P n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P) =
      (fun n => approxComponentLp (I := I) (M := M)
        g r s h_atlas i α P n) from funext h_term] at h_tendsto
  exact h_tendsto

/-- The `L²` class of the chosen weak `k`-th chart partial of the bare Euclidean
chart component of the `n`-th smooth approximant. -/
def approxPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)
    α P.1 P.2 k).toLp
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
      (tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor α P.1 P.2)
      (chartTargetEuclid (I := I) (M := M) α))

/-- The `L²` limit of `approxPartialLp`: `μ` times the candidate weak chart
partial of the eigenvector chart component. -/
def partialLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  i.fst.val •
    eigenvectorChartPartialLp (I := I) (M := M) g r s h_atlas i α P k

/-- The `n`-th approximant chart partial `L²` class converges to
`partialLpLimit`. -/
lemma approxPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => approxPartialLp (I := I) (M := M) g r s h_atlas i α P k n)
      atTop
      (𝓝 (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k)) := by
  classical
  have h_tendsto :=
    (eigenvectorChartPartialLp_tendsto (I := I) (M := M)
      g r s h_atlas i α P k).const_smul i.fst.val
  have h_term : ∀ n : ℕ,
      i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n))) =
        approxPartialLp (I := I) (M := M) g r s h_atlas i α P k n := by
    intro n
    rw [eigenvectorChartPartialLp_approx_eq (I := I) (M := M)
      g r s h_atlas i α P k n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n)))) =
      (fun n => approxPartialLp (I := I) (M := M)
        g r s h_atlas i α P k n) from funext h_term] at h_tendsto
  exact h_tendsto

/-! ## Almost-everywhere identification of the chart-partial atom

For a smooth section the chosen weak `k`-th chart partial of the Euclidean chart
component agrees, on the chart `L²` measure, with the classical chart-Euclidean
partial `euclidPartial k`. -/

/-- The Euclidean chart component is globally `C^∞`: a restatement of
`tensorChartComponent_contMDiff` via the model-space `ContMDiff ↔ ContDiff`
correspondence. -/
lemma tensorChartComponent_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp
    (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx)

/-- The topological support of the Euclidean chart component is contained in the
partition-of-unity kernel, hence in the chart target. -/
lemma tensorChartComponent_tsupport_subset_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  exact closure_minimal hsupp
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

/-- The chosen weak `k`-th chart partial of the Euclidean chart component agrees,
almost everywhere on the chart `L²` measure, with the classical chart-Euclidean
partial. -/
lemma chosenWeakPartial'_tensorChartComponent_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tensorChartComponent_tsupport_subset_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx).trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : MemWkp (d := Module.finrank ℝ E) 1 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := Module.finrank ℝ E)
    hp_one hΩ_open hu_smooth hu_W1p k
  rw [chartL2Measure]
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y; rw [euclidPartial_def]

/-! ## The summand `L²`-convergence engine

Each lower-order coefficient at `Tₙ`, restricted to the chart target, is a
finite sum of products `(C^∞ factor) · (atom)`. The next two lemmas package the
`L²`-convergence of one such product: the limit is the `L²` class of the
indicator-cut factor times the limiting atom representative, and the
`n`-dependent term is the `L²` class of the genuine product.

`tendsto_componentSummand` handles a chart-component atom; `tendsto_partialSummand`
handles a chart-partial atom. -/

/-- A chart-component summand `(C^∞ factor) · tensorChartComponent g r s wₙ α P`,
`L²`-classed and convergent. The limit is the `L²` class of the kernel-indicator
factor times the representative of `componentLpLimit`. -/
lemma tendsto_componentSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2 y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  -- The indicator-cut factor is globally bounded.
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  -- The general bounded-multiplication convergence engine.
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxComponentLp_tendsto (I := I) (M := M) g r s h_atlas i α P)
  -- Identify the `n`-th term and the limit.
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s h_atlas i α P n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    -- `ci · approxComponentLp` agrees a.e. with `c · tensorChartComponent`.
    have hcomp : (approxComponentLp (I := I) (M := M)
        g r s h_atlas i α P n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2 := by
      rw [approxComponentLp]; exact MemLp.coeFn_toLp _
    filter_upwards [hcomp] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (componentLpLimit (I := I) (M := M)
          g r s h_atlas i α P))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s h_atlas i α P n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

/-- A chart-partial summand `(C^∞ factor) · euclidPartial k (tensorChartComponent
g r s wₙ α P)`, `L²`-classed and convergent. The limit is the `L²` class of the
kernel-indicator factor times the representative of `partialLpLimit`. -/
lemma tendsto_partialSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2) y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxPartialLp_tendsto (I := I) (M := M) g r s h_atlas i α P k)
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s h_atlas i α P k n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    -- `ci · approxPartialLp` agrees a.e. with `c · euclidPartial k …`.
    have hpart : (approxPartialLp (I := I) (M := M)
        g r s h_atlas i α P k n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2) := by
      refine (MemLp.coeFn_toLp _).trans ?_
      exact chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor α P.1 P.2 k
    filter_upwards [hpart] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (partialLpLimit (I := I) (M := M)
          g r s h_atlas i α P k))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s h_atlas i α P k n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

/-! ## The finite-sum `L²`-convergence assembly

Each lower-order coefficient is a finite sum of `(C^∞ factor) · (atom)` products.
The next lemmas assemble a finite sum of `L²`-convergent sequences into a single
`L²`-convergent sequence: the `L²` class of a function equal almost everywhere
to a finite sum of `L²` functions is the finite sum of their `L²` classes, and a
finite sum of `L²`-convergent sequences converges. -/

/-- The function underlying a finite sum of `L²` classes agrees almost
everywhere with the finite sum of the underlying functions. -/
lemma coeFn_finsetSum_lp
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

/-- The function underlying a finite sum of `L²` classes of `MemLp` functions
agrees almost everywhere with the finite sum of those functions. -/
lemma coeFn_finsetSum_toLp
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, (hf a).toLp (f a)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y := by
  classical
  refine (coeFn_finsetSum_lp (I := I) (M := M) α s
    (fun a => (hf a).toLp (f a))).trans ?_
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      filter_upwards [ih, MemLp.coeFn_toLp (hf a)] with y hy hya
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hy]

/-- The `L²` class of a function equal almost everywhere to a finite sum of `L²`
functions is the finite sum of the `L²` classes of the summands. -/
lemma toLp_finsetSum_congr
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α))
    {F : EuclN → ℝ}
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y) :
    hF.toLp F = ∑ a ∈ s, (hf a).toLp (f a) := by
  classical
  apply Lp.ext
  exact (MemLp.coeFn_toLp hF).trans
    (hFeq.trans (coeFn_finsetSum_toLp (I := I) (M := M) α s hf).symm)

/-- **Finite-sum `L²`-convergence assembly.** If, for each index `a` in a finite
set, the `L²` classes `(hf a n).toLp (f a n)` converge to `(hflim a).toLp
(flim a)`, and `Fₙ` agrees almost everywhere with `∑ a, f a n` while `Flim`
agrees almost everywhere with `∑ a, flim a`, then the `L²` class of `Fₙ`
converges to the `L²` class of `Flim`. -/
lemma tendsto_toLp_finsetSum
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a))))
    {Fn : ℕ → EuclN → ℝ} {Flim : EuclN → ℝ}
    (hFn : ∀ n : ℕ, MemLp (Fn n) 2 (chartL2Measure (I := I) (M := M) α))
    (hFlim : MemLp Flim 2 (chartL2Measure (I := I) (M := M) α))
    (hFn_eq : ∀ n : ℕ, Fn n =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a n y)
    (hFlim_eq : Flim =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, flim a y) :
    Filter.Tendsto (fun n => (hFn n).toLp (Fn n)) atTop
      (𝓝 (hFlim.toLp Flim)) := by
  classical
  -- Rewrite each `L²` class as a finite sum of summand `L²` classes.
  have h_n : ∀ n : ℕ,
      (hFn n).toLp (Fn n) =
        ∑ a ∈ s, (hf a n).toLp (f a n) :=
    fun n => toLp_finsetSum_congr (I := I) (M := M) α s
      (fun a => hf a n) (hFn n) (hFn_eq n)
  have h_lim :
      hFlim.toLp Flim = ∑ a ∈ s, (hflim a).toLp (flim a) :=
    toLp_finsetSum_congr (I := I) (M := M) α s hflim hFlim hFlim_eq
  rw [show (fun n => (hFn n).toLp (Fn n)) =
      (fun n => ∑ a ∈ s, (hf a n).toLp (f a n)) from funext h_n, h_lim]
  exact tendsto_finset_sum s (fun a _ => h_tendsto a)

/-! ## `L²`-membership of the coefficient summands

The two `T`-dependent atoms are `L²`, and a `C^∞`-on-the-chart-target factor
times either atom is `L²` because each atom is supported in the compact
partition-of-unity kernel, off which the indicator-cut factor is bounded. -/

/-- The chart-Euclidean partial of the chart component of the `n`-th smooth
approximant is `L²`: it agrees almost everywhere with the chosen weak chart
partial, which is `L²`. -/
lemma euclidPartial_tensorChartComponent_approx_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2)) 2
      (chartL2Measure (I := I) (M := M) α) :=
  MemLp.ae_eq
    (chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_atlas i n).toCcTensor α P.1 P.2 k)
    (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)
      α P.1 P.2 k)

/-- A `C^∞`-on-the-chart-target factor times the chart component of the `n`-th
smooth approximant is `L²`. -/
lemma memLp_factor_mul_componentAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2 y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2 y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_atlas i n).toCcTensor α P.1 P.2)

/-- A `C^∞`-on-the-chart-target factor times the chart-Euclidean partial of the
chart component of the `n`-th smooth approximant is `L²`. -/
lemma memLp_factor_mul_partialAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2) y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor α P.1 P.2) y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (euclidPartial_tensorChartComponent_approx_memLp (I := I) (M := M)
      g r s h_atlas i α P k n)

/-- A `C^∞`-on-the-chart-target factor, indicator-cut to the partition-of-unity
kernel, times an arbitrary `L²` limit class, is `L²`. -/
lemma memLp_indicatorFactor_mul_lp
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (G : EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc) (Lp.memLp G)

/-! ## The tracing identity for the partition-of-unity-weighted approximant

The chart push-forward of the raw chart component of the partition-of-unity-
weighted approximant `Tₙ := pouSmul g r s α wₙ.toCcTensor` is the canonical
Euclidean chart component of `wₙ.toCcTensor`: this is the tracing identity
through which every lower-order coefficient at `Tₙ` reduces to the two atoms. -/

/-- The chart push-forward of the raw chart component of the partition-of-unity-
weighted section equals the canonical Euclidean chart component. -/
private lemma chartPushedRaw_tensorChartComponentRaw_pouSmul_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx) =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S Idx Jdx, tensorChartComponent_def]

/-! ## The `n → ∞` `L²`-limit of the principal rotation coefficient

The principal rotation coefficient `covPrincipalRotationCoeff g r s Tₙ α P₀`
depends on `Tₙ` only through the chart-Euclidean partial of the raw chart
component's push-forward, which by the tracing identity is the chart-Euclidean
partial of the canonical chart component of `wₙ.toCcTensor`. It is therefore a
finite `C^∞`-coefficient-weighted sum of the chart-partial atom, whose `L²`
limit is `partialLpLimit`. -/

/-- The `T`-independent `C^∞` factor of the `(P, Q, k, l)`-summand of the
principal rotation coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, and the chart-Euclidean partial of the inverse-Gram
column entry. -/
def principalRotationFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      euclidPartial (E := E) l (gramInvEntry (I := I) (M := M) g r s α Q P₀) y

/-- The `T`-independent factor of the principal rotation coefficient is `C^∞` on
the Euclidean chart target. -/
lemma principalRotationFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀))

/-- **The explicit `L²`-limit function of the principal rotation coefficient.**
A finite `C^∞`-coefficient-weighted sum, over component multi-index pairs and
chart directions, of the chart-partial limit object `partialLpLimit`, with each
coefficient cut to the partition-of-unity kernel. -/
noncomputable def covPrincipalRotationCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                EuclN → ℝ) y

/-- The principal rotation coefficient at the partition-of-unity-weighted
approximant equals, pointwise, the four-fold finite sum of `principalRotationFactor`
times the chart-partial atom of `wₙ.toCcTensor`. -/
private lemma covPrincipalRotationCoeff_pouSmul_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) (y : EuclN) :
    covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀ y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor α P.1 P.2) y := by
  classical
  rw [covPrincipalRotationCoeff_def]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
    g r s α (eigenvectorSmoothApprox (I := I) (M := M)
      g r s h_atlas i n).toCcTensor P.1 P.2]
  rw [principalRotationFactor]
  ring

/-- The principal rotation coefficient at the partition-of-unity-weighted
approximant is `L²`. -/
theorem covPrincipalRotationCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covPrincipalRotationCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ =>
            memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s h_atlas i α P k n
              (principalRotationFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))).ae_eq ?_
  exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall (fun y =>
    covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s h_atlas i α P₀ n y))

/-- The `L²`-limit function of the principal rotation coefficient is `L²`. -/
theorem covPrincipalRotationCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covPrincipalRotationCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (principalRotationFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ P Q k l)
            (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k)))))

/-- **The `n → ∞` `L²`-limit of the principal rotation coefficient.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a
chart center `α : M`, and a component multi-index `P₀`, the `L²` classes of the
principal rotation coefficient `covPrincipalRotationCoeff g r s Tₙ α P₀` at the
partition-of-unity-weighted approximants `Tₙ := pouSmul g r s α
(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor` converge, as `n → ∞`
and in `Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of the explicit limit
function `covPrincipalRotationCoeffLimit g r s h_atlas i α P₀`. -/
theorem covPrincipalRotationCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ n).toLp _)
      atTop
      (𝓝 ((covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀).toLp _)) := by
  classical
  -- The genuine `n`-th summand and the limiting summand, indexed by `(P, Q, k, l)`.
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (n : ℕ),
      MemLp (fun y => principalRotationFactor (I := I) (M := M)
            g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          euclidPartial (E := E) a.2.2.1
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor α a.1.1 a.1.2) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_partialAtom (I := I) (M := M) g r s h_atlas i α a.1
      a.2.2.1 n (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (partialLpLimit (I := I) (M := M) g r s h_atlas i α a.1 a.2.2.1 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (partialLpLimit (I := I) (M := M) g r s h_atlas i α a.1 a.2.2.1)
  -- Per-summand `L²`-convergence.
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_partialSummand (I := I) (M := M) g r s h_atlas i α a.1 a.2.2.1
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  -- The coefficient is the flattened finite sum of the genuine summands.
  have hFn_eq : ∀ n : ℕ,
      covPrincipalRotationCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          principalRotationFactor (I := I) (M := M)
              g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            euclidPartial (E := E) a.2.2.1
              (tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor α a.1.1 a.1.2) y := by
    intro n
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeff_pouSmul_eq_sum (I := I) (M := M)
      g r s h_atlas i α P₀ n y]
    simp only [Fintype.sum_prod_type]
  -- The limit function is the flattened finite sum of the limiting summands.
  have hFlim_eq :
      covPrincipalRotationCoeffLimit (I := I) (M := M) g r s h_atlas i α P₀
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (partialLpLimit (I := I) (M := M) g r s h_atlas i α a.1 a.2.2.1 :
              EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covPrincipalRotationCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ n)
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s h_atlas i α P₀)
    hFn_eq hFlim_eq

/-! ## The zeroth-order Christoffel-correction tracing identity

The zeroth-order Christoffel correction `covDerivLowerOrderTerm` of the
partition-of-unity-weighted approximant `Tₙ := pouSmul g r s α wₙ.toCcTensor`
collapses, on the chart target, to a finite `C^∞`-coefficient-weighted sum of the
canonical Euclidean chart components of `wₙ.toCcTensor`: the raw chart component
of `Tₙ` is the partition-of-unity-weighted chart component, whose value at the
chart preimage is the Euclidean chart component. -/

/-- On the Euclidean chart target, the zeroth-order Christoffel correction of the
partition-of-unity-weighted approximant is the finite linear combination, over
component multi-index pairs, of the lower-order correction coefficient times the
canonical Euclidean chart component. -/
private lemma covDerivLowerOrderTerm_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

/-! ## The `n → ∞` `L²`-limit of the chart-density-weighted lower-order gradient
coefficient

The chart-density-weighted lower-order gradient coefficient `weightedGradCoeff g
r s Tₙ α P₀ l` is zeroth-order in `Tₙ`: by the Christoffel-correction tracing
identity it is, on the chart target, a finite `C^∞`-coefficient-weighted sum of
the bare chart-component atom of `wₙ.toCcTensor`, whose `L²` limit is
`componentLpLimit`. -/

/-- The `T`-independent `C^∞` factor of the `(P, Q, k, p)`-summand of the
chart-density-weighted lower-order gradient coefficient. -/
def weightedGradFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y *
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

/-- The `T`-independent factor of the chart-density-weighted lower-order gradient
coefficient is `C^∞` on the Euclidean chart target. -/
lemma weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((((densityOnEuclid_contDiffOn (I := I) g α).mul
        (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
      g r s α k P.1 p.1 P.2 p.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

/-- **The explicit `L²`-limit function of the chart-density-weighted lower-order
gradient coefficient.** A finite `C^∞`-coefficient-weighted sum, over component
multi-index pairs and chart directions, of the chart-component limit object
`componentLpLimit`, with each coefficient cut to the partition-of-unity
kernel. -/
noncomputable def weightedGradCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                EuclN → ℝ) y

/-- On the chart target, the chart-density-weighted lower-order gradient
coefficient at the partition-of-unity-weighted approximant equals the four-fold
finite sum of `weightedGradFactor` times the bare chart-component atom of
`wₙ.toCcTensor`. -/
private lemma weightedGradCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor α p.1 p.2 y := by
  classical
  -- Expand the coefficient and the Christoffel correction at the chart-target
  -- point, then match the four-fold sum termwise.
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M)
      g r s h_atlas i n).toCcTensor k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

/-- The chart-density-weighted lower-order gradient coefficient at the
partition-of-unity-weighted approximant is `L²`. -/
theorem weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ =>
            memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s h_atlas i α p n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ l n hy)

/-- The `L²`-limit function of the chart-density-weighted lower-order gradient
coefficient is `L²`. -/
theorem weightedGradCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P _ => memLp_finset_sum
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q _ => memLp_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (weightedGradFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q k p)
            (componentLpLimit (I := I) (M := M) g r s h_atlas i α p)))))

/-- **The `n → ∞` `L²`-limit of the chart-density-weighted lower-order gradient
coefficient.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i`, a chart center `α : M`, a component multi-index `P₀`, and a
chart direction `l`, the `L²` classes of `weightedGradCoeff g r s Tₙ α P₀ l` at
the partition-of-unity-weighted approximants converge, as `n → ∞` and in
`Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of the explicit limit function
`weightedGradCoeffLimit g r s h_atlas i α P₀ l`. -/
theorem weightedGradCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l).toLp _)) := by
  classical
  have hf : ∀ (a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => weightedGradFactor (I := I) (M := M)
            g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s h_atlas i α
      a.2.2.2 n (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
  have hflim : ∀ a : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
          (componentLpLimit (I := I) (M := M) g r s h_atlas i α a.2.2.2 :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun a =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (componentLpLimit (I := I) (M := M) g r s h_atlas i α a.2.2.2)
  have h_tendsto : ∀ a : TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s ×
        Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf a n).toLp _) atTop
        (𝓝 ((hflim a).toLp _)) := fun a =>
    tendsto_componentSummand (I := I) (M := M) g r s h_atlas i α a.2.2.2
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2)
      (fun n => hf a n) (hflim a)
  have hFn_eq : ∀ n : ℕ,
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          weightedGradFactor (I := I) (M := M)
              g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor α a.2.2.2.1 a.2.2.2.2 y := by
    intro n
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ l n hy]
    simp only [Fintype.sum_prod_type]
  have hFlim_eq :
      weightedGradCoeffLimit (I := I) (M := M) g r s h_atlas i α P₀ l
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ a : TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s ×
            Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l a.1 a.2.1 a.2.2.1 a.2.2.2) y *
            (componentLpLimit (I := I) (M := M) g r s h_atlas i α a.2.2.2 :
              EuclN → ℝ) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffLimit]
    simp only [Fintype.sum_prod_type]
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ l n)
    (weightedGradCoeffLimit_memLp (I := I) (M := M) g r s h_atlas i α P₀ l)
    hFn_eq hFlim_eq

/-! ## A nested finite-sum `L²`-convergence step

The lower-order rotation value coefficient and the chart-Euclidean divergence of
the chart-density-weighted gradient coefficient are heterogeneously indexed
finite sums: the first-order chart-partial atom and the zeroth-order component
atom appear in distinct summand groups, the second carrying an extra component
multi-index sum. To assemble such a sum *without* over-flattening the product
structure of the component multi-index type, we use a single-`Finset`
convergence step that descends one nesting level at a time. Iterating it builds
the full nested `L²`-limit. -/

/-- **One nesting level of finite-sum `L²`-convergence.** If, for every index `a`
in a finite type, the `L²` classes `(hf a n).toLp (f a n)` converge to
`(hflim a).toLp (flim a)`, then the `L²` class of the finite sum `∑ a, f a n`
converges to the `L²` class of `∑ a, flim a`. The summed `L²` classes are built
from `memLp_finset_sum`, so the conclusion composes with itself across nesting
levels. -/
lemma tendsto_sumToLp
    (α : M) {ι : Type*} [Fintype ι]
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hf a n)).toLp (fun y => ∑ a, f a n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hflim a)).toLp (fun y => ∑ a, flim a y))) :=
  tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ hf hflim h_tendsto
    (fun n => memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hf a n))
    (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hflim a))
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl

/-! ## The chart-Euclidean partial of a finite sum

The chart-Euclidean partial derivative `euclidPartial l` is the Fréchet
derivative paired with a fixed basis vector; the Fréchet-derivative sum rule
`fderiv_fun_sum` therefore distributes it across a finite sum of functions, each
differentiable at the evaluation point. -/

/-- **The chart-Euclidean partial distributes across a finite sum.** For a
finite family of functions all differentiable at `y`, the `l`-th chart-Euclidean
partial of the sum is the sum of the chart-Euclidean partials. -/
lemma euclidPartial_finsetSum
    (l : Fin (Module.finrank ℝ E)) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ} {y : EuclN}
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) y) :
    euclidPartial (E := E) l (fun z => ∑ a ∈ s, f a z) y =
      ∑ a ∈ s, euclidPartial (E := E) l (f a) y := by
  classical
  rw [euclidPartial_def, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [euclidPartial_def])

/-! ## Four- and five-fold nested finite-sum `L²`-convergence

Iterating the single-level step `tendsto_sumToLp` over four and five nested
finite types assembles the `L²`-limit of a four- or five-fold nested finite sum.
The conclusion's `L²` classes are the correspondingly nested `memLp_finset_sum`
constructions, matching the per-`n` and limiting coefficient decompositions. -/

/-- **Four-fold nested finite-sum `L²`-convergence.** Per-`(a, b, c, d)`-leaf
`L²`-convergence assembles into the `L²`-convergence of the four-fold nested
finite sum. -/
private lemma tendsto_sum4
    (α : M) {κ₁ κ₂ κ₃ κ₄ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (n : ℕ),
      MemLp (f a b c d n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      MemLp (flim a b c d) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      Filter.Tendsto (fun n => (hf a b c d n).toLp (f a b c d n)) atTop
        (𝓝 ((hflim a b c d).toLp (flim a b c d)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hf a b c d n))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, f a b c d n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hflim a b c d))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, flim a b c d y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, f a b c d n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, flim a b c d y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, ∑ d, f a b c d n y)
      (flim := fun b => fun y => ∑ c, ∑ d, flim a b c d y)
      (fun b n => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n)))
      (fun b => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d)))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (f := fun c => fun n y => ∑ d, f a b c d n y)
        (flim := fun c => fun y => ∑ d, flim a b c d y)
        (fun c n => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))
        (fun c => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))
        (fun c => tendsto_sumToLp (I := I) (M := M) α
          (hf := fun d n => hf a b c d n) (hflim := fun d => hflim a b c d)
          (h_tendsto a b c))))

/-- **Five-fold nested finite-sum `L²`-convergence.** Per-`(a, b, c, d, e)`-leaf
`L²`-convergence assembles into the `L²`-convergence of the five-fold nested
finite sum. -/
private lemma tendsto_sum5
    (α : M) {κ₁ κ₂ κ₃ κ₄ κ₅ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄] [Fintype κ₅]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅) (n : ℕ),
      MemLp (f a b c d e n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      MemLp (flim a b c d e) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      Filter.Tendsto (fun n => (hf a b c d e n).toLp (f a b c d e n)) atTop
        (𝓝 ((hflim a b c d e).toLp (flim a b c d e)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hf a b c d e n)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hflim a b c d e)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hf a b c d e n)))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hflim a b c d e)))))
    (fun a => tendsto_sum4 (I := I) (M := M) α
      (f := fun b c d e n => f a b c d e n)
      (flim := fun b c d e => flim a b c d e)
      (fun b c d e n => hf a b c d e n)
      (fun b c d e => hflim a b c d e)
      (fun b c d e => h_tendsto a b c d e))

/-! ## Differentiability of the two atoms and the `C^∞` factors

The two `T`-dependent atoms — the bare Euclidean chart component and its
chart-Euclidean partial — are globally `C^∞` (the chart component) and
`C^∞`-on-the-chart-target (its partial); a `C^∞`-on-the-open-chart-target
function is differentiable at every chart-target point. These local
differentiability facts feed the Leibniz / sum rules below. -/

/-- A function `C^∞` on the open Euclidean chart target is differentiable at
every point of the chart target. -/
lemma differentiableAt_of_contDiffOn_chartTarget
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ c y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  exact (hc.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)

/-- The bare Euclidean chart component of a smooth section is differentiable at
every point. -/
lemma differentiableAt_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentiableAt ℝ
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y :=
  ((tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx).differentiable
    (by simp)).differentiableAt

/-! ## The `n → ∞` `L²`-limit of the chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient

The chart-density-weighted lower-order gradient coefficient `weightedGradCoeff g
r s Tₙ α P₀ l` is, on the chart target, a finite `C^∞`-coefficient-weighted sum
of the bare chart-component atom. Its `l`-th chart-Euclidean partial
`euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)` is therefore — by the
chart-Euclidean sum rule and the Leibniz rule — a finite sum of two summand
groups: the chart-Euclidean partial of the `C^∞` factor times the bare
chart-component atom (a component-atom summand), and the `C^∞` factor times the
chart-Euclidean partial of the bare chart-component atom (a chart-partial
summand). -/

/-- On the chart target, the `l`-th chart-Euclidean partial of the
chart-density-weighted lower-order gradient coefficient at the
partition-of-unity-weighted approximant equals the four-fold finite sum of the
Leibniz contributions: the chart-Euclidean partial of `weightedGradFactor` times
the bare chart-component atom, plus `weightedGradFactor` times the
chart-Euclidean partial of the bare chart-component atom. -/
private lemma euclidPartial_weightedGradCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) α P₀ l) y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                  tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor α p.1 p.2 y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                    euclidPartial (E := E) l
                      (tensorChartComponent (I := I) (M := M) g r s
                        (eigenvectorSmoothApprox (I := I) (M := M)
                          g r s h_atlas i n).toCcTensor α p.1 p.2) y := by
  classical
  -- The chart target is open; on it the coefficient agrees with the four-fold
  -- sum, so the chart-Euclidean partials agree at `y`.
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    with hwₙ_def
  -- The four-fold-sum representative of the coefficient on the chart target.
  set Sum4 : EuclN → ℝ := fun z =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
              tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z
    with hSum4_def
  have hcoeff_evt :
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α wₙ) α P₀ l =ᶠ[𝓝 y] Sum4 := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => ?_)
    rw [hSum4_def]
    exact weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ l n hz
  rw [euclidPartial_def, hcoeff_evt.fderiv_eq, ← euclidPartial_def]
  -- Differentiability of every `(P, Q, k, p)`-leaf at `y`.
  have hleaf_diff : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k : Fin (Module.finrank ℝ E), ∀ p : TensorCompIdx (E := E) r s,
      DifferentiableAt ℝ
        (fun z => weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
          tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z) y :=
    fun P Q k p =>
      (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        hy).mul
      (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
        p.1 p.2 y)
  -- Distribute `euclidPartial l` across the four nested finite sums.
  rw [hSum4_def, euclidPartial_finsetSum (E := E) l Finset.univ
    (fun P _ => DifferentiableAt.fun_sum (fun Q _ =>
      DifferentiableAt.fun_sum (fun k _ =>
        DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun Q _ => DifferentiableAt.fun_sum (fun k _ =>
      DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p)))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun k _ => DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun p _ => hleaf_diff P Q k p)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- Leibniz on the `(P, Q, k, p)`-leaf.
  exact euclidPartial_mul (E := E) l
    (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p) hy)
    (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
      p.1 p.2 y)

/-- The chart-Euclidean partial of the `T`-independent `C^∞` factor
`weightedGradFactor` is `C^∞` on the Euclidean chart target. -/
lemma euclidPartial_weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_target (I := I) (M := M) α l
    (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)

/-- **The explicit `L²`-limit function of the chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient.** A finite
`C^∞`-coefficient-weighted sum, over component multi-index pairs and chart
directions, of the chart-component limit object `componentLpLimit`: the
chart-Euclidean partial of `weightedGradFactor` against the component limit
(from the component-atom group), plus `weightedGradFactor` against the
chart-partial limit `partialLpLimit` (from the chart-partial group). Each
coefficient is cut to the partition-of-unity kernel. -/
noncomputable def weightedGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
                  y *
                (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
                    y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                    EuclN → ℝ) y

/-- The chart-Euclidean divergence of the chart-density-weighted lower-order
gradient coefficient at the partition-of-unity-weighted approximant is `L²`. -/
theorem euclidPartial_weightedGradCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) α P₀ l)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  -- The component-atom group: `∂_l weightedGradFactor · chart component`.
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
              g r s h_atlas i α p n
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  -- The chart-partial-atom group: `weightedGradFactor · ∂_l chart component`.
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                euclidPartial (E := E) l
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor α p.1 p.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s h_atlas i α p l n
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    euclidPartial_weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ l n hy)

/-- The `L²`-limit function of the chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient is `L²`. -/
theorem weightedGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold weightedGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (componentLpLimit (I := I) (M := M) g r s h_atlas i α p)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (weightedGradFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ l P Q k p)
              (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l)))))

/-- The `L²` class of a function equal almost everywhere to a sum of two `L²`
functions is the sum of the `L²` classes of the summands. -/
lemma toLp_add_eq
    (α : M) {f₁ f₂ F : EuclN → ℝ}
    (hf₁ : MemLp f₁ 2 (chartL2Measure (I := I) (M := M) α))
    (hf₂ : MemLp f₂ 2 (chartL2Measure (I := I) (M := M) α))
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => f₁ y + f₂ y) :
    hF.toLp F = hf₁.toLp f₁ + hf₂.toLp f₂ := by
  classical
  apply Lp.ext
  refine (MemLp.coeFn_toLp hF).trans (hFeq.trans ?_)
  refine Filter.EventuallyEq.symm ?_
  refine (Lp.coeFn_add (hf₁.toLp f₁) (hf₂.toLp f₂)).trans ?_
  filter_upwards [MemLp.coeFn_toLp hf₁, MemLp.coeFn_toLp hf₂] with y hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂]

/-- **The `n → ∞` `L²`-limit of the chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a chart
center `α : M`, a component multi-index `P₀`, and a chart direction `l`, the
`L²` classes of `euclidPartial l (weightedGradCoeff g r s Tₙ α P₀ l)` at the
partition-of-unity-weighted approximants `Tₙ := pouSmul g r s α
(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor` converge, as `n → ∞`
and in `Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of the explicit limit
function `weightedGradCoeffDivLimit g r s h_atlas i α P₀ l`. -/
theorem weightedGradCoeffDiv_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l n).toLp _)
      atTop
      (𝓝 ((weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l).toLp _)) := by
  classical
  -- The component-atom group: `∂_l weightedGradFactor · chart component`, with
  -- limit the kernel-cut `∂_l weightedGradFactor` against `componentLpLimit`.
  have h_comp := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      euclidPartial (E := E) l
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
        (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s h_atlas i α p n
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (componentLpLimit (I := I) (M := M) g r s h_atlas i α p))
    (fun P Q k p => tendsto_componentSummand (I := I) (M := M)
      g r s h_atlas i α p
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s h_atlas i α p n
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit (I := I) (M := M) g r s h_atlas i α p)))
  -- The chart-partial-atom group: `weightedGradFactor · ∂_l chart component`,
  -- with limit the kernel-cut `weightedGradFactor` against `partialLpLimit`.
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k p n y =>
      weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
        euclidPartial (E := E) l
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α p.1 p.2) y)
    (flim := fun P Q k p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
        (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
          EuclN → ℝ) y)
    (fun P Q k p n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s h_atlas i α p l n
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
    (fun P Q k p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l))
    (fun P Q k p => tendsto_partialSummand (I := I) (M := M)
      g r s h_atlas i α p l
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s h_atlas i α p l n
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l)))
  -- Add the two convergent groups.
  have h_add := h_comp.add h_part
  -- Identify the `n`-th sum with the divergence-coefficient `L²` class.
  have h_termN : ∀ n : ℕ,
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                  g r s h_atlas i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                  g r s h_atlas i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      euclidPartial_weightedGradCoeff_pouSmul_eqOn (I := I) (M := M)
        g r s h_atlas i α P₀ l n hy)
  -- Identify the limiting sum with the divergence-coefficient limit `L²` class.
  have h_termLim :
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)
                  (partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α p l)))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [weightedGradCoeffDivLimit]
  rw [show (fun n => (euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s h_atlas i α P₀ l n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                  g r s h_atlas i α p n
                  (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun p _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                  g r s h_atlas i α p l n
                  (weightedGradFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ l P Q k p)))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

/-- **The `n → ∞` `L²`-limit of the total chart-Euclidean divergence of the
chart-density-weighted lower-order gradient coefficient.** Summed over the chart
directions `l`, the `L²` classes of `∑_l euclidPartial l (weightedGradCoeff g r s
Tₙ α P₀ l)` converge, as `n → ∞` and in `Lp ℝ 2 (chartL2Measure α)`, to the `L²`
class of `∑_l weightedGradCoeffDivLimit g r s h_atlas i α P₀ l`. -/
theorem weightedGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
          g r s h_atlas i α P₀ l n).toLp _)
      atTop
      (𝓝 (∑ l : Fin (Module.finrank ℝ E),
        (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s h_atlas i α P₀ l).toLp _)) :=
  tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => weightedGradCoeffDiv_tendsto (I := I) (M := M)
      g r s h_atlas i α P₀ l)

/-! ## The `n → ∞` `L²`-limit of the lower-order rotation value coefficient

The lower-order rotation value coefficient `covLowerOrderRotationValueCoeff g r s
Tₙ α P₀` is *first-order* in `Tₙ`: it depends on `Tₙ` only through the
chart-Euclidean partial of the raw chart component's push-forward (a chart-partial
atom) and through the zeroth-order Christoffel correction `covDerivLowerOrderTerm`
(a `C^∞`-linear combination of bare chart components). By the tracing identity
and the Christoffel-correction tracing identity it is, on the chart target, the
sum of a four-fold nested chart-partial-atom sum and a five-fold nested
component-atom sum. -/

/-- The `T`-independent `C^∞` factor of the chart-partial-atom summand of the
lower-order rotation value coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, and the collapsed Christoffel coefficient. -/
def valuePartialFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y

/-- The `T`-independent `C^∞` factor of the chart-partial-atom summand is `C^∞`
on the Euclidean chart target. -/
lemma valuePartialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ l Q)

/-- The `T`-independent `C^∞` factor of the component-atom summand of the
lower-order rotation value coefficient: the chart-frame tensor-metric Gram, the
unweighted inverse Gram, the sum of the chart-Euclidean partial of the
inverse-Gram entry and the collapsed Christoffel coefficient, and the lower-order
correction coefficient. -/
def valueComponentFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        (euclidPartial (E := E) l
              (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) *
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y

/-- The `T`-independent `C^∞` factor of the component-atom summand is `C^∞` on
the Euclidean chart target. -/
lemma valueComponentFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
      ((euclidPartial_contDiffOn_target (I := I) (M := M) α l
          (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)).add
        (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M)
          g r s α P₀ l Q))).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2)

/-- On the chart target, the lower-order rotation value coefficient at the
partition-of-unity-weighted approximant equals the four-fold nested
chart-partial-atom sum (`valuePartialFactor` against the chart-Euclidean partial
of the bare chart-component atom) plus the five-fold nested component-atom sum
(`valueComponentFactor` against the bare chart-component atom). -/
private lemma covLowerOrderRotationValueCoeff_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀ y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M) g r s
                      (eigenvectorSmoothApprox (I := I) (M := M)
                        g r s h_atlas i n).toCcTensor α P.1 P.2) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p y *
                      tensorChartComponent (I := I) (M := M) g r s
                        (eigenvectorSmoothApprox (I := I) (M := M)
                          g r s h_atlas i n).toCcTensor α p.1 p.2 y := by
  classical
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    with hwₙ_def
  rw [covLowerOrderRotationValueCoeff_def]
  -- For each `(P, Q, k, l)`-summand the inner body collapses.
  have hbody : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y *
          (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y *
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) =
        chartInvGramEuclid (I := I) g α k l y *
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
            euclidPartial (E := E) k
              (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y
          + ∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y := by
    intro P Q k l
    -- Substitute the two tracing identities.
    rw [show euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y =
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y from
        congrArg (fun u : EuclN → ℝ => euclidPartial (E := E) k u y)
          (chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
            g r s α wₙ P.1 P.2)]
    rw [covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α wₙ
      k P.1 P.2 hy]
    -- The component-atom sum equals the two distributed zeroth-order groups.
    rw [show (∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y) =
          chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y) +
            chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                lowerOrderRotationLOCoeff (I := I) (M := M)
                  g r s α P₀ l Q y) from by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring]
    ring
  -- Rewrite every inner `(k, l)`-summand and split into the two parts.
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun l _ => hbody P Q k l))]))]
  -- Distribute `covChartMetricGram` and separate the partial / component parts.
  have hsplit : ∀ P Q : TensorCompIdx (E := E) r s,
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (chartInvGramEuclid (I := I) g α k l y *
                  lowerOrderRotationLOCoeff (I := I) (M := M)
                    g r s α P₀ l Q y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M)
                      g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  chartInvGramEuclid (I := I) g α k l y *
                      (euclidPartial (E := E) l
                          (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y) *
                      covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
              euclidPartial (E := E) k
                (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y)
          + ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M)
                    g r s wₙ α p.1 p.2 y := by
    intro P Q
    rw [Finset.mul_sum]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                ∑ l : Fin (Module.finrank ℝ E),
                  (chartInvGramEuclid (I := I) g α k l y *
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y *
                        euclidPartial (E := E) k
                          (tensorChartComponent (I := I) (M := M)
                            g r s wₙ α P.1 P.2) y
                    + ∑ p : TensorCompIdx (E := E) r s,
                        chartInvGramEuclid (I := I) g α k l y *
                            (euclidPartial (E := E) l
                                (gramInvEntry (I := I) (M := M)
                                  g r s α Q P₀) y +
                              lowerOrderRotationLOCoeff (I := I) (M := M)
                                g r s α P₀ l Q y) *
                            covDerivLowerOrderCoeff (I := I) (M := M)
                              g r s α k P.1 p.1 P.2 p.2 y *
                          tensorChartComponent (I := I) (M := M)
                            g r s wₙ α p.1 p.2 y)) =
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M)
                    g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  valueComponentFactor (I := I) (M := M)
                      g r s α P₀ P Q k l p y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      -- Per-`(k, l)` summand: distribute `covChartMetricGram` over the body.
      rw [mul_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [valuePartialFactor]; ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [valueComponentFactor]; ring]
    -- Separate the partial / component parts of the double sum.
    rw [Finset.sum_congr rfl (fun k _ =>
        Finset.sum_add_distrib
          (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))),
      Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
    (fun Q _ => hsplit P Q))]
  -- Separate the partial / component parts of the outer double sum.
  rw [Finset.sum_congr rfl (fun P _ =>
      Finset.sum_add_distrib (s := (Finset.univ : Finset (TensorCompIdx (E := E) r s)))),
    Finset.sum_add_distrib]

/-- The lower-order rotation value coefficient at the partition-of-unity-weighted
approximant is `L²`. -/
theorem covLowerOrderRotationValueCoeff_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  -- The chart-partial-atom group: `valuePartialFactor · ∂_k chart component`.
  have hpart : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
              g r s h_atlas i α P k n
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)))))
  -- The component-atom group: `valueComponentFactor · chart component`.
  have hcomp : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor α p.1 p.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s h_atlas i α p n
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p))))))
  refine (hpart.add hcomp).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covLowerOrderRotationValueCoeff_pouSmul_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ n hy)

/-- **The explicit `L²`-limit function of the lower-order rotation value
coefficient.** A finite `C^∞`-coefficient-weighted sum of the chart-partial limit
object `partialLpLimit` (the chart-partial-atom group) and the chart-component
limit object `componentLpLimit` (the component-atom group), each coefficient cut
to the partition-of-unity kernel. -/
noncomputable def covLowerOrderRotationValueCoeffLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
                (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                  EuclN → ℝ) y)
      + ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                      EuclN → ℝ) y

/-- The `L²`-limit function of the lower-order rotation value coefficient is
`L²`. -/
theorem covLowerOrderRotationValueCoeffLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
              (valuePartialFactor_contDiffOn (I := I) (M := M)
                g r s α P₀ P Q k l)
              (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k)))))
  · exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => memLp_finset_sum
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k _ => memLp_finset_sum
            (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l _ => memLp_finset_sum
              (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (valueComponentFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ P Q k l p)
                (componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p))))))

/-- **The `n → ∞` `L²`-limit of the lower-order rotation value coefficient.**
For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the `L²` classes
of the lower-order rotation value coefficient `covLowerOrderRotationValueCoeff g
r s Tₙ α P₀` at the partition-of-unity-weighted approximants `Tₙ := pouSmul g r s
α (eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor` converge, as `n → ∞`
and in `Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of the explicit limit
function `covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀`. -/
theorem covLowerOrderRotationValueCoeff_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ n).toLp _)
      atTop
      (𝓝 ((covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀).toLp _)) := by
  classical
  -- The chart-partial-atom group: `valuePartialFactor · ∂_k chart component`,
  -- with limit the kernel-cut `valuePartialFactor` against `partialLpLimit`.
  have h_part := tendsto_sum4 (I := I) (M := M) α
    (f := fun P Q k l n y =>
      valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P.1 P.2) y)
    (flim := fun P Q k l y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
        (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          EuclN → ℝ) y)
    (fun P Q k l n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s h_atlas i α P k n
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
    (fun P Q k l => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k))
    (fun P Q k l => tendsto_partialSummand (I := I) (M := M)
      g r s h_atlas i α P k
      (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s h_atlas i α P k n
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k)))
  -- The component-atom group: `valueComponentFactor · chart component`, with
  -- limit the kernel-cut `valueComponentFactor` against `componentLpLimit`.
  have h_comp := tendsto_sum5 (I := I) (M := M) α
    (f := fun P Q k l p n y =>
      valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α p.1 p.2 y)
    (flim := fun P Q k l p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
        (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
          EuclN → ℝ) y)
    (fun P Q k l p n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s h_atlas i α p n
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p))
    (fun P Q k l p => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (componentLpLimit (I := I) (M := M) g r s h_atlas i α p))
    (fun P Q k l p => tendsto_componentSummand (I := I) (M := M)
      g r s h_atlas i α p
      (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s h_atlas i α p n
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ P Q k l p))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit (I := I) (M := M) g r s h_atlas i α p)))
  have h_add := h_part.add h_comp
  -- Identify the `n`-th sum with the value-coefficient `L²` class.
  have h_termN : ∀ n : ℕ,
      (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                  g r s h_atlas i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                    g r s h_atlas i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeff_pouSmul_eqOn (I := I) (M := M)
        g r s h_atlas i α P₀ n hy)
  -- Identify the limiting sum with the value-coefficient limit `L²` class.
  have h_termLim :
      (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)
                  (partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α P k)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p)
                    (componentLpLimit (I := I) (M := M)
                      g r s h_atlas i α p))))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [covLowerOrderRotationValueCoeffLimit]
  rw [show (fun n => (covLowerOrderRotationValueCoeff_pouSmul_memLp
        (I := I) (M := M) g r s h_atlas i α P₀ n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                  g r s h_atlas i α P k n
                  (valuePartialFactor_contDiffOn (I := I) (M := M)
                    g r s α P₀ P Q k l)))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun P _ => memLp_finset_sum Finset.univ
            (fun Q _ => memLp_finset_sum Finset.univ
              (fun k _ => memLp_finset_sum Finset.univ
                (fun l _ => memLp_finset_sum Finset.univ
                  (fun p _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                    g r s h_atlas i α p n
                    (valueComponentFactor_contDiffOn (I := I) (M := M)
                      g r s α P₀ P Q k l p))))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
