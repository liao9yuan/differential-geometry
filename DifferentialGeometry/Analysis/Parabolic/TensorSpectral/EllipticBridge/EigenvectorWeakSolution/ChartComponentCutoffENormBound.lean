import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset

/-!
# A quantitative weighted-`eLpNorm` bound for the cutoff Euclidean chart component

For a closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, an abstract `L²`
tensor element `u : TensorL2 r s g`, a chart base point `α : M`, and a component
multi-index `P₀`, the cutoff Euclidean chart `P₀`-component
`tensorL2ChartComponentCutoff g r s u α P₀` is an element of the chart `L²`
Hilbert space `Lp ℝ 2 (chartL2Measure α)` (with `chartL2Measure α` the plain
Lebesgue measure restricted to the Euclidean chart target).

A downstream weak-solution argument measures the chart component against a
*different* reference measure on the chart target — the chart-pulled weighted
measure `chartPulledWeightedMeasure g α` (Lebesgue volume weighted by the
chart-density `densityOnEuclid g α`) restricted to the chart target. This file
provides the quantitative reconciliation: there is a constant — depending on
`g, r, s, α` but **not** on `u` — bounding the weighted `eLpNorm` of the cutoff
chart component by that constant times the abstract element's norm `‖u‖`.

## Strategy

The cutoff chart component is the value of a continuous linear map
`tensorL2ChartComponentCutoffCLM g r s α P₀` applied to `u`, so its chart `L²`
norm is `≤ ‖tensorL2ChartComponentCutoffCLM g r s α P₀‖ · ‖u‖`. The chart `L²`
norm of an `Lp ℝ 2 (chartL2Measure α)` element is the real part of its `eLpNorm`
against `chartL2Measure α`.

To convert from `chartL2Measure α` to the chart-pulled weighted measure we use
that the cutoff confines the component to the compact chart-kernel
`cutoffChartKernel α`. The cutoff component of any *smooth* section is the
concrete `cutoffComponentEuclid`, which is supported in the (Euclidean image of
the) compact kernel; the set of `Lp` classes that vanish almost everywhere off
that kernel is the kernel of a continuous linear map, so — smooth sections being
dense — *every* cutoff chart component vanishes almost everywhere off the kernel.
On the compact kernel the chart-density `densityOnEuclid g α` is bounded above,
so the weighted `eLpNorm` is bounded by a constant times the plain-volume
`eLpNorm`, i.e. by a constant times the chart `L²` norm.

## Main results

* `eLpNorm_tensorL2ChartComponentCutoff_le` — the quantitative weighted-`eLpNorm`
  bound for the cutoff Euclidean chart component.

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

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
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

/-! ## The compact Euclidean cutoff kernel

The cutoff Euclidean chart component vanishes outside the chart image of the
compact support of the chart-kernel cutoff. Pushing that compact chart image
through `toEuclidean` produces the compact subset of `EuclN` confining every
cutoff Euclidean chart component. -/

/-- The Euclidean image of the compact cutoff chart kernel: the compact subset of
`EuclN` outside which every cutoff Euclidean chart component vanishes. -/
private def cutoffKernelEuclid (α : M) : Set EuclN :=
  (toEuclidean : E ≃L[ℝ] EuclN) '' (cutoffChartKernel (I := I) (M := M) α)

private lemma cutoffKernelEuclid_isCompact (α : M) :
    IsCompact (cutoffKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernel_isCompact (I := I) (M := M) α).image
    (toEuclidean (E := E)).continuous

private lemma cutoffKernelEuclid_measurableSet (α : M) :
    MeasurableSet (cutoffKernelEuclid (I := I) (M := M) α) :=
  (cutoffKernelEuclid_isCompact (I := I) (M := M) α).isClosed.measurableSet

/-- The Euclidean cutoff kernel sits inside the Euclidean chart target: the
chart kernel is contained in the extended-chart target, and `toEuclidean` carries
the extended-chart target onto `chartTargetEuclid α`. -/
private lemma cutoffKernelEuclid_subset_chartTargetEuclid (α : M) :
    cutoffKernelEuclid (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, cutoffChartKernel_subset_target (I := I) (M := M) α hx, rfl⟩

/-- The concrete cutoff Euclidean chart component of a smooth section is
supported inside the Euclidean cutoff kernel: off the chart target it vanishes
by `chartPushedRaw`'s definition, and on the chart target it reads the cutoff
scalar at the chart preimage, whose support's chart image lands in the kernel. -/
private lemma cutoffComponentEuclid_support_subset_cutoffKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Function.support
        (cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2) ⊆
      cutoffKernelEuclid (I := I) (M := M) α := by
  classical
  intro y hy
  have hy_ne : cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y ≠ 0 :=
    hy
  by_cases hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- On the chart target the component reads the cutoff scalar at the preimage.
    rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M)
      g r s S α P₀.1 P₀.2 hy_in] at hy_ne
    -- The chart preimage of `y` lies in the support of the cutoff scalar.
    have hp_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        Function.support
          (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) :=
      hy_ne
    have hp_tsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport
          (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) :=
      subset_tsupport _ hp_supp
    -- Its chart image lands in the compact cutoff chart kernel.
    have hx_kernel :
        (extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ∈
          cutoffChartKernel (I := I) (M := M) α :=
      cutoffComponentScalar_chartImage_subset_kernel
        (I := I) (M := M) g r s S α P₀.1 P₀.2
        ⟨_, hp_tsupp, rfl⟩
    -- On the chart target `extChartAt ∘ extChartAt.symm` is the identity.
    have hy_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy_in
    rw [(extChartAt I α).right_inv hy_tgt] at hx_kernel
    -- Transfer the kernel membership through `toEuclidean`.
    refine ⟨(toEuclidean (E := E)).symm y, hx_kernel, ?_⟩
    exact (toEuclidean (E := E)).apply_symm_apply y
  · -- Off the chart target the chart-pushforward vanishes, contradicting `hy`.
    exact absurd
      (cutoffComponentEuclid_apply_of_notMem (I := I) (M := M)
        g r s S α P₀.1 P₀.2 hy_in)
      hy_ne

/-! ## On-compact density bound

On a compact subset of the Euclidean chart target the chart-density
`densityOnEuclid g α` is bounded above by a positive constant. Consequently, for
a function supported in such a compact subset, the `eLpNorm` against the
chart-pulled weighted measure restricted to the chart target is bounded by a
constant times the `eLpNorm` against plain Lebesgue volume restricted to the
chart target. -/

set_option linter.unusedSectionVars false in
/-- For a function supported in a subset `K` of the Euclidean chart target on
which the chart-density `densityOnEuclid g α` is bounded above by `densitySup`,
the `eLpNorm` against the chart-pulled weighted measure (restricted to the chart
target) is bounded by `densitySup ^ (1 / 2)` times the `eLpNorm` against plain
Lebesgue volume (restricted to the chart target). -/
private lemma eLpNorm_chartPulledWeighted_restrict_le_of_support_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (densitySup : ℝ) (hdensitySup_pos : 0 < densitySup)
    (hdensitySup_bd : ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ densitySup)
    {f : EuclN → ℝ} (hf_supp : Function.support f ⊆ K) :
    eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (densitySup ^ (1 / (2 : ℝ))) *
        eLpNorm f 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set S : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hS_def
  have hS_open : IsOpen S :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  -- `(2 : ℝ≥0∞).toReal = 2`.
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  -- Bound the `lintegral` of the enorm-power against the weighted measure.
  have h_lint_le :
      ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)
          ∂((chartPulledWeightedMeasure (I := I) g α).restrict S) ≤
        ENNReal.ofReal densitySup *
          ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂((volume : Measure EuclN).restrict S) := by
    rw [show (chartPulledWeightedMeasure (I := I) g α).restrict S =
        ((volume : Measure EuclN).restrict S).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.restrict_withDensity hS_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
    rotate_left
    · have hdens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) S :=
        densityOnEuclid_continuousOn (I := I) g α
      exact (hdens_contOn.aemeasurable hS_meas).ennreal_ofReal
    · exact Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
    rw [show ENNReal.ofReal densitySup *
          ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂((volume : Measure EuclN).restrict S) =
        ∫⁻ y, ENNReal.ofReal densitySup * ‖f y‖ₑ ^ (2 : ℝ)
          ∂((volume : Measure EuclN).restrict S) from
      (MeasureTheory.lintegral_const_mul' (r := ENNReal.ofReal densitySup) _
        ENNReal.ofReal_ne_top).symm]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Pi.mul_apply]
    by_cases hfy : f y = 0
    · simp [hfy, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    · have hy_in : y ∈ K := hf_supp hfy
      have h_dens_le :
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) ≤
            ENNReal.ofReal densitySup :=
        ENNReal.ofReal_le_ofReal (hdensitySup_bd y hy_in)
      gcongr
  -- Take the `(1 / 2)`-th power and distribute the constant.
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by positivity)) ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hdensitySup_pos]

/-! ## The restriction continuous linear map

For a measurable subset `s` of the chart target, restricting an
`Lp ℝ 2 (chartL2Measure α)` class to `s` produces an
`Lp ℝ 2 ((chartL2Measure α).restrict s)` class. Since the restricted measure is
dominated by `chartL2Measure α`, restriction is a norm-nonincreasing linear map,
hence continuous. The cutoff chart component of every smooth section restricts to
the zero class on the complement of the cutoff kernel; continuity and density
then propagate that vanishing to the cutoff chart component of every abstract
element. -/

/-- The restriction linear map sending an `Lp ℝ 2 (chartL2Measure α)` class to
its restriction as an `Lp ℝ 2 ((chartL2Measure α).restrict s)` class. -/
private def chartL2RestrictLin (α : M) (s : Set EuclN) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →ₗ[ℝ]
      Lp ℝ 2 ((chartL2Measure (I := I) (M := M) α).restrict s) where
  toFun lp :=
    ((Lp.memLp lp).restrict s).toLp (lp : EuclN → ℝ)
  map_add' lp₁ lp₂ := by
    -- Both sides are `toLp` of almost-everywhere-equal functions on the
    -- restricted measure.
    rw [show (((Lp.memLp lp₁).restrict s).toLp ((lp₁ : EuclN → ℝ)) +
          ((Lp.memLp lp₂).restrict s).toLp ((lp₂ : EuclN → ℝ))) =
        (((Lp.memLp lp₁).restrict s).add ((Lp.memLp lp₂).restrict s)).toLp
          ((lp₁ : EuclN → ℝ) + (lp₂ : EuclN → ℝ)) from
      (MemLp.toLp_add _ _).symm]
    refine MemLp.toLp_congr _ _ ?_
    exact (Measure.restrict_le_self.absolutelyContinuous).ae_eq
      (Lp.coeFn_add lp₁ lp₂)
  map_smul' c lp := by
    simp only [RingHom.id_apply]
    rw [show (c • ((Lp.memLp lp).restrict s).toLp ((lp : EuclN → ℝ))) =
        (((Lp.memLp lp).restrict s).const_smul c).toLp
          (c • (lp : EuclN → ℝ)) from (MemLp.toLp_const_smul c _).symm]
    refine MemLp.toLp_congr _ _ ?_
    exact (Measure.restrict_le_self.absolutelyContinuous).ae_eq
      (Lp.coeFn_smul c lp)

set_option linter.unusedSectionVars false in
private lemma chartL2RestrictLin_norm_le (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    ‖chartL2RestrictLin (I := I) (M := M) α s lp‖ ≤ 1 * ‖lp‖ := by
  classical
  rw [one_mul]
  -- The restricted norm is the `eLpNorm` against the restricted measure.
  rw [chartL2RestrictLin, LinearMap.coe_mk, AddHom.coe_mk,
    Lp.norm_toLp, Lp.norm_def]
  -- `eLpNorm` is monotone in the measure: the restricted measure is smaller.
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top lp) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The restriction map as a continuous linear map. -/
private def chartL2RestrictCLM (α : M) (s : Set EuclN) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →L[ℝ]
      Lp ℝ 2 ((chartL2Measure (I := I) (M := M) α).restrict s) :=
  (chartL2RestrictLin (I := I) (M := M) α s).mkContinuous 1
    (chartL2RestrictLin_norm_le (I := I) (M := M) α s)

set_option linter.unusedSectionVars false in
@[simp] private lemma chartL2RestrictCLM_apply (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    chartL2RestrictCLM (I := I) (M := M) α s lp =
      ((Lp.memLp lp).restrict s).toLp (lp : EuclN → ℝ) := rfl

/-- The restriction of an `Lp ℝ 2 (chartL2Measure α)` class to `s` is the zero
class exactly when the class's representative vanishes almost everywhere on the
restricted measure `(chartL2Measure α).restrict s`. -/
private lemma chartL2RestrictCLM_eq_zero_iff (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    chartL2RestrictCLM (I := I) (M := M) α s lp = 0 ↔
      (lp : EuclN → ℝ)
        =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict s] 0 := by
  rw [chartL2RestrictCLM_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    exact (MemLp.coeFn_toLp _).symm.trans h
  · intro h
    exact (MemLp.coeFn_toLp _).trans h

/-! ## Off-kernel vanishing of the cutoff chart component

The composite `chartL2RestrictCLM ∘ tensorL2ChartComponentCutoffCLM`, restricting
to the complement of the cutoff kernel, is a continuous linear map vanishing on
the dense subspace of smooth sections, hence identically zero. -/

/-- The cutoff chart component of a smooth section, restricted to the complement
of the cutoff kernel, is the zero `Lp` class: the smooth-section component
`cutoffComponentEuclid` is supported in the cutoff kernel. -/
private lemma chartL2RestrictCLM_tensorL2ChartComponentCutoff_smooth_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    chartL2RestrictCLM (I := I) (M := M) α
        (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
        (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S))
      = 0 := by
  classical
  -- It suffices to show the cutoff chart component vanishes a.e. off the kernel.
  have hKcompl_meas : MeasurableSet (cutoffKernelEuclid (I := I) (M := M) α)ᶜ :=
    (cutoffKernelEuclid_measurableSet (I := I) (M := M) α).compl
  -- The cutoff chart component vanishes almost everywhere off the cutoff kernel:
  -- on a smooth section it agrees a.e. with the concrete `cutoffComponentEuclid`,
  -- which is supported in the kernel.
  have h_ae :
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (S : TensorL2 r s g) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
          (cutoffKernelEuclid (I := I) (M := M) α)ᶜ] 0 := by
    refine (MeasureTheory.ae_restrict_iff' hKcompl_meas).mpr ?_
    have h_coeFn :=
      tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
        (I := I) (M := M) g r s S α P₀
    filter_upwards [h_coeFn] with y hy hy_off
    have hy_zero :
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (S : TensorL2 r s g) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [hy]
      by_contra hne
      exact hy_off
        (cutoffComponentEuclid_support_subset_cutoffKernelEuclid
          (I := I) (M := M) g r s S α P₀ hne)
    simpa using hy_zero
  -- Convert the almost-everywhere vanishing into the zero `Lp` class.
  rw [tensorL2ChartComponentCutoffCLM_apply, SmoothCcTensor.toL2_apply]
  exact (chartL2RestrictCLM_eq_zero_iff (I := I) (M := M) α
    (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (S : TensorL2 r s g) α P₀)).mpr h_ae

/-- **Off-kernel vanishing of the cutoff chart component.** For an abstract `L²`
tensor element `u`, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r s u α P₀` vanishes almost everywhere — on the
chart `L²` measure — outside the compact Euclidean cutoff kernel.

The restriction-to-`Kᶜ` of the cutoff chart component is a continuous linear map
of `u` that vanishes on the dense subspace of smooth sections (their concrete
cutoff component `cutoffComponentEuclid` is supported in the kernel), hence
vanishes identically. -/
private lemma tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        (cutoffKernelEuclid (I := I) (M := M) α)ᶜ] 0 := by
  classical
  -- The composite restriction-of-the-chart-component CLM is zero by density.
  have h_zero :
      chartL2RestrictCLM (I := I) (M := M) α
          (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
          (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀ u)
        = 0 := by
    -- The composite continuous linear map vanishes on the dense smooth range.
    refine DenseRange.induction_on
      (SmoothCcTensor.denseRange_toL2
        (g := g) (r := r) (s := s))
      u ?_ ?_
    · -- The vanishing locus is closed: preimage of `{0}` under a continuous map.
      exact isClosed_eq
        ((chartL2RestrictCLM (I := I) (M := M) α
            (cutoffKernelEuclid (I := I) (M := M) α)ᶜ).continuous.comp
          (tensorL2ChartComponentCutoffCLM
            (I := I) (M := M) g r s α P₀).continuous)
        continuous_const
    · intro S
      exact chartL2RestrictCLM_tensorL2ChartComponentCutoff_smooth_eq_zero
        (I := I) (M := M) g r s S α P₀
  -- Translate `chartL2RestrictCLM … = 0` into the almost-everywhere identity.
  have h_eq := (chartL2RestrictCLM_eq_zero_iff (I := I) (M := M) α
    (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
    (tensorL2ChartComponentCutoffCLM
      (I := I) (M := M) g r s α P₀ u)).mp h_zero
  rw [tensorL2ChartComponentCutoffCLM_apply] at h_eq
  exact h_eq

/-! ## The quantitative weighted-`eLpNorm` bound -/

/-- **A quantitative weighted-`eLpNorm` bound for the cutoff Euclidean chart
component.** For a closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, an
abstract `L²` tensor element `u : TensorL2 r s g`, a chart base point `α`, and a
component multi-index `P₀`, there is a non-negative constant `C` — depending only
on `g, r, s, α` — such that the `eLpNorm` of the cutoff Euclidean chart
`P₀`-component of `u` against the chart-pulled weighted measure
`chartPulledWeightedMeasure g α` restricted to the Euclidean chart target is
bounded by `ENNReal.ofReal C` times the abstract element's norm `‖u‖`.

The cutoff chart component is the value of a continuous linear map of `u`, so its
chart `L²` norm is bounded by the operator norm times `‖u‖`. The cutoff confines
the component to the compact Euclidean cutoff kernel
(`tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel`); on that compact set
the chart-density is bounded above, so the weighted `eLpNorm` is controlled by a
constant times the plain-volume `eLpNorm`, i.e. by the chart `L²` norm. -/
theorem eLpNorm_tensorL2ChartComponentCutoff_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (u : TensorL2 r s g) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖ := by
  classical
  -- Abbreviations: the chart component's `Lp` class, its coerced representative,
  -- the compact cutoff kernel and its complement.
  set w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ with hw_def
  set f : EuclN → ℝ := (w : EuclN → ℝ) with hf_def
  set K : Set EuclN := cutoffKernelEuclid (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    cutoffKernelEuclid_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    cutoffKernelEuclid_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α
  -- An upper bound for the chart-density on the compact cutoff kernel.
  obtain ⟨_c_min, c_max, _hc_min_pos, hc_le, h_dens_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  have hc_max_pos : 0 < c_max := lt_of_lt_of_le _hc_min_pos hc_le
  -- The operator norm of the cutoff-chart-component continuous linear map.
  set Cop : ℝ := ‖tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀‖
    with hCop_def
  have hCop_nn : 0 ≤ Cop :=
    norm_nonneg (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀)
  -- The headline constant.
  refine ⟨c_max ^ (1 / (2 : ℝ)) * Cop,
    mul_nonneg (Real.rpow_nonneg hc_max_pos.le _) hCop_nn, ?_⟩
  -- Replace `f` by its kernel-indicator: they agree a.e. on `chartL2Measure α`,
  -- and the indicator is genuinely supported in the compact kernel.
  set fK : EuclN → ℝ := K.indicator f with hfK_def
  -- `f` and `fK` agree almost everywhere on `chartL2Measure α`.
  have h_off : f =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict Kᶜ] 0 :=
    tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel
      (I := I) (M := M) g r s u α P₀
  have hf_aeEq_fK : f =ᵐ[chartL2Measure (I := I) (M := M) α] fK := by
    -- Off `K` both sides vanish; on `K` the indicator is the identity.
    rw [hfK_def]
    have hKcompl_meas : MeasurableSet Kᶜ := hK_meas.compl
    have h_off' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∈ Kᶜ → f y = 0 := by
      rw [← MeasureTheory.ae_restrict_iff' hKcompl_meas]
      filter_upwards [h_off] with y hy using hy
    filter_upwards [h_off'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy (by simpa using hyK)]
  -- `fK` is genuinely supported inside the compact kernel.
  have hfK_supp : Function.support fK ⊆ K := by
    rw [hfK_def]; exact Set.support_indicator_subset
  -- The weighted `eLpNorm` of `f` equals that of `fK` (a.e.-congruence: the
  -- restricted weighted measure is dominated by `chartL2Measure α`).
  have h_wabs : (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) ≪
        chartL2Measure (I := I) (M := M) α := by
    -- `chartL2Measure α = volume.restrict chartTarget`; the weighted measure is
    -- `volume.withDensity _`, which is absolutely continuous w.r.t. `volume`,
    -- and absolute continuity is preserved under restriction.
    have h_cl2 : chartL2Measure (I := I) (M := M) α =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := rfl
    rw [h_cl2]
    have h_base : (chartPulledWeightedMeasure (I := I) g α) ≪
        (volume : Measure EuclN) := by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    exact h_base.restrict (chartTargetEuclid (I := I) (M := M) α)
  have hf_aeEq_fK_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK :=
    h_wabs.ae_eq hf_aeEq_fK
  -- Likewise the plain-volume `eLpNorm` of `f` equals that of `fK`.
  have hf_aeEq_fK_v : f =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK := hf_aeEq_fK
  -- The chart `L²` norm of `w` is the real part of its `chartL2Measure`-`eLpNorm`.
  have hf_eLpNorm_eq : eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) =
      ‖w‖ₑ := by
    rw [hf_def, Lp.enorm_def]
  -- Operator-norm bound on the chart component.
  have hw_op : ‖w‖ ≤ Cop * ‖u‖ := by
    rw [hw_def, hCop_def,
      ← tensorL2ChartComponentCutoffCLM_apply (I := I) (M := M) g r s α P₀ u]
    exact (tensorL2ChartComponentCutoffCLM
      (I := I) (M := M) g r s α P₀).le_opNorm u
  -- Assemble the bound.
  calc eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
      = eLpNorm fK 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_congr_ae hf_aeEq_fK_w
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm fK 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_chartPulledWeighted_restrict_le_of_support_subset
          (I := I) (M := M) g α c_max hc_max_pos
          (fun y hy => (h_dens_bd y hy).2) hfK_supp
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl,
          eLpNorm_congr_ae hf_aeEq_fK_v.symm]
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) * ‖w‖ₑ := by
        rw [hf_eLpNorm_eq]
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          ENNReal.ofReal (Cop * ‖u‖) := by
        gcongr
        rw [← ofReal_norm_eq_enorm w]
        exact ENNReal.ofReal_le_ofReal hw_op
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ)) * Cop) * ENNReal.ofReal ‖u‖ := by
        rw [ENNReal.ofReal_mul hCop_nn,
          ENNReal.ofReal_mul (Real.rpow_nonneg hc_max_pos.le _), mul_assoc]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
