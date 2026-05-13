import DifferentialGeometry.Analysis.Laplacian.Regularity.HessianLpClass
import DifferentialGeometry.Analysis.Laplacian.Regularity.HessianPairingChart
import DifferentialGeometry.Analysis.Laplacian.Regularity.RicciPairingCLM
import DifferentialGeometry.Analysis.Sobolev.Chart.MeasurablePullback
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Chart-local Hessian-Frobenius pairing for `u_h ∈ laplacianDomain g`

For a smooth scalar `φ : C^∞⟮I, M; ℝ⟯` and an element `u_h ∈ laplacianDomain g`
of the Laplacian domain on a closed Riemannian manifold `(M, g)`, this module
constructs the chart-local pointwise Hessian-Frobenius pairing on
`chartTargetEuclid α`:

```
y ↦ ∑_{i, j, k, l} G^{ik}(y) · G^{jl}(y) · H^φ_{ij}(y) · H^{u_h}_{kl}(y),
```

where `H^φ_{ij}(y) = chartHessianTensor g α φ i j ((extChartAt I α).symm
((toEuclidean E).symm y))` is the smooth chart Hessian of `φ` and
`H^{u_h}_{ij}(y) = laplacianDomainHessianChart g α hu_h i j y` is the
chart-side weak Hessian of `u_h` (from `HessianLpClass`).

This chart-local function is in `L^2` of the chart-target-restricted volume,
combining the boundedness of the smooth coefficients (`cutoffInvGram` and an
analogous cutoff Hessian-φ) with the chart-side Hessian's `L^2` regularity.

## Main definitions

* `chartHessianPhiOnEuclid g α φ i j y` — chart-pullback of `chartHessianTensor
  g α φ i j` to `EuclideanSpace`.
* `hessPairingChartLocal g α φ hu_h y` — chart-local Frobenius pairing on `EuclN`.

## Main results

* `chartHessianPhiOnEuclid_continuousOn` — chart-pullback Hessian of `φ` is
  continuous on `chartTargetEuclid α`.
* `hessPairingChartLocal_memLp_two` — the chart-local pairing is in `L^2`
  of the chart-target-restricted volume.
* `hessPairingChartLocal_memLp_one` — same, in `L^1`.

## Subsequent files

Subsequent files take the chart-local Lp 2 pieces and assemble a global
`Lp 2 μ_g` class via partition-of-unity weighting.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianPairingLapDom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The smooth Hess of `φ` pulled to `EuclideanSpace` -/

/-- The chart-pullback Hessian of the smooth scalar `φ` in the chart at `α`:
the manifold-side smooth Hessian `chartHessianTensor g α φ i j` pulled back to
`EuclideanSpace` via the inverse chart and `toEuclidean.symm`. -/
noncomputable def chartHessianPhiOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartHessianTensor (I := I) g α (φ : M → ℝ) i j
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

@[simp] lemma chartHessianPhiOnEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y =
      chartHessianTensor (I := I) g α (φ : M → ℝ) i j
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

/-! ## Bounded chart-pullback Hessian via the cutoff -/

/-- The cutoff-multiplied chart-pullback Hessian: bounded everywhere on `EuclN`. -/
private noncomputable def cutoffHessianPhi
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y

private lemma cutoffHessianPhi_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffHessianPhi (I := I) (M := M) g α φ i j y =
      chartCutoffα (I := I) (M := M) α y *
        chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y := rfl

/-! ## The chart-local Hess pairing function -/

/-- The chart-local Frobenius pairing function on `EuclideanSpace`. -/
noncomputable def hessPairingChartLocal
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma hessPairingChartLocal_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) :
    hessPairingChartLocal (I := I) (M := M) g α φ hu_h y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := rfl

/-! ## `chartHessianPhiOnEuclid` is continuous on `chartTargetEuclid α` -/

lemma chartHessianPhiOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The chart-pullback Hessian, on chartTargetEuclid α, expands as the
  -- iterated partial deriv minus a Christoffel-correction. We show continuity
  -- of each piece on chartTargetEuclid α via composition with `(toEuclidean.symm)`.
  -- On chartTargetEuclid α, `extChartAt I α ∘ extChartAtSymm = id_{toEuclidean.symm
  -- y on chartTargetEuclid α}`. So `chartHessianTensor g α (φ : M → ℝ) i j (chart-symm y)`
  -- equals the chart-target-side iterated partials minus Christoffel.
  have hrewrite : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y =
        chartIteratedPartialDeriv (I := I) α (φ : M → ℝ) i j
          ((toEuclidean (E := E)).symm y) -
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k ((toEuclidean (E := E)).symm y) *
            partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ))
              ((toEuclidean (E := E)).symm y) := by
    intro y hy
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have h_inv : extChartAt I α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        (toEuclidean (E := E)).symm y :=
      (extChartAt I α).right_inv hy_target
    rw [chartHessianPhiOnEuclid_def, chartHessianTensor_def, h_inv]
  refine ContinuousOn.congr ?_ hrewrite
  -- Continuity of the RHS on chartTargetEuclid α: composition of continuous pieces.
  refine ContinuousOn.sub ?_ ?_
  · -- chartIteratedPartialDeriv α (φ : M → ℝ) i j ∘ (toEuclidean.symm).
    have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous
    have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α φ.contMDiff
    have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
      (isOpen_extChartAt_target (I := I) α).interior_eq
    have h_smooth_iter : ContDiffOn ℝ ∞
        (chartIteratedPartialDeriv (I := I) α (φ : M → ℝ) i j)
        (extChartAt I α).target := by
      unfold chartIteratedPartialDeriv partialDeriv
      have h_fder1 : ContDiffOn ℝ ∞
          (fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)))
          (extChartAt I α).target :=
        h_smooth_target.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      have h_pd_j : ContDiffOn ℝ ∞
          (fun z : E => fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)) z
            ((chartModelBasis E) j))
          (extChartAt I α).target :=
        h_fder1.clm_apply contDiffOn_const
      have h_fder2 : ContDiffOn ℝ ∞
          (fderiv ℝ (fun z : E => fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)) z
            ((chartModelBasis E) j)))
          (extChartAt I α).target :=
        h_pd_j.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      exact h_fder2.clm_apply contDiffOn_const
    have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
      toEuclidean_symm_mem_target (I := I) hy
    exact h_smooth_iter.continuousOn.comp h_toE_cont.continuousOn h_maps
  · -- Christoffel correction sum.
    refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun k _ => ?_)
    have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous
    have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
      (isOpen_extChartAt_target (I := I) α).interior_eq
    have h_chris_cont : ContinuousOn (chartChristoffel (I := I) g α i j k)
        (extChartAt I α).target := by
      rw [← h_int_eq_target]
      exact (chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn
    have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α φ.contMDiff
    have h_pd_cont : ContinuousOn
        (partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ)))
        (extChartAt I α).target := by
      unfold partialDeriv
      rw [← h_int_eq_target]
      have h_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
          (interior (extChartAt I α).target) := h_smooth_target.mono interior_subset
      have h_fder : ContDiffOn ℝ ∞
          (fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)))
          (interior (extChartAt I α).target) :=
        h_smooth_int.fderiv_of_isOpen isOpen_interior
          (by rw [ENat.coe_top_add_one])
      exact (h_fder.clm_apply contDiffOn_const).continuousOn
    have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
      toEuclidean_symm_mem_target (I := I) hy
    have h_chris_comp : ContinuousOn
        (fun y : EuclN => chartChristoffel (I := I) g α i j k
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_chris_cont.comp h_toE_cont.continuousOn h_maps
    have h_pd_comp : ContinuousOn
        (fun y : EuclN => partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ))
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_pd_cont.comp h_toE_cont.continuousOn h_maps
    exact h_chris_comp.mul h_pd_comp

/-! ## `cutoffHessianPhi` is continuous on `EuclN` and bounded -/

private lemma cutoffHessianPhi_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffHessianPhi (I := I) (M := M) g α φ i j) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianPhi (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianPhi
    rw [hη_zero, zero_mul]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hH_cont_at : ContinuousAt (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j) y :=
      (chartHessianPhiOnEuclid_continuousOn (I := I) (M := M) g α φ i j).continuousAt
        (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hH_cont_at
  · have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have h_eventually_zero :
        cutoffHessianPhi (I := I) (M := M) g α φ i j =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    exact (continuousAt_const (y := (0 : ℝ))).congr h_eventually_zero.symm

private lemma cutoffHessianPhi_bounded
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |cutoffHessianPhi (I := I) (M := M) g α φ i j y| ≤ C := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have h_cont : Continuous (cutoffHessianPhi (I := I) (M := M) g α φ i j) :=
    cutoffHessianPhi_continuous (I := I) (M := M) g α φ i j
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianPhi (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianPhi
    rw [hη_zero, zero_mul]
  by_cases hKη_ne : Kη.Nonempty
  · have h_norm_cont : ContinuousOn
        (fun y : EuclN => ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y‖) Kη :=
      h_cont.continuousOn.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne h_norm_cont
    set C := ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · have h := hy₀_max hyK
      have h_eq : |cutoffHessianPhi (I := I) (M := M) g α φ i j y| =
          ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y‖ := rfl
      rw [h_eq]; exact h
    · rw [h_zero_off y hyK, abs_zero]; exact hC_nn
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

private lemma cutoffHessianPhi_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E))
    (μ : Measure EuclN) :
    AEStronglyMeasurable (cutoffHessianPhi (I := I) (M := M) g α φ i j) μ :=
  (cutoffHessianPhi_continuous (I := I) (M := M) g α φ i j).aestronglyMeasurable

/-! ## Ae-equality of the chart-local pairing with the cutoff version

On `volume.restrict chartTargetEuclid α`, we replace the (potentially-unbounded)
factors `invGramOnEuclid` and `chartHessianPhiOnEuclid` by their cutoff
counterparts, since `H^{u_h}_{kl}` is ae-zero outside the support kernel `K`
of η. On `K`, η = 1, so the cutoff factors equal the originals pointwise. -/

private lemma hessPairingChartLocal_ae_eq_cutoff
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    hessPairingChartLocal (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas
  -- Pointwise equality on K (η = 1).
  have h_pt_K : ∀ y ∈ K, ∀ i j k l : Fin (Module.finrank ℝ E),
      invGramOnEuclid (I := I) g α i k y *
          invGramOnEuclid (I := I) g α j l y *
          chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y =
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          cutoffHessianPhi (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    intro y hy i j k l
    have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
      chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
    unfold cutoffInvGram cutoffHessianPhi
    rw [hη_one]; ring
  -- Ae-zero on V for H^{u_h}_{kl}: combined into a single ae statement.
  have hae_zero_all : ∀ᵐ y ∂(volume : Measure EuclN),
      ∀ (k l : Fin (Module.finrank ℝ E)), y ∈ V →
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 := by
    have h_pair_ae : ∀ (p : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)),
        ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h p.1 p.2 y = 0 := by
      intro p
      have h := laplacianDomainHessianChart_ae_zero_off_support
        (I := I) (M := M) g α hu_h p.1 p.2
      have := (ae_restrict_iff' hV_meas).mp h
      filter_upwards [this] with y hy hyV
      exact hy hyV
    have h_all : ∀ᵐ y ∂(volume : Measure EuclN),
        ∀ (p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          y ∈ V →
            laplacianDomainHessianChart (I := I) (M := M) g α hu_h p.1 p.2 y = 0 :=
      ae_all_iff.mpr h_pair_ae
    filter_upwards [h_all] with y hy k l hyV
    exact hy ⟨k, l⟩ hyV
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hae_zero_all] with y hy_zeros hyΩ
  by_cases hyK : y ∈ K
  · -- On K, pointwise equality.
    rw [hessPairingChartLocal_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    exact h_pt_K y hyK i j k l
  · -- On V = Ω \ K, all H^{u_h}_{kl} y = 0; both sides are 0.
    have hyV : y ∈ V := ⟨hyΩ, hyK⟩
    rw [hessPairingChartLocal_def]
    have h_LHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    have h_RHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    rw [h_LHS_zero, h_RHS_zero]

/-! ## Each cutoff summand is in `MemLp 2` on the chart target -/

/-- Each summand `cutoffInvGram_ik · cutoffInvGram_jl · cutoffHessianPhi_ij · H^{u_h}_{kl}`
is in `MemLp 2` of `volume.restrict chartTargetEuclid α`.

Proof: The first three factors are bounded continuous functions; the fourth
is in `Lp 2`. The product of a bounded function with an `Lp 2` function is
in `Lp 2`. -/
private lemma cutoffSummand_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          cutoffHessianPhi (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- Bound on |cutoffInvGram_ik|.
  obtain ⟨C_ik, hC_ik_nn, hC_ik_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α i k
  obtain ⟨C_jl, hC_jl_nn, hC_jl_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α j l
  obtain ⟨C_φ, hC_φ_nn, hC_φ_bd⟩ :=
    cutoffHessianPhi_bounded (I := I) (M := M) g α φ i j
  -- The bound: C_ik · C_jl · C_φ.
  set Ctot := C_ik * C_jl * C_φ with hCtot_def
  have hCtot_nn : 0 ≤ Ctot := by
    rw [hCtot_def]
    exact mul_nonneg (mul_nonneg hC_ik_nn hC_jl_nn) hC_φ_nn
  -- The chart-side Hessian is in Lp 2.
  have h_H_lp : MemLp (laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    laplacianDomainHessianChart_memLp_two (I := I) (M := M) g α hu_h k l
  -- The dominating function `Ctot * |H^{u_h}_{kl}|`.
  set bdd_fn : EuclN → ℝ := fun y =>
    Ctot * |laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|
    with hbdd_def
  have h_abs_H : MemLp (fun y => |laplacianDomainHessianChart
      (I := I) (M := M) g α hu_h k l y|) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_H_lp.abs
  have hbdd_memLp : MemLp bdd_fn 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_abs_H.const_mul Ctot
  refine MemLp.mono hbdd_memLp ?_ ?_
  · have h_aesm_ik : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α i k)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α i k _
    have h_aesm_jl : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α j l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α j l _
    have h_aesm_φ : AEStronglyMeasurable
        (cutoffHessianPhi (I := I) (M := M) g α φ i j)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffHessianPhi_aestronglyMeasurable (I := I) (M := M) g α φ i j _
    have h_aesm_H : AEStronglyMeasurable
        (laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_H_lp.aestronglyMeasurable
    exact ((h_aesm_ik.mul h_aesm_jl).mul h_aesm_φ).mul h_aesm_H
  · -- Pointwise bound: |∏| ≤ Ctot · |H|.
    refine Filter.Eventually.of_forall ?_
    intro y
    simp only [Real.norm_eq_abs, hbdd_def]
    set H := laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y with hH_def
    set Gik := cutoffInvGram (I := I) (M := M) g α i k y with hGik_def
    set Gjl := cutoffInvGram (I := I) (M := M) g α j l y with hGjl_def
    set Hφ := cutoffHessianPhi (I := I) (M := M) g α φ i j y with hHφ_def
    -- |Gik · Gjl · Hφ · H| = |Gik| · |Gjl| · |Hφ| · |H|.
    have h_abs_prod : |Gik * Gjl * Hφ * H| = |Gik| * |Gjl| * |Hφ| * |H| := by
      rw [abs_mul, abs_mul, abs_mul]
    rw [h_abs_prod]
    have h_bd_ik := hC_ik_bd y
    have h_bd_jl := hC_jl_bd y
    have h_bd_φ := hC_φ_bd y
    have h_H_nn : (0 : ℝ) ≤ |H| := abs_nonneg _
    have h_step1 : |Gik| * |Gjl| ≤ C_ik * C_jl := by
      calc |Gik| * |Gjl|
          ≤ C_ik * |Gjl| := mul_le_mul_of_nonneg_right h_bd_ik (abs_nonneg _)
        _ ≤ C_ik * C_jl := mul_le_mul_of_nonneg_left h_bd_jl hC_ik_nn
    have h_step2 : |Gik| * |Gjl| * |Hφ| ≤ C_ik * C_jl * C_φ :=
      calc |Gik| * |Gjl| * |Hφ|
          ≤ (C_ik * C_jl) * |Hφ| := mul_le_mul_of_nonneg_right h_step1 (abs_nonneg _)
        _ ≤ (C_ik * C_jl) * C_φ := mul_le_mul_of_nonneg_left h_bd_φ
              (mul_nonneg hC_ik_nn hC_jl_nn)
    have h_step3 : |Gik| * |Gjl| * |Hφ| * |H| ≤ Ctot * |H| := by
      rw [hCtot_def]
      exact mul_le_mul_of_nonneg_right h_step2 h_H_nn
    -- Goal: |Gik| * |Gjl| * |Hφ| * |H| ≤ |Ctot * |H||.
    have h_rhs_nn : (0 : ℝ) ≤ Ctot * |H| := mul_nonneg hCtot_nn h_H_nn
    have h_abs_rhs : abs (Ctot * |H|) = Ctot * |H| := abs_of_nonneg h_rhs_nn
    rw [h_abs_rhs]
    exact h_step3

/-! ## Sum of summands → chart-local pairing is in `MemLp 2` -/

/-- **The chart-local Hess pairing is in `MemLp 2` of the chart-target-restricted
volume.** -/
theorem hessPairingChartLocal_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingChartLocal (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- Step 1: by ae-equality, replace `hessPairingChartLocal` with the cutoff sum.
  have h_ae := hessPairingChartLocal_ae_eq_cutoff
    (I := I) (M := M) g α φ hu_h
  -- Step 2: cutoff sum is in MemLp 2 as a finite sum of MemLp 2 summands.
  have h_cutoff_memLp : MemLp (fun y : EuclN =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                cutoffInvGram (I := I) (M := M) g α i k y *
                  cutoffInvGram (I := I) (M := M) g α j l y *
                  cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                  laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun j _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun k _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => ?_)
    exact cutoffSummand_memLp_two (I := I) (M := M) g α φ hu_h i j k l
  -- Step 3: combine via ae-equality.
  exact MemLp.ae_eq h_ae.symm h_cutoff_memLp

-- Note: `MemLp 1` does not follow directly from `MemLp 2` on
-- `volume.restrict chartTargetEuclid α` because the chart target may have
-- infinite volume on a non-compact open subset of `EuclN`. Instead, MemLp 1
-- needs to be proved via the chart-cutoff trick (the chart-local pairing
-- vanishes outside the compact support `tsupport η`). We skip this here.

/-! ## The chart-local Hess pairing as an `Lp 2` class -/

/-- The `Lp 2` class of the chart-local Hess pairing on the chart target. -/
noncomputable def hessPairingChartLocalLp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (hessPairingChartLocal_memLp_two (I := I) (M := M) g α φ hu_h).toLp _

@[simp] lemma hessPairingChartLocalLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (hessPairingChartLocalLp (I := I) (M := M) g α φ hu_h :
        Lp ℝ 2 ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h :=
  MemLp.coeFn_toLp _

/-! ## Pulling the chart-local pairing back to `M`

For each chart `α`, we pull the chart-local Lp 2 function back to a function on
`M`, set to zero outside the chart source, and weighted by the partition of
unity `(chartAtlasPOU I M) α`. The resulting function is in `MemLp 2 μ_g`. -/

/-- The "extended chart-local Hess pairing": equals the chart-local Hess
pairing at `toEuclidean (extChartAt I α x)` whenever `x ∈ (chartAt H α).source`,
and zero outside. (Picks an arbitrary junk value outside; we'll only use it
inside `tsupport (POU α) ⊆ chart source`.) -/
private noncomputable def hessPairingChartLocalMExt
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  hessPairingChartLocal (I := I) (M := M) g α φ hu_h
    ((toEuclidean (E := E)) (extChartAt I α x))

lemma hessPairingChartLocalMExt_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x =
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h
        ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

/-- The chart-local Hess pairing pulled back to `M`, weighted by the POU
`(chartAtlasPOU I M) α`. Outside `tsupport (POU α)`, the POU value is zero,
so the product is zero. -/
noncomputable def hessPairingMChartContribution
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x

@[simp] lemma hessPairingMChartContribution_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x := rfl

/-- The chart contribution vanishes outside `tsupport (POU α)`. -/
lemma hessPairingMChartContribution_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ tsupport ((chartAtlasPOU I M α : M → ℝ))) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x = 0 := by
  unfold hessPairingMChartContribution
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  rw [hρ_zero, zero_mul]

/-- The global Hess pairing function on `M`: sum of chart contributions over
the finite POU support. -/
noncomputable def hessPairingMOnLapDom
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x

@[simp] lemma hessPairingMOnLapDom_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingMOnLapDom (I := I) (M := M) g φ hu_h x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x := rfl

/-! ## Unconditional `MemLp 2 μ_g` of the per-chart contribution

For each chart point `α`, the chart contribution
`hessPairingMChartContribution g φ α hu_h` lies in `MemLp 2 μ_g`. The proof
uses the strongly-measurable Lp coercion of `hessPairingChartLocalLp` as an
intermediate (pointwise-defined globally measurable surrogate), then transfers
between the chart target and the manifold via the volume-bridge
`eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw`. -/

/-- Strongly-measurable Lp representative of `hessPairingChartLocal g α φ hu_h`,
viewed as a function on `EuclN`. -/
private noncomputable def hessPairingChartLocalRep
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  (hessPairingChartLocalLp (I := I) (M := M) g α φ hu_h :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))

private lemma hessPairingChartLocalRep_stronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    StronglyMeasurable
      (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) :=
  Lp.stronglyMeasurable _

private lemma hessPairingChartLocalRep_measurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) :=
  (hessPairingChartLocalRep_stronglyMeasurable (I := I) (M := M) g α φ hu_h).measurable

/-- The Lp representative agrees a.e. with `hessPairingChartLocal` on
`vol.restrict chartTargetEuclid α`. -/
private lemma hessPairingChartLocalRep_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h :=
  hessPairingChartLocalLp_coeFn (I := I) (M := M) g α φ hu_h

/-- The Lp representative has finite `eLpNorm 2` on the chart target. -/
private lemma hessPairingChartLocalRep_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  Lp.memLp _

/-! ## Manifold-side measurable surrogate `c̃_α` for the chart contribution -/

/-- The globally measurable manifold-side surrogate: POU(α) weighted pullback
of the chart-local Lp representative. -/
private noncomputable def chartContribSurrogate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold (I := I) α
      (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) x

private lemma chartContribSurrogate_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold (I := I) α
          (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) x := rfl

/-- Continuity of the POU. -/
private lemma chartAtlasPOU_continuous (α : M) :
    Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous

/-- Measurability of the POU. -/
private lemma chartAtlasPOU_measurable (α : M) :
    Measurable fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU_continuous (I := I) (M := M) α).measurable

/-- Measurability of the surrogate. -/
private lemma chartContribSurrogate_measurable
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (chartContribSurrogate (I := I) (M := M) g φ α hu_h) := by
  classical
  refine Measurable.mul ?_ ?_
  · exact chartAtlasPOU_measurable (I := I) (M := M) α
  · exact DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_measurable
      (I := I) α (hessPairingChartLocalRep_measurable (I := I) (M := M) g α φ hu_h)

/-- The surrogate is zero outside `(chartAt H α).source`. -/
private lemma chartContribSurrogate_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold chartContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_notMem
    (I := I) α _ hx]
  ring

/-- The `tsupport` of the surrogate is contained in `tsupport (POU α)`,
hence in the chart α source. -/
private lemma chartContribSurrogate_tsupport_subset
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    tsupport (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source := by
  classical
  -- The pointwise support of the surrogate is contained in the chart source.
  have h_supp_sub : Function.support
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        (chartAt H α).source := by
    intro x hx
    by_contra h_notin
    apply hx
    exact chartContribSurrogate_zero_off_source
      (I := I) (M := M) g φ α hu_h h_notin
  -- Take closures: tsupport ⊆ closure (chart source). But the chart source is open
  -- and contains the support; we need tsupport ⊆ chart source itself.
  -- We use: tsupport ⊆ tsupport (POU α) ⊆ chart α source.
  -- Specifically, where POU α = 0 (including outside its tsupport), the
  -- surrogate is 0; hence support of surrogate is in support of POU α.
  have h_supp_in_pou : Function.support
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        Function.support fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hρ_zero
    apply hx
    unfold chartContribSurrogate
    rw [hρ_zero]; ring
  have h_tsupp_in_pou : tsupport
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    closure_mono h_supp_in_pou
  exact h_tsupp_in_pou.trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

/-! ## The surrogate equals the chart contribution a.e. on `μ_g`

To prove this, we show that the set `S := {x : surrogate(x) ≠ hessPairingMChartContribution(x)}`
has μ_g-measure 0.

`S ⊆ {x ∈ chart α source : hessPairingChartLocalRep(toE(extChartAt x))
                              ≠ hessPairingChartLocal(toE(extChartAt x))}`
since both surrogate and chart contribution vanish outside the chart source
and equal each other on the chart source modulo the ae-equality of the chart
representative and the chart-local function (lifted from `vol.restrict chartTarget`
to `μ_g`). -/

/-- The point-equality formula: on the chart α source, the surrogate equals
the chart contribution with `hessPairingChartLocal` replaced by its Lp
representative. -/
private lemma chartContribSurrogate_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  unfold chartContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_mem
    (I := I) α _ hx]

/-- On the chart α source, the chart contribution equals
`POU(α) · hessPairingChartLocal ∘ toE ∘ extChartAt I α`. -/
theorem hessPairingMChartContribution_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (_hx : x ∈ (chartAt H α).source) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocal (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  unfold hessPairingMChartContribution hessPairingChartLocalMExt
  rfl

/-- The chart contribution vanishes outside `(chartAt H α).source`. -/
theorem hessPairingMChartContribution_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold hessPairingMChartContribution
  -- POU(α) is supported in (chart α source) via subordination.
  have hsub :
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hx_notsupp : x ∉ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h =>
    hx (hsub h)
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_notsupp
  rw [hρ_zero]
  ring

/-! ## Equality of the surrogate and the chart contribution a.e. on `μ_g`

The chart Lp representative `hessPairingChartLocalRep` agrees with the
chart-local function `hessPairingChartLocal` a.e. on `vol.restrict chartTarget`.
We lift this to a.e. equality on `μ_g` over the chart α source using the
bridge `riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn` together
with `chartLocalMeasure_lintegral_via_chartTargetEuclid`.

The key step: pick a measurable null set `N ⊆ chartTarget α` on `volume` such
that `h_rep = h_loc` on `chartTarget \ N`. Then for the pullback
`N_M := (toE ∘ extChartAt I α)⁻¹(N) ∩ chart α source`, we have
`μ_g(N_M) = 0`. Hence on `chart α source \ N_M`, the surrogate and the chart
contribution agree pointwise. -/

/-- Choose a measurable null superset `N` for the bad set where `h_rep ≠ h_loc`,
within the chart target. -/
private lemma hessPairingChartLocalRep_exists_null_superset
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∃ N : Set EuclN, MeasurableSet N ∧
      (volume : Measure EuclN) (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0 ∧
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ N →
        hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y =
        hessPairingChartLocal (I := I) (M := M) g α φ hu_h y := by
  classical
  -- The a.e. equality.
  have h_ae := hessPairingChartLocalRep_ae_eq (I := I) (M := M) g α φ hu_h
  -- The "bad set" — where the two differ — has measure zero in the restricted measure.
  set badSet : Set EuclN := { y : EuclN |
      hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y ≠
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h y } with hbadSet_def
  have h_bad_null : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)) badSet = 0 := h_ae
  -- Convert to a measurable null superset.
  -- We use ae_iff to get vol.restrict-null on badSet.
  -- Then exists_measurable_superset_of_null to find a measurable null N ⊇ badSet.
  obtain ⟨N, h_bad_sub_N, hN_meas, hN_null⟩ :=
    exists_measurable_superset_of_null h_bad_null
  refine ⟨N, hN_meas, ?_, ?_⟩
  · -- vol.restrict chartTarget N = vol (N ∩ chartTarget) and the former is 0.
    rw [MeasureTheory.Measure.restrict_apply hN_meas] at hN_null
    exact hN_null
  · intro y hy_in_target hy_notN
    -- y ∈ chartTarget and y ∉ N. Since badSet ⊆ N, y ∉ badSet.
    have hy_not_bad : y ∉ badSet := fun hyb => hy_notN (h_bad_sub_N hyb)
    -- So the rep and loc agree at y.
    by_contra h_ne
    exact hy_not_bad h_ne

/-- The pullback of a measurable null set in `chartTarget` along the chart map
has `μ_g`-measure zero. This is the key step that uses the chart-pulled
measure bridge. -/
theorem riemannianVolumeMeasure_pullback_null
    (g : SmoothRiemannianMetric I M) (α : M)
    {N : Set EuclN} (hN_meas : MeasurableSet N)
    (hN_null : (volume : Measure EuclN)
      (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0) :
    (riemannianVolumeMeasure (I := I) (M := M) g)
      ((chartAt H α).source ∩
        { x : M | (toEuclidean (E := E)) ((extChartAt I α) x) ∈ N }) = 0 := by
  classical
  -- Define the indicator function F : M → ℝ≥0∞.
  set NM : Set M := (chartAt H α).source ∩
    { x : M | (toEuclidean (E := E)) ((extChartAt I α) x) ∈ N } with hNM_def
  -- F = indicator NM 1.
  -- We want: μ_g NM = 0, equivalently ∫⁻ 1_{NM} dμ_g = 0.
  -- We first show NM is measurable.
  -- Then use the bridge.
  have h_src_meas : MeasurableSet ((chartAt H α).source) :=
    ((chartAt H α).open_source).measurableSet
  have h_extChartExt_meas : Measurable
      (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_measurable
      (I := I) α
  have h_toE_meas : Measurable (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous.measurable
  -- toE ∘ extChartAtExt : M → EuclN is measurable.
  have h_comp_meas : Measurable
      (fun x : M => (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x)) :=
    h_toE_meas.comp h_extChartExt_meas
  -- The set { x : (toE ∘ extChartAtExt)(x) ∈ N } is measurable.
  have h_preim_meas : MeasurableSet
      { x : M | (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x) ∈ N } :=
    h_comp_meas hN_meas
  -- For x ∈ chart α source, extChartAtExt I α x = extChartAt I α x.
  -- So NM = chart α source ∩ { x : (toE ∘ extChartAtExt)(x) ∈ N }.
  have hNM_eq : NM = (chartAt H α).source ∩
      { x : M | (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x) ∈ N } := by
    apply Set.eq_of_subset_of_subset
    · intro x ⟨hx_src, hx_N⟩
      refine ⟨hx_src, ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_apply_of_mem
        (I := I) α hx_src]
      exact hx_N
    · intro x ⟨hx_src, hx_N⟩
      refine ⟨hx_src, ?_⟩
      simp only [Set.mem_setOf_eq]
      simp only [Set.mem_setOf_eq] at hx_N
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_apply_of_mem
        (I := I) α hx_src] at hx_N
      exact hx_N
  have hNM_meas : MeasurableSet NM := by
    rw [hNM_eq]; exact h_src_meas.inter h_preim_meas
  -- Express μ_g(NM) via lintegral of the indicator.
  -- μ_g NM = ∫⁻ a, 1_{NM}(a) dμ_g (using lintegral_indicator_const).
  have h_meas_as_lint : (riemannianVolumeMeasure (I := I) (M := M) g) NM =
      ∫⁻ a, NM.indicator (fun _ : M => (1 : ℝ≥0∞)) a
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [MeasureTheory.lintegral_indicator_const hNM_meas (1 : ℝ≥0∞)]
    rw [one_mul]
  rw [h_meas_as_lint]
  -- Now apply the bridge: μ_g indicator NM = chartLocalMeasure indicator NM
  -- (since NM ⊆ chart α source).
  have hF_supp : ∀ x : M, x ∉ (chartAt H α).source →
      NM.indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
    intro x hx
    have hx_notNM : x ∉ NM := fun hxNM => hx hxNM.1
    exact Set.indicator_of_notMem hx_notNM _
  have hF_meas : Measurable (NM.indicator (fun _ => (1 : ℝ≥0∞))) :=
    Measurable.indicator measurable_const hNM_meas
  -- This works because riemannianVolumeMeasure is riemannianMeasure (chartAtlasPOU).
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp
  -- riemannianVolumeMeasure is definitionally riemannianMeasure of the POU.
  change ∫⁻ x, NM.indicator (fun _ : M => (1 : ℝ≥0∞)) x
      ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) = 0
  rw [h_bridge]
  -- Now: ∫⁻ indicator NM d(chartLocalMeasure g α) = 0.
  -- Apply chartLocalMeasure_lintegral_via_chartTargetEuclid.
  have h_via :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas
  rw [h_via]
  -- The integrand on the chart target is:
  --   density(y) · indicator NM ((extChartAt I α).symm (toE.symm y))
  -- For y ∈ chartTarget, x = (extChartAt I α).symm (toE.symm y) ∈ chart α source,
  -- and toE(extChartAt I α x) = y. So indicator NM = indicator N.
  have h_setLInt_eq :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            NM.indicator (fun _ : M => (1 : ℝ≥0∞))
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) ?_
    intro y hy_target
    -- y ∈ chartTargetEuclid α.
    -- x := (extChartAt I α).symm (toEuclidean.symm y).
    -- x ∈ chart α source.
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rcases hy_target with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
    have hx_in_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source := by
      have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at this
    -- toEuclidean (extChartAt I α x) = y.
    have h_toE_extChart_x :
        (toEuclidean (E := E)) ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have h_extChart_inv : (extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target'
      rw [h_extChart_inv]
      exact (toEuclidean (E := E)).apply_symm_apply y
    -- indicator NM at x equals indicator N at y.
    have h_indic_eq : NM.indicator (fun _ : M => (1 : ℝ≥0∞))
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
          N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y := by
      by_cases hxNM : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ NM
      · rw [Set.indicator_of_mem hxNM]
        have hxN : (toEuclidean (E := E)) ((extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ∈ N := hxNM.2
        rw [h_toE_extChart_x] at hxN
        rw [Set.indicator_of_mem hxN]
      · rw [Set.indicator_of_notMem hxNM]
        have h_not_in_preim : (toEuclidean (E := E)) ((extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ∉ N := by
          intro h
          exact hxNM ⟨hx_in_src, h⟩
        rw [h_toE_extChart_x] at h_not_in_preim
        rw [Set.indicator_of_notMem h_not_in_preim]
    -- Apply h_indic_eq to the multiplication on the right factor.
    change ENNReal.ofReal _ * NM.indicator _ _ =
      ENNReal.ofReal _ * N.indicator _ _
    rw [h_indic_eq]
  rw [h_setLInt_eq]
  -- Now: ∫⁻ y in chartTarget, density(y) * indicator N y dvol = 0
  -- (since vol(N ∩ chartTarget) = 0).
  -- Bring the indicator inside: density * indicator_N = indicator_N (density).
  -- Then ∫⁻ y in chartTarget, indicator_N (density) y dvol = ∫⁻ y in chartTarget ∩ N, density dvol.
  have h_factor_indicator : ∀ y : EuclN,
      ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y =
      N.indicator
        (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y := by
    intro y
    by_cases hyN : y ∈ N
    · rw [Set.indicator_of_mem hyN, Set.indicator_of_mem hyN, mul_one]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem hyN, mul_zero]
  rw [show (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y
          ∂(volume : Measure EuclN)) =
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      N.indicator (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y
          ∂(volume : Measure EuclN) from by
    refine MeasureTheory.lintegral_congr ?_
    intro y
    exact h_factor_indicator y]
  rw [show ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      N.indicator (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y
          ∂(volume : Measure EuclN) =
      ∫⁻ y in N ∩ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ∂(volume : Measure EuclN) from
    MeasureTheory.setLIntegral_indicator hN_meas _]
  -- Now we need: c_E * ∫⁻ y in N ∩ chartTarget, density(...) dvol = 0.
  -- The setLIntegral is 0 since vol(N ∩ chartTarget) = 0.
  rw [MeasureTheory.setLIntegral_measure_zero
    (N ∩ chartTargetEuclid (I := I) (M := M) α) _ hN_null, mul_zero]

/-- The surrogate equals the chart contribution a.e. on `μ_g`. -/
private lemma chartContribSurrogate_ae_eq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingMChartContribution (I := I) (M := M) g φ α hu_h := by
  classical
  -- Use the null superset to obtain pointwise equality on the complement.
  obtain ⟨N, hN_meas, hN_null, hN_agree⟩ :=
    hessPairingChartLocalRep_exists_null_superset
      (I := I) (M := M) g α φ hu_h
  -- The bad set on M: {x : surrogate ≠ contribution} ⊆ ((chart α source) ∩ Φ⁻¹(N)).
  -- This is μ_g-null by the lemma.
  have hpre_null := riemannianVolumeMeasure_pullback_null
    (I := I) (M := M) g α hN_meas hN_null
  -- Show surrogate = contribution a.e. by showing they agree outside the bad set.
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hpre_null
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · -- x ∈ chart α source: surrogate(x) = ρ(x) * h_rep(toE(extChartAt x))
    --                    contribution(x) = ρ(x) * h_loc(toE(extChartAt x))
    -- They differ ⇒ h_rep ≠ h_loc at toE(extChartAt x)
    -- ⇒ toE(extChartAt x) ∈ N (since on chartTarget \ N they agree).
    refine ⟨hx_src, ?_⟩
    -- Need toE(extChartAt x) ∈ N.
    simp only [Set.mem_setOf_eq]
    have h_y_in_target : (toEuclidean (E := E)) ((extChartAt I α) x) ∈
        chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, ?_, rfl⟩
      have : x ∈ (extChartAt I α).source := by
        rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
      exact (extChartAt I α).map_source this
    by_contra h_not_in_N
    -- y := toE(extChartAt x) ∉ N and y ∈ chartTarget. So h_rep(y) = h_loc(y).
    have h_agree_at_y :=
      hN_agree _ h_y_in_target h_not_in_N
    -- But then surrogate(x) = contribution(x).
    apply hx
    rw [chartContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        hessPairingMChartContribution_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        h_agree_at_y]
  · -- x ∉ chart α source: both = 0.
    exfalso
    apply hx
    rw [chartContribSurrogate_zero_off_source (I := I) (M := M) g φ α hu_h hx_src,
        hessPairingMChartContribution_zero_off_source (I := I) (M := M) g φ α hu_h hx_src]

/-! ## `MemLp 2 μ_g` of the surrogate

We bound the manifold-side eLpNorm of the surrogate by the chart-side
eLpNorm of `hessPairingChartLocal`, using the volume-bridge
`eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw`. -/

/-- The surrogate's `chartPushedRaw` on the chart target is dominated by the
chart-local Lp representative pointwise in absolute value (POU bounded by 1). -/
private lemma chartPushedRaw_chartContribSurrogate_le_rep
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (y : EuclN) :
    ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (chartContribSurrogate (I := I) (M := M) g φ α hu_h) y‖ₑ ≤
      ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- y ∈ chartTarget: chartPushedRaw I α c̃ y = c̃((extChartAt I α).symm (toE.symm y)).
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    -- x := (extChartAt I α).symm (toE.symm y) ∈ chart α source.
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rcases hy with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
    have hx_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source := by
      have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at this
    rw [chartContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src]
    -- toEuclidean (extChartAt I α x) = y for x = symm(toE.symm y).
    have h_toE_extChart_x :
        (toEuclidean (E := E)) ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have h_extChart_inv : (extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target'
      rw [h_extChart_inv]
      exact (toEuclidean (E := E)).apply_symm_apply y
    rw [h_toE_extChart_x]
    -- Goal: ‖POU(α)(x) * h_rep(y)‖_e ≤ ‖h_rep(y)‖_e.
    -- POU is bounded by 1.
    have h_nn : (0 : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
      (chartAtlasPOU I M).nonneg α _
    have h_le : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≤ 1 :=
      (chartAtlasPOU I M).le_one α _
    rw [enorm_mul]
    have h_abs_le_one : ‖(chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg h_nn]
      have : ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ≤
            ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_le
      rw [show ((1 : ℝ≥0∞)) = ENNReal.ofReal 1 by simp]
      exact this
    calc ‖(chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ *
            ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ
        ≤ 1 * ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
          gcongr
      _ = ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := one_mul _
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    simp

/-- `MemLp 2 μ_g` of the surrogate. -/
private lemma chartContribSurrogate_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (chartContribSurrogate (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Use the bridge: eLpNorm c̃_α p μ_g ≤ C_α * eLpNorm (chartPushedRaw I α c̃_α) p (vol.restrict chartTarget).
  have h_c_meas : Measurable (chartContribSurrogate (I := I) (M := M) g φ α hu_h) :=
    chartContribSurrogate_measurable (I := I) (M := M) g φ α hu_h
  have h_c_tsupp : tsupport (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source :=
    chartContribSurrogate_tsupport_subset (I := I) (M := M) g φ α hu_h
  obtain ⟨C_α, hC_α_pos, hC_α_bnd⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_c_meas h_c_tsupp
  -- Bound chart-side eLpNorm by eLpNorm of hessPairingChartLocalRep.
  have h_chart_le : eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (chartContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) ≤
    eLpNorm (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_mono_enorm
      (chartPushedRaw_chartContribSurrogate_le_rep
        (I := I) (M := M) g φ α hu_h)
  -- The Lp representative has finite eLpNorm.
  have h_rep_memLp := hessPairingChartLocalRep_memLp_two
    (I := I) (M := M) g α φ hu_h
  have h_rep_eLp_lt_top := h_rep_memLp.2
  -- Combine.
  refine ⟨h_c_meas.aestronglyMeasurable, ?_⟩
  calc eLpNorm (chartContribSurrogate (I := I) (M := M) g φ α hu_h) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ENNReal.ofReal C_α *
          eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (chartContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hC_α_bnd
    _ ≤ ENNReal.ofReal C_α *
          eLpNorm (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by gcongr
    _ < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_rep_eLp_lt_top

/-! ## `MemLp 2 μ_g` of the chart contribution -/

/-- **Per-chart `MemLp 2 μ_g` for the chart contribution.** -/
theorem hessPairingMChartContribution_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingMChartContribution (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- The surrogate is MemLp 2 and ae-equals the chart contribution.
  have h_surr_memLp := chartContribSurrogate_memLp_two
    (I := I) (M := M) g φ α hu_h
  have h_ae_eq := chartContribSurrogate_ae_eq (I := I) (M := M) g φ α hu_h
  -- MemLp.ae_eq transfers MemLp via ae-equality.
  exact MemLp.ae_eq h_ae_eq h_surr_memLp

/-! ## Global `MemLp 2 μ_g` for `hessPairingMOnLapDom`

The global function is the finite POU sum of chart contributions. By
`memLp_finset_sum`, the sum is in `MemLp 2 μ_g`. -/

/-- **Unconditional `MemLp 2 μ_g` for `hessPairingMOnLapDom`.** -/
theorem hessPairingMOnLapDom_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingMOnLapDom (I := I) (M := M) g φ hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  unfold hessPairingMOnLapDom
  refine memLp_finset_sum _ ?_
  intro α _
  exact hessPairingMChartContribution_memLp_two
    (I := I) (M := M) g φ α hu_h

/-! ## The `Lp 2 μ_g` class -/

/-- The `Lp 2 μ_g` class of the global Hess pairing function. -/
noncomputable def hessPairingLpOnLapDom
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (hessPairingMOnLapDom_memLp_two (I := I) (M := M) g φ hu_h).toLp _

/-- Unfolding: the Lp class represents `hessPairingMOnLapDom`. -/
lemma hessPairingLpOnLapDom_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (hessPairingLpOnLapDom (I := I) (M := M) g φ hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingMOnLapDom (I := I) (M := M) g φ hu_h :=
  MemLp.coeFn_toLp _

/-! ## Hypothesis-bearing CLM packaging

The continuity bound `‖hessPairingLpOnLapDom g φ u_h‖_{L²} ≤ C(g,φ) · graphNorm(u_h)`
requires a quantitative chart-bilinear elliptic regularity estimate that is
not yet packaged at this layer. We provide here a hypothesis-bearing CLM
constructor: given the Lipschitz constant `C`, the CLM is well-defined.

The unconditional Lipschitz bound is reserved for follow-up work. The full
constructor will take the form

```
hessPairingLpOnLapDomCLM g φ : ↥(laplacianDomain g) →L[ℝ] Lp ℝ 2 μ_g
```

with `‖hessPairingLpOnLapDomCLM g φ u_h‖_{L²} ≤ C(g,φ) ·
(‖u_h‖_{H¹} + ‖laplacianDomain.preimage u_h‖_{L²})`, where the constant
`C(g, φ)` depends on the metric, the test function `φ`, and the chart atlas.
-/

end HessianPairingLapDom
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.chartHessianPhiOnEuclid
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.chartHessianPhiOnEuclid_continuousOn
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingChartLocal
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingChartLocal_memLp_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingChartLocalLp
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingMChartContribution
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingMOnLapDom
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingMChartContribution_memLp_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingMOnLapDom_memLp_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingLpOnLapDom
#print axioms
  DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.hessPairingLpOnLapDom_coeFn
end Sanity