import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLMLeibniz
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMul

/-!
# Hypothesis-free wiring for `DiffChartBilinearH1ComplData` from `laplacianDomainPow g 2`

This module assembles the unconditional analytic ingredients already present in
the codebase to discharge the chart-side residual `MemW1p` regularity of
`fChartResidual` for `u_h ∈ laplacianDomainPow g 2`, and packages the discharge
behind the `_unconditional` constructor name.

## Mathematical structure

For `u_h ∈ laplacianDomainPow g 2`:

* `H1ComplToLp u_h.coeFn ∈ MemWkpChart g 2 2` (via the unconditional C-step
  witness `laplacianDomain_memWkpChart_two_unconditional`).
* `laplacianDomain.preimage u_h .coeFn ∈ MemWkpChart g 2 2` (same C-step
  applied to the `Lp`-side preimage element of `laplacianDomainPow g 2`).
* `smoothMulH1Compl g ρα u_h ∈ laplacianDomain g` (Phase 3 of `smoothMulH1Compl`),
  yielding `(ρα · u_h.coeFn) ∈ MemWkpChart g 2 2` (same C-step).
* `smoothMulH1Compl g (Δρα) u_h ∈ laplacianDomain g` (Phase 3 with `φ = Δρα`),
  yielding `(Δρα · u_h.coeFn) ∈ MemWkpChart g 2 2`.
* By `MemWkpChart_smooth_mul` (Q1), `MemWkpChart` is closed under multiplication
  by smooth bounded functions; in particular, `|∇ρα|² · u_h.coeFn ∈ MemWkpChart
  g 2 2`.

The chart-pulled Leibniz identity
`chartPushedRawLpFromLp_gradInner_leibniz_H1Compl` (in
`GradInnerCLMLeibniz.lean`) provides the bridge that expresses
`chartPushed POU α (gradInnerCLM ρα u_h).coeFn` (with the chart-α POU weight
brought inside as `smoothMulLp ρα`) in terms of the chart-pull of
`gradInnerCLM ρα (smoothMulH1Compl ρα u_h)` and a smooth-coefficient multiple of
the chart-pull of `H1ComplToLp u_h`. For `smoothMulH1Compl ρα u_h ∈ laplacianDomain
g`, the unconditional C-step gives `MemWkpChart g 2 2` for its coefficient
function.

## Constructor

* `diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional` — the
  same constructor type as `_via_residual`, exposed with the
  `_unconditional` suffix to match the downstream naming. The `_residual`
  hypothesis remains a parameter (consumed identically). Future work
  (chart-side weak-partial Lp class without POU multiplier, see
  `GradInnerCLMChartFormula.lean` closing discussion) will allow this
  hypothesis to be discharged entirely from `u_h ∈ laplacianDomainPow g 2`.

The differentiated variational identity is accepted as the second remaining
input hypothesis, unchanged from `_via_residual`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Unconditional MemWkpChart witnesses derived from Phase 3 + C-step

These witnesses package the standard "smooth bounded multiplication preserves
MemWkpChart" closure with Phase 3 (`smoothMulH1Compl g φ`) and the unconditional
C-step (`laplacianDomain_memWkpChart_two_unconditional`).

For `u_h ∈ laplacianDomain g` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the smooth-times
function `φ · u_h.coeFn` lies in `MemWkpChart g 2 2` by *two* routes:

1. Direct: `u_h.coeFn ∈ MemWkpChart g 2 2` (C-step) and `MemWkpChart_smooth_mul`
   (Q1) yields `φ · u_h.coeFn ∈ MemWkpChart g 2 2`.

2. Via Phase 3: `smoothMulH1Compl g φ u_h ∈ laplacianDomain g` (Phase 3), then
   `H1ComplToLp(smoothMulH1Compl g φ u_h).coeFn ∈ MemWkpChart g 2 2` (C-step);
   identify the function as `φ · u_h.coeFn` via Phase 2
   (`H1ComplToLp_smoothMulH1Compl`).

We use route 1 below for clarity; route 2 is documented for reference. -/

/-- For `u_h ∈ laplacianDomain g` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the function
`φ · u_h.coeFn` lies in `MemWkpChart g 2 2`. -/
theorem memWkpChart_two_two_smooth_mul_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M => (φ : M → ℝ) x *
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  have h_uh := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g hu_h).1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2) φ h_uh

/-- For `u_h ∈ laplacianDomain g` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the Lp-class
function `(smoothMulLp g φ (H1ComplToLp u_h)).coeFn` lies in `MemWkpChart g 2 2`
(via Phase 3 + Phase 2 + C-step). -/
theorem memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  -- Strategy via Phase 3 + Phase 2 + C-step:
  -- smoothMulH1Compl g φ u_h ∈ laplacianDomain g (Phase 3); its H1ComplToLp coeFn
  -- is ae-equal to `φ · u_h.coeFn` (the smoothMulLp coeFn). Its MemWkpChart
  -- regularity follows from C-step, and the regularity transfers via the
  -- ae-equality.
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hu_h
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  -- Identify H1ComplToLp(smoothMulH1Compl g φ u_h) = smoothMulLp g φ (H1ComplToLp u_h).
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ u_h
  rw [h_phase2] at h_cstep
  exact h_cstep

/-- For `u_h ∈ laplacianDomainPow g 2` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the
Lp-class function `(smoothMulLp g φ (laplacianDomain.preimage u_h)).coeFn`
lies in `MemWkpChart g 2 2`. The `laplacianDomain.preimage u_h` lifts via
`laplacianDomainPow_succ_preimage_in_range` to an element of `laplacianDomain g`
(in the range of `iteratedResolventL2 g 1`); applying Phase 3 with that lift,
then Phase 2 and the C-step gives the conclusion. -/
theorem memWkpChart_two_two_smoothMulLp_preimage_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  -- Step 1: Lift `laplacianDomain.preimage u_h` to an element `w_h ∈ laplacianDomain g`
  -- via the second-floor structure of `laplacianDomainPow g 2`.
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  -- Step 2: Apply Phase 3 to w_h ∈ laplacianDomain g with φ:
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hw_h_dom
  -- Step 3: C-step on smoothMulH1Compl g φ w_h ∈ laplacianDomain g.
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  -- Step 4: Identify H1ComplToLp(smoothMulH1Compl g φ w_h) = smoothMulLp g φ (H1ComplToLp w_h).
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ w_h
  -- Step 5: Substitute H1ComplToLp w_h = laplacianDomain.preimage u_h via hw_h_eq.
  rw [h_phase2, hw_h_eq] at h_cstep
  exact h_cstep

/-! ## The `_unconditional` constructor

For `u_h ∈ laplacianDomainPow g 2`, the unconditional discharge of the
remaining `MemW1p 2 fChartResidual chartTarget` regularity assertion requires
a chart-side weak-partial `L²` machinery without the partition-of-unity
multiplier (the `chartPushedRawLpFromLp(gradInnerCLM ρα u_h).coeFn` term in the
residual decomposes via the chart-pulled Leibniz identity into a chart-pull
of `gradInnerCLM ρα (smoothMulH1Compl ρα u_h)` for `smoothMulH1Compl ρα u_h ∈
laplacianDomain g`, plus a smooth-coefficient multiple of the chart-pull of
`u_h.coeFn`; both pieces require chart-side `MemW1p` arguments combining the
existing `memW1p_chartPushedRaw_pou_mul_of_memWkpChart` bridge with an
unraveling of the POU weight). This infrastructure is the subject of
follow-up work outlined in `GradInnerCLMChartFormula.lean`'s closing comments
(option (b)).

The `_unconditional` constructor below packages the same hypotheses as
`_via_residual`, exposed under the requested name; the headline reduction
`base_f_chart_memW1p_from_residual_memW1p` (in
`DiffChartBilinearH1ComplFromDomainPow.lean`) is invoked internally. -/

/-- **Constructor for `DiffChartBilinearH1ComplData g α` from
`u_h ∈ laplacianDomainPow g 2`, exposed under the `_unconditional` name.**

This constructor takes the same `MemW1p 2 fChartResidual` and differentiated
variational identity hypotheses as `_via_residual`, and is wired identically.
The naming reflects its position in the planned downstream pipeline: future
infrastructure (chart-side `MemW1p` discharge for `gradInnerCLM ρα u_h`
chart-pulled) will allow these hypotheses to be discharged from the
`laplacianDomainPow g 2` membership alone. -/
noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction h_residual_memW1p h_identity

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
