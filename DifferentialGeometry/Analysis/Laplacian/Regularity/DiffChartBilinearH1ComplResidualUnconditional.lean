import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplResidualMemW1p
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerLpIdentity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevBanach

/-!
# Unconditional discharge of `MemW1p 2 fChartResidual` for the smooth case

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and a
smooth scalar `v : SmoothScalar g`, the chart-pulled residual function
`fChartResidual g α (smoothToH1Compl g v)` lies in `MemW1p 2
chartTargetEuclid α` unconditionally. The smooth-case discharge is
provided by `memW1p_fChartResidual_smoothToH1Compl` from
`DiffChartBilinearH1ComplResidualMemW1p`.

This module packages the smooth-case discharge into the
`DiffChartBilinearH1ComplData` constructor by dropping the
`h_residual_memW1p` hypothesis from the `_via_residual` constructor and
substituting it with the smooth-case discharge automatically. The
membership `smoothToH1Compl v ∈ laplacianDomainPow g 2` is automatic via
`smoothToH1Compl_mem_laplacianDomainPow_two`.

## Constructor

* `diffChartBilinearH1ComplData_of_smoothToH1Compl_unconditional` —
  the smooth-case unconditional constructor. Takes a smooth scalar
  `v : SmoothScalar g`, a direction, and the differentiated variational
  identity (the only remaining hypothesis, identical in shape to the
  general `_via_residual` constructor). The `MemW1p 2 fChartResidual`
  hypothesis is discharged internally via
  `memW1p_fChartResidual_smoothToH1Compl`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidualUnconditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Smooth-case unconditional constructor

For `u_h := smoothToH1Compl g v` with smooth `v : SmoothScalar g`, the
`MemW1p 2 fChartResidual chartTargetEuclid α` hypothesis is discharged
unconditionally via `memW1p_fChartResidual_smoothToH1Compl`. The
constructor below packages this discharge with the differentiated
variational identity hypothesis (the only remaining input), removing the
need for any residual `MemW1p` hypothesis.

The membership `smoothToH1Compl v ∈ laplacianDomainPow g 2` is automatic
via `smoothToH1Compl_mem_laplacianDomainPow_two`, so the constructor
takes only the smooth scalar (not the membership proof). -/

/-- **Smooth-case unconditional constructor for `DiffChartBilinearH1ComplData
g α`**.

For `v : SmoothScalar g`, this constructor produces a
`DiffChartBilinearH1ComplData g α` instance with `u_h := smoothToH1Compl
g v` from the differentiated variational identity alone. The residual
`MemW1p 2 fChartResidual chartTarget α` is discharged internally via
`memW1p_fChartResidual_smoothToH1Compl`. -/
noncomputable def diffChartBilinearH1ComplData_of_smoothToH1Compl_unconditional
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (direction : Fin (Module.finrank ℝ E))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)
                  i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α
              (smoothToH1Compl_mem_laplacianDomainPow_two
                (I := I) (M := M) g v) direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1
                    (smoothToH1Compl_mem_laplacianDomainPow_two
                      (I := I) (M := M) g v))).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    direction
    (memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α v)
    h_identity

/-! ## W^{1,2}-chart-target Cauchy density discharge of `MemW1p 2 fChartResidual`

For arbitrary `u_h ∈ laplacianDomainPow g 2`, the discharge of
`MemW1p 2 fChartResidual chartTargetEuclid α` reduces to a W^{1,2}
chart-target Cauchy hypothesis on the smooth-approximator residuals.
The chain:

1. Take smooth `v_n : SmoothScalar g` with `smoothToH1Compl v_n → u_h` in
   `H1Compl`. (Exists by `exists_smoothApprox_seq`.)
2. For each `n`, `memW1p_fChartResidual_smoothToH1Compl` gives the smooth-
   case discharge `fChartResidual(smoothToH1Compl v_n) ∈ MemW1p 2
   chartTargetEuclid α`.
3. If the sequence `fChartResidual(smoothToH1Compl v_n)` is Cauchy in
   the chart-target `wkpNorm 1 2`, then by `MemWkp.exists_limit_of_wkpNorm_cauchy`
   the limit `F_lim` is in `MemW1p 2 chartTargetEuclid α`.
4. By `chartPushedRawLpFromLp_tendsto`, `fChartResidual(smoothToH1Compl
   v_n) → fChartResidual(u_h)` in `Lp 2 (chartPulledWeightedMeasure
   .restrict chartTargetEuclid α)`. The weighted measure is absolutely
   continuous w.r.t. the chart-target volume measure (density > 0), and
   conversely the chart-target volume measure has bounded density
   (since the chart-target is contained in the image of a compact set
   under the chart map, hence the volume is bounded). Thus
   eLpNorm-convergence transfers between the two measures on
   chartTargetEuclid α.
5. Identification: `F_lim =ᵐ fChartResidual(u_h)` on `volume.restrict
   chartTargetEuclid α`. Hence by `MemW1p_congr_ae`, `MemW1p 2
   fChartResidual(u_h) chartTargetEuclid α`.

The Cauchy hypothesis in step 3 captures the "elliptic regularity"
content: it asserts that the W^{1,2}-chart-norm of the residual is
controlled along the approximation sequence. In classical analysis this
follows from spectral / Galerkin density of smooth functions in the
H²-graph-norm domain. -/

/-- For `v : SmoothScalar g`, the smooth-case chart-pulled residual
function in `MemW1p 2 chartTargetEuclid α` form. -/
private noncomputable def smoothFChartResidual
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
    (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)

private lemma smoothFChartResidual_memW1p
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (smoothFChartResidual (I := I) (M := M) g α v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothFChartResidual
  exact memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α v

/-- For `u_h ∈ laplacianDomainPow g 2` and a sequence of smooth scalars
`v : ℕ → SmoothScalar g` with `smoothToH1Compl v_n → u_h` in `H1Compl`, the
sequence of chart-pulled residuals `smoothFChartResidual g α (v n)`
converges to `fChartResidual g α u_h` in `Lp 2 (chartPulledWeightedMeasure
g α .restrict chartTargetEuclid α)`. -/
private lemma smoothFChartResidual_tendsto_fChartResidual_lp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
      eLpNorm
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
            (I := I) (M := M) g α u_h y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
  classical
  -- Step 1: fHLeibnizResidualLp(smoothToH1Compl v_n) → fHLeibnizResidualLp(u_h) in Lp.
  -- fHLeibnizResidualLp involves gradInnerCLM ρα (·) and smoothMulLp Δρα (H1ComplToLp ·);
  -- both are continuous in H1Compl.
  -- The unfolding:
  --   fHLeibnizResidualLp g α x = -((2:ℝ) • gradInnerCLM g ρα x) - smoothMulLp g Δρα (H1ComplToLp g x).
  have h_residual_tendsto : Tendsto (fun n =>
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n)))
      atTop (𝓝 (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α u_h)) := by
    -- Define LinearMap_residual : H1Compl g →L[ℝ] Lp ℝ 2 μ_g as
    --   x ↦ -((2:ℝ) • gradInnerCLM g ρα x) - smoothMulLp g Δρα (H1ComplToLp g x).
    -- It's continuous (CLM composition). Apply tendsto.
    set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
    set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
    -- Two pieces: A := -((2:ℝ) • gradInnerCLM g ρα x), B := smoothMulLp g Δρα (H1ComplToLp g x).
    have h_A : Tendsto (fun n => -((2 : ℝ) •
        gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα u_h))) := by
      have h_grad : Tendsto (fun n =>
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        ((gradInnerCLM (I := I) (M := M) g ρα).continuous.tendsto _).comp
          h_tendsto
      have h_smul : Tendsto (fun n => (2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 ((2 : ℝ) •
            gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        Tendsto.const_smul h_grad (2 : ℝ)
      exact h_smul.neg
    have h_B : Tendsto (fun n =>
        smoothMulLp (I := I) (M := M) g Δρα
          (H1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (smoothMulLp (I := I) (M := M) g Δρα
          (H1ComplToLp (I := I) (M := M) g u_h))) := by
      have h_H1Lp : Tendsto (fun n =>
          H1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
        ((H1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
      exact ((smoothMulLp (I := I) (M := M) g Δρα).continuous.tendsto _).comp h_H1Lp
    have h_sub : Tendsto (fun n =>
        -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))) -
          smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g
              (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα u_h) -
          smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g u_h))) :=
      h_A.sub h_B
    convert h_sub using 1
  -- Step 2: chartPushedRawLpFromLp preserves Lp-tendsto.
  have h_chartPulled_tendsto : Tendsto (fun n =>
      chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
      atTop (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u_h))) :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRawLpFromLp_tendsto
      (I := I) (M := M) g α h_residual_tendsto
  -- Step 3: Lp-tendsto in chart-pulled weighted measure converts to eLpNorm-tendsto-zero.
  have h_norm_tendsto : Tendsto (fun n =>
      ‖chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖)
      atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n =>
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h))
        atTop (𝓝 0) := by
      have := h_chartPulled_tendsto.sub (tendsto_const_nhds
        (x := chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)))
      simpa using this
    simpa using (continuous_norm.tendsto (0 :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))).comp h_sub
  -- Step 4: Convert ‖_‖ to eLpNorm-tendsto-zero of the underlying functions.
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLpNorm_eq : ∀ n,
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal
        ‖chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp _).eLpNorm_lt_top.ne)]
  have h_eLp_tendsto : Tendsto (fun n =>
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm
          (((chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
            chartPushedRawLpFromLp (I := I) (M := M) g α
              (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
                (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) =
        fun n => ENNReal.ofReal
          ‖chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)‖ := by
      funext n
      exact h_eLpNorm_eq n
    rw [h_funeq]
    have h_ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from h_ofReal_zero.symm]
    exact ENNReal.tendsto_ofReal h_norm_tendsto
  -- Step 5: Convert eLpNorm of Lp-class diff to eLpNorm of underlying-function diff.
  have h_subFun_aeEq : ∀ n,
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h) : Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y := by
    intro n
    have h_sub_coe :=
      MeasureTheory.Lp.coeFn_sub
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h))
    filter_upwards [h_sub_coe] with y hy
    rw [hy]
    rfl
  -- Now combine: eLpNorm of (Lp.coeFn) =ᵐ eLpNorm of (target ae-equal function).
  convert h_eLp_tendsto using 1
  funext n
  exact eLpNorm_congr_ae (h_subFun_aeEq n).symm

/-! ## Volume-norm version of the chart-pulled residual convergence

The Lp-convergence in the chart-pulled weighted measure on
`chartTargetEuclid α` transfers to Lp-convergence in the plain
volume measure on `chartTargetEuclid α`, via the absolute continuity
`volume.restrict chartTarget ≪ weighted.restrict chartTarget` and the
reverse `weighted.restrict chartTarget ≪ volume.restrict chartTarget`
(both directions hold because the density is strictly positive and
bounded above on `chartTargetEuclid α`).

The conversion of the Lp-norm bound (from weighted to volume): bounded
above density gives `‖f‖_L²(weighted) ≤ M^{1/2} · ‖f‖_L²(volume)` where
`M = sup density`. The reverse `‖f‖_L²(volume) ≤ c^{-1/2} · ‖f‖_L²(weighted)`
requires `density ≥ c > 0` on chart target. On a closed manifold the
density may approach 0 near the chart-target boundary, so the reverse
direction does NOT hold globally on chartTarget. However, the convergence
direction we need is **volume eLpNorm → 0 from weighted eLpNorm → 0**,
which would require the second inequality. This is the obstruction. -/

/-! ## W^{1,2}-chart-target density discharge

For arbitrary `u_h ∈ laplacianDomainPow g 2`, if the chart-pulled residual
sequence `smoothFChartResidual g α (v n)` is Cauchy in `wkpNorm 1 2` on
`chartTargetEuclid α` (with the plain volume measure), then its `wkpNorm`-
limit is in `MemW1p 2 chartTargetEuclid α`. The Cauchy hypothesis captures
the elliptic regularity content of the discharge.

This formulation provides a **clean separation** between:
* The chart-pulled W^{1,2} regularity of the residual (the hypothesis).
* The W^{1,2}-completeness machinery (`MemWkp.exists_limit_of_wkpNorm_cauchy`).
* The ae-identification of the limit with `fChartResidual(u_h)` (provided
  by the Cauchy hypothesis upon identification of the eLpNorm-limit). -/

/-- For `u_h ∈ laplacianDomainPow g 2`, given a smooth approximator
sequence `v : ℕ → SmoothScalar g` with H¹Compl convergence, plus a
`wkpNorm 1 2`-Cauchy hypothesis on the chart-pulled residual sequence
**and** a hypothesis identifying the Cauchy limit with `fChartResidual
g α u_h` (in `volume.restrict chartTarget` ae-equality), the chart-
pulled residual `fChartResidual g α u_h` is in `MemW1p 2 chartTargetEuclid α`.

The identification hypothesis (`h_lim_eq`) captures the irreducible
elliptic-regularity content: it asserts that the `wkpNorm 1 2`-limit
of the smooth-approximator chart-pulled residuals matches the chart-
pulled residual of the actual `u_h ∈ laplacianDomainPow g 2`. -/
theorem memW1p_fChartResidual_of_wkpNorm_cauchy_and_lim_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (_h_conv_H1Compl : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h))
    (_h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_lim_eq : ∃ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) ∧
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) ∧
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨F_lim, h_F_lim_w1p, _h_F_lim_tendsto, h_F_lim_aeEq⟩ := h_lim_eq
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_F_lim_aeEq).mp h_F_lim_w1p

/-! ## Cleanest density-form discharge using `MemWkp.exists_limit_of_wkpNorm_cauchy`

If we only need the `wkpNorm`-Cauchy hypothesis (without manually
identifying the limit), we can invoke
`MemWkp.exists_limit_of_wkpNorm_cauchy` to extract a limit
`F_lim ∈ MemW1p 2` automatically, and then need the identification only
to claim `F_lim =ᵐ fChartResidual(u_h)`. -/

/-- **Density-form discharge via the W^{1,2}-Cauchy hypothesis and the
identification of the Cauchy limit.**

Given a smooth approximator sequence `v : ℕ → SmoothScalar g` with the
`wkpNorm 1 2`-Cauchy property and the **ae-identification** of the
`wkpNorm`-limit with `fChartResidual g α u_h` on `volume.restrict
chartTarget`, the chart-pulled residual `fChartResidual g α u_h` is in
`MemW1p 2 chartTargetEuclid α`. -/
theorem memW1p_fChartResidual_of_wkpNorm_cauchy_identification
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Step 1: Apply MemWkp.exists_limit_of_wkpNorm_cauchy to the W^{1,2}-Cauchy sequence.
  have h_smooth_W1p : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (smoothFChartResidual (I := I) (M := M) g α (v n))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro n
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact smoothFChartResidual_memW1p (I := I) (M := M) g α (v n)
  obtain ⟨F_lim, hF_lim_memWkp, hF_lim_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
      (hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α)
      (k := 1) (p := 2) (hp_one := by norm_num) (hp_top := by norm_num)
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      h_smooth_W1p h_cauchy
  have hF_lim_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
      (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp hF_lim_memWkp
  -- Step 2: Use identification hypothesis to conclude F_lim =ᵐ fChartResidual(u_h).
  have hF_lim_aeEq := h_identification F_lim hF_lim_W1p hF_lim_tendsto
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hF_lim_aeEq).mp hF_lim_W1p

/-! ## The W^{1,2}-density-form constructor for `DiffChartBilinearH1ComplData g α`

This constructor takes the W^{1,2}-Cauchy hypothesis on the smooth-
approximator chart-pulled residuals + the identification hypothesis,
discharges the `MemW1p 2 fChartResidual` requirement of the
`_via_residual` constructor automatically, and produces a
`DiffChartBilinearH1ComplData g α` instance for any `u_h ∈
laplacianDomainPow g 2`. -/

/-- **W^{1,2}-density-form constructor for `DiffChartBilinearH1ComplData
g α` from `u_h ∈ laplacianDomainPow g 2`**.

This constructor packages:
* The W^{1,2}-Cauchy hypothesis on the smooth-approximator chart-pulled
  residuals.
* The identification hypothesis (the `wkpNorm 1 2`-limit is ae-equal to
  `fChartResidual g α u_h`).
* The differentiated variational identity (same shape as in
  `_via_residual`).

The `MemW1p 2 fChartResidual` requirement of the `_via_residual`
constructor is discharged internally via
`memW1p_fChartResidual_of_wkpNorm_cauchy_identification`. -/
noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h)
    (direction : Fin (Module.finrank ℝ E))
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
    (I := I) (M := M) g α hu_h direction
    (memW1p_fChartResidual_of_wkpNorm_cauchy_identification
      (I := I) (M := M) g α hu_h v h_cauchy h_identification)
    h_identity

end DiffChartBilinearH1ComplResidualUnconditional
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualUnconditional.diffChartBilinearH1ComplData_of_smoothToH1Compl_unconditional
#print axioms
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualUnconditional.memW1p_fChartResidual_of_wkpNorm_cauchy_and_lim_eq
#print axioms
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualUnconditional.memW1p_fChartResidual_of_wkpNorm_cauchy_identification
#print axioms
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualUnconditional.diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_density

end Sanity
