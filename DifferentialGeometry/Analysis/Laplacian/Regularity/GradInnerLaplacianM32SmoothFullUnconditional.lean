import DifferentialGeometry.Analysis.Laplacian.Regularity.HessianBridgeSmoothLp
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerLaplacianM32SmoothFull

/-!
# Full smooth-case M3.2 final theorem (unconditional on the Christoffel
discharge + per-chart transferability hypotheses)

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and a smooth scalar `v : SmoothScalar g`, this module
combines the smooth-case Lp-class Hessian bridge (delivered conditional on
`christoffelDischargeSmoothCase` + `perChartAeTransferableSmoothCase` in
`HessianBridgeSmoothLp`) with the existing M3.2 smooth-case theorem
(conditional on the Hessian bridge in `GradInnerLaplacianM32SmoothFull`)
to deliver the **full smooth-case M3.2 final theorem** conditional only on
the two clean hypotheses.

## Hypotheses

The M3.2 smooth-case final theorem is now conditional on two clean
hypotheses (replacing the broader Hessian-bridge hypothesis):

1. **Christoffel discharge** (`christoffelDischargeSmoothCase g φ v`):
   the POU-weighted Christoffel diff vanishes pointwise.

2. **Per-chart ae-transferability** (`perChartAeTransferableSmoothCase g φ v`):
   per-chart LapDom contribution ae-equals POU-weighted Euclidean pairing.

## Main results

* `gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge`
  — the smooth-case M3.2 final theorem in resolvent-of-candidate form,
  conditional on both hypotheses.

* `smoothCase_M32_full_unconditional_of_christoffel_discharge`
  — the smooth-case M3.2 image-membership form, conditional on both.

* `smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge`
  — the iterated-closure form, conditional on both.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianM32SmoothFullUnconditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpFull
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32SmoothFull

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The smooth-case M3.2 final theorem with the cleaner hypothesis pair

The Hessian bridge hypothesis in `GradInnerLaplacianM32SmoothFull` is
discharged via `HessianBridgeSmoothLp` under the two cleaner hypotheses. -/

/-- **Smooth-case M3.2 final theorem, resolvent-of-candidate form, conditional
on Christoffel discharge and per-chart transferability.** -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-! ## The image-membership form -/

/-- **Smooth-case M3.2 conclusion (image-membership form) via the unconditional
candidate, conditional on Christoffel discharge and per-chart transferability.** -/
theorem smoothCase_M32_full_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_M32_full_unconditional_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-! ## The iterated-closure form -/

/-- **Smooth-case iterated-closure form via the unconditional candidate,
conditional on Christoffel discharge and per-chart transferability.** -/
theorem smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulHC (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_via_candidate
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-! ## Headline compact restatement -/

/-- **Compact restatement.** The smooth-case variational identity holds
for the unconditional candidate, conditional on Christoffel discharge and
per-chart transferability. -/
theorem smoothCase_variational_identity_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v h_transfer h_discharge

/-! ## Theorems conditional only on the Christoffel discharge

Since per-chart ae-transferability is discharged unconditionally in
`HessianBridgeSmoothLp.perChartAeTransferableSmoothCase_holds`, the M3.2
smooth-case theorems can be restated to require only the Christoffel
discharge hypothesis. -/

/-- **Smooth-case M3.2 final theorem, resolvent-of-candidate form, conditional
only on the Christoffel discharge.** Per-chart ae-transferability is discharged
unconditionally upstream. -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Smooth-case M3.2 conclusion (image-membership form), conditional only on
the Christoffel discharge.** -/
theorem smoothCase_M32_full_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_M32_full_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Smooth-case iterated-closure form, conditional only on the Christoffel
discharge.** -/
theorem smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulHC (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Headline compact restatement, conditional only on the Christoffel
discharge.** -/
theorem smoothCase_variational_identity_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge

end GradInnerLaplacianM32SmoothFullUnconditional
end Laplacian
end Analysis
end DifferentialGeometry

end
