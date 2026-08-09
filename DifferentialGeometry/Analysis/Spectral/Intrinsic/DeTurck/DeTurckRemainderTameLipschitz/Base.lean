import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciArmPrincipalCoeffBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckTopCoeff
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartLieDeriv
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm2CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold

/-!
# Pointwise fibre-norm inputs, the DeTurck arm, and the chart Lie layer

Chunk of `DeTurckRemainderTameLipschitz`, split out of the former
46927-line monolith (no longer elaborable in a single Lean
process).  Every declaration is verbatim.  Chunk map, dependency
graph and measured peaks: `DeTurckRemainderTameLipschitz.md`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap

open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry

open DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff exists_arm1Koszul_realizedFam_rfns_ballUniform cmm_two_basis_expand unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local symmS symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)

open DifferentialGeometry.PDE.DeTurck (deTurckVF)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo realizedRicciChartSum jointContMDiff_toModel_continuous_slice hasDerivAt_realizedRicciChartSum_general realizedFam)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection symmAbsorbedCoeff_rfns_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace DeTurckRemainderTameLipschitz
end DeTurckRemainderTameLipschitz

open DeTurckRemainderTameLipschitz

namespace DeTurckRemainderTameLipschitz

theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

end DeTurckRemainderTameLipschitz

/-- **(POSIT — the pointwise order-`0` rough-Laplacian fibre bound, public jet form.)**

For a smooth compactly-supported `(0, s)`-tensor `S` there is a single nonnegative constant `C`,
uniform over `S` and the base point `x`, with the **order-`0`** pointwise domination of the rough
(connection) Laplacian `Δ_∇ S := rawTensorConnLapSmooth g₀ 0 s S` by the **order-`2`** covariant jet of
`S`:
```
rfns(Δ_∇ S)(x) ≤ C · rfns(∇²S)(x),   ∇²S := iteratedCovGrad g₀ 0 s 2 S.
```

This is the value-local order-`0` content of the rough Laplacian: pointwise `Δ_∇ S` is the diagonal
`g₀`-trace of the Hessian `∑_i ∇²_{B_i,B_i} S` (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), and
the `n`-sub-additivity of the squared fibre norm together with the per-slot two-slot-evaluation Parseval
bound dominates the trace by `dim² · rfns(∇²S)(x)` (the witness `C := dim²`).  The on-disk material
already carries this exact bound as the **private** lemma `rawConnLap_fiberNormSq_le_secondCovGrad`
(`Geometry/Connection/Laplacian/RoughLaplacianSecondCovGradL2Bound.lean`), built from the private
per-slot two-slot-evaluation bound `riemannianFiberNormSq_twoSlotUnitEval_le`; only its **public** jet
restatement (in `iteratedCovGrad g₀ 0 s 2`-form) is absent on disk.  Posited here as one precise true
order-`0` infrastructure child; its body is `sorry`, and consumers transitively depend on its `sorryAx`.

**Non-vacuity / order self-check.**  The bound reads `∇²S`; a `C = 0` witness is rejected by a
nonvanishing `Δ_∇ S` for a non-flat `S` (already at `s = 0`, `Δ_∇ f = trace ∇²f ≠ 0`). -/
private theorem rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 s S).toSection x) ≤
          C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 s 2 S).toSection x) := by
  refine ⟨((Module.finrank ℝ E : ℝ)) ^ 2, by positivity, fun S x => ?_⟩
  have hbase := rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g₀ s S x

  simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hbase

/-- **The pointwise iterated-gradient fibre bound of the single-level commutator defect.**

For every covariant rank `s` there is a nonnegative per-gradient-order constant family `K : ℕ → ℝ`,
uniform in `S`, such that for every gradient order `p` the squared fibre norm of the `p`-fold covariant
gradient of the single-level rough-Laplacian / covariant-gradient commutator defect
`pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` obeys, pointwise,
```
rfns(∇^p (pointwiseTensorCurv g s S))(x) ≤ K p · ∑_{a ∈ range (p + 2)} rfns(∇^a S)(x).
```

This is the pointwise (`riemannianFiberNormSq`) analogue of the `L²` bound
`exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le`; it is **proved** here (no `sorry`) from the
sorry-free Hom-field first-order section identity
`exists_pointwiseTensorCurv_firstOrder_homField_section` (`Curv S = appFullSec H_R (∇S) +
appFullSec H_dR S`) and the two order-shifted Hom-field jet window bounds
`exists_appFullSec_iteratedCovGrad_window_bound`, split by the `2`-sub-additivity
`riemannianFiberNormSq_add_le` of the squared fibre norm. -/
private theorem pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x) ≤
          K p * ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  classical
  obtain ⟨H_R, H_dR, hsec⟩ :=
    exists_pointwiseTensorCurv_firstOrder_homField_section (I := I) (M := M) g₀ s
  obtain ⟨ccR, hccR_nn, hccR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R
  obtain ⟨ccdR, hccdR_nn, hccdR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 s (s + 1) H_dR
  refine ⟨fun p => 2 * ccR p + 2 * ccdR p,
    fun p => by have := hccR_nn p; have := hccdR_nn p; positivity, fun p S x => ?_⟩
  set rfnsS : ℕ → ℝ := fun a =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
      ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hrfnsS_def
  have hrfnsS_nn : ∀ a, 0 ≤ rfnsS a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _
  set FULL : ℝ := ∑ a ∈ Finset.range (p + 2), rfnsS a with hFULL_def
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => hrfnsS_nn a)

  set AR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R (covGrad (I := I) (M := M) g₀ 0 s S)
    with hAR_def
  set AdR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 s (s + 1) H_dR S with hAdR_def
  have hgradsplit :
      iteratedCovGrad (I := I) g₀ 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g₀ s S) =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR + iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR := by
    rw [hsec S, ← hAR_def, ← hAdR_def, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + 1) p]
  have happ :
      (iteratedCovGrad (I := I) g₀ 0 (s + 1) p
          (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x := by
    rw [hgradsplit, SmoothCcTensor.toSection_add]; rfl
  rw [happ]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + 1) + p) x
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)) ?_

  have hAR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) := by

    have hcov1 : covGrad (I := I) (M := M) g₀ 0 s S = iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
    have h := hccR (iteratedCovGrad (I := I) g₀ 0 s 1 S) p x
    rw [hAR_def, hcov1]
    refine h.trans_eq ?_
    refine congrArg (ccR p * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    have hcomp := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s 1 i S x

    have harg : rfnsS (1 + i) = rfnsS (i + 1) := by rw [Nat.add_comm 1 i]
    rw [← harg, hrfnsS_def]
    exact hcomp
  have hAdR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x) ≤
        ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i := by
    have h := hccdR S p x
    rw [hAdR_def]
    exact h.trans_eq (by rw [hrfnsS_def])

  have hsubR : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) ≤ FULL := by
    rw [hFULL_def]
    have hIco : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) =
        ∑ a ∈ Finset.Ico 1 (1 + (p + 1)), rfnsS a := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm 1 i])
    rw [hIco]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_Ico] at ha; rw [Finset.mem_range]; omega
  have hsubdR : ∑ i ∈ Finset.range (p + 1), rfnsS i ≤ FULL := by
    rw [hFULL_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_range] at ha ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)
      ≤ 2 * (ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1)) +
          2 * (ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i) :=
        add_le_add (by linarith [hAR_w]) (by linarith [hAdR_w])
    _ ≤ 2 * (ccR p * FULL) + 2 * (ccdR p * FULL) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubR (hccR_nn p)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubdR (hccdR_nn p)) (by norm_num)
    _ = (2 * ccR p + 2 * ccdR p) * FULL := by ring

set_option linter.style.show false in
/-- **The pointwise `m`-fold rough-Laplacian / covariant-gradient iterated-commutator fibre bound.**

For every commutator order `m`, all covariant ranks `s` and all gradient orders `p`, there is a
nonnegative per-gradient-order constant family `Cfun : ℕ → ℝ`, uniform in `S`, with the pointwise
domination
```
rfns(∇^p ([Δ_∇, ∇^m] S))(x) ≤ Cfun p · ∑_{a ∈ range (m + p + 1)} rfns(∇^a S)(x),
```
where `[Δ_∇, ∇^m] S = Δ_∇(∇^m S) − ∇^m(Δ_∇ S)` (`∇^m S = iteratedCovGrad g₀ 0 s m S`,
`Δ_∇ = rawTensorConnLapSmooth`) and `∇^p (·) = iteratedCovGrad g₀ 0 (s + m) p (·)`.

This is the pointwise (`riemannianFiberNormSq`) analogue of
`iteratedRoughLapGrad_commutator_l2Norm_le_aux`; it is **proved** here (no `sorry`) by the same
telescoping induction on `m`, simultaneously for all `s` and all `p`.  The recursion
`[Δ_∇, ∇^{m+1}] S = pointwiseTensorCurv g (s + m) (∇^m S) + ∇([Δ_∇, ∇^m] S)`
(`pointwiseTensorCurv_commutator_eq` at rank `s + m` applied to `∇^m S`) feeds the first arm into the
single-level pointwise jet bound `pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le` and the second
arm into the induction hypothesis at gradient order `p + 1`, with the `2`-sub-additivity
`riemannianFiberNormSq_add_le` in place of the `L²` triangle inequality. -/
private theorem iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + m) p
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x) ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S x => ?_⟩

    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0) (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0 (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz]
    have hzero : ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x :
        TensorRSSpace 0 ((s + 0) + p) I x) = 0 := rfl
    rw [show ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x) =
        (0 : TensorRSSpace 0 ((s + 0) + p) I x) from hzero]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 ((s + 0) + p) x]
    exact mul_nonneg (le_refl 0)
      (Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => 2 * K p + 2 * Cm (p + 1),
      fun p => by have := hK_nn p; have := hCm_nn (p + 1); positivity, fun p S x => ?_⟩

    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
              (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      show rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
        ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _)

    have happ :
        (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
                (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
              iteratedCovGrad (I := I) g₀ 0 s (m + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x := by
      rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p,
        SmoothCcTensor.toSection_add]
      rfl
    rw [happ]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)) ?_

    have harm1 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) ≤
          K p * fullSum := by
      have hKb := hK p gradm x

      have hreindex : ∀ a,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + a) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) := by
        intro a
        rw [hgradm]
        exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s m a S x
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb

      refine hKb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn p)

      have hIco : ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) =
          ∑ b ∈ Finset.Ico m (m + (p + 2)),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + b) x
              ((iteratedCovGrad (I := I) g₀ 0 s b S).toSection x) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun a _ => by rw [show m + a = m + a from rfl])
      rw [hfullSum, hIco]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun b _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + b) x _)
      intro b hb; rw [Finset.mem_Ico] at hb; rw [Finset.mem_range]; omega

    have harm2 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x) ≤
          Cm (p + 1) * fullSum := by

      have hCmb := hCm (p + 1) S x
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb

      have h := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 (s + m) 1 p comm_m x
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 (s + m) 0 comm_m,
        iteratedCovGrad_zero] at h

      rw [Nat.add_comm 1 p] at h
      exact h.trans_le hCmb

    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)
        ≤ 2 * (K p * fullSum) + 2 * (Cm (p + 1) * fullSum) :=
          add_le_add (mul_le_mul_of_nonneg_left harm1 (by norm_num))
            (mul_le_mul_of_nonneg_left harm2 (by norm_num))
      _ = (2 * K p + 2 * Cm (p + 1)) * fullSum := by ring

/-- **(The genuine pointwise order-`a` covariant-jet bound of the linear connection
Laplacian, the Δ-arm of the sealed remainder difference — PROVED from the order-`0` rough-Laplacian
fibre posit and the pointwise iterated commutator telescope.)**

For a smooth compactly-supported `(0,2)`-tensor `W` (the perturbation difference `T − T'` at the call
site) there is a single nonnegative constant `C`, uniform over `W` and the base point `x`, such that
the order-`a` covariant gradient of the rough (connection) Laplacian `Δ_∇ W := rawTensorConnLapSmooth
g₀ 0 2 W` is dominated, at the squared fibre-norm level, by the **order-`(a + 2)` covariant jet** of
`W`:
```
rfns(∇^a (Δ_∇ W))(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q W)(x).
```

**The jet order is `a + 2`, not `a`** — the rough Laplacian is genuinely *second order*: pointwise it
is the diagonal `g₀`-trace of the Hessian `∑_i ∇²_{B_i,B_i} W`, so `Δ_∇ W` reads `∇²W` already at order
`0`, and commuting the order-`a` gradient past `Δ_∇` advances the read order by exactly two.  A window-`a`
bound (`q ≤ a`) is FALSE: the rough Laplacian loses exactly two derivatives.

**Assembly.**  Splitting `∇^a(Δ_∇ W) = Δ_∇(∇^a W) − [Δ_∇, ∇^a]W` (the iterated commutator, `abel`),
the `2`-sub-additivity of the squared fibre norm bounds `rfns(∇^a(Δ_∇ W))` by `2·rfns(Δ_∇(∇^a W)) +
2·rfns([Δ_∇, ∇^a]W)`.  The **top-jet** term `Δ_∇(∇^a W)` is dominated by the order-`0` rough-Laplacian
fibre posit `rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet` at rank `2 + a` applied to
`∇^a W`, whose `∇²(∇^a W)` reindexes (`rfns_iteratedCovGrad_comp`) onto the genuine `q = a + 2` jet
`∇^{a+2}W`; the **lower-order** commutator term is dominated by the pointwise iterated-commutator
telescope `iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux` at `m := a`, `p := 0`, `s := 2`,
controlled by the `∇^{≤ a}W` jets.  Both land in the read window `q ≤ a + 2`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}W`; the `q = a + 2` term is the genuine
top jet (the second-order Laplacian read), so a window-`a` weakening is rejected.  A `C = 0` witness is
rejected by a nonvanishing `∇^a (Δ_∇ W)` for a non-flat `W`. -/
private theorem rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) := by
  classical

  obtain ⟨Cpost, hCpost_nn, hCpost⟩ :=
    rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet (I := I) (M := M) g₀ (2 + a)

  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux (I := I) (M := M) g₀ a 2
  refine ⟨2 * Cpost + 2 * Cfun 0, by have := hCfun_nn 0; positivity, fun W x => ?_⟩
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _

  set Comm : SmoothCcTensor g₀ 0 (2 + a) :=
    rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) -
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) with hComm_def
  have hsplit :
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) =
        rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) +
          (-Comm) := by
    rw [hComm_def]; abel
  have hsec :
      (iteratedCovGrad (I := I) g₀ 0 2 a
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x =
        (rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x +
          (-Comm).toSection x := by
    rw [hsplit, SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
    ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x)
    ((-Comm).toSection x)) ?_

  have hΔarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) ≤ Cpost * Scol := by
    refine (hCpost (iteratedCovGrad (I := I) g₀ 0 2 a W) x).trans ?_

    have hreindex :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + a) + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + a) 2 (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (a + 2) W).toSection x) :=
      rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 a 2 W x
    rw [hreindex]
    refine mul_le_mul_of_nonneg_left ?_ hCpost_nn
    rw [hScol_def]
    refine Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) ?_
    rw [Finset.mem_range]; omega

  have hCommarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) ≤
        Cfun 0 * Scol := by

    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x) := by
      rw [SmoothCcTensor.toSection_neg]
      rw [show ((-Comm.toSection) x : TensorRSSpace 0 (2 + a) I x) = -(Comm.toSection x) from rfl]
      exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x)
    rw [hneg]

    have hC := hCfun 0 W x
    rw [iteratedCovGrad_zero] at hC
    refine hC.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
    rw [hScol_def]

    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)
    intro q hq; rw [Finset.mem_range] at hq ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
              (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x)
      ≤ 2 * (Cpost * Scol) + 2 * (Cfun 0 * Scol) :=
        add_le_add (mul_le_mul_of_nonneg_left hΔarm (by norm_num))
          (mul_le_mul_of_nonneg_left hCommarm (by norm_num))
    _ = (2 * Cpost + 2 * Cfun 0) * Scol := by ring

/-- **The reverse chart-component Euclidean coordinate bridge (`E`-jet ≤ `EuclN`-jet).**
For `S : SmoothCcTensor g 0 2`, the order-`m` `iteratedFDerivWithin` jet of the `E`-coordinate raw
chart component `rawCompOnE` on the chart-target interior is bounded by `‖toEuclidean‖^m` times the
order-`m` plain `EuclN` Fréchet jet of `rawPullR` at the `toEuclidean`-image point.  This is the
companion of the forward bridge `norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE`,
proved by the same composition-with-the-continuous-linear-equivalence argument with `toEuclidean`
in place of `toEuclidean.symm`. -/
private lemma norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
    (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ m *
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ((toEuclidean (E := E)) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn

  have hcompose :
      DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx =
        rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have hpull := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrArg (fun f => f (e z)) hpull
    simp only [Function.comp_apply, he_def, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    rw [← this]
  rw [hcompose]

  have himg_open : IsOpen (e '' O) := e.isOpenMap _ hO_open
  have hey_mem : e y ∈ e '' O := ⟨y, hy, rfl⟩
  have hOeq : O = e ⁻¹' (e '' O) := by
    ext z; constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩; rwa [e.injective hwz] at hw

  have hcomp := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    himg_open.uniqueDiffOn (x := y) hey_mem m
  rw [← hOeq] at hcomp
  rw [hcomp]

  have hplain : iteratedFDerivWithin ℝ m
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
      (e '' O) (e y) =
      iteratedFDeriv ℝ m
        (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (e y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m himg_open hey_mem
  rw [hplain]

  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he_norm : ‖(e : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ =
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ := rfl
  rw [he_norm, mul_comm]

private lemma bareChartJetContent_le_sqrt_fiberNormSq_sum_uniform
    (g : SmoothRiemannianMetric I M) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g 0 2) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))},
        y ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        bareChartJetContent (I := I) (M := M) g 0 2 D α N y ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((iteratedCovGrad (I := I) g 0 2 i D).toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    DifferentialGeometry.PDE.RicciFlow.iteratedFDeriv_rawPullR_le_zeroContent_sum
      (I := I) (M := M) g 0 2 α N N (le_refl N)
  obtain ⟨Cfib0, hCfib0_nn, hCfib0⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
      (I := I) (M := M) g 0 2 α

  have h_fib : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (D : SmoothCcTensor g 0 2)
        {z : EuclideanSpace ℝ (Fin n)},
        z ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        zeroContentR (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad (I := I) g 0 2 i D) α z ≤
          Ci * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))) := by
    intro i
    obtain ⟨Ci, hCi_nn, hCi⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
        (I := I) (M := M) g 0 (2 + i) α
    refine ⟨Ci, hCi_nn, fun D {z} hz => ?_⟩
    refine (hCi (iteratedCovGrad (I := I) g 0 2 i D) hz).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCi_nn
    letI : Bundle.RiemannianBundle (fun w : M => TensorRSSpace 0 (2 + i) I w) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (N + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  set Npair : ℝ := (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax)), by positivity, ?_⟩
  intro D y hyK
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set Fib : ℕ → ℝ := fun i => Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
    ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) with hFib_def
  have hFib_nn : ∀ i, 0 ≤ Fib i := fun i => Real.sqrt_nonneg _
  set FibSum : ℝ := ∑ i ∈ Finset.range (N + 1), Fib i with hFibSum_def
  have hFibSum_nn : 0 ≤ FibSum := Finset.sum_nonneg fun i _ => hFib_nn i
  have hyK' : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartImagePOUTsupport
      (I := I) (M := M) α := hyK
  have h_zc : ∀ i ∈ Finset.range (N + 1),
      zeroContentR (I := I) (M := M) g 0 (2 + i)
        (iteratedCovGrad (I := I) g 0 2 i D) α y ≤ Cfibmax * Fib i := by
    intro i hi
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    have hzc := hCfib i D hyK
    refine hzc.trans ?_
    rw [hFib_def, hb_def]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_sup' Cfib (Finset.mem_range.mpr hiN)) (Real.sqrt_nonneg _)
  have h_each : ∀ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
      (∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖) ≤
      (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum := by
    intro q'
    have h_per : ∀ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ ≤
          Cpeel * (Cfibmax * FibSum) := by
      intro m hm
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpeel := hCpeel D m hmN 0 (by omega) q'.1 q'.2 y hyK'
      have h0eq : (iteratedCovGrad (I := I) g 0 2 0 D) = D :=
        DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 2 D
      rw [h0eq] at hpeel
      have hreindex : (∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
              (iteratedCovGrad (I := I) g 0 2 (0 + i) D) α y) =
          ∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1 <;> rw [Nat.zero_add]
      rw [hreindex] at hpeel
      refine hpeel.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn
      calc (∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y)
          ≤ ∑ i ∈ Finset.range (m + 1), Cfibmax * Fib i :=
            Finset.sum_le_sum (fun i hi => h_zc i
              (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi)
                (Nat.succ_le_succ hmN))))
        _ = Cfibmax * ∑ i ∈ Finset.range (m + 1), Fib i := by rw [Finset.mul_sum]
        _ ≤ Cfibmax * FibSum := by
            refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
            rw [hFibSum_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega)) (fun i _ _ => hFib_nn i)
    refine (Finset.sum_le_sum h_per).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc bareChartJetContent (I := I) (M := M) g 0 2 D α N y
      = ∑ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ∑ m ∈ Finset.range (N + 1),
            ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ := rfl
    _ ≤ ∑ _q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum :=
        Finset.sum_le_sum (fun q' _ => h_each q')
    _ = Npair * ((Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]
    _ = (Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax))) * FibSum := by ring

private lemma tensorChartComponentRaw_toSection_congr
    (g g' : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (S' : SmoothCcTensor g' r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M)
    (hSS' : S.toSection x = S'.toSection x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s S α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g' r s S' α Idx Jdx x := by
  unfold DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj
  rw [hSS']

/-- Subtractivity of the raw chart-frame component in the tensor argument. -/
private lemma tensorChartComponentRaw_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₁ α Idx Jdx x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₂ α Idx Jdx x := by
  have hsub : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    rw [neg_one_smul]; abel
  rw [hsub,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_add
      (I := I) (M := M) g r s S₁ ((-1 : ℝ) • S₂) α Idx Jdx x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul
      (I := I) (M := M) g r s (-1 : ℝ) S₂ α Idx Jdx x]
  rw [smul_eq_mul]; ring

/-- **The Ricci–DeTurck RHS-arm residual, as the genuine RHS-difference smooth tensor.**
The Δ-arms cancel: `(deTurckSmoothRemainder T − deTurckSmoothRemainder T') + Δ_∇(T − T')` equals the
re-tagged Ricci–DeTurck RHS difference `deTurckRHSSectionBg g_bg (g₀+T) − deTurckRHSSectionBg g_bg (g₀+T')`
at the `toSection` level. -/
private lemma deTurckRHSArm_toSection_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')).toSection =
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection) := by
  classical
  rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
  rw [rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']

  change (((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection) -
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection)) +
      ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection) =
      _
  abel

/-- **The chart-`α` raw `(0,2)`-component of the Ricci–DeTurck RHS-arm residual equals the chart
Ricci–DeTurck carrier difference of the realized metrics, on the chart-`α` Levi–Civita good set.**
On the good set (which contains the full chart-target interior preimage and the POU support under the
boundaryless assumption) the raw chart component of `RHSarm = RHSwrap T − RHSwrap T'` reads off the
textbook chart polynomial difference `chartDeTurckRicciRHS (g₀+T) g_bg − chartDeTurckRicciRHS (g₀+T') g_bg`. -/
private lemma tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2
        ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) := by
  classical
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set S₁ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₁).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₁).hasCompactSupport } with hS₁_def
  set S₂ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₂).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₂).hasCompactSupport } with hS₂_def

  have hsec : RHSarm.toSection = (S₁ - S₂).toSection := by
    rw [SmoothCcTensor.toSection_sub]
    exact deTurckRHSArm_toSection_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hRHSeq : RHSarm = S₁ - S₂ := by
    apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
    exact hsec
  rw [hRHSeq]

  rw [tensorChartComponentRaw_sub' (I := I) (M := M) g₀ 0 2 S₁ S₂ α _ Jdx b]
  have hS₁comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₁ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₁
      (deTurckRHSSectionBg (I := I) g_bg g₁) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₁ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  have hS₂comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₂ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₂
      (deTurckRHSSectionBg (I := I) g_bg g₂) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₂ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  rw [hS₁comp, hS₂comp]

private theorem ccTensorBilinSymm_symmS_app
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_symm (I := I) g₀ T x w v, ccTensorBilinSymm_apply]
  ring

namespace DeTurckRemainderTameLipschitz

theorem gFibreOpBound_ccTensorBilinSymm_symmS
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T)) δ := by
  intro x v w
  rw [ccTensorBilinSymm_symmS_app (I := I) g₀ T x v w]
  exact hδ x v w

theorem ccTensorBilin_symmS_symm
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) g₀ T) x v w =
      ccTensorBilin (I := I) g₀ (symmS (I := I) g₀ T) x w v := by
  rw [ccTensorBilin_symmS, ccTensorBilin_symmS, ccTensorBilinSymm_symm]

end DeTurckRemainderTameLipschitz

theorem tensorSectionRealizeMetric_symmS_eq
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ₁ : ℝ} (hδ₁_lt : δ₁ < 1)
    (hδ₁ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T)) δ₁) :
    tensorSectionRealizeMetric (I := I) g₀ (symmS (I := I) g₀ T) hδ₁_lt hδ₁ =
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
  refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
    _ _ (fun b u z => ?_)
  rw [tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_symmS_app (I := I) g₀ T b u z]

private theorem tensorL2Norm_iteratedCovGrad_domDomCongrSection_eq
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 2))
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  have hbridge : ∀ (W : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 k W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + k)
      (iteratedCovGrad (I := I) g₀ 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) σ T k x
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g₀ σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hintegrand)
  have hnnA : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ :=
    norm_nonneg _
  have hnnB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  exact (sq_eq_sq₀ hnnA hnnB).mp hsq

namespace DeTurckRemainderTameLipschitz

theorem tensorL2Norm_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) g₀ T)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T with hTsw_def
  have hiter_eq : iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k Tsw := by
    rw [hTsw_def]; exact iteratedCovGrad_symmS_eq (I := I) g₀ T k
  rw [hiter_eq]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by rw [Real.norm_eq_abs]; norm_num
  rw [habs, hTsw_def,
    tensorL2Norm_iteratedCovGrad_domDomCongrSection_eq (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T k]
  have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  linarith

end DeTurckRemainderTameLipschitz

def deTurckRHSArmG0 (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport

namespace DeTurckRemainderTameLipschitz

theorem deTurckRHSArmG0_symmS_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ₁ : ℝ} (hδ₁_lt : δ₁ < 1)
    (hδ₁ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T)) δ₁) :
    deTurckRHSArmG0 (I := I) g₀ g_bg (symmS (I := I) g₀ T) hδ₁_lt hδ₁ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ := by
  refine SmoothCcTensor.ext ?_
  show (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ (symmS (I := I) g₀ T) hδ₁_lt hδ₁)).toSection =
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  rw [tensorSectionRealizeMetric_symmS_eq (I := I) g₀ T hδ_lt hδ hδ₁_lt hδ₁]

end DeTurckRemainderTameLipschitz

private theorem deTurckSmoothRemainder_eq_arm_sub_connLap
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

theorem deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' =
      (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') := by
  rw [deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T hδ_lt hδ,
    deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T' hδ'_lt hδ',
    rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']
  abel

/-- **Pointwise covariant-jet domination ⟹ integrated covariant-`L²` root-sum bound.**

If the order-`q` covariant gradient of a smooth tensor `P` (valence `2 + q`) is dominated pointwise
by `C` times the covariant-jet column of a smooth tensor `W` up to order `N`,
```
rfns(∇^q P)(x) ≤ C · ∑_{i ≤ N} rfns(∇^i W)(x)   (∀ x),
```
with `C ≥ 0`, then the integrated covariant-`L²` (semi)norm of `∇^q P` obeys the root-sum bound
```
‖∇^q P‖_{L²} ≤ √C · √(∑_{i ≤ N} ‖∇^i W‖²_{L²}).
```

The proof integrates the pointwise bound over the closed manifold against the Riemannian volume
measure: the squared `L²` norm of each jet is the integral of its fibre norm
(`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq`), every fibre norm is integrable
(`integrable_riemannianFiberNormSq_toSection`), and integral monotonicity plus finite additivity
turn the pointwise column bound into `‖∇^q P‖² ≤ C · ∑_{i ≤ N} ‖∇^i W‖²`; taking square roots and
`√(C · S) = √C · √S` gives the displayed form. -/
private theorem l2RootSum_of_pointwise_iteratedCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (q N : ℕ)
    (P W : SmoothCcTensor g₀ 0 2) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ≤
        C * ∑ i ∈ Finset.range (N + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ≤
      Real.sqrt C * Real.sqrt (∑ i ∈ Finset.range (N + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def

  have hbridgeP : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 q P), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + q)
      (iteratedCovGrad (I := I) g₀ 0 2 q P)
  have hbridgeW : ∀ i, ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) ∂μ := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 i W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)

  have hintW : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)

  set Scol : ℝ := ∑ i ∈ Finset.range (N + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
    with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _

  set RHS : M → ℝ := fun x =>
    C * ∑ i ∈ Finset.range (N + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) with hRHS_def
  have hsum_int : MeasureTheory.Integrable
      (fun x => ∑ i ∈ Finset.range (N + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def]; exact hsum_int.const_mul C
  have hP_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)

  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hP_nn_ae hRHS_int
      (Filter.Eventually.of_forall (fun x => by rw [hRHS_def]; exact hpt x))
  have hRHS_integral : (∫ x, RHS x ∂μ) = C * Scol := by
    rw [hRHS_def, MeasureTheory.integral_const_mul, hScol_def,
      MeasureTheory.integral_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)]
    refine congrArg (C * ·) (Finset.sum_congr rfl (fun i _ => (hbridgeW i).symm))

  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ C * Scol := by
    rw [hbridgeP]; exact hint_le.trans_eq hRHS_integral

  have hPq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ := norm_nonneg _
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖
      = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := (Real.sqrt_sq hPq_nn).symm
    _ ≤ Real.sqrt (C * Scol) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * Real.sqrt Scol := Real.sqrt_mul hC Scol

namespace DeTurckRemainderTameLipschitz

/-- **The linear connection-Laplacian arm is integrated covariant-`L²` tame.**

For a fixed order `a` there is one nonnegative constant `C` such that, for any smooth `W` and any
covariant order `q ≤ a`, the integrated covariant-`L²` norm of the order-`q` jet of the connection
Laplacian `Δ_∇ W := rawTensorConnLapSmooth g₀ 0 2 W` is controlled by the order-`(a+2)` covariant-`L²`
jet column of `W`:
```
‖∇^q (Δ_∇ W)‖_{L²} ≤ C · √(∑_{i ≤ a+2} ‖∇^i W‖²_{L²}).
```
The connection Laplacian is **linear**, so this is the genuine (provable, no curvature Nemytskii
content) Δ-arm of the remainder-difference tame.  The proof bundles, via `choose`, the per-order
pointwise jet bounds `rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le` into one
constant `Cunif := ∑_{q ≤ a} C(q)`; for each `q ≤ a` the order-`q` pointwise bound
`rfns(∇^q (Δ_∇ W))(x) ≤ C(q) · ∑_{i ≤ q+2} rfns(∇^i W)(x)` is widened (window `q + 2 ≤ a + 2`,
constant `C(q) ≤ Cunif`) to the order-`(a+2)` column and integrated to the `L²` root-sum bound by
`l2RootSum_of_pointwise_iteratedCovGrad_jet`. -/
theorem rawTensorConnLapSmooth_iteratedCovGrad_l2_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (q : ℕ), q ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)‖ ≤
          C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical

  choose Cfam hCfam_nn hCfam using
    (fun q : ℕ => rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
      (I := I) (M := M) g₀ q)
  set Cunif : ℝ := ∑ q ∈ Finset.range (a + 1), Cfam q with hCunif_def
  have hCunif_nn : 0 ≤ Cunif :=
    Finset.sum_nonneg fun q _ => hCfam_nn q
  refine ⟨Real.sqrt Cunif, Real.sqrt_nonneg _, fun W q hq => ?_⟩

  have hCfam_le_Cunif : Cfam q ≤ Cunif := by
    rw [hCunif_def]
    exact Finset.single_le_sum (f := Cfam) (fun i _ => hCfam_nn i)
      (Finset.mem_range.mpr (by omega))
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
        Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) := by
    intro x
    refine (hCfam q W x).trans ?_

    have hqle : q + 2 + 1 ≤ a + 2 + 1 := by omega
    have hwindow : (∑ i ∈ Finset.range (q + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) ≤
        ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hqle)
        (fun i _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_nonneg fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
    calc Cfam q * ∑ i ∈ Finset.range (q + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)
        ≤ Cfam q * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_left hwindow (hCfam_nn q)
      _ ≤ Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_right hCfam_le_Cunif hsum_nn

  exact l2RootSum_of_pointwise_iteratedCovGrad_jet (I := I) g₀ q (a + 2)
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) W Cunif hCunif_nn hpt

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The supercritical pointwise `C²`-jet column of a smooth `(0,2)`-tensor is dominated by its
integrated covariant-`L²` jet column up to order `a + 2`.**

For a smooth compactly-supported `(0,2)`-tensor `W` and a supercritical order `a` (`2·finrank E + 10 ≤
a`), there is a single nonnegative constant `Cemb` such that, at **every** base point `x`, the order-`≤
2` pointwise covariant-jet column of `W` is dominated by `Cemb²` times the **integrated** order-`(a+2)`
covariant-`L²` jet column
```
∑_{q ≤ 2} rfns(∇^q W)(x)  ≤  Cemb² · ∑_{i ≤ a+2} ‖∇^i W‖²_{L²}.
```

This is the genuine supercritical Sobolev `H^{a+2} ↪ C²` section embedding, in the project's
chart↔spectral convention.  It composes the unconditional `C²` collapse
`iteratedCovGrad_toSobolev_embedding_C2_unconditional` at a covariant window `2·k` (`2k > finrank E +
4`, supplying `∑_{q ≤ 2} ‖(∇^q W)(x)‖ ≤ C · ‖W.toHs (2k)‖`) with the **order-doubling** reverse
Hebey-Sobolev bridge `exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum` at order `2k`
(`‖W.toHs (2k)‖ ≤ C' · ∑_{j ≤ 4k} ‖∇^j W‖`), whence `4k ≤ a + 2`.  The two constraints `2k > finrank E
+ 4` and `4k ≤ a + 2` are jointly satisfiable exactly because `2·finrank E + 10 ≤ a` (choose `k :=
finrank E / 2 + 3`).  Squaring (each pointwise norm by the column bound, the integrated sum by
Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`) and widening the `4k`-window to `a + 2` produce the
single `Cemb²` constant; the fibre-norm/bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`
identifies `rfns(∇^q W)(x)` with `‖(∇^q W).toSection x‖²`. -/
theorem deTurckArmDiff_supercritical_pointwise_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical

  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega

  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_unconditional (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _,
    fun W x => ?_⟩
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _

  set Mn : ℝ := ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) (2 * k) W‖ with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hCol := hCc W x

  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm

  set Jsum : ℝ := ∑ j ∈ Finset.range (2 * (2 * k) + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ with hJsum_def
  have hJsum_nn : 0 ≤ Jsum := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hwin : (2 * (2 * k) + 1) ≤ a + 2 + 1 := by omega
  have hcol_sq_le : (∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤ S := by
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun i _ _ => sq_nonneg _)
  have hJsq : Jsum ^ 2 ≤ ((4 * k + 1 : ℕ) : ℝ) * S := by
    have hcs : Jsum ^ 2 ≤
        ((2 * (2 * k) + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
      rw [hJsum_def]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range (2 * (2 * k) + 1))
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hcard_eq : (2 * (2 * k) + 1 : ℕ) = (4 * k + 1 : ℕ) := by omega
    rw [hcard_eq] at hcs hcol_sq_le
    refine le_trans hcs ?_
    exact mul_le_mul_of_nonneg_left hcol_sq_le (by positivity)

  have hMn_sq : Mn ^ 2 ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) := by
    have hstep : Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := pow_le_pow_left₀ hMn_nn hHebey 2
    calc Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := hstep
      _ = Ch ^ 2 * Jsum ^ 2 := by ring
      _ ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) :=
          mul_le_mul_of_nonneg_left hJsq (by positivity)

  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤ 3 * (Cc * Mn) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add] at hCol
    have h0 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x‖ := norm_nonneg _
    have h1 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x‖ := norm_nonneg _
    have h2 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x‖ := norm_nonneg _
    nlinarith [hCol, h0, h1, h2, hMn_nn, hCc_pos.le, mul_nonneg hCc_pos.le hMn_nn]

  have hsqrt_sq : Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) ^ 2 =
      3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (Cc * Mn) ^ 2 := hcolsq_le
    _ = 3 * Cc ^ 2 * Mn ^ 2 := by ring
    _ ≤ 3 * Cc ^ 2 * (Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S)) :=
        mul_le_mul_of_nonneg_left hMn_sq (by positivity)
    _ = (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) * S := by ring

lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_sub]

/-- The unit read-off `unitModel` is additive in the `(0, s)`-tensor argument: `unitModel (S + S') =
unitModel S + unitModel S'`.  Re-derived locally (the `RicciDeTurckLinearization` version is `private`). -/
lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

/-- The squared fibre norm of a summed `(r, s)` coefficient field `R + L` at `x` is bounded by the
combined ball-uniform level `(√(2 ΛR² + 2 ΛL²))² = 2 ΛR² + 2 ΛL²`, from the per-arm `C⁰` sups
`rfns(R x) ≤ ΛR²`, `rfns(L x) ≤ ΛL²` and the `2`-sub-additivity of the squared fibre norm
(`riemannianFiberNormSq_add_le`). -/
lemma threeArmCoeffSum_rfns_le (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
    (R L : SmoothCcTensor g₀ r s) (ΛR ΛL : ℝ) (x : M)
    (hR : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) ≤ ΛR ^ 2)
    (hL : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (L.toSection x) ≤ ΛL ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((R + L).toSection x) ≤
      Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 := by
  have hsqrt : Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 = 2 * ΛR ^ 2 + 2 * ΛL ^ 2 := by
    refine Real.sq_sqrt ?_
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (R.toSection x)
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (L.toSection x)
    nlinarith [hR, hL]
  rw [hsqrt]
  have hsec : (R + L).toSection x = R.toSection x + L.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r s x
    (R.toSection x) (L.toSection x)
  nlinarith [hadd, hR, hL]

end DeTurckRemainderTameLipschitz

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

namespace DeTurckRemainderTameLipschitz

lemma riemannianFiberNormSq_smul_value_tame
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

end DeTurckRemainderTameLipschitz

private lemma unitModel_smul_tame (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • T) x =
      c • unitModel (I := I) (M := M) g₀ s T x := by
  rw [unitModel, unitModel]
  have hsec : (c • T).toSection x = c • T.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • T).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma appCc_smul_left_tame (g : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r 2) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r 2 (c • Φ) W =
      c • appCc (I := I) (M := M) g r 2 Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r 2 Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r 2 Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r 2 I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

namespace DeTurckRemainderTameLipschitz

lemma unitModel_appCc_smul_left_apply_tame (g : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r 2) (W : SmoothCcTensor g 0 r)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (appCc (I := I) (M := M) g r 2 (c • Φ) W) x v =
      c * unitModel (I := I) (M := M) g 2 (appCc (I := I) (M := M) g r 2 Φ W) x v := by
  rw [appCc_smul_left_tame, unitModel_smul_tame, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

lemma unitModel_add2_apply_tame (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  rw [unitModel_add_local, ContinuousMultilinearMap.add_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma threeArm_unitModel_appCc_intervalIntegrable_tame
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r)
    {δ δ' : ℝ} (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ'))
    (hcont : ∀ x : M, ContinuousOn
      (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      MeasureTheory.volume 0 1 := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have hkey : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v =
        ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
          (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Φ s).toSection x) u]
  have hcontApp : ContinuousOn (fun s : ℝ =>
      ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
        (Tensor0SSpace.toModel u)) v) (realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hstep : ContinuousOn (fun s : ℝ =>
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x)) (Tensor0SSpace.toModel u))
        (realizedSmallSet (δ := δ) (δ' := δ')) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel 2 ℝ E)
        (Tensor0SSpace.toModel u)).continuous.comp_continuousOn (hcont x)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp_continuousOn
      hstep
  have hcontFinal : ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hcontApp.congr (fun s _ => ?_)
    exact (hkey s).symm
  exact (hcontFinal.mono hSI).intervalIntegrable

theorem uniform_C0_bound_concrete_lichnerowicz_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform
    (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

end DeTurckRemainderTameLipschitz

private theorem linearizedRicciArm0BaseCoeff_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem linearizedRicciArm0CorrField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i =>
    3 * (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound
        (I := I) (M := M) g₀ a R δ₀ i * (1 + 2 * ((a : ℝ) + 2) * R ^ 2)) +
      27 / 2 * (KR i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2) +
      6 * (KC i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2),
    fun i => ?_, ?_⟩
  · have h1 :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
        (I := I) (M := M) g₀ a R δ₀ i
    have h2 : (0 : ℝ) ≤ 1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by positivity
    have h3 := hKR_nn i
    have h4 := hKC_nn i
    have h5 : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    have h6 : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    have h7 := mul_nonneg h1 h2
    linarith
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hicg_smul : ∀ (r s' j : ℕ) (c : ℝ) (w : SmoothCcTensor g₀ r s'),
        iteratedCovGrad (I := I) g₀ r s' j (c • w) =
          c • iteratedCovGrad (I := I) g₀ r s' j w := by
      intro r s' j c w
      induction j with
      | zero => simp only [iteratedCovGrad_zero]
      | succ j ih =>
        rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_gFibreOpBound
        (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      nlinarith [e1, e2]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
                (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_inner_of_mem
          (I := I) g₀ T T' hδ hδ' (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s) =
          (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
            s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, hicg_smul, hicg_smul]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
              s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
              ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
              s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hRmDiff := hKR (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
        (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
    have hCvDiff := hKC (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
        (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
    obtain ⟨_, _, hbound, _⟩ :=
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
    have hjet := ((hbound ha_super hR hδ₀ hδ_le hδ'_le hTball hT'ball).2 i hi s hs).1
    have hwin : ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤ 2 * ((a : ℝ) + 2) * R ^ 2 := by
      have hterm : ∀ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ 2 * R ^ 2 := by
        intro j hj
        have hj_le : j ≤ a + 2 := by
          have hj' := Finset.mem_range.mp hj
          omega
        have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hTball j hj_le) 2
        have h2 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hT'ball j hj_le) 2
        linarith
      have hsum := Finset.sum_le_card_nsmul (Finset.range (i + 2)) _ (2 * R ^ 2) hterm
      rw [Finset.card_range, nsmul_eq_mul] at hsum
      have hcast : ((i + 2 : ℕ) : ℝ) ≤ (a : ℝ) + 2 := by
        have hia : (i : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr hi
        push_cast
        linarith
      have h2R : (0 : ℝ) ≤ 2 * R ^ 2 := by positivity
      calc ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
          ≤ ((i + 2 : ℕ) : ℝ) * (2 * R ^ 2) := hsum
        _ ≤ ((a : ℝ) + 2) * (2 * R ^ 2) := mul_le_mul_of_nonneg_right hcast h2R
        _ = 2 * ((a : ℝ) + 2) * R ^ 2 := by ring
    have hone : (1 : ℝ) + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤
        1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by linarith
    have hK_nn :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
        (I := I) (M := M) g₀ a R δ₀ i
    have hZraw := le_trans hjet (mul_le_mul_of_nonneg_left hone hK_nn)
    rw [show linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' =
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
          (I := I) g₀ T T' hδ hδ').choose from rfl]
    set Cf := (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose s with hCf_def
    set Rmf := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hRmf_def
    set Cvf := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hCvf_def
    set Rm0 := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g₀ g₀ with hRm0_def
    set Cv0 := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
        (I := I) (M := M) g₀ g₀ with hCv0_def
    have hRm_split : iteratedCovGrad (I := I) g₀ 2 2 i Rmf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0) +
          iteratedCovGrad (I := I) g₀ 2 2 i Rm0 := by
      rw [iteratedCovGrad_sub]
      abel
    have hRm_norm : ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0)‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖ := by
      rw [hRm_split]
      exact norm_add_le _ _
    have hRm_sq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ^ 2 ≤
        2 * KR i + 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖ ^ 2 := by
      have hx := pow_le_pow_left₀ (norm_nonneg _) hRm_norm 2
      nlinarith [hRmDiff, hx,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖)]
    have hCv_split : iteratedCovGrad (I := I) g₀ 2 2 i Cvf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0) +
          iteratedCovGrad (I := I) g₀ 2 2 i Cv0 := by
      rw [iteratedCovGrad_sub]
      abel
    have hCv_norm : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0)‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖ := by
      rw [hCv_split]
      exact norm_add_le _ _
    have hCv_sq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ^ 2 ≤
        2 * KC i + 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖ ^ 2 := by
      have hx := pow_le_pow_left₀ (norm_nonneg _) hCv_norm 2
      nlinarith [hCvDiff, hx,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖)]
    have hsm : iteratedCovGrad (I := I) g₀ 2 2 i ((3 / 2 : ℝ) • Rmf) =
        (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf :=
      hicg_smul 2 2 i (3 / 2 : ℝ) Rmf
    have hCf_split : Cf = Cf + (3 / 2 : ℝ) • Rmf - Cvf - (3 / 2 : ℝ) • Rmf + Cvf := by
      abel
    have hicg_split : iteratedCovGrad (I := I) g₀ 2 2 i Cf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf) -
          (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf +
          iteratedCovGrad (I := I) g₀ 2 2 i Cvf := by
      conv_lhs => rw [hCf_split]
      rw [iteratedCovGrad_add, iteratedCovGrad_sub, hsm]
    have ht3 : ‖(3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ =
        (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ +
          (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ := by
      rw [hicg_split]
      have ht1 := norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf) -
          (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf)
        (iteratedCovGrad (I := I) g₀ 2 2 i Cvf)
      have ht2 := norm_sub_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf))
        ((3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf)
      linarith [ht1, ht2, ht3.le, ht3.ge]
    have hx2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hxsq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cf‖ ^ 2 ≤
        3 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ ^ 2 +
          27 / 4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ^ 2 +
          3 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ^ 2 := by
      nlinarith [hx2,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ -
          (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖),
        sq_nonneg ((3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖)]
    linarith [hxsq, hZraw, hRm_sq, hCv_sq]

private theorem linearizedRicciArm1BaseCoeff_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem linearizedRicciArm1CorrField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  refine ⟨fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound
        (I := I) (M := M) g₀ a R δ₀ i * (1 + 2 * ((a : ℝ) + 2) * R ^ 2),
    fun i =>
      mul_nonneg
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
          (I := I) (M := M) g₀ a R δ₀ i)
        (by positivity), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  obtain ⟨_, _, hbound, _⟩ :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
  have hjet := ((hbound ha_super hR hδ₀ hδ_le hδ'_le hTball hT'ball).2 i hi s hs).2
  have hwin : ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤ 2 * ((a : ℝ) + 2) * R ^ 2 := by
    have hterm : ∀ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ 2 * R ^ 2 := by
      intro j hj
      have hj_le : j ≤ a + 2 := by
        have hj' := Finset.mem_range.mp hj
        omega
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hTball j hj_le) 2
      have h2 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hT'ball j hj_le) 2
      linarith
    have hsum := Finset.sum_le_card_nsmul (Finset.range (i + 2)) _ (2 * R ^ 2) hterm
    rw [Finset.card_range, nsmul_eq_mul] at hsum
    have hcast : ((i + 2 : ℕ) : ℝ) ≤ (a : ℝ) + 2 := by
      have hia : (i : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr hi
      push_cast
      linarith
    have h2R : (0 : ℝ) ≤ 2 * R ^ 2 := by positivity
    calc ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
        ≤ ((i + 2 : ℕ) : ℝ) * (2 * R ^ 2) := hsum
      _ ≤ ((a : ℝ) + 2) * (2 * R ^ 2) := mul_le_mul_of_nonneg_right hcast h2R
      _ = 2 * ((a : ℝ) + 2) * R ^ 2 := by ring
  have hone : (1 : ℝ) + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤
      1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by linarith
  have hK_nn :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
      (I := I) (M := M) g₀ a R δ₀ i
  rw [show linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' =
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose from rfl]
  exact le_trans hjet (mul_le_mul_of_nonneg_left hone hK_nn)

private theorem ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.ricciArmPrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem traceHessianCoeff_realizedFam_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private lemma normSq_iteratedCovGrad_add_le_tame
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A B : SmoothCcTensor g₀ r s) (PA PB : ℝ)
    (hA : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 ≤ PA)
    (hB : ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤ PB) :
    ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2 ≤ 2 * PA + 2 * PB := by
  rw [iteratedCovGrad_add]
  have htri : ‖iteratedCovGrad (I := I) g₀ r s i A + iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      ‖iteratedCovGrad (I := I) g₀ r s i A‖ + ‖iteratedCovGrad (I := I) g₀ r s i B‖ :=
    norm_add_le _ _
  nlinarith [htri, hA, hB, norm_nonneg (iteratedCovGrad (I := I) g₀ r s i A),
    norm_nonneg (iteratedCovGrad (I := I) g₀ r s i B),
    norm_nonneg (iteratedCovGrad (I := I) g₀ r s i A + iteratedCovGrad (I := I) g₀ r s i B),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i A‖ - ‖iteratedCovGrad (I := I) g₀ r s i B‖)]

private theorem iteratedCovGrad_smul_tame (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

namespace DeTurckRemainderTameLipschitz

lemma normSq_iteratedCovGrad_sub_smul_le_tame
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A B : SmoothCcTensor g₀ r s) (c : ℝ) (PA PB : ℝ)
    (hA : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 ≤ PA)
    (hB : ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤ PB) :
    ‖iteratedCovGrad (I := I) g₀ r s i (A - c • B)‖ ^ 2 ≤ 2 * PA + 2 * c ^ 2 * PB := by
  rw [iteratedCovGrad_sub, iteratedCovGrad_smul_tame]
  have htri : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      ‖iteratedCovGrad (I := I) g₀ r s i A‖ + ‖c • iteratedCovGrad (I := I) g₀ r s i B‖ := by
    rw [sub_eq_add_neg]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_neg]
  rw [norm_smul, Real.norm_eq_abs] at htri
  have habs : |c| * ‖iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      |c| * Real.sqrt PB := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    rw [show ‖iteratedCovGrad (I := I) g₀ r s i B‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hB
  have hAsqrt : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ≤ Real.sqrt PA := by
    rw [show ‖iteratedCovGrad (I := I) g₀ r s i A‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hA
  have hPA_nn : 0 ≤ PA := le_trans (sq_nonneg _) hA
  have hPB_nn : 0 ≤ PB := le_trans (sq_nonneg _) hB
  have hsumbnd : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      Real.sqrt PA + |c| * Real.sqrt PB := by
    refine htri.trans ?_
    have := add_le_add hAsqrt habs
    linarith [this]
  have hsum_nn : 0 ≤ Real.sqrt PA + |c| * Real.sqrt PB :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg c) (Real.sqrt_nonneg _))
  have hnorm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ :=
    norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤
      (Real.sqrt PA + |c| * Real.sqrt PB) ^ 2 := by
    have := mul_self_le_mul_self hnorm_nn hsumbnd
    nlinarith [this]
  have hsqrtPA : Real.sqrt PA ^ 2 = PA := Real.sq_sqrt hPA_nn
  have hsqrtPB : Real.sqrt PB ^ 2 = PB := Real.sq_sqrt hPB_nn
  have habsc : |c| ^ 2 = c ^ 2 := sq_abs c
  refine hsq.trans ?_
  nlinarith [hsqrtPA, hsqrtPB, habsc, Real.sqrt_nonneg PA, Real.sqrt_nonneg PB,
    abs_nonneg c, sq_nonneg (Real.sqrt PA - |c| * Real.sqrt PB),
    mul_nonneg (abs_nonneg c) (mul_nonneg (Real.sqrt_nonneg PA) (Real.sqrt_nonneg PB))]

end DeTurckRemainderTameLipschitz

private theorem linearizedRicciArm_concreteField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i ∧
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i ∧
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨P0b, hP0b_nn, hP0b⟩ :=
    linearizedRicciArm0BaseCoeff_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P0c, hP0c_nn, hP0c⟩ :=
    linearizedRicciArm0CorrField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P1b, hP1b_nn, hP1b⟩ :=
    linearizedRicciArm1BaseCoeff_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P1c, hP1c_nn, hP1c⟩ :=
    linearizedRicciArm1CorrField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Pp, hPp_nn, hPp⟩ :=
    ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Ph, hPh_nn, hPh⟩ :=
    traceHessianCoeff_realizedFam_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => max (2 * P0b i + 2 * P0c i)
      (max (2 * P1b i + 2 * P1c i) (2 * Pp i + 2 * (1 / 2 : ℝ) ^ 2 * Ph i)), ?_, ?_⟩
  · intro i
    refine le_max_of_le_left ?_
    nlinarith [hP0b_nn i, hP0c_nn i]
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
    have hb0 := hP0b T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hc0 := hP0c T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hb1 := hP1b T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hc1 := hP1c T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hp := hPp T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hh := hPh T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [linearizedRicciArm0Field]
      exact (normSq_iteratedCovGrad_add_le_tame (I := I) g₀ 2 2 i
        (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
        (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s) (P0b i) (P0c i) hb0 hc0).trans
        (le_max_left _ _)
    · rw [linearizedRicciArm1Field]
      refine (normSq_iteratedCovGrad_add_le_tame (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)
        (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s) (P1b i) (P1c i) hb1 hc1).trans ?_
      exact le_max_of_le_right (le_max_left _ _)
    · rw [linearizedRicciArm2FieldLichnerowicz]
      refine (normSq_iteratedCovGrad_sub_smul_le_tame (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (1 / 2 : ℝ) (Pp i) (Ph i) hp hh).trans ?_
      exact le_max_of_le_right (le_max_right _ _)

namespace DeTurckRemainderTameLipschitz

theorem linearizedRicciArm_concreteField_jetL2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) := by
  classical
  obtain ⟨P, hP_nn, hP⟩ :=
    linearizedRicciArm_concreteField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  set Psum : ℝ := ∑ i ∈ Finset.range (a + 1), P i with hPsum_def
  have hPsum_nn : 0 ≤ Psum := Finset.sum_nonneg (fun i _ => hP_nn i)
  refine ⟨Real.sqrt Psum, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hB_sq : Real.sqrt Psum ^ 2 = Psum := Real.sq_sqrt hPsum_nn
  have hkey : ∀ (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ r 2)
      (s : ℝ),
      (∀ (i : ℕ), i ∈ Finset.range (a + 1) →
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ P i) →
      (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2) ≤ Real.sqrt Psum ^ 2 := by
    intro r Φ s hbound
    rw [hB_sq]
    calc ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1), P i := Finset.sum_le_sum hbound
      _ = Psum := hPsum_def.symm
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact hkey 2 (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).1)
  · intro s hs
    exact hkey 3 (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.1)
  · intro s hs
    exact hkey 4 (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.2)

end DeTurckRemainderTameLipschitz

private theorem uniform_rfns_bound_lichnerowicz_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC B : ℝ, 0 ≤ ΛC ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  classical
  obtain ⟨ΛC, hΛC_nn, hC0⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨B, hB_nn, hJet⟩ :=
    linearizedRicciArm_concreteField_jetL2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  refine ⟨ΛC, B, hΛC_nn, hB_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  set Φ₀ : ℝ → SmoothCcTensor g₀ 2 2 := linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ'
  set Φ₁ : ℝ → SmoothCcTensor g₀ 3 2 := linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ'
  set Φ₂ : ℝ → SmoothCcTensor g₀ 4 2 :=
    linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ'
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨hJet0, hJet1, hJet2⟩ := hJet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨Φ₀, Φ₁, Φ₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ')
  · intro s hs x v
    obtain ⟨_, _, _, hident, _, _⟩ :=
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
    exact hident hTsymm hT'symm s hs x v hδ_lt hδ'_lt
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.1
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.2.1
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.2.2
  · exact hJet0
  · exact hJet1
  · exact hJet2

private theorem ricciArm_threeArm_coeffFields_uniformC0
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  exact uniform_rfns_bound_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

private theorem ricciArm_threeArm_coeffFields_C0_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  exact ricciArm_threeArm_coeffFields_uniformC0 (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

namespace DeTurckRemainderTameLipschitz

theorem exists_ricciArm_threeArm_coeffFields_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) :=
  ricciArm_threeArm_coeffFields_C0_bound (I := I) g₀ g_bg a ha_super hR hδ₀

end DeTurckRemainderTameLipschitz

private theorem exists_ricciArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            ((-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)) x (v 0) (v 1)
                - (-2 : ℝ) * ricciTensor (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')) x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) := by
  classical
  obtain ⟨ΛR, B, hΛR_nn, hB_nn, hbrick⟩ :=
    exists_ricciArm_threeArm_coeffFields_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨2 * ΛR, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid, hb0, hb1, hb2, _, _, _⟩ :=
    hbrick T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set P₀ : SmoothCcTensor g₀ 2 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hP₀
  set P₁ : SmoothCcTensor g₀ 3 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hP₁
  set P₂ : SmoothCcTensor g₀ 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 with hP₂
  refine ⟨(-2 : ℝ) • P₀, (-2 : ℝ) • P₁, (-2 : ℝ) • P₂, ?_, ?_, ?_, ?_⟩
  · intro x v
    set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
    set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
    set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
    have hRic :=
      ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
    have htoinfty : ∀ (g : SmoothRiemannianMetric I M),
        ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x (v 0) (v 1) =
          ricciTensor (I := I) g x (v 0) (v 1) := fun g => rfl
    have hPidentity :
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1) -
            ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀ W₀
              + appCc (I := I) (M := M) g₀ 3 2 P₁ W₁
              + appCc (I := I) (M := M) g₀ 4 2 P₂ W₂) x v := by
      rw [hRic]
      have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v
              + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v
              + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v := by
        rw [MeasureTheory.ae_iff]
        have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
        refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
        rw [Set.mem_setOf_eq, Classical.not_imp] at hs
        obtain ⟨hsmem, hsneq⟩ := hs
        rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
        exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply_tame,
          unitModel_add2_apply_tame])
      rw [intervalIntegral.integral_congr_ae hintegrand]
      have hI0 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Φ₀ W₀ hSI hc0 x v
      have hI1 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 3 Φ₁ W₁ hSI hc1 x v
      have hI2 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 Φ₂ W₂ hSI hc2 x v
      rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
        intervalIntegral.integral_add hI0 hI1]
      have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Φ₀ W₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
      have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Φ₁ W₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
      have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Φ₂ W₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
      rw [← hP₀] at he0
      rw [← hP₁] at he1
      rw [← hP₂] at he2
      rw [← he0, ← he1, ← he2, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame,
      unitModel_appCc_smul_left_apply_tame, unitModel_appCc_smul_left_apply_tame,
      unitModel_appCc_smul_left_apply_tame, htoinfty, htoinfty]
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame] at hPidentity
    linarith [hPidentity]
  · intro x
    have hsmul : ((-2 : ℝ) • P₀).toSection x = (-2 : ℝ) • P₀.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (P₀.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₀]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Φ₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x ΛR hΛR_nn
        ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb0 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 2 2 x (P₀.toSection x)]
  · intro x
    have hsmul : ((-2 : ℝ) • P₁).toSection x = (-2 : ℝ) • P₁.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (P₁.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₁]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Φ₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x ΛR hΛR_nn
        ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb1 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 3 2 x (P₁.toSection x)]
  · intro x
    have hsmul : ((-2 : ℝ) • P₂).toSection x = (-2 : ℝ) • P₂.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (P₂.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₂]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Φ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 x ΛR hΛR_nn
        ((hc2 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb2 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 4 2 x (P₂.toSection x)]

namespace DeTurckRemainderTameLipschitz

/-- **(POSITED deep bedrock — the VALUE-LEVEL (`unitModel`) ball-uniform order-graded Ricci-arm
linearization of the realized `(−2)`-scaled Ricci tensor difference, with order-`0` `C⁰` operator
fibre-norm sups.)**

The ball-uniform (`ΛR` outside the `∀ T T'` quantifier) form of the per-pair Ricci-arm grading
`deTurckRicciArm_appCc_graded` (`CovGrad/RicciDeTurckRicciArm.lean`): one nonnegative ball-uniform
order-`0` `C⁰` operator level `ΛR`, and for any two `g₀`-fibre-small `T, T'` whose covariant-`L²` jets up
to order `a + 2` lie in the radius-`R` ball, the three endpoint coefficient fields with the `∀ x v`
value identity and the order-`0` `C⁰` sups `rfns(Rₘ x) ≤ ΛR²`.

The genuine deep content (the Moser ball-uniformity of the realized Ricci-arm coefficient symbol over the
supercritical ball) is isolated in the child `exists_ricciArmCoeff_ballUniform_C0_sup`, which supplies the
ball-uniform `ΛR` together with, per fibre-small `(T, T')`, the three coefficient fields satisfying the
per-pair `negTwoRicciArm_appCc_eval` value identity AND the `C⁰` sups.  This node only bridges that
mul-form `(−2)·Ric`-arm value identity to the `smul`-form stated here (`smul_sub` / `smul_eq_mul` and the
transparency of `smoothRiemannianMetricToInfty := g` to `ricciTensor`).

**Non-vacuity.**  The `(value identity)` clause genuinely constrains the triple to *reproduce the
`(−2)`-scaled Ricci-arm difference value*; the zero triple fails it whenever the realized Ricci arm is
nonzero, and a `ΛR = 0` level is rejected by the nonvanishing genuine endpoint operator symbols on the
supercritical ball. -/
theorem deTurckRicciArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            (-2 : ℝ) •
                (ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ) x (v 0) (v 1)
                  - ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) := by
  classical
  obtain ⟨ΛR, hΛR_nn, hsup⟩ :=
    exists_ricciArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛR, hΛR_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨R₀, R₁, R₂, hval, hR₀, hR₁, hR₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  refine ⟨R₀, R₁, R₂, fun x v => ?_, hR₀, hR₁, hR₂⟩

  rw [smul_sub, smul_eq_mul, smul_eq_mul]
  exact hval x v

end DeTurckRemainderTameLipschitz

private noncomputable def realizedDeTurckLiePathValue
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  lieDerivMetricClm (I := I)
    (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1))
      (max_le zero_le_one (min_le_right s 1)))
    (deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le zero_le_one (min_le_right s 1))))
      (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w

private theorem realizedDeTurckLiePathValue_one
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (1 : ℝ) 1))
          (max_le zero_le_one (min_le_right (1 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

private theorem realizedDeTurckLiePathValue_zero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (0 : ℝ) 1))
          (max_le zero_le_one (min_le_right (0 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

namespace DeTurckRemainderTameLipschitz

noncomputable def linearizedDeTurckLieAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

noncomputable def realizedDeTurckLieChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ j,
    ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
      DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
          (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)

end DeTurckRemainderTameLipschitz

private theorem realizedDeTurckLieChartSum_contDiffAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s₀ := by
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_genJointGram
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedDeTurckLieChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_))
  refine contDiffAt_const.mul ?_
  have hjoint := DifferentialGeometry.PDE.DeTurck.RicciLinearization.gen_joint_chartLieDeTurckComp
    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
      (I := I) g₀ T T' hδ hδ') x hG g_bg i j hs hy
  have hcomp : (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
            (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
      (fun p : ℝ × E =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
            (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
        (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

private theorem realizedDeTurckLiePathValue_eq_chartSum_on_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  have hxgood : x ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) x :=
    DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le zero_le_one (min_le_right s 1)) =
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
          (I := I) g₀ T T' hδ hδ' s := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_inner_of_mem
        (I := I) g₀ T T' hδ hδ' hmem, hclamp]
  rw [realizedDeTurckLiePathValue, hmetric, lieDerivMetricClm_apply,
    realizedDeTurckLieChartSum]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetric_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [smoothRiemannianMetricToInfty]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetricMatrix_def_chart,
    DeTurckCoefficients.chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
      (I := I)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
        (I := I) g₀ T T' hδ hδ' s) g_bg x i j hxgood]

private theorem realizedDeTurckLiePathValue_differentiableAt_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ
      (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

namespace DeTurckRemainderTameLipschitz

theorem linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo ht)
  rw [linearizedDeTurckLieAt]
  exact Filter.EventuallyEq.deriv_eq heq

end DeTurckRemainderTameLipschitz

private theorem deriv_realizedDeTurckLieChartSum_continuousOn
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen (by exact_mod_cast le_top)

namespace DeTurckRemainderTameLipschitz

theorem linearizedDeTurckLieAt_intervalIntegrable
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedDeTurckLieChartSum_continuousOn (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w).mono
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

end DeTurckRemainderTameLipschitz

private theorem realizedDeTurckLiePathValue_continuousOn_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs

private theorem hasDerivAt_lieDeTurck_realizedMetricPath
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedDeTurckLieAt]
    exact (realizedDeTurckLiePathValue_differentiableAt_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w

namespace DeTurckRemainderTameLipschitz

theorem lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w -
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_lieDeTurck_realizedMetricPath (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont :=
    realizedDeTurckLiePathValue_continuousOn_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedDeTurckLiePathValue_one, realizedDeTurckLiePathValue_zero]

theorem hasDerivAt_realizedDeTurckLieChartSum_general
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          deriv (fun s : ℝ =>
            DeTurckCoefficients.chartLieDeTurckComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀) s₀ := by
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_genJointGram
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hbody : (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) := by
    funext s; rw [realizedDeTurckLieChartSum]
  rw [hbody]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun j _ => ?_)
  have hcontdiff : ContDiffAt ℝ ∞
      (fun s : ℝ => DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀ := by
    have hjoint := DifferentialGeometry.PDE.DeTurck.RicciLinearization.gen_joint_chartLieDeTurckComp
      (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG g_bg i j hmem hy
    have hcomp : (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
        (fun p : ℝ × E =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
          (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
    rw [hcomp]
    exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)
  exact ((hcontdiff.differentiableAt (by simp)).hasDerivAt).const_mul _

end DeTurckRemainderTameLipschitz

private noncomputable def deTurckLieArm0Field
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
    g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg

private theorem deTurckLieArm0Field_eq_coeffField
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckLieArm0Field (I := I) g₀ g_bg T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
        g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg :=
  rfl

section

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope lieDeTurckChartSlope_eq_orderSplit contMDiffOn_clm_section_of_pointwise_jointMR)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth deTurckLieArm2PrincipalCoeff_appCc_eq cometricFinBasisTrace_eq_chartInvGram_bilin unitModel4SlotBilin unitModel4SlotBilin_apply)

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

private theorem lieArm_shell_reduction
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Φ₀b : ℝ → SmoothCcTensor g₀ 2 2)
    (hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀b (δ := δ) (δ' := δ'))
    (hjAbsorb : ∀ (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ (2 + r) 2)
      (σ' : Equiv.Perm (Fin (2 + r))),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r) Φ (δ := δ) (δ' := δ') →
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r)
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ r (Φ s) σ') (δ := δ) (δ' := δ'))
    (hcore : ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
        lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
            (extChartAt I x x) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (Φ₀b s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
              + appCc (I := I) (M := M) g₀ 3 2
                (deTurckLieArm1Coeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
              + appCc (I := I) (M := M) g₀ 4 2
                (deTurckLieArm2PrincipalCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x
            ![(chartModelBasis E) i, (chartModelBasis E) j]) :
    ∃ (Φ₀L : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁L : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂L : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂L (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 0 (Φ₀b s) σ'₀,
    fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 1
      (deTurckLieArm1Coeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁,
    fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 2
      (deTurckLieArm2PrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂,
    hjAbsorb 0 Φ₀b σ'₀ hj0,
    hjAbsorb 1 _ σ'₁ (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    hjAbsorb 2 _ σ'₂
      (deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    ?_⟩
  intro s hs x v
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (Φ₀b s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    exact hcore s hs x i j
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2 (Φ₀b s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
      + appCc (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
      + appCc (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) with hWbase
  have hexpand : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
      unitModel (I := I) (M := M) g₀ 2 Wbase x v := by
    calc (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
          deriv (fun s : ℝ =>
            DeTurckCoefficients.chartLieDeTurckComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s)
        = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s :=
          Finset.sum_comm
      _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              unitModel (I := I) (M := M) g₀ 2 Wbase x
                ![(chartModelBasis E) i, (chartModelBasis E) j] := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
          rw [hcomp i j]
      _ = unitModel (I := I) (M := M) g₀ 2 Wbase x v :=
          unitModel_basis_expand_two (I := I) (M := M) g₀ Wbase x v
  rw [hexpand]
  have habs0 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T') (Φ₀b s) σ'₀ hσ'₀ x v
  have habs1 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T')
    (deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁ hσ'₁ x v
  have habs2 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T')
    (deTurckLieArm2PrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂ hσ'₂ x v
  rw [hWbase]
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  rw [habs0, habs1, habs2]

set_option linter.unusedSectionVars false in
private lemma lieArm2_appCc_value_invGram
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 4)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          (unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) l,
                (chartModelBasis E) j, (chartModelBasis E) k₁]
            + unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k₁]
            - unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) j,
                (chartModelBasis E) l, (chartModelBasis E) k₁]) := by
  classical
  refine (deTurckLieArm2PrincipalCoeff_appCc_eq (I := I) g₀ g₁ g_bg D x
    ![(chartModelBasis E) i, (chartModelBasis E) j]).trans ?_
  have hv0 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 0 = (chartModelBasis E) i := rfl
  have hv1 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 1 = (chartModelBasis E) j := rfl
  simp only [hv0, hv1]
  have hpack13 : ∀ (u w : TangentSpace I x) (c v : E),
      unitModel4SlotBilin (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        1 3 (by decide) ![(show E from u), 0, (show E from w), 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, c, w, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpack23 : ∀ (u w : TangentSpace I x) (c v : E),
      unitModel4SlotBilin (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        2 3 (by decide) ![(show E from u), (show E from w), 0, 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, w, c, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpat : ∀ (u w : TangentSpace I x),
      (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![u, (chartModelBasis E) l, w, (chartModelBasis E) k₁] := by
    intro u w
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel4SlotBilin (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          1 3 (by decide) ![(show E from u), 0, (show E from w), 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => (hpack13 u w _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack13 u w]
  have hpatH : (∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 D x
        ![(chartModelBasis E) i, (chartModelBasis E) j,
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![(chartModelBasis E) i, (chartModelBasis E) j,
              (chartModelBasis E) l, (chartModelBasis E) k₁] := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![(chartModelBasis E) i, (chartModelBasis E) j,
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel4SlotBilin (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          2 3 (by decide)
          ![(chartModelBasis E) i, (chartModelBasis E) j, 0, 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ =>
        (hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j) _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j)]
  rw [hpat ((chartModelBasis E) i) ((chartModelBasis E) j),
    hpat ((chartModelBasis E) j) ((chartModelBasis E) i), hpatH]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (domDomCongrSection_unitModel unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul arm2ReadoutCovDerivPair arm1ReadoutCovDeriv iteratedCovGrad2_chartComponent_readout iteratedCovGrad1_chartComponent_readout partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw eP2_swap covDerivLowerOrderTerm02_center_eq covDerivLowerOrderTerm03_center_eq euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE partialDeriv_scalarOnE_eq_euclidPartial_local toEuclidean_extChartAt_mem_chartTargetEuclid symm_toEuclidean_symm_toEuclidean_extChartAt)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (tensorChartComponentRaw_eq_chartFrame chartFrameBasisModel covDerivLowerOrderTerm euclidPartial euclidPartial_def covDerivComponent_lowerOrder_contDiffOn euclidPartial_chartPushedRaw_contDiffOn chartPushedRaw_tensorChartComponentRaw_contDiffOn)
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

set_option linter.unusedSectionVars false in
private lemma lieArm_frame0_eq_unitTensor (x b : M) :
    chartFrameBasisModel (I := I) (M := M) x b 0 ![] = unitTensor (I := I) (M := M) b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm_rawComponent_eq_unitModel_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx b =
      unitModel (I := I) (M := M) g s W b
        (fun j => (show E from chartBasisVecFiber (I := I) x (Jdx j) b)) := by
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W x hb ![] Jdx]
  rw [lieArm_frame0_eq_unitTensor (I := I) (M := M) x b]
  rfl

set_option linter.unusedSectionVars false in
private lemma lieArm_euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm_covDerivLowerOrderTerm_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) x) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ r s S x m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g₀ r s S x Idx' Jdx')
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma lieArm_euclidPartial_chartPushedRaw_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ r s S x k Idx Jdx
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma lieArm_unitModel4_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      euclidPartial (E := E) a
          (fun y' => euclidPartial (E := E) b
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              h x ![] ![c, d])) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c,
        chartModelBasis E d] : Fin 4 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c, d] : Fin 4 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 2)
    (iteratedCovGrad (I := I) g₀ 0 2 2 h) x (![a, b, c, d])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad2_chartComponent_readout (I := I) g₀ h x (![a, b, c, d])]
  have hJ0 : (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJ1 : (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) 0 = b := rfl
  have hJtail2 : Matrix.vecTail (Matrix.vecTail
      (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![c, d] := by
    funext j; fin_cases j <;> rfl
  simp only [arm2ReadoutCovDerivPair, hJ0, hJ1, hJtail2]
  have hPdiff : DifferentiableAt ℝ
      (euclidPartial (E := E) b
        (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d])))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_euclidPartial_chartPushedRaw_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  have hQdiff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d])
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_covDerivLowerOrderTerm_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  rw [lieArm_euclidPartial_add_local a hPdiff hQdiff]
  ring

set_option linter.unusedSectionVars false in
private lemma lieArm_unitModel3_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] ![b, c]))
          (toEuclidean (E := E) (extChartAt I x x))
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] :
        Fin 3 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c] : Fin 3 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 1)
    (iteratedCovGrad (I := I) g₀ 0 2 1 h) x (![a, b, c])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma lieArm_symmS_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (c d : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (symmS (I := I) (M := M) g S) x ![] ![c, d] b =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![c, d] b +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b) := by
  classical
  have hswap : tensorChartComponentRaw (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) x ![] ![c, d] b =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b := by
    rw [lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 _ x ![c, d] hb,
      lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 S x ![d, c] hb]
    rw [domDomCongrSection_unitModel (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g 2 S b t) ?_
    funext j
    fin_cases j <;> rfl
  rw [show symmS (I := I) (M := M) g S =
      (1 / 2 : ℝ) • (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) from rfl]
  rw [tensorChartComponentRaw_smul, tensorChartComponentRaw_add, hswap]
  rw [smul_eq_mul]

set_option linter.unusedSectionVars false in
lemma lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![c, d]) =ᶠ[𝓝 (extChartAt I x x)]
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d := by
  classical
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget, hev] with y hy_tgt hev_y
  rw [hev_y]
  have hb : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
  rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x c d hb]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
private lemma lieArm_partialDeriv_symmS_scalar_eventuallyEq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])) =ᶠ[𝓝 (extChartAt I x x)]
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d) := by
  have hev := (lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d).eventuallyEq_nhds
  filter_upwards [hev] with y hy
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hy.fderiv_eq]

set_option linter.unusedSectionVars false in
private lemma lieArm_U4_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
          (extChartAt I x x)
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
            (symmS (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d] := by
  classical
  rw [lieArm_unitModel4_basisChart_readout_split (I := I) (M := M) g₀
    (symmS (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg (fun t : ℝ =>
    t + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d]) ?_
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) (M := M) g₀
    (symmS (I := I) (M := M) g₀ (T - T')) x b a c d]
  have hev1 := lieArm_partialDeriv_symmS_scalar_eventuallyEq (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c d
  change fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])))
      (extChartAt I x x) ((chartModelBasis E) a) = fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
      (extChartAt I x x) ((chartModelBasis E) a)
  rw [hev1.fderiv_eq]

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma lieArm_U3_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c)
          (extChartAt I x x)
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀
            (symmS (I := I) (M := M) g₀ (T - T')) x ![a, b, c] := by
  classical
  rw [lieArm_unitModel3_basisChart_readout_split (I := I) (M := M) g₀
    (symmS (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg (fun t : ℝ =>
    t + arm1ReadoutCovDeriv (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ (T - T')) x ![a, b, c]) ?_
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialDeriv_scalarOnE_eq_euclidPartial_local (I := I) (M := M)
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
      (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![b, c]) x a hYmem
  rw [hround] at h
  rw [← h]
  have hev1 := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hev1.fderiv_eq]

set_option linter.unusedSectionVars false in
lemma lieArm_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b
        (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

set_option linter.unusedSectionVars false in
lemma lieArm_chartGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x a b
        (extChartAt I x x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

set_option linter.unusedSectionVars false in
lemma lieArm_chartInvGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x a b = chartInvGramMatrix (I := I) g x x b a := by
  have hherm : (DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x)⁻¹.IsHermitian :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_isHermitian (I := I) g x x).inv
  have h := congrFun (congrFun hherm a) b
  rw [Matrix.conjTranspose_apply, star_trivial] at h
  exact h.symm

set_option linter.unusedSectionVars false in
lemma lieArm_gram_invGram_collapse (g : SmoothRiemannianMetric I M) (x : M)
    (l j : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l) =
      if l = j then (1 : ℝ) else 0 := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  have hmul := DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
  have h := congrFun (congrFun hmul l) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
        chartInvGramMatrix (I := I) g x x k l) =
    ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x l k *
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieArm_chartInvGramMatrix_symm (I := I) g x k l]; ring)]
  rw [h]

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
private lemma lieArm_partialDeriv2_realizedGramDeriv_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) := by
  rw [partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₁ m₂ a b,
    partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₂ m₁ a b]
  rw [eP2_swap (I := I) g₀ (T - T') x m₂ m₁ a b, eP2_swap (I := I) g₀ (T - T') x m₂ m₁ b a]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

set_option linter.unusedSectionVars false in
private lemma lieArm_P2_halfCollapse
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (d e : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x e k₁))
              (extChartAt I x x)
            - (1 / 2 : ℝ) *
              DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) e
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁))
                (extChartAt I x x)) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  set CGM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g₁ x x a b with hCGM
  have hHB : ∀ k a b : Fin (Module.finrank ℝ E),
      chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
          (extChartAt I x x) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b) := by
    intro k a b
    rw [chartDeTurckCorrHessBlockRaw]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]
  have hstep1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
            chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
              (extChartAt I x x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        CGM k e * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CIM a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b)) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_chartGramOnE_center (I := I) g₁ x k e]
      refine congrArg (fun t : ℝ => CGM k e * t) ?_
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b, hHB k a b]]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [hstep1]
  have hstep2 : ∀ a b : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b)))) =
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b)) := by
    intro a b
    rw [Finset.sum_congr rfl (fun l _ => by
        rw [lieArm_gram_invGram_collapse (I := I) g₁ x l e] :
      ∀ l ∈ Finset.univ,
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) =
        CIM a b * ((1 / 2 : ℝ) *
          ((if l = e then (1 : ℝ) else 0) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))))]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl, one_mul]
    · intro l _ hl
      rw [if_neg hl, zero_mul, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep2 a b))]
  have hterm1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d a e b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d l e k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hterm3 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d e l k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b))) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d a e b))
      + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d b e a))
      - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit, hterm1, hterm3]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm2PrincipalCoeff_appCc_eq cometricFinBasisTrace_eq_chartInvGram_bilin unitModel4SlotBilin unitModel4SlotBilin_apply)

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma lieArm_arm2_value_eq_principal_add_tail
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        + ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set R4 : (Fin 4 → Fin (Module.finrank ℝ E)) → ℝ := fun Jdx =>
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ (T - T')) x Jdx with hR4
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  rw [lieArm2_appCc_value_invGram (I := I) g₀ g₁ g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x i j]
  have hU4 : ∀ a b c d : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x
          ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
        pd2 a b c d + R4 ![a, b, c, d] := fun a b c d =>
    lieArm_U4_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b c d
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => by
      rw [hU4 i l j k₁, hU4 j l i k₁, hU4 i j l k₁] :
    ∀ l ∈ Finset.univ,
      chartInvGramMatrix (I := I) g₁ x x k₁ l *
        (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E l, chartModelBasis E j, chartModelBasis E k₁]
          + unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E l, chartModelBasis E i, chartModelBasis E k₁]
          - unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E l, chartModelBasis E k₁]) =
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))))]
  have hsplit : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (pd2 i l j k₁ + pd2 j l i k₁ - pd2 i j l k₁))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (R4 ![i, l, j, k₁] + R4 ![j, l, i, k₁] - R4 ![i, j, l, k₁])) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hsplit]
  refine congrArg (fun t : ℝ => t + _) ?_
  rw [show chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x) =
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k j (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i a b k
                (extChartAt I x x)) +
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x)) from rfl]
  rw [Finset.sum_congr rfl (fun k _ => by
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g₁ x i k
        (extChartAt I x x)] :
    ∀ k ∈ Finset.univ,
      chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x) =
      chartGramOnE (I := I) g₁ x k i (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x))]
  rw [lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j,
    lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [hpd2]
  rw [lieArm_partialDeriv2_realizedGramDeriv_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i j l k₁]
  ring

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private def lieArm_slot34Eval (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u w : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => F c v u w
          map_add' := fun v₁ v₂ => by simp
          map_smul' := fun r v => by simp }
      map_add' := fun c₁ c₂ => by
        ext v
        simp
      map_smul' := fun r c => by
        ext v
        simp }

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_slot34Eval_apply (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u w c v : E) :
    lieArm_slot34Eval (E := E) F u w c v = F c v u w := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_cometric_doubleTrace_eq_invGram
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l)
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              F (chartModelBasis E m) (chartModelBasis E l₁)
                (chartModelBasis E p) (chartModelBasis E k₁)) := by
  classical
  have hinner : ∀ c v : E,
      (∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) c v) =
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ)) c v := by
    intro c v
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ))
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => (hinner _ _))]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [smul_eq_mul]
  rw [show (∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k₁ p *
        (chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁))) =
    chartInvGramMatrix (I := I) g₁ x x k₁ p *
      ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l₁ _ => ?_)
    rw [Finset.mul_sum]]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k₁ p * t) ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) (chartModelBasis E p) (chartModelBasis E k₁)) =
    ∑ l : Fin (Module.finrank ℝ E),
      lieArm_slot34Eval (E := E) F (chartModelBasis E p) (chartModelBasis E k₁)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) from
    Finset.sum_congr rfl (fun l _ => rfl)]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [smul_eq_mul]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel3SlotBilin metricConnDiffLoweredTrilin metricConnDiffLoweredTrilin_apply deTurckLieArm1Coeff deTurckLieArm1Coeff_appCc_eq)

set_option linter.unusedSectionVars false in
private lemma lieArm_unitModel3SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) (c v : E) :
    unitModel3SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
private def lieArm_F4mul (A B : E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => LinearMap.toContinuousLinearMap
            { toFun := fun c' => LinearMap.toContinuousLinearMap
                { toFun := fun v' => A c c' * B v v'
                  map_add' := fun v₁ v₂ => by
                    simp [LinearMap.toContinuousLinearMap, map_add,
                      ContinuousLinearMap.add_apply, mul_add]
                  map_smul' := fun r v' => by
                    simp [LinearMap.toContinuousLinearMap, map_smul,
                      ContinuousLinearMap.smul_apply, smul_eq_mul]
                    ring }
              map_add' := fun c₁ c₂ => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_add,
                  ContinuousLinearMap.add_apply, add_mul]
              map_smul' := fun r c' => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_smul,
                  ContinuousLinearMap.smul_apply, smul_eq_mul]
                ring }
          map_add' := fun v₁ v₂ => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_add,
              ContinuousLinearMap.add_apply, mul_add]
          map_smul' := fun r v => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_smul,
              ContinuousLinearMap.smul_apply, smul_eq_mul]
            ring }
      map_add' := fun c₁ c₂ => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_add,
          ContinuousLinearMap.add_apply, add_mul]
      map_smul' := fun r c => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in
private lemma lieArm_F4mul_apply (A B : E →L[ℝ] E →L[ℝ] ℝ) (c v c' v' : E) :
    lieArm_F4mul (E := E) A B c v c' v' = A c c' * B v v' := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedSectionVars false in
private def lieArm_fix3 (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (e : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f c v e
          map_add' := fun v₁ v₂ => by
            simp [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun r v => by
            simp [map_smul, ContinuousLinearMap.smul_apply] }
      map_add' := fun c₁ c₂ => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_add, ContinuousLinearMap.add_apply]
      map_smul' := fun r c => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_smul, ContinuousLinearMap.smul_apply] }

set_option linter.unusedSectionVars false in
private lemma lieArm_fix3_apply (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (e c v : E) :
    lieArm_fix3 (E := E) f e c v = f c v e := rfl

set_option linter.unusedSectionVars false in
private lemma lieArm_doubleTrace_slotBilin
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i₁ i₂ : Fin 3) (h12 : i₁ ≠ i₂) (base : Fin 3 → E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)))
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) *
          B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
                  (chartModelBasis E m) (chartModelBasis E p) *
                B (chartModelBasis E l₁) (chartModelBasis E k₁))) := by
  classical
  have hbrick := lieArm_cometric_doubleTrace_eq_invGram (I := I) g₁ x
    (lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B)
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) *
        B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))]
  · rw [hbrick]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [lieArm_F4mul_apply]
  · rw [lieArm_F4mul_apply]

set_option linter.unusedSectionVars false in
private lemma lieArm_slot12_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![w, 0, 0] c v = W3 ![w, c, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

set_option linter.unusedSectionVars false in
private lemma lieArm_slot02_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, w, 0] c v = W3 ![c, w, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_arm1_group_traced
    (g₀X g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1)
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))) =
    ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1)))
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))) := by
  classical
  have hT2 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT3 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] (lieArm_fix3 (E := E) (metricConnDiffLoweredTrilin (I := I) g₁ g₁ g_bg x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT5 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] (((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0).flip)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT7 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT6 : (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁]) := by
    have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
      (unitModel3SlotBilin (E := E) W3 0 2 (by decide)
        ![0, (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0])
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_slot02_pack]
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      rw [smul_eq_mul, lieArm_slot02_pack]
  rw [hT2, hT3, hT5, hT7, hT6]

set_option linter.unusedSectionVars false in
private lemma lieArm_arm1_T14_traced
    (g₀X g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide)
      ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0, 0])
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lieArm_slot12_pack]
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    rw [smul_eq_mul, lieArm_slot12_pack]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_arm1_value_traced
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 3)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg) D) x
        ![chartModelBasis E i, chartModelBasis E j] =
      unitModel (I := I) (M := M) g₀ 3 D x
        ![(show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
          chartModelBasis E i, chartModelBasis E j]
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E j))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), (chartModelBasis E j),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E i))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), (chartModelBasis E i),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E i)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  refine (deTurckLieArm1Coeff_appCc_eq (I := I) g₀ g₁ g_bg D x
    ![chartModelBasis E i, chartModelBasis E j]).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E j) (chartModelBasis E i)
  · exact lieArm_arm1_T14_traced (I := I) g₀ g₁ x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma lieArm_inner_chartBasis_center (g : SmoothRiemannianMetric I M) (x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    g.inner x ((chartModelBasis E) p : TangentSpace I x)
        ((chartModelBasis E) q : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x p q := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x q]

set_option linter.unusedSectionVars false in
lemma lieArm_connDiff_chartBasis_center
    (gA gB : SmoothRiemannianMetric I M) (x : M) (j k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connDiff (I := I) gA gB x
        ((chartModelBasis E) j : TangentSpace I x)
        ((chartModelBasis E) k : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x k j p
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x k j p
            (extChartAt I x x)) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [show ((chartModelBasis E) j : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x j x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x j).symm]
  rw [show ((chartModelBasis E) k : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x k x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x k).symm]
  rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) gA gB x
    (DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
    j k]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_bilin_expand_fst (F : E →L[ℝ] E →L[ℝ] ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) (v : E) :
    F (∑ q : Fin (Module.finrank ℝ E), c q • w q) v =
      ∑ q : Fin (Module.finrank ℝ E), c q * F (w q) v := by
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_bilin_expand_snd (F : E →L[ℝ] E →L[ℝ] ℝ) (u : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) :
    F u (∑ q : Fin (Module.finrank ℝ E), c q • w q) =
      ∑ q : Fin (Module.finrank ℝ E), c q * F u (w q) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_sum_slot0
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (u v : E) :
    W3 ![∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, u, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![chartModelBasis E q, u, v] := by
  refine ((lieArm_slot02_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, u, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot02_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_sum_slot1
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u : E) (c : Fin (Module.finrank ℝ E) → ℝ) (v : E) :
    W3 ![u, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, chartModelBasis E q, v] := by
  refine ((lieArm_slot12_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_sum_slot2
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u v : E) (c : Fin (Module.finrank ℝ E) → ℝ) :
    W3 ![u, v, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, v, chartModelBasis E q] := by
  refine ((lieArm_slot12_pack (E := E) W3 u v
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q)).symm).trans ?_
  refine (lieArm_bilin_expand_snd (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) v c
    (fun q => chartModelBasis E q)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u v (chartModelBasis E q))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_inner_connDiff_chartBasis_value
    (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c d : Fin (Module.finrank ℝ E)) :
    gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (chartModelBasis E a) (chartModelBasis E c))
        (chartModelBasis E d) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) gm x x q d := by
  refine (congrArg (fun t : TangentSpace I x => gm.inner x t (chartModelBasis E d))
    (lieArm_connDiff_chartBasis_center (I := I) gA gB x a c)).trans ?_
  refine (lieArm_bilin_expand_fst (E := E) (gm.inner x)
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x))
    (fun q => chartModelBasis E q) (chartModelBasis E d)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul _) (lieArm_inner_chartBasis_center (I := I) gm x q d)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_deTurckVF_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![(show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x), u, v] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![chartModelBasis E w, u, v] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![t, u, v]) hW).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_deTurckVF_slot2_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![u, v, (show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x)] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![u, v, chartModelBasis E w] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![u, v, t]) hW).trans ?_
  exact lieArm_U3_sum_slot2 (E := E) W3 u v
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_connDiff_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![(show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), u, v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![chartModelBasis E q, u, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![t, u, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma lieArm_U3_connDiff_slot1_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![u, (show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![u, chartModelBasis E q, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![u, t, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot1 (E := E) W3 u
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) v

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
lemma lieArm_arm1_value_realized
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j] =
      (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x i j q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) := by
  classical
  refine (lieArm_arm1_value_traced (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x i j).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · exact lieArm_U3_deTurckVF_slot0_value (I := I)
      (unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
      (chartModelBasis E i) (chartModelBasis E j)
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ j)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E i) (chartModelBasis E j)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ i)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E j) (chartModelBasis E i)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j i
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    exact congrArg (HMul.hMul _)
      (lieArm_U3_connDiff_slot0_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
        (chartModelBasis E p) (chartModelBasis E k₁))

end DeTurckRemainderTameLipschitz

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
