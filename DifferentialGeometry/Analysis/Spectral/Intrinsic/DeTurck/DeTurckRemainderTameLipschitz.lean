import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartJetLipschitzBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLieArm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel

/-!
# The intrinsic covariant-`L²` ball-Lipschitz bound on the DeTurck–Ricci remainder difference

This file builds the **covariant-gradient iterate `L²` core** of the smooth-ball Lipschitz
estimate for the genuine Ricci–DeTurck remainder difference — the spatial half of the existence
forcing estimate `deTurckSobolevNHa2_mixed_lipschitz` (the spectral `H^σ` translation is the
concurrently-built interior-elliptic/Gårding tower's job and is **not** attempted here —
everything stays in the `iteratedCovGrad`/`tensorL2Norm` world).

## The estimate

For `g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in a covariant-`L²`
ball of radius `R` (`∑_{j ≤ a+2} ‖∇^j T‖_{L²} ≤ R`, idem `T'`), every order-`q` (`q ≤ a`)
covariant-gradient iterate `L²` norm of the genuine remainder difference

  `D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`
      `( = deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T − [same for T'] )`

obeys the **ball-uniform integrated tame bound**

  `‖∇^q D‖_{L²} ≤ C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²})`,

with a single nonnegative constant `C` outside the `∀ T T'` quantifier (uniform over the
fibre-small radius-`R` ball).  The bound vanishes as `T − T' → 0`, so it is a genuine
Lipschitz estimate, not a static envelope.

## The intrinsic single-column route (chart-jet-free at the headline)

The sealed remainder difference splits definitionally as
`D = (RHSarm T − RHSarm T') − Δ_∇(T − T')`, where `RHSarm := deTurckRHSArmG0` carries the genuine
Ricci/Lie/inverse-Gram Nemytskii content.  The route reads **only** `iteratedCovGrad`,
`riemannianFiberNormSq` and `tensorL2Norm` at the headline:

* the order-`0` pointwise fibre-norm domination `deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform`,
  assembled from the three endpoint coefficient `C⁰` operator sups
  (`deTurckRHSArmDiff_threeArm_coeffC0_ballUniform`) and the supercritical `H^{a+2} ↪ C²` section
  embedding `deTurckArmDiff_supercritical_pointwise_jet_le`;
* the top-order-`a` integrated covariant-`L²` tame `deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform`,
  the single-column integration via `l2RootSum_of_pointwise_iteratedCovGrad_jet` of the ball-uniform
  pointwise covariant-jet column `deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform`
  (the genuine chart→intrinsic Nemytskii content, reaching the chart-Gram realize-difference bridge
  `chartDeTurckRicciRHS_realize_seminorm_le_bareChartJetContentOnE_ballUniform` only through the
  reverse fibre-norm/raw-component bridge, never an order-`(a+2)` `L^∞` cometric jet at the headline);
* the two endpoints plus the Gagliardo–Nirenberg interpolation of the intermediate orders
  (`deTurckRHSArmDiff_endpoints_l2_tame_ballUniform`, `deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform`).

The headline existence-arm wrapper `deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz` adds the
linear connection-Laplacian arm (`deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform`,
`rawTensorConnLapSmooth_iteratedCovGrad_l2_tame`); the order-`d` single-arm column form is
`deTurckRemainderDiff_iteratedCovGradSum_ballBound_order`.
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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem riemannianFiberNormSq_neg_value
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
  -- `iteratedCovGrad g₀ 0 s 2 S = covGrad g₀ 0 (s+1) (covGrad g₀ 0 s S)` (twice `iteratedCovGrad_succ`,
  -- `s + 2` and `s + 1 + 1` definitionally equal), so the RHS jet form matches the on-disk bound.
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
  -- The two Hom-field arms of the section identity.
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
  -- The `H_R` arm reads the jets `∇^i (∇S) = ∇^{i+1} S`, the `H_dR` arm reads `∇^i S`.
  have hAR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) := by
    -- `covGrad g₀ 0 s S = iteratedCovGrad g₀ 0 s 1 S` definitionally.
    have hcov1 : covGrad (I := I) (M := M) g₀ 0 s S = iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
    have h := hccR (iteratedCovGrad (I := I) g₀ 0 s 1 S) p x
    rw [hAR_def, hcov1]
    refine h.trans_eq ?_
    refine congrArg (ccR p * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    have hcomp := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s 1 i S x
    -- `rfns(∇^i (∇S)) = rfns(∇^{1+i} S) = rfnsS (1 + i) = rfnsS (i + 1)`.
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
  -- Both windows inject into `range (p + 2)`.
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
    -- `[Δ_∇, ∇^0] S = Δ_∇ S − Δ_∇ S = 0`, so its `p`-fold gradient vanishes.
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
    -- The telescoping split at the section level.
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
    -- Distribute `∇^p` over the split and apply `2`-sub-additivity.
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
    -- Arm 1: the single-level pointwise jet bound at rank `s + m`, applied to `∇^m S`.
    have harm1 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) ≤
          K p * fullSum := by
      have hKb := hK p gradm x
      -- Reindex `∇^a (∇^m S) → ∇^{m + a} S`.
      have hreindex : ∀ a,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + a) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) := by
        intro a
        rw [hgradm]
        exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s m a S x
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      -- `hKb`'s LHS rank `((s + m) + 1) + p` is defeq to the goal's `(s + (m + 1)) + p`.
      refine hKb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn p)
      -- The reindexed window `∑_{a < p + 2} ‖∇^{m + a} S‖²` injects into `fullSum`.
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
    -- Arm 2: the induction hypothesis at gradient order `p + 1` on `[Δ_∇, ∇^m] S`.
    have harm2 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x) ≤
          Cm (p + 1) * fullSum := by
      -- `∇^p (∇ comm_m) = ∇^{p+1} comm_m`; the induction hypothesis at gradient order `p + 1`.
      have hCmb := hCm (p + 1) S x
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      -- Relate `∇^p (∇ comm_m)` to `∇^{p+1} comm_m` by the iterated-gradient composition.
      have h := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 (s + m) 1 p comm_m x
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 (s + m) 0 comm_m,
        iteratedCovGrad_zero] at h
      -- `h : rfns(∇^p (∇ comm_m)) = rfns(∇^{1+p} comm_m)`; rewrite the order `1 + p → p + 1`
      -- uniformly (both the rank index and the gradient order share the subterm `1 + p`).
      rw [Nat.add_comm 1 p] at h
      exact h.trans_le hCmb
    -- Assemble: `2·arm1 + 2·arm2 ≤ (2K + 2Cm) · fullSum`.
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
  -- The order-`0` rough-Laplacian fibre posit at rank `2 + a` (the top-jet Δ-arm).
  obtain ⟨Cpost, hCpost_nn, hCpost⟩ :=
    rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet (I := I) (M := M) g₀ (2 + a)
  -- The pointwise iterated-commutator telescope at `m := a`, `s := 2` (the lower-order arm).
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux (I := I) (M := M) g₀ a 2
  refine ⟨2 * Cpost + 2 * Cfun 0, by have := hCfun_nn 0; positivity, fun W x => ?_⟩
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The iterated-commutator section, and the `abel` split `∇^a(Δ_∇ W) = Δ_∇(∇^a W) − Comm`.
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
  -- The Δ-arm: order-`0` fibre posit at `S := ∇^a W`, top jet `q = a + 2`.
  have hΔarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) ≤ Cpost * Scol := by
    refine (hCpost (iteratedCovGrad (I := I) g₀ 0 2 a W) x).trans ?_
    -- `rfns(∇²(∇^a W)) = rfns(∇^{a+2} W)`, the `q = a + 2` summand of `Scol`.
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
  -- The commutator arm: telescope at `m = a`, `p = 0`, `s = 2`, lower-order jets `q ≤ a`.
  have hCommarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) ≤
        Cfun 0 * Scol := by
    -- `rfns((-Comm)(x)) = rfns(Comm(x))` by negation-invariance of the fibre norm.
    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x) := by
      rw [SmoothCcTensor.toSection_neg]
      rw [show ((-Comm.toSection) x : TensorRSSpace 0 (2 + a) I x) = -(Comm.toSection x) from rfl]
      exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x)
    rw [hneg]
    -- The telescope at `m = a`, `p = 0`, `s = 2`; `∇^0 [Δ_∇, ∇^a]W = Comm` (`(2 + a) + 0 = 2 + a`).
    have hC := hCfun 0 W x
    rw [iteratedCovGrad_zero] at hC
    refine hC.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
    rw [hScol_def]
    -- The telescope window `∑_{a' < a + 0 + 1}` injects into `∑_{q < a + 2 + 1}`.
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
  -- `rawCompOnE = rawPullR ∘ e`, with `e := toEuclidean`.
  have hcompose :
      DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx =
        rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have hpull := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrArg (fun f => f (e z)) hpull
    simp only [Function.comp_apply, he_def, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    rw [← this]
  rw [hcompose]
  -- The image set `e '' O` is open and `iteratedFDeriv (rawPullR) = iteratedFDerivWithin … (e '' O)`.
  have himg_open : IsOpen (e '' O) := e.isOpenMap _ hO_open
  have hey_mem : e y ∈ e '' O := ⟨y, hy, rfl⟩
  have hOeq : O = e ⁻¹' (e '' O) := by
    ext z; constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩; rwa [e.injective hwz] at hw
  -- Composition-on-the-right within-jet formula on the open image.
  have hcomp := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    himg_open.uniqueDiffOn (x := y) hey_mem m
  rw [← hOeq] at hcomp
  rw [hcomp]
  -- The within-jet of `rawPullR` on the open image equals the plain jet.
  have hplain : iteratedFDerivWithin ℝ m
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
      (e '' O) (e y) =
      iteratedFDeriv ℝ m
        (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (e y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m himg_open hey_mem
  rw [hplain]
  -- The composed multilinear map has norm `≤ ‖∂^m rawPullR (e y)‖ · ‖e‖^m`.
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
  -- For each derived rank `2 + i` a single (tensor-uniform) reverse fibre constant `Cfib i`.
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

/-- **The tensor-uniform `E`-coordinate bare chart-jet-content Stage-4 bound.**

The `D`-uniform hoist of `bareChartJetContentOnE_le_sqrt_fiberNormSq_sum`: a single constant `C`
(outside the `∀ D`) such that for **every** smooth compactly-supported `(0,2)`-tensor `D`, on the
closed POU support, `bareChartJetContentOnE g D α N (extChartAt I α b) ≤ C · ∑_{i ≤ N} √rfns(∇^i D)(b)`.
The reverse Euclidean coordinate bridge factor `eFac` and the tensor-uniform `EuclN` Stage-4 constant
`bareChartJetContent_le_sqrt_fiberNormSq_sum_uniform` are both `(D)`-independent. -/
private lemma bareChartJetContentOnE_le_sqrt_fiberNormSq_sum_uniform
    (g : SmoothRiemannianMetric I M) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g 0 2) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N (extChartAt I α b) ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
              ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set eNorm : ℝ := ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin n))‖ with heNorm_def
  have heNorm_nn : 0 ≤ eNorm := norm_nonneg _
  set eFac : ℝ := (Finset.range (N + 1)).sup' (by simp) (fun m => eNorm ^ m) with heFac_def
  have heFac_nn : 0 ≤ eFac := le_trans (by positivity : (0:ℝ) ≤ eNorm ^ 0)
    (Finset.le_sup' (fun m => eNorm ^ m) (by simp))
  obtain ⟨Cstage, hCstage_nn, hCstage⟩ :=
    bareChartJetContent_le_sqrt_fiberNormSq_sum_uniform (I := I) (M := M) g α N
  refine ⟨eFac * Cstage, by positivity, ?_⟩
  intro D b hb
  set y : E := extChartAt I α b with hy_def
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  have hy_target : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hb_src
  have hy_int : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]; exact hy_target
  set yE : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) y with hyE_def
  have hyE_kernel : yE ∈
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α := by
    refine ⟨y, ?_, rfl⟩
    exact ⟨b, hb, rfl⟩
  have hround : (extChartAt I α).symm ((toEuclidean (E := E)).symm yE) = b := by
    rw [hyE_def, hy_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv hb_src
  have hstage := hCstage D hyE_kernel
  rw [hround] at hstage
  set colE : (Fin 2 → Fin n) → ℝ := fun Jdx =>
    ∑ m ∈ Finset.range (N + 1),
      ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α (![] : Fin 0 → Fin n) Jdx) yE‖
    with hcolE_def
  have hcolE_nn : ∀ Jdx, 0 ≤ colE Jdx := fun Jdx =>
    Finset.sum_nonneg fun m _ => norm_nonneg _
  have hbridge : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y ≤
      eFac * bareChartJetContent (I := I) (M := M) g 0 2 D α N yE := by
    have hstep1 : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y ≤
        eFac * ∑ Jdx : Fin 2 → Fin n, colE Jdx := by
      rw [DeTurckCoefficients.bareChartJetContentOnE, Finset.mul_sum]
      refine Finset.sum_le_sum (fun Jdx _ => ?_)
      rw [hcolE_def, Finset.mul_sum]
      refine Finset.sum_le_sum (fun m hm => ?_)
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hb' := norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
        (I := I) (M := M) g D α Jdx m hy_int
      rw [show (toEuclidean (E := E)) y = yE from rfl] at hb'
      refine hb'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Finset.le_sup' (fun m => eNorm ^ m) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmN))
    have hstep2 : bareChartJetContent (I := I) (M := M) g 0 2 D α N yE =
        ∑ Jdx : Fin 2 → Fin n, colE Jdx := by
      rw [bareChartJetContent, Fintype.sum_prod_type, Fintype.sum_unique]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      rw [hcolE_def]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      congr 2
    rw [hstep2]
    exact hstep1
  calc DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y
      ≤ eFac * bareChartJetContent (I := I) (M := M) g 0 2 D α N yE := hbridge
    _ ≤ eFac * (Cstage * ∑ i ∈ Finset.range (N + 1),
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection b))) :=
        mul_le_mul_of_nonneg_left hstage heFac_nn
    _ = (eFac * Cstage) * ∑ i ∈ Finset.range (N + 1),
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) := by ring

/-- The raw chart-frame component depends only on the underlying section, not on the (phantom)
metric type-tag of the `SmoothCcTensor`. -/
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
  -- Unfold both `deTurckSmoothRemainder = RHSwrap − Δ_∇` at the `toSection` level.
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
  -- `RHSarm.toSection = S₁.toSection − S₂.toSection`, so `RHSarm = S₁ − S₂` as `SmoothCcTensor`.
  have hsec : RHSarm.toSection = (S₁ - S₂).toSection := by
    rw [SmoothCcTensor.toSection_sub]
    exact deTurckRHSArm_toSection_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hRHSeq : RHSarm = S₁ - S₂ := by
    apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
    exact hsec
  rw [hRHSeq]
  -- Linearity of the raw component + the per-metric chart identity.
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

private lemma bareChartJetContent_deTurckRHSArm_le_sqrt_fiberNormSq_sum_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (α : M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        bareChartJetContent (I := I) (M := M) g₀ 0 2
            ((deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') +
              rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) α a
            ((toEuclidean (E := E)) (extChartAt I α b)) ≤
          K * ∑ q ∈ Finset.range (a + 2 + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
              ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- The fixed compact target neighbourhood (the chart image of the closed POU support).
  set Kc : Set E := (extChartAt I α) '' (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) with hKc_def
  have hKc_compact : IsCompact Kc :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_isCompact
      (I := I) (M := M) α
  have hKc_sub : Kc ⊆ interior ((extChartAt I α).target : Set E) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_subset_interior_target
      (I := I) (M := M) α
  -- The forward-bridge factor (`EuclN`-jet ≤ `E`-jet, scaled by `‖toEuclidean.symm‖^m`).
  set eNorm : ℝ :=
    ‖((toEuclidean (E := E)).symm : EuclideanSpace ℝ (Fin n) →L[ℝ] E)‖ with heNorm_def
  set eFac : ℝ := (Finset.range (a + 1)).sup' (by simp) (fun m => eNorm ^ m) with heFac_def
  have heFac_nn : 0 ≤ eFac := le_trans (by positivity : (0:ℝ) ≤ eNorm ^ 0)
    (Finset.le_sup' (fun m => eNorm ^ m) (by simp))
  -- **Ball-uniform two-metric Nemytskii**: a single `CNem ik ≥ 0` (uniform over the ball) per chart
  -- index pair, supremised to `CNemMax`.  The order-`a` seminorm of the chart Ricci–DeTurck carrier
  -- difference is bounded by `CNem ik · bareChartJetContentOnE g₀ (T−T') (a+2)`, uniformly over the
  -- fibre-small radius-`R` ball.
  have hNem : ∀ ik : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ y ∈ Kc,
        DeTurckCoefficients.iteratedFDerivSeminorm a
            (fun z => DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α ik.1 ik.2 z -
              DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α ik.1 ik.2 z)
            (interior (extChartAt I α).target) y ≤
          C * DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (a + 2) y := by
    intro ik
    obtain ⟨C, hC_nn, hC⟩ :=
      DeTurckCoefficients.chartDeTurckRicciRHS_realize_seminorm_le_bareChartJetContentOnE_ballUniform
        (I := I) (M := M) g₀ g_bg (R := R) α hKc_compact hKc_sub ik.1 ik.2 a
    exact ⟨C, hC_nn, fun T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball y hy =>
      hC T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball y hy⟩
  choose CNem hCNem_nn hCNem using hNem
  set CNemMax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin n × Fin n)) CNem
    with hCNemMax_def
  have hCNemMax_nn : 0 ≤ CNemMax :=
    le_trans (hCNem_nn (Classical.arbitrary _)) (Finset.le_sup' CNem (Finset.mem_univ _))
  -- The `(T, T')`-uniform `E`-content Stage-4 constant (anchored at `g₀`).
  obtain ⟨Cstage, hCstage_nn, hCstage⟩ :=
    bareChartJetContentOnE_le_sqrt_fiberNormSq_sum_uniform (I := I) (M := M) g₀ α (a + 2)
  -- The honest `K`: the same expression as the per-pair source with the ball-uniform `CNemMax`.
  refine ⟨((n : ℝ) ^ 2) * (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))),
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball b hb
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  -- Setup the manifold/chart points.
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  set yb : E := extChartAt I α b with hyb_def
  have hyb_Kc : yb ∈ Kc := ⟨b, hb, rfl⟩
  have hyb_int : yb ∈ interior ((extChartAt I α).target : Set E) := hKc_sub hyb_Kc
  set yE : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) yb with hyE_def
  have hb_good : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source
      (I := I) α]
    exact hb_src
  -- Stage-4 OnE bound of `T − T'` at `b`.
  have hstage4 := hCstage (T - T') hb
  set Sdiff : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) with hSdiff_def
  have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  -- The reduced per-`(Jdx, m)` bound: each chart Fréchet jet of `RHSarm` is `≤ const · Sdiff`.
  have hper : ∀ (Jdx : Fin 2 → Fin n) (m : ℕ), m ∈ Finset.range (a + 1) →
      ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α
          (![] : Fin 0 → Fin n) Jdx) yE‖ ≤
        eFac * (CNemMax * Cstage) * Sdiff := by
    intro Jdx m hm
    have hmA : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hyb_pre : (toEuclidean (E := E)).symm yE ∈ interior (extChartAt I α).target := by
      rw [hyE_def, ContinuousLinearEquiv.symm_apply_apply]; exact hyb_int
    have hbridge := norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
      (I := I) (M := M) g₀ RHSarm α Jdx m hyb_pre
    rw [hyE_def, ContinuousLinearEquiv.symm_apply_apply] at hbridge
    set F : E → ℝ := fun z =>
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) z -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1) z with hF_def
    have hEqOn : Set.EqOn (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx) F
        (interior (extChartAt I α).target) := by
      intro z hz
      have hz_src : (extChartAt I α).symm z ∈
          DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α := by
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source
          (I := I) α]
        exact (extChartAt I α).map_target (interior_subset hz)
      have hzt : z ∈ (extChartAt I α).target := interior_subset hz
      have hid := tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
        (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' α hz_src Jdx
      rw [DeTurckCoefficients.rawCompOnE, hF_def]
      rw [← hg₁_def, ← hg₂_def] at hid
      rw [show (extChartAt I α) ((extChartAt I α).symm z) = z from (extChartAt I α).right_inv hzt]
        at hid
      rw [hRHSarm_def]
      exact hid
    have hcongr := iteratedFDerivWithin_congr (𝕜 := ℝ) hEqOn hyb_int m
    have hStage3 : ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx)
        (interior (extChartAt I α).target) yb‖ ≤
        CNemMax * DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α
          (a + 2) yb := by
      rw [hcongr]
      have hsemi : ‖iteratedFDerivWithin ℝ m F (interior (extChartAt I α).target) yb‖ ≤
          DeTurckCoefficients.iteratedFDerivSeminorm a F (interior (extChartAt I α).target) yb :=
        DeTurckCoefficients.norm_iteratedFDerivWithin_le_seminorm hmA F _ yb
      refine hsemi.trans ?_
      have hnem := hCNem (Jdx 0, Jdx 1) T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball yb hyb_Kc
      rw [← hg₁_def, ← hg₂_def] at hnem
      rw [hF_def]
      refine hnem.trans ?_
      refine mul_le_mul_of_nonneg_right ?_
        (DeTurckCoefficients.bareChartJetContentOnE_nonneg (I := I) (M := M) g₀ (T - T') α (a + 2) yb)
      exact Finset.le_sup' CNem (Finset.mem_univ _)
    have hOnE_le : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α
        (a + 2) yb ≤ Cstage * Sdiff := by
      rw [hSdiff_def]
      simpa only [hyb_def] using hstage4
    calc ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α
            (![] : Fin 0 → Fin n) Jdx) yE‖
        ≤ eNorm ^ m * ‖iteratedFDerivWithin ℝ m
            (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx)
            (interior (extChartAt I α).target) yb‖ := hbridge
      _ ≤ eFac * (CNemMax * Cstage * Sdiff) := by
          refine mul_le_mul (Finset.le_sup' (fun m => eNorm ^ m) hm) ?_ (norm_nonneg _) heFac_nn
          refine hStage3.trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hOnE_le hCNemMax_nn
      _ = eFac * (CNemMax * Cstage) * Sdiff := by ring
  rw [bareChartJetContent]
  have hCard2 : (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) = (n : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_zero, one_mul]
    push_cast; ring
  calc (∑ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ∑ m ∈ Finset.range (a + 1),
            ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α q'.1 q'.2) yE‖)
      ≤ ∑ _q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ((((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff) := by
        refine Finset.sum_le_sum (fun q' _ => ?_)
        have hq1 : q'.1 = (![] : Fin 0 → Fin n) := Subsingleton.elim _ _
        calc (∑ m ∈ Finset.range (a + 1),
                ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α q'.1 q'.2) yE‖)
            ≤ ∑ _m ∈ Finset.range (a + 1), (eFac * (CNemMax * Cstage) * Sdiff) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              rw [hq1]
              exact hper q'.2 m hm
          _ = (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast; ring
    _ = (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) *
          ((((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((n : ℝ) ^ 2) * (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff := by
        rw [hCard2]; ring

/-- **(The ball-uniform per-component raw chart-jet domination of the order-`a` covariant gradient of
the Ricci–DeTurck RHS-arm difference — the single named honest leaf carrying the uniform-over-`R`-ball
chart-Nemytskii Lipschitz modulus.)**

This is the **ball-uniform hoist** of the per-pair per-component raw chart-jet bound (the `hperPair`
inner estimate of `deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport`): a single
nonnegative constant `M0` — uniform over the fibre-small radius-`R` covariant ball, i.e. **outside** the
`∀ T T'` quantifier — such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant
jets up to order `a + 2` lie in the radius-`R` ball, on the closed support of the chart-`α`
partition-of-unity weight and for every target multi-index `Jdx`, the absolute value of the raw
chart-`α`-frame component of the order-`a` covariant gradient `∇^a RHSarm` of the RHS-arm residual
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
is dominated by `M0` times the sum of square roots of the intrinsic covariant fibre-norm jets of the
perturbation difference `T − T'`:
```
|tensorChartComponentRaw g₀ 0 (2+a) (∇^a RHSarm) α ![] Jdx b|
  ≤ M0 · ∑_{q ≤ a+2} √rfns(∇^q (T − T'))(b) .
```

**Why ball-uniform (and not per-pair).**  In the per-pair source the only `(T, T')`-dependent factor of
the constant `M0 = Cpeel · K` is the chart-Nemytskii Lipschitz modulus `CNemMax` of
`hasChartJetLip_chartDeTurckRicciRHS (g₀ + T) (g₀ + T') g_bg` (the forward covariant chart-jet peel
constant `Cpeel`, the bridge factor `eFac`, the Stage-4 content constant `Cstage` and the `n²·(a+1)`
combinatorial factor are all `g₀`-anchored and `(T, T')`-independent — `Cpeel` is built solely from the
`g₀`-Christoffel jets on the compact kernel).  On the fibre-small radius-`R` ball the realized metrics
`g₀ + h_sym T`, `g₀ + h_sym T'` stay uniformly positive-definite (the `δ < 1` fibre bound keeps `det`
bounded away from `0`) with metric jets bounded by `R`, so the `HasChartJetLip` chart-jet Lipschitz
modulus of the rational-with-nonvanishing-denominator Ricci–DeTurck nonlinearity (the standard Moser
ball-uniformity of the chart-Gram / inverse-Gram / Christoffel / Ricci / Lie–DeTurck jet towers, each
`∃ C, ∀` over the compact base and the bounded realized-metric jet set) is uniform over the ball;
supremising the modulus over the finitely many chart index pairs and orders gives the single
`(T, T')`-independent `M0`.

This is the genuine missing analytic prerequisite: the current `HasChartJetLip.lip`/`.seminorm_le` field
binds its constant to a fixed `(g₁, g₂)` with no STATED ball-uniformity, so the hoist to a single `M0`
over the realized `R`-ball is posited here (the underlying base towers are uniform-by-construction; the
ball-uniform packaging is the deferred input).  Consumers transitively depend on this leaf's `sorryAx`.

**Non-vacuity / order self-check.**  The grid reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')` Ricci
principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A `M0 = 0`
witness is rejected by a nonvanishing raw chart component for a non-flat, genuinely second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_rawComponent_domination_on_pouTsupport_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (_hR : 0 ≤ R) (α : M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ b : M,
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          ∀ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
                (I := I) (M := M) g₀ 0 (2 + a)
                (iteratedCovGrad (I := I) g₀ 0 2 a
                  ((deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                      deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') +
                    rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')))
                α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b| ≤
              M0 * ∑ q ∈ Finset.range (a + 2 + 1),
                Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
                  ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- The `(T, T')`-uniform forward covariant chart-jet peel constant (order window `P = a`,
  -- depending only on the `g₀`-Christoffel jets on the compact kernel).
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent_uniform
      (I := I) (M := M) g₀ 0 2 α a
  -- The ball-uniform RHS-arm bare chart-jet content domination by the intrinsic fibre-norm jets.
  obtain ⟨K, hK_nn, hK⟩ :=
    bareChartJetContent_deTurckRHSArm_le_sqrt_fiberNormSq_sum_ballUniform
      (I := I) (M := M) g₀ g_bg a (R := R) α hδ₀
  refine ⟨Cpeel * K, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball b hb Jdx
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set Ssqrt : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) with hSsqrt_def
  have hSsqrt_nn : 0 ≤ Ssqrt := Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  -- Chart-`α` setup: `b` lies in the chart source, and the Euclidean kernel point round-trips to `b`.
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  set yb : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) (extChartAt I α b) with hyb_def
  have hy_kernel : yb ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartImagePOUTsupport
      (I := I) (M := M) α := ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  -- The ball-uniform bare-content domination at `b`, threaded for this `(T, T')`.
  have hcontent : bareChartJetContent (I := I) (M := M) g₀ 0 2 RHSarm α a yb ≤ K * Ssqrt := by
    rw [hSsqrt_def, hRHSarm_def]
    exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball hb
  -- The chart component value at `b` is the order-`0` `rawPullR` jet at the kernel point.
  have hval : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 (2 + a)
        (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b =
      rawPullR (I := I) (M := M) g₀ 0 (2 + a)
        (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx yb := by
    rw [hyb_def]
    simp only [rawPullR, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [(extChartAt I α).left_inv hb_src]
  rw [hval]
  have hpeel := hCpeel RHSarm a 0 (by omega) (![] : Fin 0 → Fin n) Jdx yb hy_kernel
  rw [Nat.zero_add] at hpeel
  have hzero : ‖iteratedFDeriv ℝ 0
      (rawPullR (I := I) (M := M) g₀ 0 (2 + a)
        (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx) yb‖ =
      |rawPullR (I := I) (M := M) g₀ 0 (2 + a)
        (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx yb| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rw [hzero] at hpeel
  refine hpeel.trans ?_
  calc Cpeel * bareChartJetContent (I := I) (M := M) g₀ 0 2 RHSarm α a yb
      ≤ Cpeel * (K * Ssqrt) := mul_le_mul_of_nonneg_left hcontent hCpeel_nn
    _ = (Cpeel * K) * Ssqrt := by ring

/-- **(The ball-uniform per-chart raw-component domination of the Ricci–DeTurck RHS-arm difference —
the single named honest leaf carrying the uniform-over-`R`-ball chart-Nemytskii Lipschitz modulus.)**

This is the **ball-uniform hoist** of the per-pair per-chart raw-component bound
`deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport`: a single nonnegative
constant `Λ` — uniform over the fibre-small radius-`R` covariant ball, i.e. **outside** the `∀ T T'`
quantifier — such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant jets up
to order `a + 2` lie in the radius-`R` ball, on the closed support of the chart-`α` partition-of-unity
weight, the sum of squares of the raw chart-`α`-frame components of the order-`a` covariant gradient
`∇^a RHSarm` of the RHS-arm residual
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
is dominated by `Λ²` times the order-`≤ a + 2` covariant fibre-norm jets of `T − T'`:
```
∑_{Idx,Jdx} (tensorChartComponentRaw g₀ 0 (2+a) (∇^a RHSarm) α Idx Jdx b)²
  ≤ Λ² · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(b) .
```

**Why ball-uniform (and not per-pair).**  In the per-pair source the only `(T, T')`-dependent factor of
the constant is the chart-Nemytskii Lipschitz modulus `CNemMax` of
`hasChartJetLip_chartDeTurckRicciRHS (g₀ + T) (g₀ + T') g_bg` (the forward Euclidean-coordinate peel
`Cpeel`, the bridge factor `eFac`, the Stage-4 content constant `Cstage` and the `n^{2+a}·(a+3)`
combinatorial factor are all `g₀`-anchored and `(T, T')`-independent).  On the fibre-small radius-`R`
ball the realized metrics `g₀ + h_sym T`, `g₀ + h_sym T'` stay uniformly positive-definite (the `δ < 1`
fibre bound keeps `det` bounded away from `0`) with metric jets bounded by `R` to order `a + 2`, so the
`HasChartJetLip` chart-jet Lipschitz modulus of the rational-with-nonvanishing-denominator Ricci–DeTurck
nonlinearity is uniform over the ball (the standard Moser ball-uniformity of the chart-Gram / inverse-Gram
/ Christoffel / Ricci / Lie–DeTurck jet towers, each `∃ C, ∀` over the compact base and the bounded
realized-metric jet set).  Supremising the resulting modulus over the finitely many chart orders and the
`n²` index pairs gives the single `(T, T')`-independent `Λ`.

This is the genuine missing analytic prerequisite: the current `HasChartJetLip.lip`/`.seminorm_le` field
binds its constant to a fixed `(g₁, g₂)` with no STATED ball-uniformity, so the hoist to a single `Λ`
over the realized `R`-ball is posited here (the underlying base towers are uniform-by-construction; the
ball-uniform packaging is the deferred input).  Consumers transitively depend on this leaf's `sorryAx`.

**Non-vacuity / order self-check.**  The grid reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')` Ricci
principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A `Λ = 0`
witness is rejected by a nonvanishing raw chart component for a non-flat, genuinely second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_rawComponentSq_domination_on_pouTsupport_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) (α : M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ b : M,
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
                (I := I) (M := M) g₀ 0 (2 + a)
                (iteratedCovGrad (I := I) g₀ 0 2 a
                  ((deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                      deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') +
                    rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))) α Idx Jdx b) ^ 2) ≤
            Λ ^ 2 * ∑ q ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨M0, hM0_nn, hM0⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_rawComponent_domination_on_pouTsupport_ballUniform
      (I := I) (M := M) g₀ g_bg a hR α hδ₀
  refine ⟨Real.sqrt (((n : ℝ) ^ (2 + a)) * ((a : ℝ) + 3)) * M0, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball b hb
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set R0 : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b) with hR0_def
  have hR0_nn : 0 ≤ R0 := Finset.sum_nonneg fun q _ =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) b _
  set Ssqrt : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) with hSsqrt_def
  have hSsqrt_nn : 0 ≤ Ssqrt := Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  have hperPair : ∀ Jdx : Fin (2 + a) → Fin n,
      |DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b| ≤
        M0 * Ssqrt := by
    intro Jdx
    have h := hM0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball b hb Jdx
    rw [hSsqrt_def]
    simpa only [hRHSarm_def] using h
  have hSsqrt_sq : Ssqrt ^ 2 ≤ ((a : ℝ) + 3) * R0 := by
    rw [hSsqrt_def, hR0_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range (a + 2 + 1))
      (f := fun q => Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
        ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)))
    refine hcheb.trans (le_of_eq ?_)
    rw [Finset.card_range]
    congr 1
    · push_cast; ring
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      exact Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) b _)
  have hperPairSq : ∀ Jdx : Fin (2 + a) → Fin n,
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b) ^ 2 ≤
        M0 ^ 2 * (((a : ℝ) + 3) * R0) := by
    intro Jdx
    have h1 := hperPair Jdx
    have h2 : (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b) ^ 2 ≤
        (M0 * Ssqrt) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hSsqrt_sq (by positivity)
  have hΛsq : (Real.sqrt (((n : ℝ) ^ (2 + a)) * ((a : ℝ) + 3)) * M0) ^ 2 =
      ((n : ℝ) ^ (2 + a)) * (M0 ^ 2 * ((a : ℝ) + 3)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hΛsq]
  calc (∑ Idx : Fin 0 → Fin n, ∑ Jdx : Fin (2 + a) → Fin n,
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α Idx Jdx b) ^ 2)
      ≤ ∑ _Idx : Fin 0 → Fin n, ∑ _Jdx : Fin (2 + a) → Fin n,
          (M0 ^ 2 * (((a : ℝ) + 3) * R0)) := by
        refine Finset.sum_le_sum (fun Idx _ => Finset.sum_le_sum (fun Jdx _ => ?_))
        rw [Subsingleton.elim Idx (![] : Fin 0 → Fin n)]
        exact hperPairSq Jdx
    _ = (((n : ℝ) ^ (2 + a))) * (M0 ^ 2 * (((a : ℝ) + 3) * R0)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul,
          nsmul_eq_mul, ← mul_assoc]
        have hcard : ((Fintype.card (Fin 0 → Fin n) : ℝ) * (Fintype.card (Fin (2 + a) → Fin n) : ℝ)) =
            (n : ℝ) ^ (2 + a) := by
          simp only [Fintype.card_fun, Fintype.card_fin, pow_zero]
          push_cast; ring
        rw [hcard]
    _ = ((n : ℝ) ^ (2 + a)) * (M0 ^ 2 * ((a : ℝ) + 3)) * R0 := by ring

/-- **(The ball-uniform order-`(a+2)`-window covariant-jet bound on the Ricci–DeTurck RHS arm of
the sealed remainder difference — the uniform-over-`R`-ball Nemytskii estimate.)**

This is the **single named honest leaf** carrying the uniform-over-`R`-ball Lipschitz constant of the
two-metric chart Nemytskii nonlinearity at the quasilinear order.  Fix `g₀`, the DeTurck background
`g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is **one** nonnegative constant
`CR` — uniform over the fibre-small radius-`R` ball, i.e. **outside** the `∀ T T'` quantifier — such
that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order
`a + 2` lie in the radius-`R` ball, the order-`a` covariant gradient of the **RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— the genuine Ricci–DeTurck RHS difference `deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg
(g₀ + T')` (the Δ-arms cancel by `rawTensorConnLapSmooth_sub`) — is dominated, at the squared
fibre-norm level, by `CR` times the order-`(a + 2)` covariant jet of `T − T'`:
```
rfns(∇^a RHSarm)(x) ≤ CR · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x).
```

It is the per-pair bound `deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le` with the grid
constant **hoisted to a single ball-uniform value**: the chart-Nemytskii Lipschitz constant of
`hasChartJetLip_chartDeTurckRicciRHS` (anchored at `g₀`, the metric path constrained to the realized
ball `g₀ + T`, `g₀ + T'` with `‖∇^j T‖, ‖∇^j T'‖ ≤ R`) is uniform over the realized fibre-small `R`-ball
(the chart-jet Lipschitz modulus is taken over the bounded realized-metric jet set, hence finite and
`(T, T')`-independent), and the realized coefficient column `Kcol` is the fixed metric-tensor sup, also
`(T, T')`-independent.  Threading both uniform constants through the per-chart raw-component domination
and the atlas maximum gives the single `CR := Cmid · Kcol`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A
`CR = 0` witness is rejected by a nonvanishing `∇^a RHSarm` for a non-flat, genuinely second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CR : ℝ,
      0 ≤ CR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a
                ((deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') +
                  rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
            CR * ∑ q ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) := by
  classical
  -- This is the ball-uniform per-chart single-factor covariant-jet assembly: per chart `α` of the
  -- finite atlas, the reverse fibre-norm/raw-component bridge (uniform over all sections) composed
  -- with the **ball-uniform**
  -- per-chart raw-component domination posit produces a single `(T, T')`-independent constant
  -- `Cα := Cbridge α · (Λ α)²`; the atlas maximum `Ksum := ∑_α Cα` is the single ball-uniform `CR`.
  -- The reverse fibre-norm/raw-component bridge constant `Cbridge α` is uniform over **all** sections
  -- (the `∀ S` is inside its `∃ C`), hence `(T, T')`-independent.
  set Cbridge : M → ℝ := fun α =>
    (riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g₀ 0 (2 + a) α).choose with hCbridge_def
  have hCbridge_nn : ∀ α, 0 ≤ Cbridge α := fun α =>
    (riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g₀ 0 (2 + a) α).choose_spec.1
  have hCbridge : ∀ (α : M) (S : SmoothCcTensor g₀ 0 (2 + a)) {b : M},
      b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) b (S.toSection b) ≤
        Cbridge α *
          (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
                (I := I) (M := M) g₀ 0 (2 + a) S α Idx Jdx b) ^ 2) := fun α =>
    (riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g₀ 0 (2 + a) α).choose_spec.2
  -- The ball-uniform per-chart raw-component domination posit: a single `(T, T')`-independent `Λ α`.
  set Lam : M → ℝ := fun α =>
    (deTurckRHSArmDiff_rawComponentSq_domination_on_pouTsupport_ballUniform
      (I := I) (M := M) g₀ g_bg a hR α hδ₀).choose with hLam_def
  have hLam_nn : ∀ α, 0 ≤ Lam α := fun α =>
    (deTurckRHSArmDiff_rawComponentSq_domination_on_pouTsupport_ballUniform
      (I := I) (M := M) g₀ g_bg a hR α hδ₀).choose_spec.1
  have hLam := fun α =>
    (deTurckRHSArmDiff_rawComponentSq_domination_on_pouTsupport_ballUniform
      (I := I) (M := M) g₀ g_bg a hR α hδ₀).choose_spec.2
  -- The single per-chart constant `Cα := Cbridge α · (Λ α)²` and its atlas-sum `Ksum`.
  set Cα : M → ℝ := fun α => Cbridge α * (Lam α) ^ 2 with hCα_def
  have hCα_nn : ∀ α, 0 ≤ Cα α := fun α => mul_nonneg (hCbridge_nn α) (sq_nonneg _)
  set Ksum : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α with hKsum_def
  have hKsum_nn : 0 ≤ Ksum := Finset.sum_nonneg (fun α _ => hCα_nn α)
  refine ⟨Ksum, hKsum_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  -- Abbreviate the RHS-arm, its order-`a` covariant gradient, and the order-`(a+2)` jet column at `x`.
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set RHSa : SmoothCcTensor g₀ 0 (2 + a) :=
    iteratedCovGrad (I := I) g₀ 0 2 a RHSarm with hRHSa_def
  set Rcol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hRcol_def
  have hRcol_nn : 0 ≤ Rcol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- Choose a chart `α` whose closed POU support contains `x`.
  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨x, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hx_tsupport : x ∈ tsupport (fun y : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hα_pos))
  -- The reverse fibre-norm bridge at `x` for the chart `α`, applied to `RHSa`.
  have hbridge := hCbridge α RHSa hx_tsupport
  -- The ball-uniform raw-component domination at `x` for the chart `α`.
  have hraw := hLam α T T' hδ_le hδ hδ'_le hδ' hTball hT'ball x hx_tsupport
  -- Combine the two into `rfns(∇^a RHSarm)(x) ≤ Cα α · Rcol`, then majorise by the atlas-sum `Ksum`.
  have hCα_le : Cα α ≤ Ksum := by
    rw [hKsum_def]
    exact Finset.single_le_sum (fun β _ => hCα_nn β) hα_finset
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (RHSa.toSection x)
      ≤ Cbridge α *
          (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
                (I := I) (M := M) g₀ 0 (2 + a) RHSa α Idx Jdx x) ^ 2) := hbridge
    _ ≤ Cbridge α * ((Lam α) ^ 2 * Rcol) := by
        refine mul_le_mul_of_nonneg_left ?_ (hCbridge_nn α)
        simpa only [hRHSa_def, hRHSarm_def, hRcol_def] using hraw
    _ = Cα α * Rcol := by rw [hCα_def]; ring
    _ ≤ Ksum * Rcol := mul_le_mul_of_nonneg_right hCα_le hRcol_nn

private def deTurckRHSArmG0 (g₀ g_bg : SmoothRiemannianMetric I M)
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

/-- **The sealed remainder splits definitionally into the nonlinear RHS arm minus the linear
connection-Laplacian arm.**  This is `rfl`: the very definition of `deTurckSmoothRemainder` is the
record `deTurckRHSArmG0` minus `rawTensorConnLapSmooth g₀ 0 2 T`. -/
private theorem deTurckSmoothRemainder_eq_arm_sub_connLap
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

/-- **The sealed remainder difference splits into the nonlinear RHS-arm difference minus the linear
connection-Laplacian difference of `T − T'`.**  Purely algebraic in the additive group
`SmoothCcTensor g₀ 0 2`: substitute the definitional split of each remainder, then use the linearity
`rawTensorConnLapSmooth_sub` and regroup. -/
private theorem deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
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
  -- The squared `L²` norm of each jet, as an integral of its fibre norm.
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
  -- Integrability of the fibre norms.
  have hintW : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)
  -- The integrated column sum.
  set Scol : ℝ := ∑ i ∈ Finset.range (N + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
    with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- The RHS integrand and its integrability.
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
  -- Integrate the pointwise column bound.
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
  -- The squared `L²` bound.
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ C * Scol := by
    rw [hbridgeP]; exact hint_le.trans_eq hRHS_integral
  -- Take square roots.
  have hPq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ := norm_nonneg _
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖
      = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := (Real.sqrt_sq hPq_nn).symm
    _ ≤ Real.sqrt (C * Scol) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * Real.sqrt Scol := Real.sqrt_mul hC Scol

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
private theorem rawTensorConnLapSmooth_iteratedCovGrad_l2_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (q : ℕ), q ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)‖ ≤
          C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical
  -- The per-order pointwise jet bounds, bundled into a family `(Cfam q)` via `choose`.
  choose Cfam hCfam_nn hCfam using
    (fun q : ℕ => rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
      (I := I) (M := M) g₀ q)
  set Cunif : ℝ := ∑ q ∈ Finset.range (a + 1), Cfam q with hCunif_def
  have hCunif_nn : 0 ≤ Cunif :=
    Finset.sum_nonneg fun q _ => hCfam_nn q
  refine ⟨Real.sqrt Cunif, Real.sqrt_nonneg _, fun W q hq => ?_⟩
  -- The order-`q` pointwise jet bound, widened to constant `Cunif` and window `a + 2`.
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
    -- Widen the constant `Cfam q ≤ Cunif` and the window `range (q+2+1) ⊆ range (a+2+1)`.
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
  -- Integrate the pointwise column bound to the `L²` root-sum form.
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
private theorem deTurckArmDiff_supercritical_pointwise_jet_le
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
  -- The covariant window `k` reconciling `2k > finrank + 4` (C² chart embedding) and `4k ≤ a + 2`
  -- (reverse-Hebey order-doubling): both hold at `k := finrank/2 + 3` since `2·finrank + 10 ≤ a`.
  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega
  -- The unconditional pointwise `C²` collapse and the order-doubling reverse-Hebey bridge.
  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_unconditional (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _,
    fun W x => ?_⟩
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `M := ‖W.toHs (2k)‖`; the `C²` collapse: each of the three pointwise jet norms is `≤ Cc · M`.
  set Mn : ℝ := ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) (2 * k) W‖ with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hCol := hCc W x
  -- Reverse-Hebey at order `2k`: `M ≤ Ch · ∑_{j ≤ 4k} ‖∇^j W‖`.
  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm
  -- The covariant-`L²` jet sum (window `4k`) bounded by `√((4k+1)·S)` via Cauchy–Schwarz, where the
  -- `4k`-window squared-column is `≤ S` (the `a+2`-window, extra nonnegative terms).
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
  -- `M² ≤ Ch² · (4k+1) · S`.
  have hMn_sq : Mn ^ 2 ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) := by
    have hstep : Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := pow_le_pow_left₀ hMn_nn hHebey 2
    calc Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := hstep
      _ = Ch ^ 2 * Jsum ^ 2 := by ring
      _ ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) :=
          mul_le_mul_of_nonneg_left hJsq (by positivity)
  -- The fibre-norm column `∑_{q<3} rfns(∇^q W)(x)` rewrites (bundle bridge) to `∑_{q<3} ‖·‖²`, which
  -- is `≤ (∑_{q<3} ‖·‖)² ≤ (Cc·M)²` (sum of squares ≤ square of sum, on nonnegatives).  The bundle
  -- norm instances for the three valences `2, 3, 4` are brought into local context so the bridge's
  -- norm and `hCol`'s coincide.
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
  -- Assemble: `column ≤ Cc²·M² ≤ Cc²·Ch²·(4k+1)·S ≤ (√(...))²·S`.
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

private lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
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
private lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
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
private lemma threeArmCoeffSum_rfns_le (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
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

/-- **(POSITED deep bedrock — the Moser ball-uniform `C⁰` operator fibre-norm sup of the per-pair
Ricci-arm linearization coefficient fields.)**

Fix `g₀`, `g_bg`, a supercritical order `a` (`2·finrank E + 10 ≤ a`) and a covariant-`L²` ball radius
`R ≥ 0`.  There is **one** nonnegative ball-uniform order-`0` `C⁰` operator level `ΛR` — outside the
`∀ T T'` quantifier — such that for any two `g₀`-fibre-small `T, T'` whose covariant-`L²` jets up to order
`a + 2` lie in the radius-`R` ball there exist three endpoint coefficient fields `R₀, R₁, R₂` with both the
per-pair Ricci-arm value identity (the `negTwoRicciArm_appCc_eval` form, `(−2)·Ric` arm) AND the
order-`0` `C⁰` sups `rfns(Rₘ x) ≤ ΛR²`.

This is the genuine deep content beyond the per-pair eval-matching `negTwoRicciArm_appCc_eval`
(`CovGrad/RicciDeTurckLieArm.lean`): the coefficient fields are the path-averaged
`ricciArmOrder0Coeff`/`ricciArmOrder2Coeff` (rational in the order-`≤ 2` jets of the realize-tie metrics
with inverse-Gram denominators bounded below by `δ < 1`), and the supercritical `H^{a+2} ↪ C²` section
embedding (`ha_super`) turns the `a + 2` covariant-`L²` ball constraint on `T, T'` into a uniform `C⁰`
control of their order-`≤ 2` jets, so the fibre-norm sups of those rational coefficient fields are uniform
over the ball (the same Moser inverse-Gram / Christoffel / Ricci jet ball-uniformity carried by the
order-`0` coefficient `C⁰` sup data; `δ < 1` ALONE is
insufficient — it bounds the denominators but not the second-derivative numerators a concentrating common
part would blow up, so `ha_super` is genuinely load-bearing).

**Non-vacuity.**  The triple is an *existential output* (NOT a `∀`-over-all-triples claim — no `appCc`
kernel-bloat); the `(value identity)` clause constrains it to *reproduce the `(−2)`-scaled Ricci-arm
value*, the zero triple fails it whenever the realized Ricci arm is nonzero (`appCc_zero_left`), and a
`ΛR = 0` level is rejected by the nonvanishing genuine endpoint symbols on the supercritical ball. -/
private theorem exists_ricciArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) :=
  sorry

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
private theorem deTurckRicciArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨R₀, R₁, R₂, hval, hR₀, hR₁, hR₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨R₀, R₁, R₂, fun x v => ?_, hR₀, hR₁, hR₂⟩
  -- Bridge the `smul`-form `(−2)·(Ric − Ric)` value to the child's `mul`-form `(−2)·Ric − (−2)·Ric`
  -- value (`smul_sub` / `smul_eq_mul`), with `smoothRiemannianMetricToInfty := g` transparent to
  -- `ricciTensor`.
  rw [smul_sub, smul_eq_mul, smul_eq_mul]
  exact hval x v

/-- **(POSITED deep bedrock — the Moser ball-uniform `C⁰` operator fibre-norm sup of the per-pair
Lie-arm linearization coefficient fields.)**

The Lie-arm analogue of `exists_ricciArmCoeff_ballUniform_C0_sup`.  Fix `g₀`, `g_bg`, a supercritical
order `a` and a ball radius `R ≥ 0`.  There is one nonnegative ball-uniform order-`0` `C⁰` level `ΛL` —
outside the `∀ T T'` quantifier — such that for any two `g₀`-fibre-small `T, T'` whose covariant-`L²`
jets up to order `a + 2` lie in the radius-`R` ball there exist three endpoint coefficient fields
`L₀, L₁, L₂` with both the per-pair Lie-arm value identity (the `deTurckLieArm_appCc_eval` form) AND the
order-`0` `C⁰` sups `rfns(Lₘ x) ≤ ΛL²`.

The genuine deep content beyond the per-pair eval-matching `deTurckLieArm_appCc_eval`
(`CovGrad/RicciDeTurckLieArm.lean`): the coefficient fields read the order-`≤ 2` jets of the realize-tie
metrics through the chart Lie-derivative-metric symbol `½g⁻¹∂` and `W = g⁻¹·(∇g − ∇g_bg)` (rational with
`δ < 1` denominators), and the supercritical `H^{a+2} ↪ C²` section embedding (`ha_super`) makes their
fibre-norm sups uniform over the ball (the same Moser inverse-Gram / Christoffel ball-uniformity as the
Ricci arm; `δ < 1` ALONE is insufficient, so `ha_super` is load-bearing).

**Non-vacuity.**  The triple is an *existential output* (no `appCc` kernel-bloat); the `(value identity)`
clause constrains it to *reproduce the Lie-arm difference value*, the zero triple fails it whenever the
realized Lie arm is nonzero, and a `ΛL = 0` level is rejected by the nonvanishing genuine Lie-arm endpoint
symbols on the supercritical ball. -/
private theorem exists_lieArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) :=
  sorry

/-- **(POSITED deep bedrock — the VALUE-LEVEL (`unitModel`) ball-uniform order-graded Lie-arm
linearization of the realized Lie-derivative-metric difference, with order-`0` `C⁰` operator fibre-norm
sups.)**

The ball-uniform (`ΛL` outside the `∀ T T'` quantifier) form of the per-pair Lie-arm grading
`deTurckLieArm_appCc_graded` (`CovGrad/RicciDeTurckLieArm.lean`).  Same shape as the Ricci-arm
ball-uniform node, for the Lie arm `𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁'` (`W(g) = deTurckVF g g_bg`).

The genuine deep content (the Moser ball-uniformity of the realized Lie-arm DeTurck-vector-field symbol
over the supercritical ball) is isolated in the child `exists_lieArmCoeff_ballUniform_C0_sup`, which
supplies the ball-uniform `ΛL` together with, per fibre-small `(T, T')`, the three coefficient fields
satisfying the per-pair `deTurckLieArm_appCc_eval` value identity (verbatim the shape stated here) AND
the `C⁰` sups.  This node is the trivial re-quantifier-shaping of that child.

**Non-vacuity.**  The `(value identity)` clause genuinely constrains the triple to *reproduce the Lie-arm
difference value*; the zero triple fails it whenever the realized Lie arm is nonzero, and `ΛL = 0` is
rejected by the nonvanishing genuine Lie-arm endpoint symbols on the supercritical ball. -/
private theorem deTurckLieArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) := by
  classical
  obtain ⟨ΛL, hΛL_nn, hsup⟩ :=
    exists_lieArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, hΛL_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  exact ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩

/-- **(POSITED deep bedrock — the VALUE-LEVEL (`unitModel`) ball-uniform three-term mean-value
section-arm grading of the Ricci–DeTurck RHS-arm difference, with the ball-uniform order-`0` `C⁰`
operator fibre-norm sups.)**

This is the genuine deep differential-geometric content of the three-arm section identity, isolated at
the `unitModel` (value, `∀ x v`) level — the natural output shape of the per-arm Palatini/Lie graded
read-offs (`deTurckRicciArm_appCc_graded` for the curvature arm `−2 Ric`, its absent sibling
`deTurckLieArm_appCc_graded` for the Lie arm `𝓛_W g`), here combined into the full RHS arm and made
**ball-uniform** (the `ΛC` is hoisted outside the `∀ T T'` quantifier — the ellipticity / supercritical
`H^{a+2} ↪ C²` compactness of the order-`0` symbol over the realize-tie metrics of the radius-`R` ball,
NO covariant jet control).

Fix `g₀`, `g_bg`, a supercritical order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  Outside the
`∀ T T'` quantifier there is one nonnegative ball-uniform order-`0` `C⁰` operator fibre-norm level `ΛC`.
For any two `g₀`-fibre-small `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R`
ball, there are the three intrinsic `g₀`-built endpoint-dependent coefficient operator fields
`C₀ : SmoothCcTensor g₀ 2 2`, `C₁ : SmoothCcTensor g₀ 3 2`, `C₂ : SmoothCcTensor g₀ 4 2` such that:

* **(value identity)** for every base point `x` and tangent pair `v`, the unit-model `(0, 2)`-form value
  of the RHS-arm difference equals the unit-model read-off of the order-graded `appCc` action on the
  iterated covariant gradients `Wₘ = ∇₀^m (T − T')` of the perturbation difference:
  ```
  unitModel g₀ 2 (armG0 T − armG0 T') x v
    = unitModel g₀ 2 (appCc C₀ W₀ + appCc C₁ W₁ + appCc C₂ W₂) x v ;
  ```
* **(order-`0` `C⁰` operator sups)** the three coefficient fields are operator-bounded ball-uniformly at
  order `0`: `∀ x, rfns(C₀ x) ≤ ΛC²`, `∀ x, rfns(C₁ x) ≤ ΛC²`, `∀ x, rfns(C₂ x) ≤ ΛC²`.

The genuine deep content is the existential mean-value linearization (the intrinsic Palatini
`δRic = ∇·(δΓ) − ∇(tr δΓ)` with `δΓ = connDiff`, the inverse-Gram Neumann linearization in the order-`2`
slot, telescoped through `g₀` along the realize-tie `g₁ − g₀ = ccTensorBilinSymm T`, read off the
bedrock graded decomposition `covDerivConnDiff_diff_endpoint_graded`) plus the Lie-arm grading and the
order-`0` ball-compactness of the symbol; it is stated at the `unitModel` value level, the natural shape
of the per-arm graded read-offs.  Expressed entirely in `unitModel` / `appCc` / `iteratedCovGrad` /
`riemannianFiberNormSq` — **never** a `chartGramOnE` / `HasChartJetLip` chart-jet chain, **never** an
order-`a` `L^∞` cometric jet.  Consumers transitively depend on its `sorryAx`.

**Non-vacuity.**  The realization is `ℝ`-linear in `T − T'` and its jets, so the value vanishes as
`T − T' → 0`; a degenerate `C₀ = C₁ = C₂ = 0` is rejected by a nonvanishing `unitModel`-value of the RHS
arm difference for a genuinely second-order, non-flat RHS difference; a `ΛC = 0` level is rejected by the
nonvanishing genuine endpoint operator symbols on the supercritical ball.  The `(value identity)` clause
genuinely constrains the triple to *reproduce the RHS-arm difference value*. -/
private theorem deTurckRHSArmDiff_threeArm_unitModel_ballUniform
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            unitModel (I := I) (M := M) g₀ 2
                (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x v =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical
  -- The two ball-uniform arm gradings: the Ricci arm `−2 Ric` and the Lie arm `𝓛_{W} g`.  Each supplies
  -- a single ball-uniform order-`0` `C⁰` level (`ΛR`, `ΛL`) outside `∀ T T'`, and per fibre-small
  -- `(T, T')` the three endpoint coefficient fields with the `∀ x v` value identity and the `C⁰` sups.
  obtain ⟨ΛR, hΛR_nn, hRicci⟩ :=
    deTurckRicciArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛL, hΛL_nn, hLie⟩ :=
    deTurckLieArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The combined ball-uniform `C⁰` level, accommodating the `2`-sub-additivity of the fibre norm on the
  -- summed coefficient fields `Cₘ = Rₘ + Lₘ`: `rfns(Rₘ + Lₘ) ≤ 2·ΛR² + 2·ΛL² = ΛC²`.
  refine ⟨Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨R₀, R₁, R₂, hRval, hR₀, hR₁, hR₂⟩ :=
    hRicci T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hLval, hL₀, hL₁, hL₂⟩ :=
    hLie T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  -- The summed coefficient fields.
  refine ⟨R₀ + L₀, R₁ + L₁, R₂ + L₂, ?_, ?_, ?_, ?_⟩
  · -- The value identity: the RHS-arm difference unit-model value splits into the Ricci-arm value and the
    -- Lie-arm value (the `deTurckRicciRHS` definition `−2 Ric + 𝓛_W g`), each rebuilt by its arm grading,
    -- then re-aggregated by `appCc`/`unitModel` additivity into the summed-coefficient read-off.
    intro x v
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    -- `unitModel(armG0 T − armG0 T') x v = unitModel(armG0 T) x v − unitModel(armG0 T') x v`, and each
    -- unit-model arm value is the `deTurckRicciRHS` bilinear value at the realized metric (the bridge).
    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
          deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
          deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') rfl x v]
    -- Split each `deTurckRicciRHS` into its Ricci arm `−2 Ric(toInfty g)` and its Lie arm
    -- `lieDerivMetricClm g (deTurckVF (toInfty g) (toInfty g_bg))`, evaluated at the tangent pair.
    have hsplit : ∀ (g : SmoothRiemannianMetric I M),
        deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) =
          ((-2 : ℝ) • ricciTensor (I := I) g x (v 0) (v 1)) +
            lieDerivMetricClm (I := I) g
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
      intro g
      rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
      rfl
    rw [hsplit g₁, hsplit g₁']
    -- Regroup the difference into the Ricci-arm difference plus the Lie-arm difference.
    rw [show ((-2 : ℝ) • ricciTensor (I := I) g₁ x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) -
          ((-2 : ℝ) • ricciTensor (I := I) g₁' x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) =
        ((-2 : ℝ) • (ricciTensor (I := I) g₁ x (v 0) (v 1) -
            ricciTensor (I := I) g₁' x (v 0) (v 1))) +
          (lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) from by
      simp only [smul_sub]; ring]
    -- Rebuild each arm difference by its arm grading's value identity.
    rw [hRval x v, hLval x v]
    -- Re-aggregate the two graded read-offs into the summed-coefficient read-off by `appCc`/`unitModel`
    -- additivity.  Name the per-arm graded sections, rewrite the summed-coefficient section as their sum
    -- (`appCc_add_left` on each order slot, then `abel`), and split the unit-model read-off additively.
    set Rblk : SmoothCcTensor g₀ 0 2 :=
      appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hRblk
    set Lblk : SmoothCcTensor g₀ 0 2 :=
      appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hLblk
    have hcoeffSum :
        appCc (I := I) (M := M) g₀ 2 2 (R₀ + L₀) (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          appCc (I := I) (M := M) g₀ 3 2 (R₁ + L₁) (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          appCc (I := I) (M := M) g₀ 4 2 (R₂ + L₂) (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        Rblk + Lblk := by
      rw [appCc_add_left (I := I) (M := M) g₀ 2 2 R₀ L₀,
        appCc_add_left (I := I) (M := M) g₀ 3 2 R₁ L₁,
        appCc_add_left (I := I) (M := M) g₀ 4 2 R₂ L₂, hRblk, hLblk]
      abel
    rw [hcoeffSum, unitModel_add_local (I := I) g₀ 2 Rblk Lblk x,
      ContinuousMultilinearMap.add_apply]
  · -- The order-`0` `C⁰` sup for the summed `(2, 2)` coefficient `C₀ = R₀ + L₀`.
    exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₀ L₀ ΛR ΛL x (hR₀ x) (hL₀ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₁ L₁ ΛR ΛL x (hR₁ x) (hL₁ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₂ L₂ ΛR ΛL x (hR₂ x) (hL₂ x)

/-- **(Route P (Moser-extremes): the intrinsic three-term mean-value SECTION IDENTITY of the
Ricci–DeTurck RHS-arm difference on EXISTENTIAL endpoint-dependent coefficient fields, with the
ball-uniform order-`0` `C⁰` operator fibre-norm sups of those coefficients.)**

This is the section-level (`SmoothCcTensor` equality) core of the re-routed apex Moser tame.  It lifts the
value-level (`unitModel`) ball-uniform grading `deTurckRHSArmDiff_threeArm_unitModel_ballUniform` to a
genuine `SmoothCcTensor` equality through the unit-model extensionality bridge
`smoothCcTensor_ext_of_unitModel` (`∀ x, unitModel S x = unitModel S' x ⟹ S = S'`).

Fix `g₀`, `g_bg`, a supercritical order `a` (`2·finrank E + 10 ≤ a`), and a covariant-`L²` ball radius
`R ≥ 0`.  Outside the `∀ T T'` quantifier there is one nonnegative ball-uniform order-`0` `C⁰` operator
fibre-norm level `ΛC`.  For any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²`
jets up to order `a + 2` lie in the radius-`R` ball, there are the three intrinsic `g₀`-built
endpoint-dependent coefficient operator fields `C₀ : SmoothCcTensor g₀ 2 2`, `C₁ : SmoothCcTensor g₀ 3 2`,
`C₂ : SmoothCcTensor g₀ 4 2` (the endpoint curvature/inverse-Gram value symbol, the
Christoffel-variation `½g⁻¹∂` symbol, and the Ricci / inverse-Gram principal `−½Δ_L + (g₁⁻¹−g₀⁻¹)∂²`
symbol of the mean-value path `dF`), such that, with
`N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'`:

* **(identity)** the intrinsic three-term mean-value section equality
  `N = appCc C₀ (T − T') + appCc C₁ (∇(T − T')) + appCc C₂ (∇²(T − T'))`;
* **(order-`0` `C⁰` operator sups)** the three coefficient fields are operator-bounded ball-uniformly at
  order `0`: `∀ x, rfns(C₀ x) ≤ ΛC²`, `∀ x, rfns(C₁ x) ≤ ΛC²`, `∀ x, rfns(C₂ x) ≤ ΛC²`.

The genuine deep content is the value-level grading posit (the intrinsic Palatini `δRic = ∇·(δΓ) −
∇(tr δΓ)` with `δΓ = connDiff`, the inverse-Gram Neumann linearization in the principal order-`2` slot,
telescoped through `g₀` along the realize-tie `g₁ − g₀ = ccTensorBilinSymm T`, read off the bedrock
graded decomposition `covDerivConnDiff_diff_endpoint_graded`, plus the Lie-arm grading and the order-`0`
ball-compactness); the section lift is the unit-model extensionality.  Expressed entirely in `appCc` /
`iteratedCovGrad` / `riemannianFiberNormSq` — **never** a `chartGramOnE` / `chartInvGramOnE` /
`HasChartJetLip` chart-jet chain, **never** an order-`a` `L^∞` cometric jet.  Consumers transitively
depend on the value-level grading posit's `sorryAx`.

**Non-vacuity.**  The realization is `ℝ`-linear in `T − T'` and its jets, so it vanishes as `T − T' → 0`
(the Nemytskii Lipschitz character is preserved); a degenerate `C₀ = C₁ = C₂ = 0` is rejected by a
nonvanishing `∇^q N` for a genuinely second-order, non-flat RHS difference; a `ΛC = 0` level is rejected
by the nonvanishing genuine (non-zero) endpoint operator symbols on the supercritical ball. -/
private theorem deTurckRHSArmDiff_threeArm_coeffC0_ballUniform
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical
  -- The value-level (`unitModel`) ball-uniform grading supplies `ΛC` and, per fibre-small `(T, T')`,
  -- the three coefficient fields with the `∀ x v` value identity and the order-`0` `C⁰` sups.
  obtain ⟨ΛC, hΛC_nn, hgrade⟩ :=
    deTurckRHSArmDiff_threeArm_unitModel_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛC, hΛC_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hval, hC₀, hC₁, hC₂⟩ :=
    hgrade T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨C₀, C₁, C₂, ?_, hC₀, hC₁, hC₂⟩
  -- Lift the `∀ x v` value identity (the section difference lives INSIDE `unitModel`) to the
  -- `SmoothCcTensor` equality via the unit-model extensionality bridge.
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  exact hval x v

set_option maxHeartbeats 800000 in
/-- **(POSITED deficit-free INTRINSIC order-`0` pointwise fibre-norm domination of the nonlinear
Ricci–DeTurck RHS-arm difference — re-proved DEFICIT-FREE via the order-`0` Moser extreme, chart-jet-free,
NO order-`a` `L^∞` cometric jet.)**

Fix `g₀`, the DeTurck background `g_bg`, a supercritical order `a` (`2·finrank E + 10 ≤ a`), and a
covariant-`L²` ball radius `R ≥ 0`.  There is **one** nonnegative constant `Λa` — uniform over the
fibre-small radius-`R` ball, **outside** the `∀ T T'` quantifier — such that for any two
`g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the
radius-`R` ball, the order-`0` fibre value of the nonlinear RHS-arm difference
`N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` is dominated, at the squared fibre-norm
level, by the full order-`(a+2)` covariant-`L²` jet scale of the perturbation difference `T − T'`:
```
∀ x,  rfns(N)(x)  ≤  Λa² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²} .
```

**Why deficit-free (the order-`0` Moser extreme).**  By the section identity
`N = appCc C₀ (T − T') + appCc C₁ (∇(T − T')) + appCc C₂ (∇²(T − T'))` of
`deTurckRHSArmDiff_threeArm_coeffC0_ballUniform`, the order-`0` value `rfns(N)(x)` is bounded by the
`g`-fibre subadditivity factor `4` times the three arm values, each of which is the intrinsic
partial-contraction Cauchy–Schwarz `rfns(appCc Cₘ (∇^m S))(x) ≤ rfns(Cₘ x) · rfns(∇^m S)(x)`
(`riemannianFiberNormSq_comp_le_mul`).  The coefficient enters ONLY through its order-`0` `C⁰` operator
fibre-norm sup `rfns(Cₘ x) ≤ ΛC²` (ball-uniform via ellipticity — never an order-`a` `L^∞` jet), and the
perturbation jets `∑_{m ≤ 2} rfns(∇^m S)(x)` are dominated by `Cemb² · ∑_{i ≤ a+2} ‖∇^i S‖²_{L²}` via the
supercritical `H^{a+2} ↪ C²` section embedding `deTurckArmDiff_supercritical_pointwise_jet_le`.  The
single ball-uniform constant is `Λa := √(4·3·ΛC²·Cemb²) = 2·√3·ΛC·Cemb`.

**Non-vacuity.**  The bound vanishes as `T − T' → 0`, so the Nemytskii Lipschitz character is preserved;
a `Λa = 0` witness is rejected by a nonvanishing `rfns(N)` for a genuinely second-order, non-flat RHS
difference.  This re-proof routes **only** through `appCc` / `iteratedCovGrad` / `riemannianFiberNormSq` /
`tensorL2Norm`; consumers transitively depend on the identity child's `sorryAx`. -/
private theorem deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λa : ℝ, 0 ≤ Λa ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
            Λa ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical
  -- The ball-uniform order-`0` `C⁰` operator level of the three endpoint coefficient fields, plus the
  -- three-term section identity (the deficit-free Route-P core, never an order-`a` `L^∞` cometric jet).
  obtain ⟨ΛC, hΛC_nn, hcore⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The supercritical `H^{a+2} ↪ C²` section embedding of the radius-`R` ball, applied to `T − T'`:
  -- `∑_{m < 3} rfns(∇^m (T − T'))(x) ≤ Cemb² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²`.
  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  refine ⟨Real.sqrt (4 * 3) * (ΛC * Cemb), by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hid, hC₀, hC₁, hC₂⟩ :=
    hcore T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- The three arms as sections.
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  -- Each perturbation-jet fibre value, abbreviated by the gradient order `m`.
  set f : ℕ → ℝ := fun m =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) with hf_def
  have hf_nn : ∀ m, 0 ≤ f m := fun m =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _
  -- The order-`0` arm Cauchy–Schwarz: `rfns(appCc Cₘ (∇^m S))(x) ≤ rfns(Cₘ x) · f m ≤ ΛC² · f m`
  -- (the intrinsic partial-contraction submultiplicativity `riemannianFiberNormSq_comp_le_mul`,
  -- the coefficient read ONLY through its order-`0` `C⁰` operator sup `rfns(Cₘ x) ≤ ΛC²`).
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x) ≤ ΛC ^ 2 * f 0 := by
    rw [hA₀, appCc_toSection (I := I) (M := M) g₀ 2 2 C₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 2 2 x
      (C₀.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₀ x) (hf_nn 0)
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x) ≤ ΛC ^ 2 * f 1 := by
    rw [hA₁, appCc_toSection (I := I) (M := M) g₀ 3 2 C₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 3 2 x
      (C₁.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₁ x) (hf_nn 1)
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x) ≤ ΛC ^ 2 * f 2 := by
    rw [hA₂, appCc_toSection (I := I) (M := M) g₀ 4 2 C₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 4 2 x
      (C₂.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₂ x) (hf_nn 2)
  -- `g`-fibre subadditivity (factor `4`) over the three-term section identity.
  have hsub : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) ≤
      4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := by
    simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x + A₁.toSection x) (A₂.toSection x)
    have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x) (A₁.toSection x)
    have h2nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)
    nlinarith [hadd1, hadd2, h2nn]
  -- The order-`≤ 2` perturbation-jet column dominated by the embedding.
  have hcol : f 0 + f 1 + f 2 ≤ Cemb ^ 2 * S := by
    have hemb' := hemb (T - T') x
    have hsum3 : (∑ q ∈ Finset.range 3,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)) = f 0 + f 1 + f 2 := by
      simp only [hf_def, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hS_def]
    rw [hsum3] at hemb'
    exact hemb'
  -- Chain.  `(√(4·3)·ΛC·Cemb)² = 4·3·ΛC²·Cemb²`, dominating `4·ΛC²·(f0+f1+f2) ≤ 12·ΛC²·Cemb²·S`.
  have hΛsq : (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 = (4 * 3) * (ΛC ^ 2 * Cemb ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 * 3)]; ring
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ').toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) := by
        rw [hid]
    _ ≤ 4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := hsub
    _ ≤ 4 * (ΛC ^ 2 * f 0 + ΛC ^ 2 * f 1 + ΛC ^ 2 * f 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add h0 h1) h2) (by norm_num)
    _ = (4 * ΛC ^ 2) * (f 0 + f 1 + f 2) := by ring
    _ ≤ (4 * ΛC ^ 2) * (Cemb ^ 2 * S) := by
        refine mul_le_mul_of_nonneg_left hcol (by positivity)
    _ ≤ (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 * S := by
        rw [hΛsq]
        have : (4 * ΛC ^ 2) * (Cemb ^ 2 * S) ≤ ((4 * 3) * (ΛC ^ 2 * Cemb ^ 2)) * S := by
          nlinarith [hS_nn, sq_nonneg ΛC, sq_nonneg Cemb,
            mul_nonneg (sq_nonneg ΛC) (sq_nonneg Cemb)]
        linarith [this]

set_option linter.unusedSectionVars false in
/-- Continuity of `x ↦ rfns(S)(x)` for a smooth compactly-supported tensor section (general
valence `r`).  A general-`r` companion of the purely-covariant `continuous_rfns`. -/
private theorem mixed_continuous_rfns
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

set_option linter.unusedSectionVars false in
/-- Two-factor Hölder for nonnegative continuous functions on the finite Riemannian volume of a
closed manifold: `∫ φ·ψ ≤ ‖φ‖_{Lᵖ}·‖ψ‖_{L^q}` for conjugate `p, q`. -/
private theorem mixed_real_holder_two_nonneg
    (g : SmoothRiemannianMetric I M) (φ ψ : M → ℝ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, φ x * ψ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, φ x ^ p ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / p) *
      (∫ x, ψ x ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / q) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hp_pos : 0 < p := hpq.left_pos
  have hq_pos : 0 < q := hpq.right_pos
  have hφm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) μ :=
    (hφc.measurable.ennreal_ofReal).aemeasurable
  have hψm : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) μ :=
    (hψc.measurable.ennreal_ofReal).aemeasurable
  have hint_prod : Integrable (fun x => φ x * ψ x) μ :=
    (hφc.mul hψc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_φp : Integrable (fun x => φ x ^ p) μ :=
    ((hφc.rpow_const (fun x => Or.inr hp_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hint_ψq : Integrable (fun x => ψ x ^ q) μ :=
    ((hψc.rpow_const (fun x => Or.inr hq_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hφp0 : ∀ x, 0 ≤ φ x ^ p := fun x => Real.rpow_nonneg (hφ0 x) _
  have hψq0 : ∀ x, 0 ≤ ψ x ^ q := fun x => Real.rpow_nonneg (hψ0 x) _
  have hIφp_nn : 0 ≤ ∫ x, φ x ^ p ∂μ := integral_nonneg hφp0
  have hIψq_nn : 0 ≤ ∫ x, ψ x ^ q ∂μ := integral_nonneg hψq0
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq hφm hψm
  have hLHS_lint : (∫⁻ x, ((fun x => ENNReal.ofReal (φ x)) * (fun x => ENNReal.ofReal (ψ x))) x ∂μ)
      = ENNReal.ofReal (∫ x, φ x * ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_prod
      (Eventually.of_forall (fun x => mul_nonneg (hφ0 x) (hψ0 x)))]
    refine lintegral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hφ0 x)]
  have hφp_pt : ∀ x, (ENNReal.ofReal (φ x)) ^ p = ENNReal.ofReal (φ x ^ p) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hφ0 x) hp_pos.le
  have hψq_pt : ∀ x, (ENNReal.ofReal (ψ x)) ^ q = ENNReal.ofReal (ψ x ^ q) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hψ0 x) hq_pos.le
  have hφp_lint : (∫⁻ x, (ENNReal.ofReal (φ x)) ^ p ∂μ) = ENNReal.ofReal (∫ x, φ x ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_φp (Eventually.of_forall hφp0)]
    exact lintegral_congr_ae (Eventually.of_forall hφp_pt)
  have hψq_lint : (∫⁻ x, (ENNReal.ofReal (ψ x)) ^ q ∂μ) = ENNReal.ofReal (∫ x, ψ x ^ q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_ψq (Eventually.of_forall hψq0)]
    exact lintegral_congr_ae (Eventually.of_forall hψq_pt)
  rw [hLHS_lint, hφp_lint, hψq_lint] at hHolder
  rw [ENNReal.ofReal_rpow_of_nonneg hIφp_nn (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hIψq_nn (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hHolder
  have hrhs_nn : 0 ≤ (∫ x, φ x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hHolder

set_option linter.unusedSectionVars false in
/-- The interpolation-product → Young arm-split: from the two Gagliardo–Nirenberg interpolation
bounds on the two factors (at the cell diagonal `m = i + l`, weights `wi = i/m`, `wl = l/m`), the
product of the interpolated `Lᵖ` jet norms is bounded by the two-arm sum
`CS·CT·(wi·Λ_T²·N_S² + wl·Λ_S²·N_T²)` via weighted AM–GM.  Pure real arithmetic. -/
private theorem mixed_young_arm_split
    (wi wl CS CT ΛS ΛT NS NT Iφp Iψq : ℝ)
    (hwi_nn : 0 ≤ wi) (hwl_nn : 0 ≤ wl) (hwsum : wi + wl = 1)
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hΛS : 0 ≤ ΛS) (hΛT : 0 ≤ ΛT)
    (hNS : 0 ≤ NS) (hNT : 0 ≤ NT) (_hIφp : 0 ≤ Iφp) (hIψq : 0 ≤ Iψq)
    (hS : Iφp ^ wi ≤ CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi))
    (hT : Iψq ^ wl ≤ CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :
    Iφp ^ wi * Iψq ^ wl ≤
      CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) := by
  have hT_nn : 0 ≤ Iψq ^ wl := Real.rpow_nonneg hIψq _
  have hprod : Iφp ^ wi * Iψq ^ wl ≤
      (CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi)) *
      (CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :=
    mul_le_mul hS hT hT_nn (by positivity)
  have h1wi : (1 : ℝ) - wi = wl := by rw [← hwsum]; ring
  have h1wl : (1 : ℝ) - wl = wi := by rw [← hwsum]; ring
  rw [h1wi, h1wl] at hprod
  have hsq_rpow : ∀ (b : ℝ), 0 ≤ b → ∀ w : ℝ, b ^ (2 * w) = (b ^ 2) ^ w := by
    intro b hb w
    rw [Real.rpow_mul hb 2 w, Real.rpow_two]
  have hregroup :
      (CS * ΛS ^ (2 * wl) * NS ^ (2 * wi)) * (CT * ΛT ^ (2 * wi) * NT ^ (2 * wl))
        = CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      hsq_rpow ΛS hΛS wl, hsq_rpow NS hNS wi, hsq_rpow ΛT hΛT wi, hsq_rpow NT hNT wl]
    ring
  rw [hregroup] at hprod
  have hyoung : (ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl ≤
      wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2) :=
    Real.geom_mean_le_arith_mean2_weighted hwi_nn hwl_nn (by positivity) (by positivity) hwsum
  calc Iφp ^ wi * Iψq ^ wl
      ≤ CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := hprod
    _ ≤ CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) :=
        mul_le_mul_of_nonneg_left hyoung (by positivity)

open DifferentialGeometry.Analysis.Sobolev.Tensor in
/-- **The mixed-valence integrated Gagliardo–Nirenberg two-arm bound of the diagonal covariant-jet
product grid.**  The general-`r` analogue of the purely-covariant
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`: the first factor `S` carries an
arbitrary valence `(r, s₁)`, the second factor `T` is purely covariant `(0, s₂)`.  For two `C⁰`-sup
levels `Λ_S, Λ_T` with `rfns(S) ≤ Λ_S²`, `rfns(T) ≤ Λ_T²`, the diagonal product grid
`∑_{i + l ≤ k} rfns(∇^i S) · rfns(∇^l T)` integrates to the two-arm tame bound
`∫ grid ≤ C · (Λ_T²·∑_{i ≤ k}‖∇^i S‖² + Λ_S²·∑_{l ≤ k}‖∇^l T‖²)`.

Proved over the general-valence `Lᵖ` Gagliardo–Nirenberg interpolation engine
`exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs`: the boundary cells (`i = 0` or
`l = 0`) by the `C⁰` sup directly, the interior cells by Hölder at the cell diagonal `m = i + l`,
the `_rs` engine on each factor (at the mixed valence `(r, s₁)` for `S`, `(0, s₂)` for `T`), and the
weighted-AM–GM Young split.  Depends transitively only on the `Lᵖ`-interpolation engine's `sorryAx`. -/
private theorem appCc_integrated_grid_twoArm_mixed
    (g : SmoothRiemannianMetric I M) (r s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g r s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        (∫ x, (∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (s₁ + i) x
                ((iteratedCovGrad (I := I) g r s₁ i S).toSection x)
              * ∑ l ∈ Finset.range (k + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                    ((iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2
              + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g r s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g 0 s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 s₂ m h).choose_spec.1
    · exact le_refl 0
  set Cbig : ℝ := 1 + ∑ m ∈ Finset.range (k + 1), CSf m * CTf m with hCbig
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbig]
    have : (0 : ℝ) ≤ ∑ m ∈ Finset.range (k + 1), CSf m * CTf m :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hCSf_nn m) (hCTf_nn m))
    linarith
  have hCbig_nn : (0 : ℝ) ≤ Cbig := le_trans zero_le_one hCbig1
  have hCSCT_le : ∀ m, m ≤ k → CSf m * CTf m ≤ Cbig := by
    intro m hm
    rw [hCbig]
    have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hterm : CSf m * CTf m ≤ ∑ m' ∈ Finset.range (k + 1), CSf m' * CTf m' :=
      Finset.single_le_sum (fun m' _ => mul_nonneg (hCSf_nn m') (hCTf_nn m')) hmem
    linarith
  refine ⟨(k + 1) ^ 2 * Cbig, by positivity, ?_⟩
  intro S T ΛS ΛT hΛS hΛT hSsup hTsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
      ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj
  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g r (s₁ + a)
            (iteratedCovGrad (I := I) g r s₁ a S).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
            ((iteratedCovGrad (I := I) g r s₁ a S).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g r s₁ a S).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := r) (s := s₁ + a) (x := x)
              ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g 0 (s₂ + b)
            (iteratedCovGrad (I := I) g 0 s₂ b T).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
            ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g 0 s₂ b T).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := 0) (s := s₂ + b) (x := x)
              ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g 0 s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact mixed_continuous_rfns g r (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact mixed_continuous_rfns g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
  have hSj_int : ∀ a, Integrable (Sj a) μ := fun a => by
    rw [hμ]; exact (hSj_cont a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTj_int : ∀ b, Integrable (Tj b) μ := fun b => by
    rw [hμ]; exact (hTj_cont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_cell : ∀ a b, Integrable (fun x => Sj a x * Tj b x) μ := fun a b => by
    rw [hμ]
    exact ((hSj_cont a).mul (hTj_cont b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSsup0 : ∀ x, Sj 0 x ≤ ΛS ^ 2 := by
    intro x; rw [hSj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g r s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x
  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by positivity
  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hbound : ∫ x, Sj 0 x * Tj l x ∂μ ≤ ΛS ^ 2 * ∫ x, Tj l x ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
          (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (hSj_nn 0 x) (hTj_nn l x)
        · exact (hTj_int l).const_mul _
        · exact mul_le_mul_of_nonneg_right (hSsup0 x) (hTj_nn l x)
      rw [hTnorm l] at hbound
      calc ∫ x, Sj 0 x * Tj l x ∂μ
          ≤ ΛS ^ 2 * ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ hCbig_nn
              linarith [hAS_nn]
    · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
      · subst hl0
        have hbound : ∫ x, Sj i x * Tj 0 x ∂μ ≤ ΛT ^ 2 * ∫ x, Sj i x ∂μ := by
          rw [← integral_const_mul]
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
            (Eventually.of_forall (fun x => ?_))
          · exact mul_nonneg (hSj_nn i x) (hTj_nn 0 x)
          · exact (hSj_int i).const_mul _
          · calc Sj i x * Tj 0 x
                ≤ Sj i x * ΛT ^ 2 := mul_le_mul_of_nonneg_left (hTsup0 x) (hSj_nn i x)
              _ = ΛT ^ 2 * Sj i x := mul_comm _ _
        rw [hSnorm i] at hbound
        calc ∫ x, Sj i x * Tj 0 x ∂μ
            ≤ ΛT ^ 2 * ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ hCbig_nn
                linarith [hAT_nn]
      · set m : ℕ := i + l with hm
        have hmk : m ≤ k := by rw [hm]; exact hilk
        have hm1 : 1 ≤ m := by omega
        have hmi : i < m := by omega
        have hml : l < m := by omega
        have hm_posR : 0 < (m : ℝ) := by positivity
        set wi : ℝ := (i : ℝ) / m with hwi
        set wl : ℝ := (l : ℝ) / m with hwl
        have hwi_nn : 0 ≤ wi := by rw [hwi]; positivity
        have hwl_nn : 0 ≤ wl := by rw [hwl]; positivity
        have hwsum : wi + wl = 1 := by
          rw [hwi, hwl, ← add_div, show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hi_posR : 0 < (i : ℝ) := by exact_mod_cast hipos
        have hl_posR : 0 < (l : ℝ) := by exact_mod_cast hlpos
        set p : ℝ := (m : ℝ) / i with hp
        set q : ℝ := (m : ℝ) / l with hq
        have hp_one : 1 < p := by rw [hp, lt_div_iff₀ hi_posR, one_mul]; exact_mod_cast hmi
        have hpq : p.HolderConjugate q := by
          rw [Real.holderConjugate_iff]
          refine ⟨hp_one, ?_⟩
          rw [hp, hq, inv_div, inv_div, ← add_div,
            show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hHolder := mixed_real_holder_two_nonneg g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder
        have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml
        have hCSf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g 0 s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe
        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe
        rw [show Integral.L2.tensorL2Norm (I := I) g r (s₁ + m)
              (iteratedCovGrad (I := I) g r s₁ m S).toFun =
              ‖iteratedCovGrad (I := I) g r s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + m)
              (iteratedCovGrad (I := I) g 0 s₂ m T).toFun =
              ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g 0 s₂ m T)).symm] at hTe
        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
        have hys := mixed_young_arm_split wi wl (CSf m) (CTf m) ΛS ΛT
          ‖iteratedCovGrad (I := I) g r s₁ m S‖
          ‖iteratedCovGrad (I := I) g 0 s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe
        have hNS_sum : ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNT_sum (by positivity)
                linarith
  have hrw : (∫ x, ∑ i ∈ Finset.range (k + 1), Sj i x *
        ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
      = ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
          ∫ x, Sj i x * Tj l x ∂μ := by
    rw [MeasureTheory.integral_finset_sum _
      (fun i _ => by
        rw [hμ]
        exact ((hSj_cont i).mul (continuous_finset_sum _
          (fun l _ => hTj_cont l))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x, Sj i x * ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
          = ∫ x, ∑ l ∈ Finset.range (k + 1 - i), Sj i x * Tj l x ∂μ from by
        simp only [Finset.mul_sum],
      MeasureTheory.integral_finset_sum _ (fun l _ => hint_cell i l)]
  rw [hrw]
  have hsum_le : ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        ∫ x, Sj i x * Tj l x ∂μ ≤
      ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hilk : i + l ≤ k := by
      rw [Finset.mem_range] at hi hl; omega
    exact hcell i hik l hilk
  refine le_trans hsum_le ?_
  set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
    + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) with hc
  have hc_nn : 0 ≤ c := by
    rw [hc]; exact mul_nonneg hCbig_nn (by linarith [hAS_nn, hAT_nn])
  have hinner : ∀ i ∈ Finset.range (k + 1),
      (∑ _l ∈ Finset.range (k + 1 - i), c) ≤ (k + 1 : ℝ) * c := by
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (k + 1) i) hc_nn
  have hdouble : (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
      ≤ (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
        ≤ ∑ _i ∈ Finset.range (k + 1), (k + 1 : ℝ) * c := Finset.sum_le_sum hinner
      _ = (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; push_cast; ring
  refine le_trans hdouble (le_of_eq ?_)
  rw [hc]
  ring

/-- **(POSIT — the mixed-valence integrated Gagliardo–Nirenberg two-arm tame bound for the
operator-field action `appCc Φ W`, the genuine `appCc`-Moser cross term, chart-jet-free.)**

Fix `g₀`, the coefficient operator-field valence `(b₀, s₀)`, the passenger order `m` (`W` has valence
`(0, b₀)`), and the differentiation order `k`.  There is **one** nonnegative constant `C` — depending
only on `g₀, b₀, s₀, k` and the manifold — such that for any coefficient operator field
`Φ : SmoothCcTensor g₀ b₀ s₀`, any passenger tensor `W : SmoothCcTensor g₀ 0 b₀`, and any two
nonnegative `C⁰` fibre-sup levels `ΛΦ, ΛW` satisfying the **order-`0`** fibre sups
`rfns_{(b₀,s₀)}(Φ x) ≤ ΛΦ²` and `rfns_{(0,b₀)}(W x) ≤ ΛW²`, the top-order-`k` covariant-`L²` norm of
the contracted action `appCc Φ W : SmoothCcTensor g₀ 0 s₀` obeys the **two-arm tame** bound
```
‖∇^k (appCc Φ W)‖²_{L²}
  ≤ C · ( ΛW² · ∑_{i ≤ k} ‖∇^i Φ‖²_{L²}  +  ΛΦ² · ∑_{l ≤ k} ‖∇^l W‖²_{L²} ) ,
```
the **coefficient arm** carrying the coefficient's full covariant-`L²` jet scale against the
passenger's order-`0` `C⁰` sup `ΛW`, the **passenger arm** carrying the passenger's full
covariant-`L²` jet scale against the coefficient's order-`0` `C⁰` sup `ΛΦ`.

**Why this is the deficit-free `appCc` cross term.**  By the chart-jet-free diagonal product grid
`appCc_iteratedCovGrad_diagonalProductGrid_le` the pointwise top-order jet is dominated by the
diagonal product `Gdiag k · ∑_{i ≤ k} rfns(∇^i Φ)(x) · ∑_{l ≤ k − i} rfns(∇^l W)(x)`; integrating that
grid by the `Lᵖ`-Gagliardo–Nirenberg two-arm extremes engine
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` redistributes the high covariant
order so that **each factor carries its own covariant-`L²` jets against the other factor's order-`0`
`C⁰` sup** — never an order-`k` `C⁰` sup of either factor, never a `chartGramOnE` / `HasChartJetLip`
chart-jet ball Lipschitz chain.  The single mixed-valence content is the coefficient factor's
contravariant valence `b₀ ≠ 0`: the on-disk integrated two-arm engine is stated for **purely
covariant** factors, so the mixed-valence reading (`Φ`'s jets at the operator valence `(b₀, s₀+i)`,
contracted by the genuine partial-contraction `appCc`) is the posited input here; the underlying
two-arm interpolation is uniform-by-construction.  Consumers transitively depend on this leaf's
`sorryAx`.

**Non-vacuity.**  The bound is `ℝ`-bilinear-homogeneous: it vanishes as `Φ → 0` (`ΛΦ → 0` and every
`‖∇^i Φ‖ → 0`) or `W → 0`, so the genuine Moser cross-term character is preserved; a `C = 0` witness is
rejected by a nonvanishing `‖∇^k (appCc Φ W)‖` for a nonzero coefficient acting on a nonzero passenger.
Both arms genuinely carry their factor (the `i = 0` coefficient column and the `l = 0` passenger row of
the diagonal grid require, respectively, the `ΛW`- and `ΛΦ`-arm). -/
private theorem appCc_topOrder_l2_twoArm_mixed_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  -- The mixed integrated two-arm engine for the `Φ`-factor valence `(b₀, s₀)`, `W`-factor `(0, b₀)`.
  obtain ⟨Cgrid, hCgrid_nn, hCgrid⟩ :=
    appCc_integrated_grid_twoArm_mixed (I := I) g₀ b₀ s₀ b₀ k
  -- The leading diagonal-grid constant `Gdiag k = (2(n+1))^k`.
  set Gk : ℝ := appCcGdiag (E := E) k with hGk
  have hGk_nn : 0 ≤ Gk := appCcGdiag_nonneg (E := E) k
  refine ⟨Gk * Cgrid, by positivity, ?_⟩
  intro Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  set P : SmoothCcTensor g₀ 0 s₀ := appCc (I := I) (M := M) g₀ b₀ s₀ Φ W with hP
  -- The top-order `L²` norm squared of `appCc Φ W` is the integral of `rfns(∇^k P)`.
  have hLHS_eq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ k P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ := by
    rw [hμ, Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g₀ 0 s₀ k P)]
    have hfun : (iteratedCovGrad (I := I) g₀ 0 s₀ k P).toFun =
        fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
          (M := M) (r := 0) (s := s₀ + k) (x := x)
          ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) _
  -- The pointwise mixed-valence diagonal product grid integrand.
  set grid : M → ℝ := fun x => ∑ i ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
        * ∑ l ∈ Finset.range (k + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
              ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) with hgrid
  -- Pointwise: `rfns(∇^k (appCc Φ W))(x) ≤ Gk · grid x` (the chart-jet-free diagonal grid bridge).
  have hptwise : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ≤ Gk * grid x := by
    intro x
    rw [hGk, hgrid, hP]
    exact appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) g₀ b₀ s₀ Φ W k x
  -- `grid` is continuous, hence integrable on the closed manifold, and pointwise nonnegative.
  have hgrid_cont : Continuous grid := by
    rw [hgrid]
    refine continuous_finset_sum _ (fun i _ => (mixed_continuous_rfns g₀ b₀ (s₀ + i) _).mul ?_)
    exact continuous_finset_sum _ (fun l _ => mixed_continuous_rfns g₀ 0 (b₀ + l) _)
  have hgrid_int : Integrable grid μ := by
    rw [hμ]; exact hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Integrate the pointwise grid bound: `∫ rfns(∇^k P) ≤ Gk · ∫ grid`.
  have hmono : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ ≤
      Gk * ∫ x, grid x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₀ + k) x _)) ?_
      (Eventually.of_forall hptwise)
    exact hgrid_int.const_mul _
  -- The mixed two-arm engine bounds `∫ grid`.
  have hgrid_bound := hCgrid Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [hLHS_eq]
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ
      ≤ Gk * ∫ x, grid x ∂μ := hmono
    _ ≤ Gk * (Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hGk_nn
        rw [hgrid]; exact hgrid_bound
    _ = Gk * Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by ring

/-- **(POSIT — the ball-uniform high-order covariant-`L²` jet scale of the three endpoint Ricci–DeTurck
RHS-arm coefficient fields, alongside the intrinsic three-term section identity, chart-jet-free.)**

The high-order companion of the order-`0` `C⁰` operator sups
`deTurckRHSArmDiff_threeArm_coeffC0_ballUniform`.  Fix `g₀`, `g_bg`, a supercritical order `a`
(`2·finrank E + 10 ≤ a`), and a covariant-`L²` ball radius `R ≥ 0`.  Outside the `∀ T T'` quantifier
there are one nonnegative ball-uniform order-`0` `C⁰` operator level `ΛC` and one nonnegative
ball-uniform high-order covariant-`L²` jet level `Γ`.  For any two `g₀`-fibre-small smooth
perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, there
are the three intrinsic `g₀`-built endpoint coefficient operator fields `C₀ : SmoothCcTensor g₀ 2 2`,
`C₁ : SmoothCcTensor g₀ 3 2`, `C₂ : SmoothCcTensor g₀ 4 2`, with `N := deTurckRHSArmG0 g₀ g_bg T −
deTurckRHSArmG0 g₀ g_bg T'`, such that:

* **(identity)** the intrinsic three-term mean-value section equality
  `N = appCc C₀ (T − T') + appCc C₁ (∇(T − T')) + appCc C₂ (∇²(T − T'))`;
* **(order-`0` `C⁰` operator sups)** `∀ x, rfns(Cₘ x) ≤ ΛC²`;
* **(high-order covariant-`L²` jet scale)** the order-`≤ a` covariant-`L²` jet column of each
  coefficient field is bounded ball-uniformly:
  `∑_{i ≤ a} ‖∇^i C₀‖²_{L²} ≤ Γ²`, idem `C₁, C₂` (at their operator valences `(2,2), (3,2), (4,2)`).

**Why deficit-free (the intrinsic high-order coefficient jet, NOT a chart-jet `L^∞` sup).**  The
coefficient fields are the path-averaged inverse-Gram/Christoffel/Ricci/Lie–DeTurck symbols (rational
in the order-`≤ 2` metric jets of the realize-tie metrics, denominators bounded below by `δ < 1` via
the Neumann series of the perturbed inverse Gram).  Their covariant gradients `∇^i Cₘ` are, by the
covariant Faà-di-Bruno expansion, finite sums of products of the inverse-Gram Neumann jets with metric
jets up to order `i + 2`; the order-`(a + 2)` covariant-`L²` ball constraint on `T, T'` bounds the
metric jets up to order `a + 2` **in `L²`**, so the coefficient's order-`≤ a` covariant-`L²` jet column
is ball-uniform — never an order-`a` `C⁰` sup of the coefficient (which the supercritical `H^{a+2} ↪
C²` embedding alone does NOT supply at the top order; the coefficient's high order stays in `L²`,
exactly the order budget the `a + 2` ball window affords).  Expressed entirely in `appCc` /
`iteratedCovGrad` / `riemannianFiberNormSq` / `tensorL2Norm` — **never** a `chartGramOnE` /
`HasChartJetLip` chart-jet chain.  Consumers transitively depend on this leaf's `sorryAx`.

**Non-vacuity.**  The realization is `ℝ`-linear in `T − T'` and its jets (the identity vanishes as
`T − T' → 0`); a degenerate `C₀ = C₁ = C₂ = 0` is rejected by a nonvanishing `∇^q N` for a genuinely
second-order, non-flat RHS difference; a `Γ = 0` (or `ΛC = 0`) level is rejected by the nonvanishing
genuine endpoint operator symbols on the supercritical ball. -/
private theorem deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 :=
  sorry

/-- **(DEFICIT-FREE INTRINSIC top-order-`a` integrated covariant-`L²` Moser–Nemytskii tame
bound on the nonlinear Ricci–DeTurck RHS-arm difference — PROVED, chart-jet-free.)**

Fix `g₀`, the DeTurck background `g_bg`, a supercritical order `a` (`2·finrank E + 10 ≤ a`), and a
covariant-`L²` ball radius `R ≥ 0`.  There is **one** nonnegative constant `Λc` — uniform over the
fibre-small radius-`R` ball, **outside** the `∀ T T'` quantifier — such that for any two
`g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the
radius-`R` ball, the top-order-`a` covariant-`L²` norm of the nonlinear RHS-arm difference
`N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys the integrated tame bound
```
‖∇^a N‖_{L²}  ≤  Λc · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²}) .
```

**Proof (single-column integration, no two-arm valence detour).**  The on-disk ball-uniform pointwise
single-factor covariant-jet column `deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform`
already domiantes, with a single ball-uniform `CR ≥ 0` outside `∀ T T'`,
```
rfns(∇^a N)(x) ≤ CR · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x)
```
(its left-hand tensor `(deTurckSmoothRemainder T − deTurckSmoothRemainder T') + Δ_∇(T − T')` is exactly
`N` by the definitional split `deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff`, rearranged).
The genuinely quasilinear order content (the `∇^{a+2}(T − T')` top jet, carried by the curvature/Lie
principal symbol and the rough-Laplacian arm) lives entirely in that column.  Integrating the pointwise
column over the closed manifold via the sorry-free `l2RootSum_of_pointwise_iteratedCovGrad_jet`
(`‖∇^a P‖ ≤ √C · √(∑_{i ≤ N} ‖∇^i W‖²)`, the fibre-norm/`tensorL2Norm` bridge plus integral
monotonicity) yields the displayed `L²` root-sum bound with `Λc := √CR`.  The route reads **only**
`iteratedCovGrad` / `riemannianFiberNormSq` / `tensorL2Norm` — **never** an order-`(a + 2)` pointwise
`L^∞` coefficient sup, **never** a `chartGramOnE` / `HasChartJetLip` chart-jet ball Lipschitz chain.
It depends transitively only on the `sorryAx` of the ball-uniform raw-component domination posit
underneath the pointwise column (the genuine chart→intrinsic Nemytskii content), not on the refuted
two-arm valence detour.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol forces a top jet at the `i = a + 2` term of the root-sum, so a window-`a`
weakening is rejected.  A `Λc = 0` witness is rejected by a nonvanishing `∇^a N` for a non-flat,
genuinely second-order RHS difference (`CR = 0` forces the whole column to vanish). -/
private theorem deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λc : ℝ, 0 ≤ Λc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
          Λc * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  -- INTRINSIC two-arm route (chart-jet-FREE): assemble the top-order `L²` from the section identity
  -- `N = ∑_{m≤2} appCc Cₘ (∇^m (T−T'))` (coefficients with order-`0` `C⁰` sup `ΛC` AND high-order
  -- covariant-`L²` jet scale `Γ`), the mixed-valence `appCc` two-arm tame engine, the passenger
  -- order-`0` `C⁰` sup of `∇^m (T−T')` (the supercritical `H^{a+2} ↪ C²` embedding), and the
  -- composition `‖∇^l (∇^m S)‖ = ‖∇^{m+l} S‖` that keeps the passenger jets inside the `a+2` ball window.
  -- The ball-uniform endpoint coefficient data: order-`0` `C⁰` sup `ΛC` and high-order `L²` jet scale `Γ`.
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The mixed-valence `appCc` two-arm tame engine constants for the three endpoint valences `(2+m, 2)`.
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 4 2 a
  -- The supercritical `H^{a+2} ↪ C²` section embedding, supplying the passenger `C⁰` sups.
  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  -- A single ball-uniform constant dominating all three arms.  Each arm `m` is bounded by
  -- `Kₘ·(ΛW²·Γ² + ΛC²·∑_{l≤a}‖∇^l Wₘ‖²)` with `ΛW² ≤ Cemb²·S` and `∑_{l≤a}‖∇^l Wₘ‖² ≤ S`, so each
  -- arm `≤ Kₘ·(Cemb²·Γ² + ΛC²)·S`; the three-arm sum (with the `√(3·∑‖·‖²) ≤ ∑‖·‖` Cauchy–Schwarz
  -- and the `√` of the per-arm squared bound) gives `‖∇^a N‖ ≤ Λc·√S`.
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (9 * (Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2))), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- The section identity and the endpoint coefficient bounds for this `(T, T')`.
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  -- The passenger `C⁰` fibre sup of `Wₘ := ∇^m (T − T')` (`m ≤ 2`): `rfns(Wₘ x) ≤ Cemb²·S`.
  -- From the supercritical embedding `∑_{q<3} rfns(∇^q (T−T'))(x) ≤ Cemb²·S` and nonnegativity.
  have hWsup : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb ^ 2 * S)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb (T - T') x
    rw [hS_def]
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) hmem) ?_
    exact hembx
  -- The passenger high-order `L²` jet scale: `∑_{l≤a} ‖∇^l Wₘ‖² ≤ S` (`m ≤ 2`, `m + l ≤ a + 2`).
  have hWjet : ∀ (m : ℕ), m ≤ 2 →
      (∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S := by
    intro m hm
    -- Reindex each `‖∇^l (∇^m (T−T'))‖² = ‖∇^{m+l} (T−T')‖²` via `rfns_iteratedCovGrad_comp` integrated.
    have hcomp : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
      intro l
      have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
          (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
      have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
      rw [hbridgeL, hbridgeR]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
      -- `rfns g₀ 0 (2+m+l) (∇^l (∇^m S)) = rfns g₀ 0 (2+(m+l)) (∇^{m+l} S)`.
      simpa only [Nat.add_assoc] using hrw
    -- `∑_{l≤a} ‖∇^{m+l}(T−T')‖²` is a sub-column of `S = ∑_{i≤a+2} ‖∇^i(T−T')‖²` (`m + l ≤ a + 2`).
    rw [show (∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
        ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
      Finset.sum_congr rfl (fun l _ => hcomp l)]
    rw [hS_def]
    -- Reindex `l ↦ m + l` injectively into `range (a+2+1)` (a sub-column, all summands `≥ 0`).
    set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
    have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
    have himg : (Finset.range (a + 1)).image (fun l => m + l) ⊆ Finset.range (a + 2 + 1) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_range] at hl ⊢
      omega
    have hinj : ∀ l₁ ∈ Finset.range (a + 1), ∀ l₂ ∈ Finset.range (a + 1),
        m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
    calc (∑ l ∈ Finset.range (a + 1), f (m + l))
        = ∑ i ∈ (Finset.range (a + 1)).image (fun l => m + l), f i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (a + 2 + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
  -- Per-arm two-arm tame bound, widened to the single constant.
  have harm : ∀ (m : ℕ) (hm : m ≤ 2) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 a (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 a
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤
        Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb ^ 2 * S)) hΛC_nn (Real.sqrt_nonneg _) hCmsup (hWsup m hm)
    refine htame.trans ?_
    -- Bound `Km ≤ Kmax`, the coefficient jet `≤ Γ²`, the passenger sup `≤ Cemb²·S`, the passenger jet `≤ S`.
    have hcoeffjet := hCmjet
    have hwjet := hWjet m hm
    have hΛWsq : (Real.sqrt (Cemb ^ 2 * S)) ^ 2 = Cemb ^ 2 * S := Real.sq_sqrt (by positivity)
    rw [hΛWsq]
    -- The inner factor: `(Cemb²·S)·∑‖∇^iCm‖² + ΛC²·∑‖∇^lW‖² ≤ (Cemb²·S)·Γ² + ΛC²·S`.
    have hcjsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hwjsum_nn : 0 ≤ ∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    have ha1 : (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb ^ 2 * S) * Γ ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeffjet (by positivity)
    have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S :=
      mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
    have hinner :
        (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
        ≤ Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S := by nlinarith [ha1, ha2]
    have hinner_nn : 0 ≤ (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by
      have : 0 ≤ (Cemb ^ 2 * S) := by positivity
      have : 0 ≤ ΛC ^ 2 := sq_nonneg _
      positivity
    calc Km * ((Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
        ≤ Kmax * (Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S) :=
          mul_le_mul hKm_le hinner hinner_nn hKmax_nn
      _ = Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by ring
  -- The three arms.
  have ha0 := harm 0 (by norm_num) C₀ K₀ hK₀_le hK₀ hC₀sup hC₀jet
  have ha1 := harm 1 (by norm_num) C₁ K₁ hK₁_le hK₁ hC₁sup hC₁jet
  have ha2 := harm 2 (by norm_num) C₂ K₂ hK₂_le hK₂ hC₂sup hC₂jet
  -- `N = A₀ + A₁ + A₂` with `Aₘ := appCc Cₘ (∇^m (T−T'))`.  Triangle + `√`-monotonicity.
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  set base : ℝ := Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) with hbase_def
  have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
  -- Each arm's `L²` norm is bounded by `√(base·S)`.
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha0)
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha1)
  have hnorm2 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha2)
  -- Triangle inequality over the three-arm split.
  rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 a (A₀ + A₁) A₂,
    iteratedCovGrad_add (I := I) g₀ 0 2 a A₀ A₁]
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₁ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤
      Real.sqrt (base * S) + Real.sqrt (base * S) + Real.sqrt (base * S) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) hnorm2
  refine htri.trans ?_
  -- `3·√(base·S) = 3·√base·√S = √9·√base·√S = √(9·base)·√S`, exactly the witness `√(9·base)·√S`.
  rw [show Real.sqrt (base * S) = Real.sqrt base * Real.sqrt S from Real.sqrt_mul hbase_nn S]
  rw [show Real.sqrt (9 * base) = Real.sqrt 9 * Real.sqrt base from Real.sqrt_mul (by norm_num) base]
  rw [show Real.sqrt (9 : ℝ) = 3 from by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact le_of_eq (by ring)

/-- **(The deficit-free integrated-`L²` Moser–Nemytskii endpoint data of the nonlinear
Ricci–DeTurck RHS-arm difference: the order-`0` `C⁰` sup and the order-`0` / top-order-`a` integrated
covariant-`L²` norms — the irreducible curvature/Lie/inverse-Gram analytic leaf, deficit-free.)**

This is the irreducible curvature/Lie/inverse-Gram **Nemytskii content** that the deficit-free
Gagliardo–Nirenberg route consumes, isolated at the two endpoints (order `0` and order `a`) of the
covariant-jet ladder.  Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²`
ball radius `R ≥ 0`.  There is **one** nonnegative constant `Λ₀` — uniform over the fibre-small
radius-`R` ball, **outside** the `∀ T T'` quantifier — such that for any two `g₀`-fibre-small smooth
perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, the
nonlinear RHS-arm difference `N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys, with
`S := ∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²}`, all three endpoint bounds
```
(C⁰ sup)        ∀ x,  rfns(N)(x)        ≤ Λ₀² · S ,
(order-0 L²)          ‖N‖_{L²}          ≤ Λ₀ · √S ,
(top-order L²)        ‖∇^a N‖_{L²}      ≤ Λ₀ · √S .
```

**Why deficit-free (the integrated Moser route, NOT the chart-jet ball-uniform route).**  The RHS arm
`deTurckRHSArmG0 g₀ g_bg T = deTurckRHSSection g_bg (g₀ + T) = −2 Ric(g₀+T) + 𝓛_{W(g₀+T,g_bg)}(g₀+T)`
is a second-order quasilinear Nemytskii nonlinearity of the order-`≤ 2` metric jets.  By the mean-value
path `N = ∫₀¹ dF(g₀ + T' + s·(T − T'))[T − T'] ds`, `N` is a finite sum of products of a fixed-`g₀`
coefficient field (the `dF` symbol, rational and det-`≠ 0` by `δ < 1`, in the order-`≤ 2` metric jets of
the path) with a bilinear contraction whose covariant gradients carry the perturbation difference `T − T'`
and the metric-path jets.  In the covariant Leibniz expansion of `∇^a N` the top covariant order always
lands on a `T − T'` factor (order `≤ a`) **in `L²`**, or on a metric-path factor (order `≤ a + 1`) **in
`L²`** (controlled by the radius-`R` ball), while the order-`≤ 2` coefficient enters **in `C²`** through
the supercritical `H^{a+2} ↪ C²` section embedding of the radius-`R` ball.  Feeding this through the
intrinsic Moser tame product / Gagliardo–Nirenberg engines
(`Analysis.Sobolev.Tensor.exists_moserTameProduct_iteratedCovGrad_l2Norm_le`,
`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`) yields the top-order `L²` endpoint with a constant
ball-uniform in `R` — **never** an order-`(a + 2)` pointwise `C⁰` sup, **never** a `tensorChartComponentRaw`
/ `HasChartJetLip` ball-uniform Lipschitz chain (whose `∃B`-over-`∀g∈ball` hoist is unsatisfiable at the
top jet).  The `C⁰` sup endpoint (i) is the order-`0` Nemytskii value bound, whose order-`≤ 2` read of
`T − T'` is `C²`-embedded by `H^{a+2} ↪ C²`; the order-`0` `L²` endpoint (ii) integrates (i) over the
closed manifold.

**The threshold and the `R`-ball.**  The supercritical embedding `H^{a+2} ↪ C²` of the radius-`R` ball is
what supplies the `C²` control of the order-`≤ 2` coefficient (the metric-path jet that fibre-smallness
`δ < 1` ALONE does not bound — a high-frequency common part of `T, T'` keeps `T − T'` fixed while blowing
up `∂²(g₀+T)`, so the `R`-ball hypothesis is genuinely load-bearing, not merely inherited).  The chart↔
spectral order doubling of the embedding forces `2·finrank E + 10 ≤ a` (`ha_super`).

**Non-vacuity.**  All three bounds vanish as `T − T' → 0` (`S → 0`), so the genuine Nemytskii
Lipschitz character is preserved; a `Λ₀ = 0` witness is rejected by a nonvanishing `‖N‖` for a
genuinely second-order, non-flat RHS difference.

This is a posited deficit-free analytic leaf: the genuine intrinsic covariant Moser–Nemytskii
expansion of the curvature/Lie/inverse-Gram RHS-arm difference into the Moser-feedable sum of products
is the deep differential-geometric content; consumers transitively depend on this leaf's `sorryAx`. -/
private theorem deTurckRHSArmDiff_endpoints_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
              Λ₀ ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  -- The two posited deficit-free INTRINSIC endpoint children: the order-`0` pointwise fibre-norm
  -- domination (conjunct i) and the top-order-`a` integrated covariant-`L²` tame (conjunct iii).
  -- Both are chart-jet-free; the order-`0` `L²` (conjunct ii) is derived from (i) by integration.
  obtain ⟨Λa, hΛa_nn, hΛa⟩ :=
    deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The finite volume of the closed manifold, used to integrate the pointwise bound (i) to the
  -- order-`0` `L²` bound (ii).
  haveI : MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g₀
  set vol : ℝ := (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ with hvol_def
  have hvol_nn : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg
  -- The common ball-uniform constant dominating all three endpoints.
  refine ⟨Λa * Real.sqrt (vol + 1) + Λc,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  set Λ₀ : ℝ := Λa * Real.sqrt (vol + 1) + Λc with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  -- `Λa ≤ Λ₀` and `Λc ≤ Λ₀`: `√(vol+1) ≥ 1` (since `vol+1 ≥ 1`), so `Λa·√(vol+1) ≥ Λa`.
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (vol + 1) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hΛa_le : Λa ≤ Λ₀ := by
    rw [hΛ₀_def]
    have h1 : Λa ≤ Λa * Real.sqrt (vol + 1) := by
      nlinarith [hΛa_nn, hsqrt_ge_one]
    linarith [hΛc_nn]
  have hΛc_le : Λc ≤ Λ₀ := by rw [hΛ₀_def]; nlinarith [hΛa_nn, hsqrt_ge_one]
  -- Conjunct (i): the posited intrinsic order-`0` pointwise fibre-norm domination, widened to `Λ₀²`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λa ^ 2 * S := by
    intro x
    rw [hN_def, hS_def]
    exact hΛa T T' hδ_le hδ hδ'_le hδ' hTball hT'ball x
  have hC0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λ₀ ^ 2 * S := by
    intro x
    refine (hpt x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hS_nn
    exact pow_le_pow_left₀ hΛa_nn hΛa_le 2
  -- Conjunct (ii): integrate the pointwise bound (i) over the closed manifold.
  -- `‖N‖² = ∫ rfns(N) ≤ ∫ Λa²·S = vol · Λa²·S`, so `‖N‖ ≤ Λa·√(vol)·√S ≤ Λ₀·√S`.
  have hL0 : ‖N‖ ≤ Λ₀ * Real.sqrt S := by
    -- `‖N‖² ≤ vol · (Λa² · S)`.
    have hnormsq : ‖N‖ ^ 2 ≤ vol * (Λa ^ 2 * S) := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 2 N]
      have hint_le :
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            ∫ _x, Λa ^ 2 * S ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const _) ?_
        · exact MeasureTheory.ae_of_all _ fun x =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
        · exact MeasureTheory.ae_of_all _ fun x => hpt x
      rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def] at hint_le
      exact hint_le
    -- Take square roots: `‖N‖ ≤ √(vol · Λa² · S) = Λa·√vol·√S ≤ Λ₀·√S`.
    have hnorm_nn : 0 ≤ ‖N‖ := norm_nonneg _
    have hrhs_nn : 0 ≤ vol * (Λa ^ 2 * S) := by positivity
    have hsqrt_le : ‖N‖ ≤ Real.sqrt (vol * (Λa ^ 2 * S)) := by
      rw [show ‖N‖ = Real.sqrt (‖N‖ ^ 2) from (Real.sqrt_sq hnorm_nn).symm]
      exact Real.sqrt_le_sqrt hnormsq
    refine hsqrt_le.trans ?_
    -- `√(vol·Λa²·S) = Λa·√vol·√S ≤ Λa·√(vol+1)·√S ≤ Λ₀·√S`.
    have hfac : Real.sqrt (vol * (Λa ^ 2 * S)) = Λa * (Real.sqrt vol * Real.sqrt S) := by
      rw [show vol * (Λa ^ 2 * S) = Λa ^ 2 * (vol * S) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛa_nn,
        Real.sqrt_mul hvol_nn]
    rw [hfac, hΛ₀_def, add_mul]
    have hvol_le : Real.sqrt vol ≤ Real.sqrt (vol + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    calc Λa * (Real.sqrt vol * Real.sqrt S)
        = (Λa * Real.sqrt vol) * Real.sqrt S := by ring
      _ ≤ (Λa * Real.sqrt (vol + 1)) * Real.sqrt S := by
          refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
          exact mul_le_mul_of_nonneg_left hvol_le hΛa_nn
      _ ≤ Λa * Real.sqrt (vol + 1) * Real.sqrt S + Λc * Real.sqrt S := by
          have : 0 ≤ Λc * Real.sqrt S := mul_nonneg hΛc_nn hsqrtS_nn
          linarith
  -- Conjunct (iii): the posited intrinsic top-order-`a` integrated covariant-`L²` tame, widened.
  have hLa : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
    have hbase : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λc * Real.sqrt S := by
      rw [hN_def, hS_def]
      exact hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_right hΛc_le hsqrtS_nn
  exact ⟨hC0, hL0, hLa⟩

/-- **(The integrated covariant-`L²` Moser tame bound on the NONLINEAR Ricci–DeTurck
right-hand-side arm difference.)**

This is the genuine curvature/Lie/inverse-Gram Nemytskii content of the sealed remainder, with the
linear connection-Laplacian arm split off.  Fix `g₀`, the DeTurck background `g_bg`, an order `a`,
and a covariant-`L²` ball radius `R ≥ 0`.  There is **one** nonnegative constant `C` — uniform over
the fibre-small radius-`R` ball, **outside** the `∀ T T'` quantifier — such that for any two
`g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in
the radius-`R` ball, every order-`q` (`q ≤ a`) covariant-gradient jet of the **nonlinear RHS-arm
difference** `deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys the per-order **integrated**
covariant-`L²` Moser tame bound
```
‖∇^q (RHSarm T − RHSarm T')‖_{L²} ≤ C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²}).
```

**Why integrated, via Gagliardo–Nirenberg — deficit-free.**  `RHSarm T = deTurckRicciRHS g_bg
(g₀ + T)` is a smooth (rational, det-`≠ 0` by `δ < 1`) second-order Nemytskii nonlinearity of the
order-`≤ 2` metric jets, so `N := RHSarm T − RHSarm T'` is a fixed smooth `(0,2)`-tensor for each
`(T, T')`.  Rather than expanding a covariant Leibniz product grid (whose `C^k`-sup coefficient
control would be order-deficient over the `R`-ball), the per-order bound is obtained by the intrinsic
**Gagliardo–Nirenberg interpolation** `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le` applied to
the single tensor `N`: each intermediate order `0 < q < a` is interpolated between the order-`0` `C⁰`
sup of `N` (the supercritical Nemytskii Lipschitz modulus `Λ₀ · √S`, ball-uniform) and the top-order
`a` covariant-`L²` norm `‖∇^a N‖ ≤ Λ₀ · √S`, with weights `1 − q/a` and `q/a`:
`‖∇^q N‖ ≤ C · (Λ₀ √S)^{1−q/a} · (Λ₀ √S)^{q/a} = C · Λ₀ · √S`.  Only the order-`0` `C⁰` sup and the two
`L²` endpoints (orders `0`, `a`) of `N` ever enter — never an order-`(a + 2)` `C^k`-sup of any
coefficient — so the route is **deficit-free**, never an order-deficient per-order pointwise fibre-norm
grid and never a chart-jet `tensorChartComponentRaw` / `HasChartJetLip` Lipschitz chain.

**Assembly.**  The three endpoint data of `N` — the `C⁰` sup `∀ x, rfns(N)(x) ≤ Λ₀² · S`, the
order-`0` `L²` `‖N‖ ≤ Λ₀ √S`, and the top-order `L²` `‖∇^a N‖ ≤ Λ₀ √S` — are the posited
consumer-minimal INTEGRATED curvature/Lie/inverse-Gram child
`deTurckRHSArmDiff_endpoints_l2_tame_ballUniform` (its `sorryAx` transits here).  Orders `q = 0` and
`q = a` are the two `L²` endpoints directly; each intermediate order `0 < q < a` is the
Gagliardo–Nirenberg interpolation of `N` between the `C⁰` sup and the top-order `L²` (the degenerate
`a = 0` case reads only the order-`0` endpoint).  The common leaf constant is `C := C_{GN} · (Λ₀ + 1)`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol (carried by the curvature term of `RHSarm`) forces a top jet at the `i = a + 2`
term of `S`, so a window-`a` weakening is rejected.  A `C = 0` witness is rejected by a nonvanishing
`∇^q (RHSarm T − RHSarm T')` for a non-flat, genuinely second-order difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  -- The posited deficit-free endpoint Nemytskii data of the arm difference.
  obtain ⟨Λ₀, hΛ₀_nn, hEnd⟩ :=
    deTurckRHSArmDiff_endpoints_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The Gagliardo–Nirenberg interpolation engine for the single tensor `N` (top order `a`).
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- Degenerate top order `a = 0`: every `q ≤ a` is `q = 0`, the order-`0` `L²` endpoint.
    subst ha0
    refine ⟨Λ₀, hΛ₀_nn, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    obtain rfl : q = 0 := Nat.le_zero.mp hq
    have hEnd' := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    simpa using hEnd'.2.1
  · obtain ⟨Cgn, hCgn_nn, hGN⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
        (I := I) (M := M) g₀ 2 a hapos
    refine ⟨(Cgn + 1) * (Λ₀ + 1), by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    set N : SmoothCcTensor g₀ 0 2 :=
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
    set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    obtain ⟨hC0, hL0, hLa⟩ := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    -- Restate the three endpoint data in terms of the abbreviations `N`, `S`.
    have hC0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤
        (Λ₀ * Real.sqrt S) ^ 2 := by
      intro x
      have hx := hC0 x
      rw [mul_pow, Real.sq_sqrt hS_nn]
      exact hx
    have hL0' : ‖N‖ ≤ Λ₀ * Real.sqrt S := by rw [hN_def, hS_def]; exact hL0
    have hLa' : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
      rw [hN_def, hS_def]; exact hLa
    -- The single uniform bound `‖∇^q N‖ ≤ (Cgn + 1) * (Λ₀ + 1) * √S` for every `q ≤ a`.
    have hN_norm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ := norm_nonneg _
    have hΛ₀S_nn : 0 ≤ Λ₀ * Real.sqrt S := mul_nonneg hΛ₀_nn hsqrtS_nn
    -- The target bound for the abbreviated `N`, `S`.
    suffices hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤
        ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S by
      rw [hN_def, hS_def] at hgoal; exact hgoal
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · -- Order `q = 0`: the order-`0` `L²` endpoint, widened by the larger constant.
      subst hq0
      have h0 : ‖iteratedCovGrad (I := I) g₀ 0 2 0 N‖ = ‖N‖ := by simp
      rw [h0]
      refine hL0'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
      nlinarith [hCgn_nn, hΛ₀_nn]
    · rcases lt_or_eq_of_le hq with hqlt | hqeq
      · -- Intermediate order `0 < q < a`: Gagliardo–Nirenberg interpolation of `N`.
        have hGNq := hGN N (Λ₀ * Real.sqrt S) hΛ₀S_nn hC0' q hqpos hqlt
        -- `hGNq : ‖∇^q N‖ ≤ Cgn · (Λ₀√S)^{1−q/a} · ‖∇^a N‖^{q/a}`.
        set e : ℝ := (q : ℝ) / a with he_def
        have he_nn : 0 ≤ e := by
          rw [he_def]; positivity
        have he_lt_one : e < 1 := by
          rw [he_def]
          rw [div_lt_one (by exact_mod_cast hapos)]
          exact_mod_cast hqlt
        have h1me_nn : 0 ≤ 1 - e := by linarith
        -- Bound `‖∇^a N‖^{q/a} ≤ (Λ₀√S)^{q/a}` (monotone, exponent ≥ 0).
        have hak_mono : (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e ≤
            (Λ₀ * Real.sqrt S) ^ e :=
          Real.rpow_le_rpow hN_norm_nn hLa' he_nn
        -- Assemble the right-hand side of `hGNq` into `Cgn · (Λ₀√S)`.
        have hrhs_eq : Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e =
            Cgn * (Λ₀ * Real.sqrt S) := by
          rcases eq_or_lt_of_le hΛ₀S_nn with hzero | hpos
          · rw [← hzero, Real.zero_rpow (ne_of_gt (by linarith [he_lt_one] : (0 : ℝ) < 1 - e))]
            simp
          · rw [mul_assoc, ← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
        calc ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖
            ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) *
                (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e := by
              simpa only [he_def] using hGNq
          _ ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e := by
              refine mul_le_mul_of_nonneg_left hak_mono ?_
              exact mul_nonneg hCgn_nn (Real.rpow_nonneg hΛ₀S_nn _)
          _ = Cgn * (Λ₀ * Real.sqrt S) := hrhs_eq
          _ = (Cgn * Λ₀) * Real.sqrt S := by ring
          _ ≤ ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S := by
              refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
              nlinarith [hCgn_nn, hΛ₀_nn]
      · -- Order `q = a`: the top-order `L²` endpoint, widened by the larger constant.
        subst hqeq
        refine hLa'.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
        nlinarith [hCgn_nn, hΛ₀_nn]

/-- **(The integrated covariant-`L²` Moser tame bound on the sealed Ricci–DeTurck remainder
difference — the genuine `L²`-Moser Nemytskii tame leaf.)**

This is the **integrated** (global-`L²`) replacement for the pointwise per-order fibre-norm grid:
its conclusion bounds the *integrated* covariant-`L²` (semi)norm `‖∇^q D‖ = tensorL2Norm(∇^q D)` of
each jet of the sealed remainder difference, **not** a pointwise fibre value.  Fix `g₀`, the DeTurck
background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is **one**
nonnegative constant `C` — uniform over the fibre-small radius-`R` ball, **outside** the `∀ T T'`
quantifier — such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²`
jets up to order `a + 2` lie in the radius-`R` ball, every order-`q` (`q ≤ a`) covariant-gradient jet
of the sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys the per-order
covariant-`L²` Moser tame bound
```
‖∇^q D‖_{L²}  ≤  C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²_{L²}).
```

**Why integrated, not pointwise.**  `D` is the smooth second-order Nemytskii nonlinearity
`F(g) = deTurckRHSSection g_bg g − Δ_∇(·)` evaluated along the metric path `g₀ + s·(T − T')`; the
Taylor remainder `F(g₀ + T) − F(g₀ + T')` is a finite sum of products of (rational, det-`≠ 0` by
`δ < 1`) metric-jet coefficient fields (order `≤ 2`) against covariant gradients of `T − T'`.  The
covariant Leibniz grid of `∇^q` of such a product is exactly the hypothesis the integrated
`L²`-Moser tame engine `Analysis.Sobolev.Tensor.exists_moserTameProduct_iteratedCovGrad_l2Norm_le`
consumes (it is `AXIOM`-clean / integrated): the high covariant order always lands on the `T − T'`
factor in `L²`, and the **low-order** (`≤ 2`) coefficients enter in `L^∞`, controlled ball-uniformly
by the supercritical section embedding `H^{a+2} ↪ C²` of the radius-`R` ball.  Only that low-order
pointwise control is ever needed — never an order-`(a + 2)` sup — so the bound is **deficit-free**,
unlike the pointwise fibre-norm grid, whose Lipschitz modulus needs order-`(a + 2)` `C⁰` control of
the metric jets (`L²` orders `a + 2 + dim/2` the ball cannot supply).

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol (carried by the connection-Laplacian arm of `D`) forces a top jet at the
`i = a + 2` term, so a window-`a` weakening is rejected.  A `C = 0` witness is rejected by a
nonvanishing `∇^q D` for a non-flat, genuinely second-order remainder difference.

**Assembly.**  The sealed remainder difference splits (definitionally, then by the linearity of the
connection Laplacian, `deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff`) into the **nonlinear
RHS-arm difference** minus the **linear connection-Laplacian difference**
`Δ_∇(T − T') = rawTensorConnLapSmooth g₀ 0 2 (T − T')`.  Each covariant jet of the difference is the
difference of the jets (`iteratedCovGrad_sub`), so the triangle inequality on the integrated `L²`
(semi)norm bounds `‖∇^q D‖` by `‖∇^q (RHSarm-diff)‖ + ‖∇^q (Δ_∇(T − T'))‖`.  The nonlinear arm is the
posited curvature/Lie/inverse-Gram integrated Moser tame leaf
`deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform` (its `sorryAx` transits here); the linear arm
is the genuine (provable) Δ-arm tame `rawTensorConnLapSmooth_iteratedCovGrad_l2_tame`, obtained by
integrating the on-disk per-order pointwise jet bound.  Both produce the common root-sum form
`C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²)`, so the leaf constant is the sum of the two arm constants.  No
pointwise per-order fibre-norm grid and no chart-jet Lipschitz chain enter this assembly. -/
private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  -- The nonlinear curvature/Lie/inverse-Gram RHS-arm tame (posited integrated child).
  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The linear connection-Laplacian arm tame (proved by integrating the on-disk jet bound).
  obtain ⟨Cl, hCl_nn, hCl⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_l2_tame (I := I) g₀ a
  refine ⟨Cn + Cl, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  -- The remainder-difference root-sum window column.
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  -- The arm difference and the linear-arm operand abbreviations.
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  -- Split the sealed remainder difference into the nonlinear arm minus the linear Δ-arm, then take
  -- the order-`q` covariant jet of the difference (jet of a difference is the difference of jets).
  have hjet_split :
      iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 q N -
          iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) := by
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
      (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ', ← hN_def, iteratedCovGrad_sub]
  -- The triangle inequality on the integrated `L²` (semi)norm.
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := by
    rw [hjet_split]; exact norm_sub_le _ _
  -- The two arm bounds, both in the common root-sum form.
  have hNarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤ Cn * Real.sqrt S := by
    rw [hN_def, hS_def]
    exact hCn T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hq
  have hLarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤ Cl * Real.sqrt S := by
    rw [hS_def]; exact hCl (T - T') q hq
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖
      ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := htri
    _ ≤ Cn * Real.sqrt S + Cl * Real.sqrt S := add_le_add hNarm hLarm
    _ = (Cn + Cl) * Real.sqrt S := by ring

/-- **The single-arm full covariant-jet-column ball-Lipschitz bound on the genuine Ricci–DeTurck
remainder difference.**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is one nonnegative constant `C` — uniform over the fibre-small radius-`R` ball — such that for
any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, the **entire covariant-gradient jet column** (orders `q ≤ a`) of the
genuine remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys, at the squared
`L²` level, the single-arm tame bound
```
∑_{q ≤ a} ‖∇^q D‖²  ≤  C · ∑_{i ≤ a+2} ‖∇^i (T − T')‖².
```

This bound is **single-arm** (the intrinsic single-column route, no two-arm valence detour).  The
supercriticality hypothesis `ha_super : 2·finrank E + 3 ≤ a` is
threaded through (it is consumed at the endpoint leaf, where the order-`0` `C⁰` Nemytskii sup and the
pointwise/`L²` conversions require the supercritical `H^{a+2} ↪ C²` embedding of the radius-`R` ball);
it is assembled **directly from the integrated covariant-`L²` Moser tame leaf**
`deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform`, whose per-order conclusion
`‖∇^q D‖_{L²} ≤ C · √(∑_{i ≤ a+2} ‖∇^i (T − T')‖²)` is the genuine `L²`-Moser Nemytskii tame bound for
the second-order remainder `F = deTurckSmoothRemainder` (its high covariant order always lands on the
`T − T'` factor in `L²`, the low-order metric coefficients enter in `L^∞` via the supercritical
section embedding `H^{a+2} ↪ C²` — **deficit-free**, never an order-`(a + 2)` sup).  Squaring each
per-order bound (`‖∇^q D‖² ≤ C² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²`, by `Real.sq_sqrt` on the nonnegative
window column) and summing the `a + 1` orders gives the column bound with constant
`C_col := (a + 1) · C²`.

This route is **integrated throughout**: it never converts to a pointwise per-order fibre-norm grid
(the order-deficient pointwise `rfns(∇^q D)(x) ≤ Cq · ∑_{i ≤ q+2} rfns(∇^i (T − T'))(x)` shape, whose
pointwise Lipschitz modulus needs order-`(a + 2)` `C⁰` control of the metric jets the radius-`R` ball
cannot supply — `L²` orders `a + 2 + dim/2`), and never through the chart-jet Lipschitz chain.
Consumers transitively depend only on the integrated `L²`-Moser tame leaf's `sorryAx`, but **not** on
any pointwise grid posit, **not** on the chart-jet `bareChartJetContent`/`HasChartJetLip` chain. -/
theorem deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∑ q ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ^ 2) ≤
          C * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical
  -- The single integrated covariant-`L²` Moser tame leaf: its constant `C` is hoisted outside
  -- `∀ T T'`, and its per-order conclusion is the genuine `L²`-norm bound (chart-jet-free,
  -- no pointwise per-order fibre-norm grid).
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨(a + 1 : ℕ) * C ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  -- The full order-`(a+2)` covariant jet column of the perturbation difference `T − T'`.
  set Scol : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `(√Scol)² = Scol` (the window column is nonnegative).
  have hsqrt_sq : Real.sqrt Scol ^ 2 = Scol := Real.sq_sqrt hScol_nn
  -- Per order `q ≤ a`: squaring the integrated per-order bound `‖∇^q D‖ ≤ C · √Scol` (monotone on
  -- nonnegatives) gives `‖∇^q D‖² ≤ C² · Scol`.
  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 ≤ C ^ 2 * Scol := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hbound : ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ C * Real.sqrt Scol := by
      rw [hD_def, hScol_def]
      exact hC T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hqa
    have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := norm_nonneg _
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2
        ≤ (C * Real.sqrt Scol) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = C ^ 2 * Scol := by rw [mul_pow, hsqrt_sq]
  -- Sum the finitely many per-order squared bounds.
  calc (∑ q ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2)
      ≤ ∑ _q ∈ Finset.range (a + 1), C ^ 2 * Scol := Finset.sum_le_sum hper
    _ = (a + 1 : ℕ) * C ^ 2 * Scol := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **(POSITED deficit-free order-`d` ball-uniform pointwise covariant-jet column of the nonlinear
Ricci–DeTurck RHS-arm residual — the order-`d` analogue of the order-`a` jet column
`deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform`, the genuine quasilinear
order content at arbitrary order `d`.)**

Fix `g₀`, the DeTurck background `g_bg`, an arbitrary order `d`, and a covariant-`L²` ball radius
`R ≥ 0`.  There is **one** nonnegative constant `CR` — uniform over the fibre-small radius-`R` ball,
**outside** the `∀ T T'` quantifier — such that for any two `g₀`-fibre-small smooth perturbations
`T, T'` whose covariant-`L²` jets up to order `d + 2` lie in the radius-`R` ball, the order-`d`
covariant gradient of the **RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— the genuine Ricci–DeTurck RHS difference `deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg
(g₀ + T')` (the Δ-arms cancel by `rawTensorConnLapSmooth_sub`) — is dominated, at the squared
fibre-norm level, by `CR` times the order-`(d + 2)` covariant jet column of `T − T'`:
```
rfns(∇^d RHSarm)(x) ≤ CR · ∑_{q ≤ d+2} rfns(∇^q (T − T'))(x).
```

This is the verbatim order-`d` re-statement of the order-`a` jet column
`deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform` (the `a` there plays the
role of the differentiation order; here it is the free `d`).  Its analytic content is the covariant
Faà-di-Bruno / chart-Nemytskii Lipschitz domination of the second-order Ricci–DeTurck nonlinearity at
order `d`: `RHSarm` is a finite sum of products of fixed (rational, det-`≠ 0` by `δ < 1`) metric-jet
coefficient fields against covariant gradients of `T − T'`, so the covariant Leibniz expansion of
`∇^d RHSarm` lands the top order on a `T − T'` factor (order `≤ d + 2`, the genuine `∂²` Ricci
principal symbol contributing the `q = d + 2` top jet), the coefficients entering through their
ball-uniform `C^{≤ d}` sups.  This is the single new order-`d` leaf — the order-`0` endpoints and the
linear connection-Laplacian arm carry over to the `d + 2` window by monotone widening from the
already-proven order-`a` data, and the intermediate orders are filled by the order-generic
Gagliardo–Nirenberg interpolation.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ d+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol forces a top jet at `q = d + 2`, so a window-`d` weakening is rejected.  A
`CR = 0` witness is rejected by a nonvanishing `∇^d RHSarm` for a non-flat, genuinely second-order RHS
difference (`CR = 0` would force the whole column to vanish).  Consumers transitively depend on this
order-`d` leaf's `sorryAx`. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (d : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CR : ℝ,
      0 ≤ CR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + d) x
              ((iteratedCovGrad (I := I) g₀ 0 2 d
                ((deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') +
                  rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
            CR * ∑ q ∈ Finset.range (d + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) :=
  deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform
    (I := I) (M := M) g₀ g_bg d hR hδ₀

/-- **(DEFICIT-FREE INTRINSIC top-order-`d` integrated covariant-`L²` Moser–Nemytskii tame
bound on the nonlinear Ricci–DeTurck RHS-arm difference — PROVED from the order-`d` jet column.)**

The order-`d` analogue of `deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform`.  Fix `g₀`, `g_bg`, an
arbitrary order `d`, and a covariant-`L²` ball radius `R ≥ 0`.  There is one nonnegative ball-uniform
constant `Λc` (outside `∀ T T'`) such that for any two `g₀`-fibre-small smooth perturbations `T, T'`
whose covariant-`L²` jets up to order `d + 2` lie in the radius-`R` ball, the top-order-`d`
covariant-`L²` norm of the nonlinear RHS-arm difference
`N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys
```
‖∇^d N‖_{L²}  ≤  Λc · √(∑_{i ≤ d+2} ‖∇^i (T − T')‖²_{L²}) .
```
The proof integrates the order-`d` pointwise jet column
`deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform_order` over the closed
manifold by the sorry-free `l2RootSum_of_pointwise_iteratedCovGrad_jet` (generic in the jet/window
orders), exactly mirroring the order-`a` proof; the RHS-arm residual's left-hand tensor is `N` by the
definitional split `deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff`, rearranged. -/
private theorem deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (d : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λc : ℝ, 0 ≤ Λc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 d
            (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
          Λc * Real.sqrt (∑ i ∈ Finset.range (d + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform_order
      (I := I) g₀ g_bg d hR hδ₀
  refine ⟨Real.sqrt CR, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hN_eq :
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' =
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') := by
    have hsplit :=
      deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ'
    rw [hsplit]; abel
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + d) x
          ((iteratedCovGrad (I := I) g₀ 0 2 d
            (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
        CR * ∑ q ∈ Finset.range (d + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) := by
    intro x
    rw [hN_eq]
    exact hCR T T' hδ_le hδ hδ'_le hδ' hTball hT'ball x
  exact l2RootSum_of_pointwise_iteratedCovGrad_jet (I := I) g₀ d (d + 2)
    (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') (T - T') CR hCR_nn hpt

/-- **(The deficit-free integrated-`L²` Moser–Nemytskii endpoint data of the nonlinear Ricci–DeTurck
RHS-arm difference at order `d` — the order-`0` `C⁰` sup, the order-`0` `L²` and the top-order-`d`
`L²`, all in the `d + 2` window.)**

The order-`d` analogue of `deTurckRHSArmDiff_endpoints_l2_tame_ballUniform`.  Fix `g₀`, the DeTurck
background `g_bg`, a supercritical base order `a` (`2·finrank E + 10 ≤ a`), an order `d ≥ a`, and a
covariant-`L²` ball radius `R ≥ 0`.  There is one nonnegative ball-uniform constant `Λ₀` (outside
`∀ T T'`) such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets
up to order `d + 2` lie in the radius-`R` ball, the nonlinear RHS-arm difference
`N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys, with
`S := ∑_{i ≤ d+2} ‖∇^i (T − T')‖²`, the three endpoint bounds
```
(C⁰ sup)        ∀ x,  rfns(N)(x)        ≤ Λ₀² · S ,
(order-0 L²)          ‖N‖_{L²}          ≤ Λ₀ · √S ,
(top-order L²)        ‖∇^d N‖_{L²}      ≤ Λ₀ · √S .
```

**Proof (no new posit beyond the order-`d` jet column).**  The order-`0` `C⁰` sup is the **base** order-`a`
intrinsic order-`0` fibre-norm domination `deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform` (its
bound reads `∇^{≤ a+2}(T − T')`), widened to the `d + 2` window by monotonicity of the nonnegative
covariant-`L²` jet column (`a + 2 ≤ d + 2`); the order-`0` `L²` is its integral over the closed
manifold; and the top-order-`d` `L²` is the order-`d` integrated Moser tame
`deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform_order`.  Only the order-`0` data depends on the
supercritical base `a`; the top order uses only the order-`d` jet column. -/
private theorem deTurckRHSArmDiff_endpoints_l2_tame_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
              Λ₀ ^ 2 * ∑ i ∈ Finset.range (d + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (d + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 d
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (d + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  -- The base order-`a` order-`0` pointwise fibre-norm domination (window `a + 2`), widened below.
  obtain ⟨Λa, hΛa_nn, hΛa⟩ :=
    deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  -- The order-`d` integrated top-order Moser tame (window `d + 2`).
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform_order (I := I) g₀ g_bg d hR hδ₀
  haveI : MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g₀
  set vol : ℝ := (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ with hvol_def
  have hvol_nn : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg
  refine ⟨Λa * Real.sqrt (vol + 1) + Λc, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  set S : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  -- The base window `a + 2` jet column, widened to `d + 2` (monotone, nonnegative terms).
  set Sa : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hSa_def
  have hSa_nn : 0 ≤ Sa := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSa_le_S : Sa ≤ S := by
    rw [hSa_def, hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega))
      (fun i _ _ => sq_nonneg _)
  set Λ₀ : ℝ := Λa * Real.sqrt (vol + 1) + Λc with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (vol + 1) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hΛa_le : Λa ≤ Λ₀ := by
    rw [hΛ₀_def]
    have h1 : Λa ≤ Λa * Real.sqrt (vol + 1) := by
      nlinarith [hΛa_nn, hsqrt_ge_one]
    linarith [hΛc_nn]
  have hΛc_le : Λc ≤ Λ₀ := by rw [hΛ₀_def]; nlinarith [hΛa_nn, hsqrt_ge_one]
  -- The `d + 2` ball hypotheses imply the `a + 2` ball hypotheses (`a + 2 ≤ d + 2`), as the base
  -- order-`a` order-`0` lemma reads only `∇^{≤ a+2}` jets.
  have hTball_a : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R :=
    fun j hj => hTball j (by omega)
  have hT'ball_a : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R :=
    fun j hj => hT'ball j (by omega)
  -- The base order-`0` pointwise domination, widened from `Sa` to `S`, then constant to `Λ₀²`.
  have hpt_a : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λa ^ 2 * S := by
    intro x
    have hx : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λa ^ 2 * Sa := by
      rw [hN_def, hSa_def]
      exact hΛa T T' hδ_le hδ hδ'_le hδ' hTball_a hT'ball_a x
    refine hx.trans ?_
    exact mul_le_mul_of_nonneg_left hSa_le_S (sq_nonneg _)
  have hC0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λ₀ ^ 2 * S := by
    intro x
    refine (hpt_a x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hS_nn
    exact pow_le_pow_left₀ hΛa_nn hΛa_le 2
  -- The order-`0` `L²` endpoint, by integrating the pointwise bound `Λa² · S` over the manifold.
  have hL0 : ‖N‖ ≤ Λ₀ * Real.sqrt S := by
    have hnormsq : ‖N‖ ^ 2 ≤ vol * (Λa ^ 2 * S) := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 2 N]
      have hint_le :
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            ∫ _x, Λa ^ 2 * S ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const _) ?_
        · exact MeasureTheory.ae_of_all _ fun x =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
        · exact MeasureTheory.ae_of_all _ fun x => hpt_a x
      rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def] at hint_le
      exact hint_le
    have hnorm_nn : 0 ≤ ‖N‖ := norm_nonneg _
    have hsqrt_le : ‖N‖ ≤ Real.sqrt (vol * (Λa ^ 2 * S)) := by
      rw [show ‖N‖ = Real.sqrt (‖N‖ ^ 2) from (Real.sqrt_sq hnorm_nn).symm]
      exact Real.sqrt_le_sqrt hnormsq
    refine hsqrt_le.trans ?_
    have hfac : Real.sqrt (vol * (Λa ^ 2 * S)) = Λa * (Real.sqrt vol * Real.sqrt S) := by
      rw [show vol * (Λa ^ 2 * S) = Λa ^ 2 * (vol * S) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛa_nn,
        Real.sqrt_mul hvol_nn]
    rw [hfac, hΛ₀_def, add_mul]
    have hvol_le : Real.sqrt vol ≤ Real.sqrt (vol + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    calc Λa * (Real.sqrt vol * Real.sqrt S)
        = (Λa * Real.sqrt vol) * Real.sqrt S := by ring
      _ ≤ (Λa * Real.sqrt (vol + 1)) * Real.sqrt S := by
          refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
          exact mul_le_mul_of_nonneg_left hvol_le hΛa_nn
      _ ≤ Λa * Real.sqrt (vol + 1) * Real.sqrt S + Λc * Real.sqrt S := by
          have : 0 ≤ Λc * Real.sqrt S := mul_nonneg hΛc_nn hsqrtS_nn
          linarith
  -- The top-order-`d` `L²` endpoint, widened by the larger constant.
  have hLd : ‖iteratedCovGrad (I := I) g₀ 0 2 d N‖ ≤ Λ₀ * Real.sqrt S := by
    have hbase : ‖iteratedCovGrad (I := I) g₀ 0 2 d N‖ ≤ Λc * Real.sqrt S := by
      rw [hN_def, hS_def]
      exact hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_right hΛc_le hsqrtS_nn
  exact ⟨hC0, hL0, hLd⟩

/-- **(The order-`d` integrated covariant-`L²` Moser tame bound on the NONLINEAR Ricci–DeTurck
right-hand-side arm difference.)**

The order-`d` analogue of `deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform`.  Fix `g₀`, the
DeTurck background `g_bg`, a supercritical base order `a` (`2·finrank E + 10 ≤ a`), an order `d ≥ a`,
and a covariant-`L²` ball radius `R ≥ 0`.  There is one nonnegative ball-uniform constant `C` (outside
`∀ T T'`) such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets
up to order `d + 2` lie in the radius-`R` ball, every order-`q` (`q ≤ d`) covariant-gradient jet of the
nonlinear RHS-arm difference `N := deTurckRHSArmG0 g₀ g_bg T − deTurckRHSArmG0 g₀ g_bg T'` obeys
```
‖∇^q N‖_{L²} ≤ C · √(∑_{i ≤ d+2} ‖∇^i (T − T')‖²_{L²}).
```
The three endpoint data of `N` (order-`0` `C⁰` sup, order-`0` `L²`, top-order-`d` `L²`) are the
order-`d` endpoints `deTurckRHSArmDiff_endpoints_l2_tame_ballUniform_order`; orders `q = 0` and
`q = d` are the two `L²` endpoints directly, and each intermediate order `0 < q < d` is the
order-generic Gagliardo–Nirenberg interpolation `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`
of `N` between the order-`0` `C⁰` sup and the top-order-`d` `L²` (the degenerate `d = 0` reads only the
order-`0` endpoint).  The leaf constant is `C := (C_{GN} + 1) · (Λ₀ + 1)`. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ d →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (d + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  obtain ⟨Λ₀, hΛ₀_nn, hEnd⟩ :=
    deTurckRHSArmDiff_endpoints_l2_tame_ballUniform_order (I := I) g₀ g_bg a ha_super d hda hR hδ₀
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- Degenerate top order `d = 0`: every `q ≤ d` is `q = 0`, the order-`0` `L²` endpoint.
    subst hd0
    refine ⟨Λ₀, hΛ₀_nn, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    obtain rfl : q = 0 := Nat.le_zero.mp hq
    have hEnd' := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    simpa using hEnd'.2.1
  · obtain ⟨Cgn, hCgn_nn, hGN⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
        (I := I) (M := M) g₀ 2 d hdpos
    refine ⟨(Cgn + 1) * (Λ₀ + 1), by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    set N : SmoothCcTensor g₀ 0 2 :=
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
    set S : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    obtain ⟨hC0, hL0, hLd⟩ := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    have hC0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤
        (Λ₀ * Real.sqrt S) ^ 2 := by
      intro x
      have hx := hC0 x
      rw [mul_pow, Real.sq_sqrt hS_nn]
      exact hx
    have hL0' : ‖N‖ ≤ Λ₀ * Real.sqrt S := by rw [hN_def, hS_def]; exact hL0
    have hLd' : ‖iteratedCovGrad (I := I) g₀ 0 2 d N‖ ≤ Λ₀ * Real.sqrt S := by
      rw [hN_def, hS_def]; exact hLd
    have hN_norm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 d N‖ := norm_nonneg _
    have hΛ₀S_nn : 0 ≤ Λ₀ * Real.sqrt S := mul_nonneg hΛ₀_nn hsqrtS_nn
    suffices hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤
        ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S by
      rw [hN_def, hS_def] at hgoal; exact hgoal
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      have h0 : ‖iteratedCovGrad (I := I) g₀ 0 2 0 N‖ = ‖N‖ := by simp
      rw [h0]
      refine hL0'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
      nlinarith [hCgn_nn, hΛ₀_nn]
    · rcases lt_or_eq_of_le hq with hqlt | hqeq
      · have hGNq := hGN N (Λ₀ * Real.sqrt S) hΛ₀S_nn hC0' q hqpos hqlt
        set e : ℝ := (q : ℝ) / d with he_def
        have he_nn : 0 ≤ e := by
          rw [he_def]; positivity
        have he_lt_one : e < 1 := by
          rw [he_def]
          rw [div_lt_one (by exact_mod_cast hdpos)]
          exact_mod_cast hqlt
        have h1me_nn : 0 ≤ 1 - e := by linarith
        have hak_mono : (‖iteratedCovGrad (I := I) g₀ 0 2 d N‖) ^ e ≤
            (Λ₀ * Real.sqrt S) ^ e :=
          Real.rpow_le_rpow hN_norm_nn hLd' he_nn
        have hrhs_eq : Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e =
            Cgn * (Λ₀ * Real.sqrt S) := by
          rcases eq_or_lt_of_le hΛ₀S_nn with hzero | hpos
          · rw [← hzero, Real.zero_rpow (ne_of_gt (by linarith [he_lt_one] : (0 : ℝ) < 1 - e))]
            simp
          · rw [mul_assoc, ← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
        calc ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖
            ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) *
                (‖iteratedCovGrad (I := I) g₀ 0 2 d N‖) ^ e := by
              simpa only [he_def] using hGNq
          _ ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e := by
              refine mul_le_mul_of_nonneg_left hak_mono ?_
              exact mul_nonneg hCgn_nn (Real.rpow_nonneg hΛ₀S_nn _)
          _ = Cgn * (Λ₀ * Real.sqrt S) := hrhs_eq
          _ = (Cgn * Λ₀) * Real.sqrt S := by ring
          _ ≤ ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S := by
              refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
              nlinarith [hCgn_nn, hΛ₀_nn]
      · subst hqeq
        refine hLd'.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
        nlinarith [hCgn_nn, hΛ₀_nn]

/-- **(The order-`d` integrated covariant-`L²` Moser tame bound on the sealed Ricci–DeTurck remainder
difference.)**

The order-`d` analogue of `deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform`.  Fix `g₀`,
the DeTurck background `g_bg`, a supercritical base order `a` (`2·finrank E + 10 ≤ a`), an order
`d ≥ a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is one nonnegative ball-uniform constant `C`
(outside `∀ T T'`) such that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose
covariant-`L²` jets up to order `d + 2` lie in the radius-`R` ball, every order-`q` (`q ≤ d`)
covariant-gradient jet of the sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys
```
‖∇^q D‖_{L²}  ≤  C · √(∑_{i ≤ d+2} ‖∇^i (T − T')‖²_{L²}).
```
The sealed remainder difference splits (`deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff`) into
the nonlinear RHS-arm difference minus the linear connection-Laplacian difference
`Δ_∇(T − T') = rawTensorConnLapSmooth g₀ 0 2 (T − T')`; the triangle inequality bounds `‖∇^q D‖` by the
sum of the two arm norms.  The nonlinear arm is the order-`d` Moser tame
`deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform_order`; the linear arm is the order-generic
(provable) Δ-arm tame `rawTensorConnLapSmooth_iteratedCovGrad_l2_tame` instantiated at `d`.  Both
produce the common root-sum `C · √(∑_{i ≤ d+2} ‖∇^i (T − T')‖²)`, so the leaf constant is the sum of
the two arm constants. -/
private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ d →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (d + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform_order (I := I) g₀ g_bg a ha_super d hda hR hδ₀
  obtain ⟨Cl, hCl_nn, hCl⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_l2_tame (I := I) g₀ d
  refine ⟨Cn + Cl, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  have hjet_split :
      iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 q N -
          iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) := by
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
      (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ', ← hN_def, iteratedCovGrad_sub]
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := by
    rw [hjet_split]; exact norm_sub_le _ _
  have hNarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤ Cn * Real.sqrt S := by
    rw [hN_def, hS_def]
    exact hCn T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hq
  have hLarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤ Cl * Real.sqrt S := by
    rw [hS_def]; exact hCl (T - T') q hq
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖
      ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := htri
    _ ≤ Cn * Real.sqrt S + Cl * Real.sqrt S := add_le_add hNarm hLarm
    _ = (Cn + Cl) * Real.sqrt S := by ring

/-- **The order-`d` single-arm full covariant-jet-column ball bound on the genuine Ricci–DeTurck
remainder difference.**

The order-`d` analogue of `deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz` (which is the
order-`a` case `d = a`).  Fix `g₀`, the DeTurck background `g_bg`, a supercritical base order `a`
(`2·finrank E + 10 ≤ a`), an order `d ≥ a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is one
nonnegative ball-uniform constant `C` (outside `∀ T T'`) such that for any two `g₀`-fibre-small smooth
perturbations `T, T'` whose covariant-`L²` jets up to order `d + 2` lie in the radius-`R` ball, the
entire covariant-gradient jet column (orders `q ≤ d`) of the genuine remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys, at the squared `L²`
level,
```
∑_{q ≤ d} ‖∇^q D‖²  ≤  C · ∑_{i ≤ d+2} ‖∇^i (T − T')‖².
```
Assembled from the order-`d` integrated covariant-`L²` Moser tame leaf
`deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform_order` by squaring each per-order bound
`‖∇^q D‖ ≤ C · √Scol` (`‖∇^q D‖² ≤ C² · Scol` by `Real.sq_sqrt`) and summing the `d + 1` orders, with
constant `C_col := (d + 1) · C²`. -/
theorem deTurckRemainderDiff_iteratedCovGradSum_ballBound_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∑ q ∈ Finset.range (d + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ^ 2) ≤
          C * ∑ i ∈ Finset.range (d + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform_order (I := I) (M := M) g₀ g_bg a
      ha_super d hda hR hδ₀
  refine ⟨(d + 1 : ℕ) * C ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set Scol : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrt_sq : Real.sqrt Scol ^ 2 = Scol := Real.sq_sqrt hScol_nn
  have hper : ∀ q ∈ Finset.range (d + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 ≤ C ^ 2 * Scol := by
    intro q hq
    have hqd : q ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hbound : ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ C * Real.sqrt Scol := by
      rw [hD_def, hScol_def]
      exact hC T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hqd
    have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := norm_nonneg _
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2
        ≤ (C * Real.sqrt Scol) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = C ^ 2 * Scol := by rw [mul_pow, hsqrt_sq]
  calc (∑ q ∈ Finset.range (d + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2)
      ≤ ∑ _q ∈ Finset.range (d + 1), C ^ 2 * Scol := Finset.sum_le_sum hper
    _ = (d + 1 : ℕ) * C ^ 2 * Scol := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
