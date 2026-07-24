import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap

/-!
# Class-uniform Dirichlet–Bochner gap (item-6 packet, spine S1)

This file is the `Λ`-uniform sibling of `DirichletSpectralBochnerGap.lean`.  The
per-metric Gårding recursion there produces its constants by `Classical.choose`
sups of the Riemann curvature (via `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le`);
those constants are not trackable through the `Λ`-comparability class.  Here we
mirror the SAME recursion structurally but take the curvature input as an
ABSTRACT hypothesis `hcurv` in the currency the recursion consumes — the uniform
per-order bound on the Weitzenböck defect `pointwiseTensorCurv` — with an explicit
constant family `Fc : ℕ → ℝ`.  Downstream (brick 2a, `HCGCompactness/`) discharges
`hcurv` from `MetricCovDerivOrderBoundOn` via `sup_x ‖∇^{g₀,a} Riemann(g₀)‖ ≤ F(Λ,n)`.

**Stage α (this file): the uniform single Bochner step** `bochner_step_unif` — the
uniform version of `iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`,
with an EXPLICIT constant `Cbase + Fc 0` (no `Classical.choose`).  The
commutator-base input `hbase` (the uniform sibling of
`rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`)
is taken as a hypothesis; expressing `Cbase` itself through `Fc` (re-deriving the
`m`-fold commutator recursion `iteratedRoughLapGrad_commutator_l2Norm_le_local`)
is the next sub-brick.  Route/status: `UnifBochnerGap.md`.

The proof body is the structural mirror of the private `…succ_le_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1220`): Weitzenböck integrated identity
(`weitzenbock_integrated_covGrad_l2_normSq`) + Cauchy–Schwarz on the curvature
pairing.  Only the two curvature-dependent obtains are replaced by `hcurv`/`hbase`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor
open Tensor0SBundle
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Composition/reindex of iterated covariant gradients under the `L²` fibre norm:**
`‖∇^i(∇^j S)‖ = ‖∇^{j+i} S‖`.  Local inline of the `private`
`DirichletSpectralBochnerGap.norm_iteratedCovGrad_comp_local` (that declaration is not
importable, being `private`); the pointwise input is `rfns_iteratedCovGrad_comp`. -/
private theorem norm_iterCovGrad_comp
    (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i) (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

set_option maxHeartbeats 1600000 in
-- The final `nlinarith` (Weitzenböck identity + Cauchy–Schwarz curvature pairing) is
-- elaboration-heavy; the budget is raised as at `DirichletSpectralBochnerGap.lean:1219`.
/-- **The class-uniform single Bochner step.**  Uniform sibling of
`iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1220`) with an EXPLICIT constant `Cbase + Fc 0`.

Hypotheses (both discharged downstream, not `Classical.choose`):
* `hcurv` — the class-uniform Weitzenböck-defect bound, order/rank-generic, with
  constant family `Fc`.  It is exactly the conclusion of
  `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` but with the explicit `Fc`
  in place of the choose-witness `K`.  Discharged by brick 2a from
  `sup_x ‖∇^{g₀,a} Riemann(g₀)‖ ≤ F(Λ,n)`.
* `hbase` — the class-uniform commutator base+lower bound (uniform sibling of
  `rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`),
  with constant `Cbase`.  Expressing `Cbase` through `Fc` is the next sub-brick.

Conclusion: for every smooth compactly-supported `(0,s)`-tensor `u`,
`‖∇^{k+2} u‖²_{L²} ≤ ‖∇^{k}(Δ_∇ u)‖²_{L²} + (Cbase + Fc 0)·(∑_{a≤k+1} ‖∇^a u‖)²`. -/
theorem bochner_step_unif
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (Cbase : ℝ)
    (hbase : ∀ (u : SmoothCcTensor g₀ 0 s),
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k)
            (iteratedCovGrad (I := I) g₀ 0 s k u)‖ ^ 2 ≤
          ‖iteratedCovGrad (I := I) g₀ 0 s k
              (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2
          + Cbase * (∑ a ∈ Finset.range (k + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2) :
    ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 ≤
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2
        + (Cbase + Fc 0) * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  classical
  intro u
  set P : SmoothCcTensor g₀ 0 (s + k) := iteratedCovGrad (I := I) g₀ 0 s k u with hP_def
  set SUM : ℝ := ∑ a ∈ Finset.range (k + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ with hSUM
  have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hPnorm : ‖P‖ ≤ SUM := by
    rw [hP_def, hSUM]
    refine Finset.single_le_sum (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a u‖)
      (fun a _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hgradP_eq : covGrad (I := I) (M := M) g₀ 0 (s + k) P =
      iteratedCovGrad (I := I) g₀ 0 s (k + 1) u := by
    rw [hP_def, iteratedCovGrad_succ]
  have hgradPnorm : ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ ≤ SUM := by
    rw [hgradP_eq, hSUM]
    refine Finset.single_le_sum (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a u‖)
      (fun a _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hLHS_eq : iteratedCovGrad (I := I) g₀ 0 s (k + 2) u =
      covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
        (covGrad (I := I) (M := M) g₀ 0 (s + k) P) := by
    rw [hP_def]
    rfl
  have hLHS_norm_sq :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 =
        tensorL2Norm (I := I) (M := M) g₀ 0 (s + k + 1 + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + k) P)).toFun ^ 2 := by
    rw [SmoothCcTensor.norm_toL2, hLHS_eq,
      DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + k + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P))]
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ (s + k) P
  have hcurv_eq :
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + k + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P) -
        covGrad (I := I) (M := M) g₀ 0 (s + k)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P) =
      pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P := rfl
  rw [hcurv_eq] at hweitz
  have hbase_eq :
      tensorL2Norm (I := I) (M := M) g₀ 0 (s + k)
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P).toFun ^ 2 =
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P‖ ^ 2 := by
    rw [DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
      (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 (s + k) P)]
  have hpair_le :
      |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun| ≤
        ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ *
          ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := by
    have habs :
        tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
            (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun =
          (⟪pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P,
              covGrad (I := I) (M := M) g₀ 0 (s + k) P⟫_ℝ : ℝ) :=
      (SmoothCcTensor.inner_def (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P)
        (covGrad (I := I) (M := M) g₀ 0 (s + k) P)).symm
    rw [habs]
    exact abs_real_inner_le_norm
      (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P)
      (covGrad (I := I) (M := M) g₀ 0 (s + k) P)
  have hcurvnorm :
      ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ ≤ Fc 0 * SUM := by
    have hKb := hcurv (s + k) 0 P
    have hsumexp :
        ∑ a ∈ Finset.range (0 + 2), ‖iteratedCovGrad (I := I) g₀ 0 (s + k) a P‖ =
          ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := by
      rw [show (0 + 2) = 2 by ring, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
    rw [iteratedCovGrad_zero] at hKb
    rw [hsumexp] at hKb
    refine le_trans hKb ?_
    have hsum_le : ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ ≤ SUM := by
      have hPexpand : ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s k u‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 s (k + 1) u‖ := by
        rw [hgradP_eq, hP_def]
      rw [hPexpand, hSUM]
      have hpair : ({k, k + 1} : Finset ℕ) ⊆ Finset.range (k + 2) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_range]; omega
      have hsub :=
        Finset.sum_le_sum_of_subset_of_nonneg hpair
          (fun a _ _ => norm_nonneg (iteratedCovGrad (I := I) g₀ 0 s a u))
      have hpairsum :
          ∑ a ∈ ({k, k + 1} : Finset ℕ), ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 s k u‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 s (k + 1) u‖ := by
        rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      rw [hpairsum] at hsub
      exact hsub
    nlinarith [hsum_le, hFc 0, hSUM_nn]
  have hpair_bound :
      |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun| ≤ Fc 0 * SUM ^ 2 := by
    calc |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
            (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun|
        ≤ ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ *
            ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := hpair_le
      _ ≤ (Fc 0 * SUM) * SUM := by
          refine mul_le_mul hcurvnorm hgradPnorm (norm_nonneg _) ?_
          exact mul_nonneg (hFc 0) hSUM_nn
      _ = Fc 0 * SUM ^ 2 := by ring
  have hbase_le := hbase u
  rw [← hP_def] at hbase_le
  have hbase_toL2 :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_toL2]
  rw [hLHS_norm_sq, hweitz, hbase_eq, hbase_toL2]
  have hneg_le := neg_abs_le
    (tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
      (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
      (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun)
  nlinarith [hbase_le, hpair_bound, hneg_le, hSUM_nn, hFc 0]

/-- **The class-uniform iterated rough-Laplacian / covariant-gradient commutator.**
Uniform sibling of the `private` `iteratedRoughLapGrad_commutator_l2Norm_le_local`
(`DirichletSpectralBochnerGap.lean:616`): the `m`-fold commutator
`Δ_∇(∇^m S) − ∇^m(Δ_∇ S)` has an `L²`-jet bound whose constant family is built from `Fc`
(via `hcurv`) — the recursion `Cfun p = Fc p + Cfun_{m-1}(p+1)` — with NO
`Classical.choose` of curvature sups.  This EXPRESSES the commutator constant through the
`Fc` family, the first half of discharging the `Cbase` input of `bochner_step_unif`.

The `base+lower` assembler `rawConnLap_iteratedCovGrad_…_base_add_lower`
(`:1085`) that turns this into `bochner_step_unif`'s `hbase` additionally needs the
`covDivergence ≤ covGrad` bound, whose only realization is a ~130-line `private` tower in
`DirichletSpectralBochnerGap.lean` (`:479–597`); that step awaits publicizing that tower
(see `UnifBochnerGap.md`). -/
theorem roughLapComm_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    refine ⟨fun p => Fc p + Cm (p + 1), fun p => add_nonneg (hFc p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      change rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S
      with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p]
    refine le_trans (norm_add_le _ _) ?_
    have harm1 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ ≤
          Fc p * fullSum := by
      have hKb := hcurv (s + m) p gradm
      have hreindex : ∀ a, ‖iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, norm_iterCovGrad_comp (I := I) (M := M) g₀ s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      have hsub : ∑ a ∈ Finset.range (p + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ (fun a _ => rfl)
          congr 1
          omega
        rw [hIco]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_Ico] at hb
        rw [Finset.mem_range]
        omega
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖
          ≤ Fc p * ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s (m + a) S‖ := hKb
        _ ≤ Fc p * fullSum := mul_le_mul_of_nonneg_left hsub (hFc p)
    have harm2 :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      have hcomp :
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + m) (p + 1) comm_m‖ := by
        have h := norm_iterCovGrad_comp (I := I) (M := M) g₀ (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    have hfinal : Fc p * fullSum + Cm (p + 1) * fullSum =
        (Fc p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖
        ≤ Fc p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (Fc p + Cm (p + 1)) * fullSum := hfinal

/-- **Class-uniform iterated `∇^a ∘ Δ_∇` `L²` bound.**  Uniform sibling of the `private`
`exists_iteratedCovGrad_rawConnLap_l2Norm_le_local` (`DirichletSpectralBochnerGap.lean:759`):
consumes the PUBLIC dimension-only `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen`
(its constant `K` is a fixed dimension quantity, class-independent) and `roughLapComm_unif`
(constant `Fc`-explicit). -/
theorem rawConnLapIter_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (a : ℕ) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
          C * ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  intro s
  obtain ⟨K, hK_one, hK⟩ :=
    exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g₀
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    roughLapComm_unif (I := I) (M := M) g₀ Fc hFc hcurv a s
  have hK_nn : 0 ≤ K := le_trans (by norm_num) hK_one
  refine ⟨K + Cfun 0, add_nonneg hK_nn (hCfun_nn 0), fun S => ?_⟩
  set FULL : ℝ := ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hlap_second :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ ≤
        K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
    have hgen := hK (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)
    rw [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
        (covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
          (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)))] at hgen
    have hcomp :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
      have h := norm_iterCovGrad_comp (I := I) (M := M) g₀ s a 2 S
      have heq :
          iteratedCovGrad (I := I) g₀ 0 (s + a) 2 (iteratedCovGrad (I := I) g₀ 0 s a S) =
            covGrad (I := I) (M := M) g₀ 0 (s + a + 1)
              (covGrad (I := I) (M := M) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)) :=
        rfl
      rw [heq] at h
      rw [h]
    rw [hcomp] at hgen
    exact hgen
  have hcomm :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
          iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
    have h := hCfun 0 S
    simpa only [iteratedCovGrad_zero, Nat.add_zero] using h
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
        ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := by
    have := norm_sub_le
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S))
      (rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
        iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
    simpa using this
  have hsecond_le : ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.single_le_sum (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun b _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  have hsub_le : ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
    rw [hFULL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
    intro b hb; rw [Finset.mem_range] at hb ⊢; omega
  calc ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
      ≤ ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ +
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S) -
            iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := htri
    _ ≤ K * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ +
          Cfun 0 * ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ :=
        add_le_add hlap_second hcomm
    _ ≤ K * FULL + Cfun 0 * FULL :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond_le hK_nn)
          (mul_le_mul_of_nonneg_left hsub_le (hCfun_nn 0))
    _ = (K + Cfun 0) * FULL := by ring

set_option maxHeartbeats 1600000 in
-- The IBP cross-term + Cauchy–Schwarz `nlinarith` is elaboration-heavy; the budget is
-- raised as at `DirichletSpectralBochnerGap.lean:1219`.
/-- **Class-uniform base+lower Bochner defect** — the `hbase` provider.  Uniform sibling of
the `private` `rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1085`).  Its conclusion is EXACTLY the `hbase` hypothesis of
`bochner_step_unif`, with an explicit constant `(Cfun 0)² + 2·Crc·√finrank·Cfun 1` built from
`roughLapComm_unif`/`rawConnLapIter_unif` (both `Fc`-explicit) and the now-public
`covDivergence_l2Norm_le_covGrad_local`.  Assembly: IBP
(`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`) on the cross term. -/
theorem baseAddLower_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k)
          (iteratedCovGrad (I := I) g₀ 0 s k u)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 s k
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2
        + C * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  classical
  rcases k with _ | j
  · refine ⟨0, le_refl _, fun u => ?_⟩
    have hD0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 u) =
          iteratedCovGrad (I := I) g₀ 0 s 0
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero]
    rw [hD0]
    simp
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      roughLapComm_unif (I := I) (M := M) g₀ Fc hFc hcurv (j + 1) s
    obtain ⟨Crc, hCrc_nn, hCrc⟩ :=
      rawConnLapIter_unif (I := I) (M := M) g₀ Fc hFc hcurv j s
    set dimR : ℝ := Real.sqrt (Module.finrank ℝ E) with hdimR
    have hdimR_nn : 0 ≤ dimR := Real.sqrt_nonneg _
    refine ⟨(Cfun 0) ^ 2 + 2 * (Crc * (dimR * Cfun 1)),
      add_nonneg (sq_nonneg _)
        (by have := hCfun_nn 0; have := hCfun_nn 1
            exact mul_nonneg (by norm_num)
              (mul_nonneg hCrc_nn (mul_nonneg hdimR_nn (hCfun_nn 1)))),
      fun u => ?_⟩
    set SUM : ℝ := ∑ a ∈ Finset.range (j + 1 + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ with hSUM
    have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
    set B : SmoothCcTensor g₀ 0 (s + (j + 1)) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
        (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) with hB_def
    set A : SmoothCcTensor g₀ 0 (s + (j + 1)) :=
      iteratedCovGrad (I := I) g₀ 0 s (j + 1)
        (rawTensorConnLapSmooth (I := I) g₀ 0 s u) with hA_def
    set D : SmoothCcTensor g₀ 0 (s + (j + 1)) := B - A with hD_def
    have hBAD : B = A + D := by rw [hD_def]; abel
    have hnorm_add :
        ‖B‖ ^ 2 = ‖A‖ ^ 2 + 2 * (⟪A, D⟫_ℝ : ℝ) + ‖D‖ ^ 2 := by
      rw [hBAD, ← SmoothCcTensor.norm_toL2 (A + D), map_add,
        @norm_add_sq_real _ _ _ (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 D),
        SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2,
        SmoothCcTensor.inner_toL2]
    have hD_eq_comm : D =
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
            (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) -
          iteratedCovGrad (I := I) g₀ 0 s (j + 1)
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u) := by
      rw [hD_def, hB_def, hA_def]
    have hDnorm : ‖D‖ ≤ Cfun 0 * SUM := by
      have h := hCfun 0 u
      simp only [iteratedCovGrad_zero, Nat.add_zero] at h
      rw [hD_eq_comm]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
      rw [hSUM]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
      intro b hb; rw [Finset.mem_range] at hb ⊢; omega
    have hgradDnorm :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + (j + 1)) D‖ ≤ Cfun 1 * SUM := by
      have h := hCfun 1 u
      have hcovD :
          ‖covGrad (I := I) (M := M) g₀ 0 (s + (j + 1)) D‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + (j + 1)) 1
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
                  (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u) -
                iteratedCovGrad (I := I) g₀ 0 s (j + 1)
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ := by
        rw [hD_eq_comm]
        simp only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
      rw [hcovD]
      have hrange : ∑ a ∈ Finset.range (j + 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a u‖ = SUM := by
        rw [hSUM, show j + 1 + 1 + 1 = j + 1 + 2 from by omega]
      rw [hrange] at h
      exact h
    set T : SmoothCcTensor g₀ 0 (s + j) :=
      iteratedCovGrad (I := I) g₀ 0 s j (rawTensorConnLapSmooth (I := I) g₀ 0 s u) with hT_def
    have hA_covGrad : A = covGrad (I := I) (M := M) g₀ 0 (s + j) T := by
      rw [hA_def, hT_def, iteratedCovGrad_succ]
    have hTnorm : ‖T‖ ≤ Crc * SUM := by
      have h := hCrc u
      rw [hT_def]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrc_nn
      rw [hSUM, show j + 3 = j + 1 + 2 from by omega]
    have hcovDivD :
        ‖covDivergence (I := I) (M := M) g₀ (s + j) D‖ ≤ dimR * (Cfun 1 * SUM) := by
      have hp1 := covDivergence_l2Norm_le_covGrad_local (I := I) (M := M) g₀ (s + j) D
      refine le_trans hp1 ?_
      exact mul_le_mul_of_nonneg_left hgradDnorm hdimR_nn
    have hIBP :
        (⟪A, D⟫_ℝ : ℝ) =
          - tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun := by
      rw [SmoothCcTensor.inner_def A D, hA_covGrad]
      exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
        (I := I) (M := M) g₀ (s + j) T D
    have hcross_abs : |(⟪A, D⟫_ℝ : ℝ)| ≤ (Crc * SUM) * (dimR * (Cfun 1 * SUM)) := by
      rw [hIBP, abs_neg]
      have habs_inner :
          |tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun| ≤
            ‖T‖ * ‖covDivergence (I := I) (M := M) g₀ (s + j) D‖ := by
        rw [show tensorL2Inner (I := I) (M := M) g₀ 0 (s + j) T.toFun
              (covDivergence (I := I) (M := M) g₀ (s + j) D).toFun =
            (⟪T, covDivergence (I := I) (M := M) g₀ (s + j) D⟫_ℝ : ℝ) from
          (SmoothCcTensor.inner_def T (covDivergence (I := I) (M := M) g₀ (s + j) D)).symm]
        exact abs_real_inner_le_norm T (covDivergence (I := I) (M := M) g₀ (s + j) D)
      refine le_trans habs_inner ?_
      exact mul_le_mul hTnorm hcovDivD (norm_nonneg _)
        (mul_nonneg hCrc_nn hSUM_nn)
    have hDnorm_sq : ‖D‖ ^ 2 ≤ (Cfun 0) ^ 2 * SUM ^ 2 := by
      have h1 : ‖D‖ ^ 2 ≤ (Cfun 0 * SUM) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hDnorm 2
      calc ‖D‖ ^ 2 ≤ (Cfun 0 * SUM) ^ 2 := h1
        _ = (Cfun 0) ^ 2 * SUM ^ 2 := by ring
    rw [show ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
          (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u)‖ ^ 2 = ‖B‖ ^ 2 from rfl,
      show ‖iteratedCovGrad (I := I) g₀ 0 s (j + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 = ‖A‖ ^ 2 from rfl,
      hnorm_add]
    have hcross_le : 2 * (⟪A, D⟫_ℝ : ℝ) ≤
        2 * ((Crc * SUM) * (dimR * (Cfun 1 * SUM))) := by
      have := (abs_le.mp hcross_abs).2
      linarith [this]
    nlinarith [hcross_le, hDnorm_sq, hSUM_nn, hCrc_nn, hdimR_nn, hCfun_nn 0, hCfun_nn 1]

/-- **The fully class-uniform single Bochner step** (`hbase` discharged).  Combines
`baseAddLower_unif` (supplying the `Cbase` input) with `bochner_step_unif`, so the only
remaining hypothesis is the abstract curvature bound `hcurv` (with its explicit `Fc`).  This
is the induction-ready form consumed by the strong induction toward
`covsum_hs_unif`/`hs_covsum_unif`. -/
theorem bochner_step_hcurv
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 s),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 ≤
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2
        + C * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  obtain ⟨Cbase, hCbase_nn, hbase⟩ :=
    baseAddLower_unif (I := I) (M := M) g₀ Fc hFc hcurv s k
  exact ⟨Cbase + Fc 0, add_nonneg hCbase_nn (hFc 0),
    bochner_step_unif (I := I) (M := M) g₀ s k Fc hFc hcurv Cbase hbase⟩

/-- **Reindex of the iterated rough Laplacian under one extra `Δ_∇`:**
`Δ_∇^i(Δ_∇ S) = Δ_∇^{i+1} S`.  Local inline of the `private`
`AllOrderGardingConstant.rawTensorConnLapIter_rawTensorConnLapSmooth` (that declaration is not
importable, being `private`). -/
private theorem rawIter_lap_reindex
    (g₀ : SmoothRiemannianMetric I M) (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    rawTensorConnLapIter (I := I) g₀ 0 s i (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
      rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [rawTensorConnLapIter_succ (I := I) g₀ 0 s n
        (rawTensorConnLapSmooth (I := I) g₀ 0 s S), ih,
      rawTensorConnLapIter_succ (I := I) g₀ 0 s (n + 1) S]

omit [CompactSpace M] [I.Boundaryless] in
/-- The shifted rough-Laplacian jet sum `∑_{i < m} ‖Δ_∇^{i+1} S‖` is dominated by the full jet
sum `∑_{i < n} ‖Δ_∇^i S‖` whenever `m + 1 ≤ n`.  A curvature-free monotonicity used to fold the
induction-hypothesis Laplacian budget of `Δ_∇ S` into the target budget of `S`. -/
private theorem lap_shift_le
    (g₀ : SmoothRiemannianMetric I M) (s m n : ℕ) (hmn : m + 1 ≤ n)
    (S : SmoothCcTensor g₀ 0 s) :
    ∑ i ∈ Finset.range m, ‖rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S‖ ≤
      ∑ i ∈ Finset.range n, ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
  have key :
      (∑ i ∈ Finset.range m, ‖rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S‖) +
          ‖rawTensorConnLapIter (I := I) g₀ 0 s 0 S‖ =
        ∑ i ∈ Finset.range (m + 1), ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ :=
    (Finset.sum_range_succ' (fun i => ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖) m).symm
  have hmono :
      ∑ i ∈ Finset.range (m + 1), ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ ≤
        ∑ i ∈ Finset.range n, ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
      (fun _ _ _ => norm_nonneg _)
  have hnn : 0 ≤ ‖rawTensorConnLapIter (I := I) g₀ 0 s 0 S‖ := norm_nonneg _
  linarith [key, hmono, hnn]

set_option maxHeartbeats 1600000 in
/-- **Uniform elliptic jet engine (strong form).**  For every jet-order budget `J` there is a
single nonnegative constant `C` such that every covariant-gradient iterate up to order `J` is
controlled by the rough-Laplacian jet up to order `⌈a/2⌉`:
`‖∇^a S‖ ≤ C · ∑_{i ≤ ⌈a/2⌉} ‖Δ_∇^i S‖` for all `a ≤ J`.  Proved by induction on `J` using the
class-uniform Bochner step `bochner_step_hcurv` (top order `≥ 2`) and the curvature-free order-1
Dirichlet-energy estimate `covGrad_l2NormSq_le_rawConnLap_mul_self_gen` (top order `1`); the
constant chain is `Fc`-explicit (no `Classical.choose` of curvature).  This is the `Fc`-explicit
sibling of the per-metric strong induction inside
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`. -/
private theorem elliptic_engine
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s : ℕ) :
    ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ, a ≤ J → ∀ S : SmoothCcTensor g₀ 0 s,
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤
        C * ∑ i ∈ Finset.range ((a + 1) / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
  intro J
  induction J with
  | zero =>
    refine ⟨1, zero_le_one, fun a ha S => ?_⟩
    obtain rfl : a = 0 := Nat.le_zero.mp ha
    rw [iteratedCovGrad_zero, one_mul]
    exact Finset.single_le_sum (a := 0)
      (fun i _ => norm_nonneg (rawTensorConnLapIter (I := I) g₀ 0 s i S))
      (by rw [Finset.mem_range]; omega)
  | succ J ih =>
    obtain ⟨CJ, hCJ_nn, hCJ⟩ := ih
    obtain ⟨Ctop, hCtop_nn, hCtop⟩ :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
          ‖iteratedCovGrad (I := I) g₀ 0 s (J + 1) S‖ ≤
            C * ∑ i ∈ Finset.range ((J + 1 + 1) / 2 + 1),
              ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
      rcases J with _ | J'
      · -- top order `a = 1`: curvature-free order-1 Dirichlet-energy estimate
        refine ⟨1, zero_le_one, fun S => ?_⟩
        have hdir :
            ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ^ 2 ≤
              ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ * ‖S‖ := by
          have h := covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g₀ s S
          rw [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
              (covGrad (I := I) (M := M) g₀ 0 s S),
            tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S),
            tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀ S] at h
          exact h
        have hsum :
            ∑ i ∈ Finset.range ((0 + 1 + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ =
              ‖S‖ + ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ := by
          have hidx : (0 + 1 + 1) / 2 + 1 = 2 := by norm_num
          rw [hidx, Finset.sum_range_succ, Finset.sum_range_one, rawTensorConnLapIter_zero,
            rawTensorConnLapIter_one]
        rw [hsum, one_mul]
        have hsq :
            ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ^ 2 ≤
              (‖S‖ + ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖) ^ 2 := by
          nlinarith [hdir, norm_nonneg S,
            norm_nonneg (rawTensorConnLapSmooth (I := I) g₀ 0 s S),
            mul_nonneg (norm_nonneg S)
              (norm_nonneg (rawTensorConnLapSmooth (I := I) g₀ 0 s S))]
        exact le_of_sq_le_sq hsq (add_nonneg (norm_nonneg _) (norm_nonneg _))
      · -- top order `a = J' + 2 ≥ 2`: the class-uniform Bochner step at `k = J'`
        obtain ⟨Cb, hCb_nn, hstep⟩ :=
          bochner_step_hcurv (I := I) (M := M) g₀ Fc hFc hcurv s J'
        have hpos : (0 : ℝ) ≤ 1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2 := by positivity
        refine ⟨CJ * Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2),
          mul_nonneg hCJ_nn (Real.sqrt_nonneg _), fun S => ?_⟩
        set L : ℝ := ∑ i ∈ Finset.range ((J' + 1 + 1 + 1) / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ with hL
        have hL_nn : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have hterm1 :
            ‖iteratedCovGrad (I := I) g₀ 0 s J'
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤ CJ * L := by
          refine le_trans (hCJ J' (by omega) (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) ?_
          refine mul_le_mul_of_nonneg_left ?_ hCJ_nn
          calc ∑ i ∈ Finset.range ((J' + 1) / 2 + 1),
                  ‖rawTensorConnLapIter (I := I) g₀ 0 s i
                    (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
              = ∑ i ∈ Finset.range ((J' + 1) / 2 + 1),
                  ‖rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S‖ :=
                Finset.sum_congr rfl
                  (fun i _ => by rw [rawIter_lap_reindex (I := I) (M := M) g₀ s i S])
            _ ≤ L := by
                rw [hL]
                exact lap_shift_le (I := I) (M := M) g₀ s ((J' + 1) / 2 + 1)
                  ((J' + 1 + 1 + 1) / 2 + 1) (by omega) S
        have hterm2 :
            ∑ a' ∈ Finset.range (J' + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖ ≤
              ((J' + 2 : ℕ) : ℝ) * (CJ * L) := by
          have hbound_each : ∀ a' ∈ Finset.range (J' + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖ ≤ CJ * L := by
            intro a' ha'
            rw [Finset.mem_range] at ha'
            refine le_trans (hCJ a' (by omega) S) ?_
            refine mul_le_mul_of_nonneg_left ?_ hCJ_nn
            rw [hL]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun i _ _ => norm_nonneg _)
          calc ∑ a' ∈ Finset.range (J' + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖
              ≤ ∑ _a' ∈ Finset.range (J' + 2), (CJ * L) := Finset.sum_le_sum hbound_each
            _ = ((J' + 2 : ℕ) : ℝ) * (CJ * L) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hstepS := hstep S
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hstepS
        have t1 :
            ‖iteratedCovGrad (I := I) g₀ 0 s J'
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ^ 2 ≤ (CJ * L) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hterm1 2
        have t2 :
            (∑ a' ∈ Finset.range (J' + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖) ^ 2 ≤
              (((J' + 2 : ℕ) : ℝ) * (CJ * L)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hterm2 2
        have hCbt2 :
            Cb * (∑ a' ∈ Finset.range (J' + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖) ^ 2 ≤
              Cb * (((J' + 2 : ℕ) : ℝ) * (CJ * L)) ^ 2 :=
          mul_le_mul_of_nonneg_left t2 hCb_nn
        have hstep2 :
            ‖iteratedCovGrad (I := I) g₀ 0 s (J' + 2) S‖ ^ 2 ≤
              (CJ * L) ^ 2 + Cb * (((J' + 2 : ℕ) : ℝ) * (CJ * L)) ^ 2 := by
          linarith [hstepS, t1, hCbt2]
        have hexpand :
            (CJ * L) ^ 2 + Cb * (((J' + 2 : ℕ) : ℝ) * (CJ * L)) ^ 2 =
              CJ ^ 2 * (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L ^ 2 := by ring
        have e1 :
            (CJ * Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2 =
              CJ ^ 2 * (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L ^ 2 := by
          have hs2 : Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) ^ 2 =
              1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2 := Real.sq_sqrt hpos
          calc (CJ * Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2
              = CJ ^ 2 * Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) ^ 2 * L ^ 2 := by ring
            _ = CJ ^ 2 * (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L ^ 2 := by rw [hs2]
        have hfinal :
            ‖iteratedCovGrad (I := I) g₀ 0 s (J' + 2) S‖ ^ 2 ≤
              (CJ * Real.sqrt (1 + Cb * ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2 := by
          rw [e1, ← hexpand]; exact hstep2
        exact le_of_sq_le_sq hfinal
          (mul_nonneg (mul_nonneg hCJ_nn (Real.sqrt_nonneg _)) hL_nn)
    refine ⟨max CJ Ctop, le_trans hCJ_nn (le_max_left _ _), fun a ha S => ?_⟩
    rcases Nat.lt_or_ge a (J + 1) with hlt | hge
    · refine le_trans (hCJ a (by omega) S) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    · obtain rfl : a = J + 1 := by omega
      refine le_trans (hCtop S) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- **Class-uniform all-orders elliptic jet bound** (the `Λ`-uniform sibling of
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`, `AllOrderGardingConstant.lean:918`).  For
every covariant rank `s` and rough-Laplacian budget `k` there is a single nonnegative constant
`C`, uniform in `S`, controlling every covariant-gradient iterate up to order `2 * k` by the
rough-Laplacian jet up to order `k`:
`‖∇^j S‖ ≤ C · ∑_{i ≤ k} ‖Δ_∇^i S‖` for all `j ≤ 2 * k`.  The constant is `Fc`-explicit
(threaded through `elliptic_engine`, hence `bochner_step_hcurv`), never a `Classical.choose` of a
curvature sup — the class-uniform content the per-metric `:918` does not expose. -/
theorem elliptic_lapSum_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g₀ 0 s,
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
        C * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
  obtain ⟨C, hC_nn, hC⟩ := elliptic_engine (I := I) (M := M) g₀ Fc hFc hcurv s (2 * k)
  refine ⟨C, hC_nn, fun j hj S => ?_⟩
  refine le_trans (hC j hj S) ?_
  refine mul_le_mul_of_nonneg_left ?_ hC_nn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => norm_nonneg _)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
