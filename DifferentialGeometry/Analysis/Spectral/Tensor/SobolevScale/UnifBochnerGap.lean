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

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
