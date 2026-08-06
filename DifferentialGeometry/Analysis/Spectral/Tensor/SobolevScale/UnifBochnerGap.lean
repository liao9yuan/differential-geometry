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

/-- **Dimension-explicit `L²` rough-Laplacian bound:** `‖Δ_∇ S‖ ≤ d · ‖∇²S‖`, `d = finrank ℝ E`.
The explicit-constant face of `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen`
(`RoughLaplacianSecondCovGradL2Bound.lean:537`), whose `∃ K` hides the witness `K = d`.  Obtained
from the PUBLIC pointwise `rawConnLap_fiberNormSq_le_secondCovGrad` (`:441`, constant `d²`) by the
standard `L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`. -/
private theorem rawLap_le_secGrad_dim
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ ≤
      (Module.finrank ℝ E : ℝ) *
        ‖covGrad (I := I) (M := M) g₀ 0 (s + 1)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ := by
  classical
  set HH : SmoothCcTensor g₀ 0 (s + 1 + 1) :=
    covGrad (I := I) (M := M) g₀ 0 (s + 1) (covGrad (I := I) (M := M) g₀ 0 s S) with hHH_def
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 s S).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * ∑ _i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 1 + 1) x (HH.toSection x) := by
    intro x
    rw [Finset.sum_const, Finset.card_range, one_nsmul, hHH_def]
    exact rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g₀ s S x
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀ 1
    (fun _ => s + 1 + 1) (fun _ => HH) (rawTensorConnLapSmooth (I := I) g₀ 0 s S)
    (Module.finrank ℝ E : ℝ) (Nat.cast_nonneg _) hpt
  rw [Finset.sum_const, Finset.card_range, one_nsmul] at hpack
  exact hpack

/-! ### The explicit constant chain (brick E1)

Closed-form constants for the class-uniform Gårding/Bochner chain proved below.  Each is a
function of the abstract curvature-jet family `Fc : ℕ → ℝ`, the ambient dimension
`d = Module.finrank ℝ E`, and the order arguments only — no `Classical.choose`, no metric, no
`∃`.  This is what makes the chain genuinely class-uniform: two metrics of the same `Λ`-class
sharing one `Fc` receive the SAME constant, so the endpoints can floor a class-level quantity.
Nonnegativity is proved separately (`…_nonneg`), so the closed formulas stay readable. -/

/-- Constant of `roughLapComm_unif` — the `m`-fold `[Δ_∇, ∇^m]` commutator at gradient order `p`.
Closed form of the recursion `C_{m+1}(p) = Fc p + C_m (p+1)`, `C_0 = 0`. -/
def roughLapCommC (Fc : ℕ → ℝ) (m p : ℕ) : ℝ := ∑ q ∈ Finset.range m, Fc (p + q)

/-- Constant of `rawConnLapIter_unif` at gradient order `a`: the dimension constant `d` of
`rawConnLap_fiberNormSq_le_secondCovGrad` plus the order-`0` commutator constant. -/
def rawLapIterC (Fc : ℕ → ℝ) (d a : ℕ) : ℝ := (d : ℝ) + roughLapCommC Fc a 0

/-- Constant of `baseAddLower_unif` at Laplacian-jet depth `k`:
`C_k(0)² + 2·(rawLapIterC (k-1))·√d·C_k(1)`.  At `k = 0` every summand vanishes, matching the
trivial `k = 0` branch. -/
def baseLowerC (Fc : ℕ → ℝ) (d k : ℕ) : ℝ :=
  roughLapCommC Fc k 0 ^ 2 +
    2 * (rawLapIterC Fc d (k - 1) * (Real.sqrt (d : ℝ) * roughLapCommC Fc k 1))

/-- Constant of `bochner_step_hcurv`: the base+lower defect plus the order-`0` curvature bound. -/
def bochnerStepC (Fc : ℕ → ℝ) (d k : ℕ) : ℝ := baseLowerC Fc d k + Fc 0

/-- Top-order factor of the `elliptic_engine` recursion at step `J`: `1` at `J = 0` (the
curvature-free order-`1` Dirichlet estimate) and `√(1 + bochnerStepC (J-1) · (J+1)²)` above. -/
def ellipticTopC (Fc : ℕ → ℝ) (d J : ℕ) : ℝ :=
  if J = 0 then 1
  else Real.sqrt (1 + bochnerStepC Fc d (J - 1) * ((J + 1 : ℕ) : ℝ) ^ 2)

/-- Constant of the uniform elliptic jet engine at jet budget `J`. -/
def ellipticEngC (Fc : ℕ → ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | J + 1 => max (ellipticEngC Fc d J) (ellipticEngC Fc d J * ellipticTopC Fc d J)

/-- Constant of `jetEven_unif`: `(2k+1)·ellipticEngC(2k)·(k+1)`. -/
def jetEvenC (Fc : ℕ → ℝ) (d k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ) * (ellipticEngC Fc d (2 * k) * ((k : ℝ) + 1))

/-- Constant family of `iterRawLap_unif` (`‖∇^p(Δ_∇^i S)‖`), recursion
`C_{i+1}(p) = C_i(p) · ∑_{a ≤ 2i+p} rawLapIterC a`, `C_0 = 1`. -/
def iterRawLapC (Fc : ℕ → ℝ) (d : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | i + 1, p => iterRawLapC Fc d i p * ∑ a ∈ Finset.range (2 * i + p + 1), rawLapIterC Fc d a

/-- Constant of `modeLeJet_unif` at spectral order `j`: the square of `iterRawLapC` at
Laplacian depth `j / 2` and gradient order `j % 2` (even/odd branches unified). -/
def modeJetC (Fc : ℕ → ℝ) (d j : ℕ) : ℝ := iterRawLapC Fc d (j / 2) (j % 2) ^ 2

/-- Constant of the endpoint `hsCovsum_unif`: `√(2^{n-1}·(modeJetC 0 + modeJetC n))`. -/
def hsCovsumC (Fc : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ (n - 1) * (modeJetC Fc d 0 + modeJetC Fc d n))

/-- Constant family of `iterLapGradComm_unif` (`‖∇^p([Δ_∇^i, ∇] S)‖`), recursion
`C_{i+1}(p) = Fc p · ∑_{a<p+2} iterRawLapC i a + rawLapIterC p · ∑_{q<p+3} C_i q`, `C_0 = 0`. -/
def lapGradCommC (Fc : ℕ → ℝ) (d : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | i + 1, p =>
      Fc p * (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc d i a) +
        rawLapIterC Fc d p * ∑ q ∈ Finset.range (p + 3), lapGradCommC Fc d i q

/-- Constant of `jetOdd_unif`: `Clow + Cgard·((k+1) + Ccommsum·Ceven)` with
`Clow = Ceven = jetEvenC k`, `Cgard = ellipticEngC (2k)`, `Ccommsum = ∑_{i ≤ k} lapGradCommC i 0`. -/
def jetOddC (Fc : ℕ → ℝ) (d k : ℕ) : ℝ :=
  jetEvenC Fc d k +
    ellipticEngC Fc d (2 * k) *
      (((k + 1 : ℕ) : ℝ) +
        (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc d i 0) * jetEvenC Fc d k)

/-- Constant of the endpoint `covsum_hs_unif`: the even branch `jetEvenC (n/2)` and the odd
branch `jetOddC (n/2)`. -/
def covsumHsC (Fc : ℕ → ℝ) (d n : ℕ) : ℝ :=
  if n % 2 = 0 then jetEvenC Fc d (n / 2) else jetOddC Fc d (n / 2)

/-- The defining recursion of `roughLapCommC`: `C_{m+1}(p) = Fc p + C_m (p+1)`. -/
theorem roughLapCommC_succ (Fc : ℕ → ℝ) (m p : ℕ) :
    roughLapCommC Fc (m + 1) p = Fc p + roughLapCommC Fc m (p + 1) := by
  have hre : ∑ q ∈ Finset.range m, Fc (p + (q + 1)) =
      ∑ q ∈ Finset.range m, Fc (p + 1 + q) :=
    Finset.sum_congr rfl (fun q _ => by rw [show p + (q + 1) = p + 1 + q from by omega])
  unfold roughLapCommC
  simp only [Finset.sum_range_succ', Nat.add_zero]
  rw [hre]
  exact add_comm _ _

theorem ellipticTopC_nonneg (Fc : ℕ → ℝ) (d J : ℕ) : 0 ≤ ellipticTopC Fc d J := by
  unfold ellipticTopC
  split
  · norm_num
  · exact Real.sqrt_nonneg _

theorem ellipticEngC_nonneg (Fc : ℕ → ℝ) (d J : ℕ) : 0 ≤ ellipticEngC Fc d J := by
  induction J with
  | zero => norm_num [ellipticEngC]
  | succ J ih =>
      rw [ellipticEngC]
      exact le_trans ih (le_max_left _ _)

theorem jetEvenC_nonneg (Fc : ℕ → ℝ) (d k : ℕ) : 0 ≤ jetEvenC Fc d k := by
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (ellipticEngC_nonneg Fc d (2 * k)) ?_)
  positivity

theorem modeJetC_nonneg (Fc : ℕ → ℝ) (d j : ℕ) : 0 ≤ modeJetC Fc d j := sq_nonneg _

theorem hsCovsumC_nonneg (Fc : ℕ → ℝ) (d n : ℕ) : 0 ≤ hsCovsumC Fc d n := Real.sqrt_nonneg _

section ConstNonneg

variable {Fc : ℕ → ℝ} (hFc : ∀ p, 0 ≤ Fc p) {d : ℕ}
include hFc

theorem roughLapCommC_nonneg (m p : ℕ) : 0 ≤ roughLapCommC Fc m p :=
  Finset.sum_nonneg (fun _ _ => hFc _)

theorem rawLapIterC_nonneg (a : ℕ) : 0 ≤ rawLapIterC Fc d a :=
  add_nonneg (Nat.cast_nonneg d) (roughLapCommC_nonneg hFc a 0)

theorem baseLowerC_nonneg (k : ℕ) : 0 ≤ baseLowerC Fc d k := by
  refine add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) ?_)
  exact mul_nonneg (rawLapIterC_nonneg hFc (k - 1))
    (mul_nonneg (Real.sqrt_nonneg _) (roughLapCommC_nonneg hFc k 1))

theorem bochnerStepC_nonneg (k : ℕ) : 0 ≤ bochnerStepC Fc d k :=
  add_nonneg (baseLowerC_nonneg hFc k) (hFc 0)

theorem iterRawLapC_nonneg (i p : ℕ) : 0 ≤ iterRawLapC Fc d i p := by
  induction i generalizing p with
  | zero => rw [iterRawLapC]; norm_num
  | succ i ih =>
      rw [iterRawLapC]
      exact mul_nonneg (ih p) (Finset.sum_nonneg (fun a _ => rawLapIterC_nonneg hFc a))

theorem lapGradCommC_nonneg (i p : ℕ) : 0 ≤ lapGradCommC Fc d i p := by
  induction i generalizing p with
  | zero => rw [lapGradCommC]
  | succ i ih =>
      rw [lapGradCommC]
      refine add_nonneg (mul_nonneg (hFc p)
        (Finset.sum_nonneg (fun a _ => iterRawLapC_nonneg hFc i a))) ?_
      exact mul_nonneg (rawLapIterC_nonneg hFc p)
        (Finset.sum_nonneg (fun q _ => ih q))

theorem jetOddC_nonneg (k : ℕ) : 0 ≤ jetOddC Fc d k := by
  refine add_nonneg (jetEvenC_nonneg Fc d k)
    (mul_nonneg (ellipticEngC_nonneg Fc d (2 * k)) (add_nonneg (Nat.cast_nonneg _) ?_))
  exact mul_nonneg (Finset.sum_nonneg (fun i _ => lapGradCommC_nonneg hFc i 0))
    (jetEvenC_nonneg Fc d k)

theorem covsumHsC_nonneg (n : ℕ) : 0 ≤ covsumHsC Fc d n := by
  unfold covsumHsC
  split
  · exact jetEvenC_nonneg Fc d _
  · exact jetOddC_nonneg hFc _

end ConstNonneg

/-- A rank-fixed, order-zero package for the curvature action in the Bochner identity.

Unlike the all-order `hcurv` interface below, this records only the estimate actually used by
one Bochner step: `pointwiseTensorCurv` at one covariant rank, with no differentiated curvature
action and no quantification over unrelated tensor ranks. -/
structure IsCurvAction0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  bound : ∀ S : SmoothCcTensor g₀ 0 s,
    ‖pointwiseTensorCurv (I := I) (M := M) g₀ s S‖ ≤
      K * ∑ a ∈ Finset.range 2, ‖iteratedCovGrad (I := I) g₀ 0 s a S‖

set_option maxHeartbeats 1600000 in
-- The final `nlinarith` (Weitzenböck identity + Cauchy–Schwarz curvature pairing) is
-- elaboration-heavy; the budget is raised as at `DirichletSpectralBochnerGap.lean:1219`.
/-- **The rank-fixed single Bochner step.**  Uniform sibling of
`iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1220`) with an explicit constant `Cbase + K`.

Hypotheses (both discharged downstream, not `Classical.choose`):
* `hact` — the finite order-zero curvature-action package at rank `s + k`;
* `hbase` — the class-uniform commutator base+lower bound (uniform sibling of
  `rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`),
  with constant `Cbase`.  Expressing `Cbase` through `Fc` is the next sub-brick.

Conclusion: for every smooth compactly-supported `(0,s)`-tensor `u`,
`‖∇^{k+2} u‖²_{L²} ≤ ‖∇^{k}(Δ_∇ u)‖²_{L²} + (Cbase + K)·(∑_{a≤k+1} ‖∇^a u‖)²`. -/
theorem bochner_step_action
    (g₀ : SmoothRiemannianMetric I M) (s k : ℕ)
    (K : ℝ) (hact : IsCurvAction0 (I := I) (M := M) g₀ (s + k) K)
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
        + (Cbase + K) * (∑ a ∈ Finset.range (k + 2),
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
      ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ ≤ K * SUM := by
    have hKb := hact.bound P
    have hsumexp :
        ∑ a ∈ Finset.range 2, ‖iteratedCovGrad (I := I) g₀ 0 (s + k) a P‖ =
          ‖P‖ + ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
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
    nlinarith [hsum_le, hact.nonneg, hSUM_nn]
  have hpair_bound :
      |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
          (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
          (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun| ≤ K * SUM ^ 2 := by
    calc |tensorL2Inner (I := I) (M := M) g₀ 0 (s + k + 1)
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P).toFun
            (covGrad (I := I) (M := M) g₀ 0 (s + k) P).toFun|
        ≤ ‖pointwiseTensorCurv (I := I) (M := M) g₀ (s + k) P‖ *
            ‖covGrad (I := I) (M := M) g₀ 0 (s + k) P‖ := hpair_le
      _ ≤ (K * SUM) * SUM := by
          refine mul_le_mul hcurvnorm hgradPnorm (norm_nonneg _) ?_
          exact mul_nonneg hact.nonneg hSUM_nn
      _ = K * SUM ^ 2 := by ring
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
  nlinarith [hbase_le, hpair_bound, hneg_le, hSUM_nn, hact.nonneg]

/-- The all-rank/all-order compatibility wrapper around `bochner_step_action`. -/
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
  refine bochner_step_action (I := I) (M := M) g₀ s k (Fc 0) ?_ Cbase hbase
  refine ⟨hFc 0, ?_⟩
  intro S
  simpa only [iteratedCovGrad_zero, Nat.zero_add] using hcurv (s + k) 0 S

/-- Closed covariant-jet constant for the finite `H²` Bochner estimate. -/
def h2CovsumC (K : ℝ) : ℝ := 2 + Real.sqrt (1 + 4 * K)

/-- The finite `H²` covariant-jet constant is nonnegative. -/
theorem h2CovsumC_nonneg (K : ℝ) : 0 ≤ h2CovsumC K := by
  unfold h2CovsumC
  positivity

/-- The finite curvature-action specialization of the hard `H²` Sobolev comparison.

Only `IsCurvAction0 g₀ s K` is needed: the order-zero curvature action at the tensor rank being
estimated.  No differentiated action, unrelated tensor rank, or all-order curvature family enters
this estimate. -/
theorem covsum_hs_two
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g₀ s K)
    (S : SmoothCcTensor g₀ 0 s) :
    ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      h2CovsumC K * ‖ccTensorToHs (I := I) (M := M) g₀ s (2 : ℝ) S‖ := by
  classical
  set N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ s (2 : ℝ) S‖ with hN
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hbase : ‖S‖ ≤ N := by
    have hzero := rawIter_even (I := I) (M := M) g₀ s 0 S
    rw [rawTensorConnLapIter_zero, SmoothCcTensor.norm_toL2] at hzero
    refine hzero.trans ?_
    rw [hN]
    exact ccToHs_norm_mono (I := I) (M := M) g₀ s (by norm_num) S
  have hlap : ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ ≤ N := by
    have hone := rawIter_even (I := I) (M := M) g₀ s 1 S
    rw [rawTensorConnLapIter_one, SmoothCcTensor.norm_toL2] at hone
    simpa [hN] using hone
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
  have hgrad_sq : ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ^ 2 ≤ N ^ 2 := by
    calc
      ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ^ 2
          ≤ ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ * ‖S‖ := hdir
      _ ≤ N * N := mul_le_mul hlap hbase (norm_nonneg _) hN_nn
      _ = N ^ 2 := by ring
  have hgrad : ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ≤ N :=
    le_of_sq_le_sq hgrad_sq hN_nn
  have hcomm : ∀ u : SmoothCcTensor g₀ 0 s,
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
          (iteratedCovGrad (I := I) g₀ 0 s 0 u)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 s 0
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 +
          0 * (∑ a ∈ Finset.range (0 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
    intro u
    simp only [Nat.add_zero, iteratedCovGrad_zero, zero_mul, add_zero]
    exact le_rfl
  have hstep := bochner_step_action (I := I) (M := M) g₀ s 0 K hact 0 hcomm S
  rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hstep
  simp only [zero_add, iteratedCovGrad_zero] at hstep
  have hsum01 :
      ∑ a ∈ Finset.range 2, ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤ 2 * N := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedCovGrad_zero]
    nlinarith
  have hlap_sq : ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hlap 2
  have hsum_sq :
      (∑ a ∈ Finset.range 2, ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 ≤
        (2 * N) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsum01 2
  have hKsum :
      K * (∑ a ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 ≤ K * (2 * N) ^ 2 :=
    mul_le_mul_of_nonneg_left hsum_sq hact.nonneg
  have hsqrt_arg : 0 ≤ 1 + 4 * K := by nlinarith [hact.nonneg]
  have hsqrt_sq : Real.sqrt (1 + 4 * K) ^ 2 = 1 + 4 * K :=
    Real.sq_sqrt hsqrt_arg
  have hsecond_sq :
      ‖iteratedCovGrad (I := I) g₀ 0 s 2 S‖ ^ 2 ≤
        (Real.sqrt (1 + 4 * K) * N) ^ 2 := by
    calc
      ‖iteratedCovGrad (I := I) g₀ 0 s 2 S‖ ^ 2 ≤
          ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖ ^ 2 +
            K * (∑ a ∈ Finset.range 2,
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := hstep
      _ ≤ N ^ 2 + K * (2 * N) ^ 2 := add_le_add hlap_sq hKsum
      _ = (1 + 4 * K) * N ^ 2 := by ring
      _ = Real.sqrt (1 + 4 * K) ^ 2 * N ^ 2 := by rw [hsqrt_sq]
      _ = (Real.sqrt (1 + 4 * K) * N) ^ 2 := by ring
  have hsecond : ‖iteratedCovGrad (I := I) g₀ 0 s 2 S‖ ≤
      Real.sqrt (1 + 4 * K) * N :=
    le_of_sq_le_sq hsecond_sq (mul_nonneg (Real.sqrt_nonneg _) hN_nn)
  calc
    ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ =
        ‖S‖ + ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 s 2 S‖ := by
            norm_num [Finset.sum_range_succ, iteratedCovGrad_zero]
    _ ≤ N + N + Real.sqrt (1 + 4 * K) * N := by linarith
    _ = h2CovsumC K *
        ‖ccTensorToHs (I := I) (M := M) g₀ s (2 : ℝ) S‖ := by
      rw [hN]
      unfold h2CovsumC
      ring

/-- **Constant-exposed form of `roughLapComm_unif`** (brick E1).  Same bound, but with the closed
formula `roughLapCommC Fc m p = ∑_{q<m} Fc (p+q)` in place of an existential witness, so two
metrics of the same `Λ`-class sharing one `Fc` receive the SAME constant. -/
theorem roughLapComm_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (m : ℕ) :
    ∀ (s p : ℕ) (S : SmoothCcTensor g₀ 0 s),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + m) p
          (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
              (iteratedCovGrad (I := I) g₀ 0 s m S) -
            iteratedCovGrad (I := I) g₀ 0 s m
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖ ≤
        roughLapCommC Fc m p * ∑ a ∈ Finset.range (m + p + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction m with
  | zero =>
    intro s p S
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
    have h0 : roughLapCommC Fc 0 p = 0 := by simp [roughLapCommC]
    rw [hz, norm_zero, h0, zero_mul]
  | succ m ih =>
    intro s p S
    rw [roughLapCommC_succ]
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
          roughLapCommC Fc m (p + 1) * fullSum := by
      have hcomp :
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 (s + m) (p + 1) comm_m‖ := by
        have h := norm_iterCovGrad_comp (I := I) (M := M) g₀ (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := ih s (p + 1) S
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    have hfinal : Fc p * fullSum + roughLapCommC Fc m (p + 1) * fullSum =
        (Fc p + roughLapCommC Fc m (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)‖
        ≤ Fc p * fullSum + roughLapCommC Fc m (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (Fc p + roughLapCommC Fc m (p + 1)) * fullSum := hfinal

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
  intro s
  exact ⟨roughLapCommC Fc m, fun p => roughLapCommC_nonneg hFc m p,
    fun p S => roughLapComm_const (I := I) (M := M) g₀ Fc hFc hcurv m s p S⟩

/-- **Constant-exposed form of `rawConnLapIter_unif`** (brick E1): the constant is the closed
formula `rawLapIterC Fc d a = d + ∑_{q<a} Fc q`, `d = finrank ℝ E`.  The dimension summand is the
explicit witness of `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen`, supplied here by
`rawLap_le_secGrad_dim`. -/
theorem rawConnLapIter_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (a s : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
      rawLapIterC Fc (Module.finrank ℝ E) a *
        ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  unfold rawLapIterC
  have hK_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hCfun_nn : 0 ≤ roughLapCommC Fc a 0 := roughLapCommC_nonneg hFc a 0
  set FULL : ℝ := ∑ b ∈ Finset.range (a + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hlap_second :
      ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + a) (iteratedCovGrad (I := I) g₀ 0 s a S)‖ ≤
        (Module.finrank ℝ E : ℝ) * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ := by
    have hgen := rawLap_le_secGrad_dim (I := I) (M := M) g₀ (s + a)
      (iteratedCovGrad (I := I) g₀ 0 s a S)
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
        roughLapCommC Fc a 0 *
          ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
    have h := roughLapComm_const (I := I) (M := M) g₀ Fc hFc hcurv a s 0 S
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
    _ ≤ (Module.finrank ℝ E : ℝ) * ‖iteratedCovGrad (I := I) g₀ 0 s (a + 2) S‖ +
          roughLapCommC Fc a 0 *
            ∑ b ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ :=
        add_le_add hlap_second hcomm
    _ ≤ (Module.finrank ℝ E : ℝ) * FULL + roughLapCommC Fc a 0 * FULL :=
        add_le_add (mul_le_mul_of_nonneg_left hsecond_le hK_nn)
          (mul_le_mul_of_nonneg_left hsub_le hCfun_nn)
    _ = ((Module.finrank ℝ E : ℝ) + roughLapCommC Fc a 0) * FULL := by ring

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
  exact ⟨rawLapIterC Fc (Module.finrank ℝ E) a, rawLapIterC_nonneg hFc a,
    fun S => rawConnLapIter_const (I := I) (M := M) g₀ Fc hFc hcurv a s S⟩

set_option maxHeartbeats 1600000 in
-- The IBP cross-term + Cauchy–Schwarz `nlinarith` is elaboration-heavy; the budget is
-- raised as at `DirichletSpectralBochnerGap.lean:1219`.
/-- **Constant-exposed form of `baseAddLower_unif`** (brick E1): the constant is the closed formula
`baseLowerC Fc d k = C_k(0)² + 2·rawLapIterC(k-1)·√d·C_k(1)` in the commutator constants
`C_k = roughLapCommC Fc k`, `d = finrank ℝ E`. -/
theorem baseAddLower_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) (u : SmoothCcTensor g₀ 0 s) :
    ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + k)
        (iteratedCovGrad (I := I) g₀ 0 s k u)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2
      + baseLowerC Fc (Module.finrank ℝ E) k * (∑ a ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  classical
  rcases k with _ | j
  · have hD0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0)
            (iteratedCovGrad (I := I) g₀ 0 s 0 u) =
          iteratedCovGrad (I := I) g₀ 0 s 0
            (rawTensorConnLapSmooth (I := I) g₀ 0 s u) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero]
    rw [hD0]
    exact le_add_of_nonneg_right (mul_nonneg (baseLowerC_nonneg hFc _) (sq_nonneg _))
  · unfold baseLowerC
    simp only [Nat.add_sub_cancel]
    have hCfun : ∀ (p : ℕ) (v : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + (j + 1)) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
                (iteratedCovGrad (I := I) g₀ 0 s (j + 1) v) -
              iteratedCovGrad (I := I) g₀ 0 s (j + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 s v))‖ ≤
          roughLapCommC Fc (j + 1) p * ∑ a ∈ Finset.range (j + 1 + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a v‖ :=
      fun p v => roughLapComm_const (I := I) (M := M) g₀ Fc hFc hcurv (j + 1) s p v
    have hCrc : ∀ v : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s j (rawTensorConnLapSmooth (I := I) g₀ 0 s v)‖ ≤
          rawLapIterC Fc (Module.finrank ℝ E) j *
            ∑ b ∈ Finset.range (j + 3), ‖iteratedCovGrad (I := I) g₀ 0 s b v‖ :=
      fun v => rawConnLapIter_const (I := I) (M := M) g₀ Fc hFc hcurv j s v
    have hC0_nn : 0 ≤ roughLapCommC Fc (j + 1) 0 := roughLapCommC_nonneg hFc (j + 1) 0
    have hC1_nn : 0 ≤ roughLapCommC Fc (j + 1) 1 := roughLapCommC_nonneg hFc (j + 1) 1
    have hCrc_nn : 0 ≤ rawLapIterC Fc (Module.finrank ℝ E) j := rawLapIterC_nonneg hFc j
    have hdimR_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
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
    have hDnorm : ‖D‖ ≤ roughLapCommC Fc (j + 1) 0 * SUM := by
      have h := hCfun 0 u
      simp only [iteratedCovGrad_zero, Nat.add_zero] at h
      rw [hD_eq_comm]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ hC0_nn
      rw [hSUM]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
      intro b hb; rw [Finset.mem_range] at hb ⊢; omega
    have hgradDnorm :
        ‖covGrad (I := I) (M := M) g₀ 0 (s + (j + 1)) D‖ ≤
          roughLapCommC Fc (j + 1) 1 * SUM := by
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
    have hTnorm : ‖T‖ ≤ rawLapIterC Fc (Module.finrank ℝ E) j * SUM := by
      have h := hCrc u
      rw [hT_def]
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrc_nn
      rw [hSUM, show j + 3 = j + 1 + 2 from by omega]
    have hcovDivD :
        ‖covDivergence (I := I) (M := M) g₀ (s + j) D‖ ≤
          Real.sqrt (Module.finrank ℝ E : ℝ) * (roughLapCommC Fc (j + 1) 1 * SUM) := by
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
    have hcross_abs : |(⟪A, D⟫_ℝ : ℝ)| ≤
        (rawLapIterC Fc (Module.finrank ℝ E) j * SUM) *
          (Real.sqrt (Module.finrank ℝ E : ℝ) * (roughLapCommC Fc (j + 1) 1 * SUM)) := by
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
    have hDnorm_sq : ‖D‖ ^ 2 ≤ roughLapCommC Fc (j + 1) 0 ^ 2 * SUM ^ 2 := by
      have h1 : ‖D‖ ^ 2 ≤ (roughLapCommC Fc (j + 1) 0 * SUM) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hDnorm 2
      calc ‖D‖ ^ 2 ≤ (roughLapCommC Fc (j + 1) 0 * SUM) ^ 2 := h1
        _ = roughLapCommC Fc (j + 1) 0 ^ 2 * SUM ^ 2 := by ring
    rw [show ‖rawTensorConnLapSmooth (I := I) g₀ 0 (s + (j + 1))
          (iteratedCovGrad (I := I) g₀ 0 s (j + 1) u)‖ ^ 2 = ‖B‖ ^ 2 from rfl,
      show ‖iteratedCovGrad (I := I) g₀ 0 s (j + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u)‖ ^ 2 = ‖A‖ ^ 2 from rfl,
      hnorm_add]
    have hcross_le : 2 * (⟪A, D⟫_ℝ : ℝ) ≤
        2 * ((rawLapIterC Fc (Module.finrank ℝ E) j * SUM) *
          (Real.sqrt (Module.finrank ℝ E : ℝ) * (roughLapCommC Fc (j + 1) 1 * SUM))) := by
      have := (abs_le.mp hcross_abs).2
      linarith [this]
    nlinarith [hcross_le, hDnorm_sq, hSUM_nn, hCrc_nn, hdimR_nn, hC0_nn, hC1_nn]

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
  exact ⟨baseLowerC Fc (Module.finrank ℝ E) k, baseLowerC_nonneg hFc k,
    fun u => baseAddLower_const (I := I) (M := M) g₀ Fc hFc hcurv s k u⟩

/-- **Constant-exposed form of `bochner_step_hcurv`** (brick E1): the constant is the closed
formula `bochnerStepC Fc d k = baseLowerC Fc d k + Fc 0`. -/
theorem bochnerStep_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) (u : SmoothCcTensor g₀ 0 s) :
    ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s (k + 2) u)‖ ^ 2 ≤
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 s k
          (rawTensorConnLapSmooth (I := I) g₀ 0 s u))‖ ^ 2
      + bochnerStepC Fc (Module.finrank ℝ E) k * (∑ a ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s a u‖) ^ 2 := by
  unfold bochnerStepC
  exact bochner_step_unif (I := I) (M := M) g₀ s k Fc hFc hcurv
    (baseLowerC Fc (Module.finrank ℝ E) k)
    (fun v => baseAddLower_const (I := I) (M := M) g₀ Fc hFc hcurv s k v) u

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
  exact ⟨bochnerStepC Fc (Module.finrank ℝ E) k, bochnerStepC_nonneg hFc k,
    fun u => bochnerStep_const (I := I) (M := M) g₀ Fc hFc hcurv s k u⟩

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
/-- **Constant-exposed uniform elliptic jet engine** (brick E1).  The `∀ a ≤ J` bound
`‖∇^a S‖ ≤ C · ∑_{i ≤ ⌈a/2⌉} ‖Δ_∇^i S‖` with the closed constant `ellipticEngC Fc d J`
(`d = finrank ℝ E`) instead of an existential witness. -/
private theorem elliptic_engine_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s : ℕ) :
    ∀ (J a : ℕ), a ≤ J → ∀ S : SmoothCcTensor g₀ 0 s,
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤
        ellipticEngC Fc (Module.finrank ℝ E) J * ∑ i ∈ Finset.range ((a + 1) / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
  intro J
  induction J with
  | zero =>
    intro a ha S
    obtain rfl : a = 0 := Nat.le_zero.mp ha
    have hc : ellipticEngC Fc (Module.finrank ℝ E) 0 = 1 := by unfold ellipticEngC; rfl
    rw [iteratedCovGrad_zero, hc, one_mul]
    exact Finset.single_le_sum (a := 0)
      (fun i _ => norm_nonneg (rawTensorConnLapIter (I := I) g₀ 0 s i S))
      (by rw [Finset.mem_range]; omega)
  | succ J ih =>
    have hCtop : ∀ S : SmoothCcTensor g₀ 0 s,
        ‖iteratedCovGrad (I := I) g₀ 0 s (J + 1) S‖ ≤
          ellipticEngC Fc (Module.finrank ℝ E) J *
              ellipticTopC Fc (Module.finrank ℝ E) J *
            ∑ i ∈ Finset.range ((J + 1 + 1) / 2 + 1),
              ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
      rcases J with _ | J'
      · -- top order `a = 1`: curvature-free order-1 Dirichlet-energy estimate
        intro S
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
        have hc : ellipticEngC Fc (Module.finrank ℝ E) 0 *
            ellipticTopC Fc (Module.finrank ℝ E) 0 = 1 := by
          unfold ellipticEngC ellipticTopC
          norm_num
        rw [hc, one_mul, hsum]
        have hsq :
            ‖iteratedCovGrad (I := I) g₀ 0 s 1 S‖ ^ 2 ≤
              (‖S‖ + ‖rawTensorConnLapSmooth (I := I) g₀ 0 s S‖) ^ 2 := by
          nlinarith [hdir, norm_nonneg S,
            norm_nonneg (rawTensorConnLapSmooth (I := I) g₀ 0 s S),
            mul_nonneg (norm_nonneg S)
              (norm_nonneg (rawTensorConnLapSmooth (I := I) g₀ 0 s S))]
        exact le_of_sq_le_sq hsq (add_nonneg (norm_nonneg _) (norm_nonneg _))
      · -- top order `a = J' + 2 ≥ 2`: the class-uniform Bochner step at `k = J'`
        intro S
        have hCJ_nn : (0 : ℝ) ≤ ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) :=
          ellipticEngC_nonneg Fc (Module.finrank ℝ E) (J' + 1)
        have hCb_nn : (0 : ℝ) ≤ bochnerStepC Fc (Module.finrank ℝ E) J' :=
          bochnerStepC_nonneg hFc J'
        have hpos : (0 : ℝ) ≤
            1 + bochnerStepC Fc (Module.finrank ℝ E) J' * ((J' + 2 : ℕ) : ℝ) ^ 2 := by
          nlinarith [hCb_nn, sq_nonneg ((J' + 2 : ℕ) : ℝ)]
        have htop_eq : ellipticTopC Fc (Module.finrank ℝ E) (J' + 1) =
            Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' * ((J' + 2 : ℕ) : ℝ) ^ 2) := by
          unfold ellipticTopC
          have h1 : J' + 1 - 1 = J' := by omega
          have h2 : J' + 1 + 1 = J' + 2 := by omega
          rw [if_neg (by omega : ¬ (J' + 1 = 0)), h1, h2]
        rw [htop_eq]
        set L : ℝ := ∑ i ∈ Finset.range ((J' + 1 + 1 + 1) / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ with hL
        have hL_nn : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have hterm1 :
            ‖iteratedCovGrad (I := I) g₀ 0 s J'
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
              ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L := by
          refine le_trans (ih J' (by omega) (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) ?_
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
              ((J' + 2 : ℕ) : ℝ) * (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) := by
          have hbound_each : ∀ a' ∈ Finset.range (J' + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖ ≤
                ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L := by
            intro a' ha'
            rw [Finset.mem_range] at ha'
            refine le_trans (ih a' (by omega) S) ?_
            refine mul_le_mul_of_nonneg_left ?_ hCJ_nn
            rw [hL]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun i _ _ => norm_nonneg _)
          calc ∑ a' ∈ Finset.range (J' + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖
              ≤ ∑ _a' ∈ Finset.range (J' + 2),
                  (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) :=
                Finset.sum_le_sum hbound_each
            _ = ((J' + 2 : ℕ) : ℝ) *
                  (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hstepS := bochnerStep_const (I := I) (M := M) g₀ Fc hFc hcurv s J' S
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hstepS
        have t1 :
            ‖iteratedCovGrad (I := I) g₀ 0 s J'
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ^ 2 ≤
              (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hterm1 2
        have t2 :
            (∑ a' ∈ Finset.range (J' + 2), ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖) ^ 2 ≤
              (((J' + 2 : ℕ) : ℝ) *
                (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hterm2 2
        have hCbt2 :
            bochnerStepC Fc (Module.finrank ℝ E) J' *
                (∑ a' ∈ Finset.range (J' + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 s a' S‖) ^ 2 ≤
              bochnerStepC Fc (Module.finrank ℝ E) J' *
                (((J' + 2 : ℕ) : ℝ) *
                  (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L)) ^ 2 :=
          mul_le_mul_of_nonneg_left t2 hCb_nn
        have hstep2 :
            ‖iteratedCovGrad (I := I) g₀ 0 s (J' + 2) S‖ ^ 2 ≤
              (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) ^ 2 +
                bochnerStepC Fc (Module.finrank ℝ E) J' *
                  (((J' + 2 : ℕ) : ℝ) *
                    (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L)) ^ 2 := by
          linarith [hstepS, t1, hCbt2]
        have hexpand :
            (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L) ^ 2 +
                bochnerStepC Fc (Module.finrank ℝ E) J' *
                  (((J' + 2 : ℕ) : ℝ) *
                    (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) * L)) ^ 2 =
              ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) ^ 2 *
                (1 + bochnerStepC Fc (Module.finrank ℝ E) J' * ((J' + 2 : ℕ) : ℝ) ^ 2) *
                L ^ 2 := by ring
        have e1 :
            (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) *
                Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
                  ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2 =
              ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) ^ 2 *
                (1 + bochnerStepC Fc (Module.finrank ℝ E) J' * ((J' + 2 : ℕ) : ℝ) ^ 2) *
                L ^ 2 := by
          have hs2 : Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
              ((J' + 2 : ℕ) : ℝ) ^ 2) ^ 2 =
              1 + bochnerStepC Fc (Module.finrank ℝ E) J' * ((J' + 2 : ℕ) : ℝ) ^ 2 :=
            Real.sq_sqrt hpos
          calc (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) *
                  Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
                    ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2
              = ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) ^ 2 *
                  Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
                    ((J' + 2 : ℕ) : ℝ) ^ 2) ^ 2 * L ^ 2 := by ring
            _ = ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) ^ 2 *
                  (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
                    ((J' + 2 : ℕ) : ℝ) ^ 2) * L ^ 2 := by rw [hs2]
        have hfinal :
            ‖iteratedCovGrad (I := I) g₀ 0 s (J' + 2) S‖ ^ 2 ≤
              (ellipticEngC Fc (Module.finrank ℝ E) (J' + 1) *
                Real.sqrt (1 + bochnerStepC Fc (Module.finrank ℝ E) J' *
                  ((J' + 2 : ℕ) : ℝ) ^ 2) * L) ^ 2 := by
          rw [e1, ← hexpand]; exact hstep2
        exact le_of_sq_le_sq hfinal
          (mul_nonneg (mul_nonneg hCJ_nn (Real.sqrt_nonneg _)) hL_nn)
    intro a ha S
    rw [ellipticEngC]
    rcases Nat.lt_or_ge a (J + 1) with hlt | hge
    · refine le_trans (ih a (by omega) S) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    · obtain rfl : a = J + 1 := by omega
      refine le_trans (hCtop S) ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- **Constant-exposed form of `elliptic_lapSum_unif`** (brick E1): constant
`ellipticEngC Fc d (2k)`. -/
theorem ellipticLapSum_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k j : ℕ) (hj : j ≤ 2 * k) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * ∑ i ∈ Finset.range (k + 1),
        ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ := by
  refine le_trans
    (elliptic_engine_const (I := I) (M := M) g₀ Fc hFc hcurv s (2 * k) j hj S) ?_
  refine mul_le_mul_of_nonneg_left ?_
    (ellipticEngC_nonneg Fc (Module.finrank ℝ E) (2 * k))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => norm_nonneg _)

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
  exact ⟨ellipticEngC Fc (Module.finrank ℝ E) (2 * k),
    ellipticEngC_nonneg Fc (Module.finrank ℝ E) (2 * k),
    fun j hj S => ellipticLapSum_const (I := I) (M := M) g₀ Fc hFc hcurv s k j hj S⟩

/-- **Constant-exposed form of `jetEven_unif`** (brick E1): constant
`jetEvenC Fc d k = (2k+1)·ellipticEngC Fc d (2k)·(k+1)`. -/
theorem jetEven_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      jetEvenC Fc (Module.finrank ℝ E) k *
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ := by
  unfold jetEvenC
  have hCg_nn : (0 : ℝ) ≤ ellipticEngC Fc (Module.finrank ℝ E) (2 * k) :=
    ellipticEngC_nonneg Fc (Module.finrank ℝ E) (2 * k)
  have hCg : ∀ (j : ℕ), j ≤ 2 * k → ∀ S' : SmoothCcTensor g₀ 0 s,
      ‖iteratedCovGrad (I := I) g₀ 0 s j S'‖ ≤
        ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 s i S'‖ :=
    fun j hj S' => ellipticLapSum_const (I := I) (M := M) g₀ Fc hFc hcurv s k j hj S'
  set Nspec : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ with hNspec
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ ≤ Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S), hNspec]
    refine le_trans (rawIter_even (I := I) (M := M) g₀ s i S) ?_
    exact ccToHs_norm_mono (I := I) (M := M) g₀ s
      (by exact_mod_cast (show (2 * i : ℕ) ≤ 2 * k by omega)) S
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖ ≤ ((k : ℝ) + 1) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1), ‖rawTensorConnLapIter (I := I) g₀ 0 s i S‖
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((k : ℝ) + 1) * Nspec := by push_cast; ring
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
        ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * (((k : ℝ) + 1) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact le_trans (hCg j hj2k S) (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1),
          ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * (((k : ℝ) + 1) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * ((k : ℝ) + 1)) * Nspec := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **Class-uniform even-order covariant jet ≤ spectral `H^{2k}` norm.**  The `Λ`-uniform,
`Fc`-explicit sibling of the private `jet_even` (`IteratedCovGradHsJetBound.lean:603`): the
covariant `L²` jet through order `2k` is bounded by the spectral `H^{2k}` norm.  Hard-direction
(covsum ≤ `Hs`) even case; consumes `elliptic_lapSum_unif` and the curvature-free spectral bridge
`rawIter_even` (`‖Δ_∇^i S‖ ≤ ‖ccTensorToHs (2i) S‖`) + `ccToHs_norm_mono`. -/
theorem jetEven_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ := by
  exact ⟨jetEvenC Fc (Module.finrank ℝ E) k, jetEvenC_nonneg Fc (Module.finrank ℝ E) k,
    fun S => jetEven_const (I := I) (M := M) g₀ Fc hFc hcurv s k S⟩

/-- **Constant-exposed form of `iterRawLap_unif`** (brick E1): constant family
`iterRawLapC Fc d i p`, the closed recursion
`C_{i+1}(p) = C_i(p)·∑_{a ≤ 2i+p} rawLapIterC Fc d a`. -/
theorem iterRawLap_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (i : ℕ) :
    ∀ (s p : ℕ) (S : SmoothCcTensor g₀ 0 s),
      ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        iterRawLapC Fc (Module.finrank ℝ E) i p * ∑ b ∈ Finset.range (2 * i + p + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  classical
  induction i with
  | zero =>
    intro s p S
    rw [iterRawLapC, rawTensorConnLapIter_zero, one_mul]
    refine Finset.single_le_sum (f := fun b => ‖iteratedCovGrad (I := I) g₀ 0 s b S‖)
      (fun b _ => norm_nonneg _) ?_
    rw [Finset.mem_range]; omega
  | succ i ih =>
    intro s p S
    rw [iterRawLapC]
    have hcoef_nn : ∀ a, (0 : ℝ) ≤ rawLapIterC Fc (Module.finrank ℝ E) a :=
      fun a => rawLapIterC_nonneg hFc a
    have hcoef_bound : ∀ (a : ℕ) (S' : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapSmooth (I := I) g₀ 0 s S')‖ ≤
          rawLapIterC Fc (Module.finrank ℝ E) a * ∑ b ∈ Finset.range (a + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 s b S'‖ :=
      fun a S' => rawConnLapIter_const (I := I) (M := M) g₀ Fc hFc hcurv a s S'
    have hCfun_nn : ∀ q, (0 : ℝ) ≤ iterRawLapC Fc (Module.finrank ℝ E) i q :=
      fun q => iterRawLapC_nonneg hFc i q
    set FULL : ℝ := ∑ b ∈ Finset.range (2 * (i + 1) + p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ with hFULL
    have hpeel :
        rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S =
          rawTensorConnLapIter (I := I) g₀ 0 s i (rawTensorConnLapSmooth (I := I) g₀ 0 s S) :=
      (rawIter_lap_reindex (I := I) (M := M) g₀ s i S).symm
    rw [hpeel]
    have hih := ih s p (rawTensorConnLapSmooth (I := I) g₀ 0 s S)
    have hinner :
        ∑ a ∈ Finset.range (2 * i + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ ≤
          (∑ a ∈ Finset.range (2 * i + p + 1),
            rawLapIterC Fc (Module.finrank ℝ E) a) * FULL := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun a ha => ?_)
      have hsub : ∑ b ∈ Finset.range (a + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
        rw [hFULL]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_range] at ha hb ⊢
        omega
      calc ‖iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖
          ≤ rawLapIterC Fc (Module.finrank ℝ E) a * ∑ b ∈ Finset.range (a + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := hcoef_bound a S
        _ ≤ rawLapIterC Fc (Module.finrank ℝ E) a * FULL :=
            mul_le_mul_of_nonneg_left hsub (hcoef_nn a)
    calc ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapIter (I := I) g₀ 0 s i
            (rawTensorConnLapSmooth (I := I) g₀ 0 s S))‖
        ≤ iterRawLapC Fc (Module.finrank ℝ E) i p * ∑ a ∈ Finset.range (2 * i + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S)‖ := hih
      _ ≤ iterRawLapC Fc (Module.finrank ℝ E) i p *
            ((∑ a ∈ Finset.range (2 * i + p + 1),
              rawLapIterC Fc (Module.finrank ℝ E) a) * FULL) :=
          mul_le_mul_of_nonneg_left hinner (hCfun_nn p)
      _ = (iterRawLapC Fc (Module.finrank ℝ E) i p * ∑ a ∈ Finset.range (2 * i + p + 1),
            rawLapIterC Fc (Module.finrank ℝ E) a) * FULL := by ring

/-- **Class-uniform iterated rough-Laplacian gradient-jet bound.**  The `Λ`-uniform,
`Fc`-explicit sibling of `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le`
(`AllOrderGardingConstant.lean:609`): `‖∇^p(Δ_∇^i S)‖ ≤ Cfun(p)·∑_{b ≤ 2i+p} ‖∇^b S‖`, with the
constant family `Fc`+dimension-explicit (built by iterating `rawConnLapIter_unif`, never a
`Classical.choose` of a curvature sup).  Induction on `i`; the peel step reuses
`rawIter_lap_reindex`.  Easy-direction (`Hs` ≤ covsum) engine, consumed at `p = 0, 1` by
`modeLeJet_unif`. -/
theorem iterRawLap_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (i : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 s p (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
          Cfun p * ∑ b ∈ Finset.range (2 * i + p + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := by
  intro s
  exact ⟨iterRawLapC Fc (Module.finrank ℝ E) i,
    fun p => iterRawLapC_nonneg hFc i p,
    fun p S => iterRawLap_const (I := I) (M := M) g₀ Fc hFc hcurv i s p S⟩

/-- Local inline of the private `mode_summable` (`IteratedCovGradHsJetBound.lean:533`): the
eigen-mode series `∑' λ_m^j · coeff_m^2` is summable, dominated by the (public) weighted
`H^j`-summability of `ccTensorToHs`.  Curvature-free; all dependencies are public spectral API. -/
private theorem mode_summable_inl
    (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    Summable (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s =>
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ j *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
          (SmoothCcTensor.toL2 S) m) ^ 2) := by
  have hfull := (ccTensorToHs (I := I) (M := M) g₀ s (j : ℝ) S).weighted_summable
  refine Summable.of_nonneg_of_le ?_ ?_ hfull
  · intro m
    have hbase_nn : (0 : ℝ) ≤
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m := tensor_lambda_nonneg (I := I) (M := M) m
    positivity
  · intro m
    have hbase_nn : (0 : ℝ) ≤
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m := tensor_lambda_nonneg (I := I) (M := M) m
    have hbase_le :
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m ≤
          1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m := by linarith
    have hweight : tensorSobolevWeight (I := I) (M := M) m (j : ℝ) =
        (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ j := by
      unfold tensorSobolevWeight
      rw [Real.rpow_natCast]
    rw [hweight, ccTensorToHs_coeff]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbase_nn hbase_le j) (sq_nonneg _)

/-- **Constant-exposed form of `modeLeJet_unif`** (brick E1): constant
`modeJetC Fc d j = (iterRawLapC Fc d (j/2) (j%2))²`, which unifies the even (`p = 0`) and odd
(`p = 1`) branches of the per-order spectral mass bound. -/
theorem modeLeJet_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s j : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m) ^ j *
        (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2 ≤
      modeJetC Fc (Module.finrank ℝ E) j *
        (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
  classical
  unfold modeJetC
  have hsum_nn : 0 ≤
      ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hj : j = 2 * i := by omega
    have hd : j / 2 = i := by omega
    have hm : j % 2 = 0 := by omega
    rw [hd, hm]
    have hCfun_nn : (0 : ℝ) ≤ iterRawLapC Fc (Module.finrank ℝ E) i 0 :=
      iterRawLapC_nonneg hFc i 0
    have htsum :
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 := by
      rw [rawIter_tsum (I := I) (M := M) g₀ s i S, hj]
    rw [htsum]
    have hnorm_le : ‖SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        iterRawLapC Fc (Module.finrank ℝ E) i 0 *
          ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
      have h := iterRawLap_const (I := I) (M := M) g₀ Fc hFc hcurv i s 0 S
      rw [iteratedCovGrad_zero (I := I) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)] at h
      rw [SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)]
      have hrange : 2 * i + 0 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hnn : 0 ≤ ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ := norm_nonneg _
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2
        ≤ (iterRawLapC Fc (Module.finrank ℝ E) i 0 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg hCfun_nn hsum_nn]
          · exact hnorm_le
      _ = iterRawLapC Fc (Module.finrank ℝ E) i 0 ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by ring
  · have hj : j = 2 * i + 1 := by omega
    have hd : j / 2 = i := by omega
    have hm : j % 2 = 1 := by omega
    rw [hd, hm]
    have hCfun_nn : (0 : ℝ) ≤ iterRawLapC Fc (Module.finrank ℝ E) i 1 :=
      iterRawLapC_nonneg hFc i 1
    have htsum :
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
          ‖covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2 := by
      rw [covIter_tsum (I := I) (M := M) g₀ s i S, hj]
    rw [htsum]
    have hnorm_le : ‖covGrad (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        iterRawLapC Fc (Module.finrank ℝ E) i 1 *
          ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
      have h := iterRawLap_const (I := I) (M := M) g₀ Fc hFc hcurv i s 1 S
      have hcov : iteratedCovGrad (I := I) g₀ 0 s 1
            (rawTensorConnLapIter (I := I) g₀ 0 s i S) =
          covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S) := rfl
      rw [hcov] at h
      have hrange : 2 * i + 1 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hnn : 0 ≤ ‖covGrad (I := I) (M := M) g₀ 0 s
        (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ := norm_nonneg _
    calc ‖covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ^ 2
        ≤ (iterRawLapC Fc (Module.finrank ℝ E) i 1 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg hCfun_nn hsum_nn]
          · exact hnorm_le
      _ = iterRawLapC Fc (Module.finrank ℝ E) i 1 ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by ring

/-- **Class-uniform per-order spectral mass ≤ covariant jet.**  The `Λ`-uniform, `Fc`-explicit
sibling of the private `mode_le_jet` (`IteratedCovGradHsJetBound.lean:438`): the order-`j`
eigen-mode mass `∑' λ_m^j · coeff_m^2` is bounded by the covariant `L²` jet through order `j`.
Even case via `rawIter_tsum` at `iterRawLap_unif p = 0`; odd case via `covIter_tsum` at
`iterRawLap_unif p = 1`.  Easy-direction building block for `hsCovsum_unif`. -/
theorem modeLeJet_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ j *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 S) m) ^ 2 ≤
        C * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 := by
  exact ⟨modeJetC Fc (Module.finrank ℝ E) j, modeJetC_nonneg Fc (Module.finrank ℝ E) j,
    fun S => modeLeJet_const (I := I) (M := M) g₀ Fc hFc hcurv s j S⟩

/-- **Constant-exposed form of the endpoint `hsCovsum_unif`** (brick E1, easy direction):
`‖ccTensorToHs g₀ s n S‖ ≤ hsCovsumC Fc d n · ∑_{j ≤ n} ‖∇^j S‖` with the closed constant
`hsCovsumC Fc d n = √(2^{n-1}·(modeJetC Fc d 0 + modeJetC Fc d n))`, `d = finrank ℝ E`.  Unlike
`hsCovsum_unif`'s `∃ C`, this constant depends only on `(Fc, n, d)` — the class-uniformity the
`(N)` horizon floor consumes. -/
theorem hsCovsum_unif_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s n : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ≤
      hsCovsumC Fc (Module.finrank ℝ E) n * ∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ := by
  classical
  unfold hsCovsumC
  have hC₀ := modeLeJet_const (I := I) (M := M) g₀ Fc hFc hcurv s 0 S
  have hCₙ := modeLeJet_const (I := I) (M := M) g₀ Fc hFc hcurv s n S
  have hC₀_nn : (0 : ℝ) ≤ modeJetC Fc (Module.finrank ℝ E) 0 :=
    modeJetC_nonneg Fc (Module.finrank ℝ E) 0
  have hCₙ_nn : (0 : ℝ) ≤ modeJetC Fc (Module.finrank ℝ E) n :=
    modeJetC_nonneg Fc (Module.finrank ℝ E) n
  set C₀ : ℝ := modeJetC Fc (Module.finrank ℝ E) 0 with hC₀_def
  set Cₙ : ℝ := modeJetC Fc (Module.finrank ℝ E) n with hCₙ_def
  set F : ℝ := (2 : ℝ) ^ (n - 1) with hF_def
  have hF_nn : 0 ≤ F := by rw [hF_def]; positivity
  have hcoef_nn : 0 ≤ F * (C₀ + Cₙ) :=
    mul_nonneg hF_nn (add_nonneg hC₀_nn hCₙ_nn)
  set Sall : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ with hSall_def
  have hSall_nn : 0 ≤ Sall := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set term : ℕ →
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 s → ℝ := fun j m =>
    (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) m) ^ j *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
        (SmoothCcTensor.toL2 S) m) ^ 2 with hterm_def
  set mass : ℕ → ℝ := fun j => ∑' m, term j m with hmass_def
  have hterm_sum (j : ℕ) : Summable (term j) := by
    simpa only [hterm_def] using mode_summable_inl (I := I) (M := M) g₀ s j S
  have hsum₀ : ∑ a ∈ Finset.range (0 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤ Sall := by
    rw [hSall_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    exact Finset.range_mono (by omega)
  have hsum₀_nn : 0 ≤ ∑ a ∈ Finset.range (0 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmass₀ : mass 0 ≤ C₀ * Sall ^ 2 := by
    have hbase := hC₀
    have hsq : (∑ a ∈ Finset.range (0 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 ≤ Sall ^ 2 :=
      pow_le_pow_left₀ hsum₀_nn hsum₀ 2
    refine (show mass 0 ≤ C₀ * (∑ a ∈ Finset.range (0 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖) ^ 2 from ?_).trans ?_
    · simpa only [hmass_def, hterm_def] using hbase
    · exact mul_le_mul_of_nonneg_left hsq hC₀_nn
  have hmassₙ : mass n ≤ Cₙ * Sall ^ 2 := by
    simpa only [hmass_def, hterm_def, hSall_def] using hCₙ
  have hmass : mass 0 + mass n ≤ (C₀ + Cₙ) * Sall ^ 2 := by
    calc mass 0 + mass n ≤ C₀ * Sall ^ 2 + Cₙ * Sall ^ 2 :=
        add_le_add hmass₀ hmassₙ
      _ = (C₀ + Cₙ) * Sall ^ 2 := by ring
  have hrhs_sum : Summable (fun m => F * (term 0 m + term n m)) :=
    (hterm_sum 0).add (hterm_sum n) |>.mul_left F
  have hsq_le :
      ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ^ 2 ≤
        F * (C₀ + Cₙ) * Sall ^ 2 := by
    rw [ccToHs_norm_sq]
    calc
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 s,
        tensorSobolevWeight (I := I) (M := M) m (n : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
            (SmoothCcTensor.toL2 S) m) ^ 2
          ≤ ∑' m, F * (term 0 m + term n m) := by
            refine Summable.tsum_le_tsum (fun m => ?_)
              (ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S).weighted_summable
              hrhs_sum
            set L : ℝ :=
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m with hL_def
            set c : ℝ := tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 s)
              (SmoothCcTensor.toL2 S) m with hc_def
            have hL_nn : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
            have hpow : (1 + L) ^ n ≤ F * (1 ^ n + L ^ n) := by
              rw [hF_def]
              exact add_pow_le (by norm_num) hL_nn n
            have hc_nn : 0 ≤ c ^ 2 := sq_nonneg c
            have hweight : tensorSobolevWeight (I := I) (M := M) m (n : ℝ) =
                (1 + L) ^ n := by
              unfold tensorSobolevWeight
              rw [Real.rpow_natCast, hL_def]
            rw [hweight]
            calc (1 + L) ^ n * c ^ 2 ≤ (F * (1 ^ n + L ^ n)) * c ^ 2 :=
                mul_le_mul_of_nonneg_right hpow hc_nn
              _ = F * (term 0 m + term n m) := by
                rw [hterm_def, hL_def, hc_def]
                ring
      _ = F * (mass 0 + mass n) := by
          rw [tsum_mul_left, Summable.tsum_add (hterm_sum 0) (hterm_sum n)]
      _ ≤ F * ((C₀ + Cₙ) * Sall ^ 2) :=
          mul_le_mul_of_nonneg_left hmass hF_nn
      _ = F * (C₀ + Cₙ) * Sall ^ 2 := by ring
  have hrhs_nn : 0 ≤ Real.sqrt (F * (C₀ + Cₙ)) * Sall :=
    mul_nonneg (Real.sqrt_nonneg _) hSall_nn
  have hsqrt_sq : (Real.sqrt (F * (C₀ + Cₙ)) * Sall) ^ 2 =
      F * (C₀ + Cₙ) * Sall ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcoef_nn]
  have hnorm_nn : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ :=
    norm_nonneg _
  have hsquare : ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ^ 2 ≤
      (Real.sqrt (F * (C₀ + Cₙ)) * Sall) ^ 2 := by
    rw [hsqrt_sq]
    exact hsq_le
  have hsqrt := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq hnorm_nn, Real.sqrt_sq hrhs_nn] at hsqrt
  simpa only [hSall_def] using hsqrt

/-- **Class-uniform spectral `H^n` norm ≤ covariant jet** (endpoint `hs_covsum_unif`).  The
`Λ`-uniform, `Fc`-explicit sibling of `hs_le_jet` (`IteratedCovGradHsJetBound.lean:855`):
`‖ccTensorToHs g₀ s n S‖ ≤ C · ∑_{j ≤ n} ‖∇^j S‖`.  Easy direction; combines `modeLeJet_unif`
at orders `0` and `n` through the two-mass split `(1+λ)^n ≤ 2^{n-1}(1 + λ^n)` (`add_pow_le`),
with `mode_summable_inl` for the tsum manipulations.  Constant `√(2^{n-1}·(C₀ + Cₙ))`. -/
theorem hsCovsum_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ ≤
        C * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ := by
  exact ⟨hsCovsumC Fc (Module.finrank ℝ E) n, hsCovsumC_nonneg Fc (Module.finrank ℝ E) n,
    fun S => hsCovsum_unif_const (I := I) (M := M) g₀ Fc hFc hcurv s n S⟩

/-- **Constant-exposed form of `iterLapGradComm_unif`** (brick E1): constant family
`lapGradCommC Fc d i p`, the closed recursion
`C_{i+1}(p) = Fc p·∑_{a<p+2} iterRawLapC i a + rawLapIterC p·∑_{q<p+3} C_i q`. -/
theorem lapGradComm_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s i : ℕ) :
    ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
          (rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s
              (rawTensorConnLapIter (I := I) g₀ 0 s i S))‖ ≤
        lapGradCommC Fc (Module.finrank ℝ E) i p * ∑ a ∈ Finset.range (2 * i + p),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  classical
  induction i with
  | zero =>
    intro p S
    have hzero :
        rawTensorConnLapIter (I := I) g₀ 0 (s + 1) 0 (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s 0 S) =
          (0 : SmoothCcTensor g₀ 0 (s + 1)) := by
      rw [rawTensorConnLapIter_zero, rawTensorConnLapIter_zero, sub_self]
    have hgz : iteratedCovGrad (I := I) g₀ 0 (s + 1) p (0 : SmoothCcTensor g₀ 0 (s + 1)) =
        (0 : SmoothCcTensor g₀ 0 (s + 1 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 1) p
        (0 : SmoothCcTensor g₀ 0 (s + 1)) (0 : SmoothCcTensor g₀ 0 (s + 1))
      simpa using this
    rw [hzero, hgz, norm_zero, lapGradCommC, zero_mul]
  | succ i ih =>
    intro p S
    rw [lapGradCommC]
    have hCfun_nn : ∀ q, (0 : ℝ) ≤ lapGradCommC Fc (Module.finrank ℝ E) i q :=
      fun q => lapGradCommC_nonneg hFc i q
    have hCmaster_nn : ∀ a, (0 : ℝ) ≤ iterRawLapC Fc (Module.finrank ℝ E) i a :=
      fun a => iterRawLapC_nonneg hFc i a
    have hCmaster : ∀ (a : ℕ) (S' : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 s a (rawTensorConnLapIter (I := I) g₀ 0 s i S')‖ ≤
          iterRawLapC Fc (Module.finrank ℝ E) i a * ∑ b ∈ Finset.range (2 * i + a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 s b S'‖ :=
      fun a S' => iterRawLap_const (I := I) (M := M) g₀ Fc hFc hcurv i s a S'
    have hcoefB_nn : ∀ q, (0 : ℝ) ≤ rawLapIterC Fc (Module.finrank ℝ E) q :=
      fun q => rawLapIterC_nonneg hFc q
    have hcoefB_bound : ∀ (q : ℕ) (W : SmoothCcTensor g₀ 0 (s + 1)),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) W)‖ ≤
          rawLapIterC Fc (Module.finrank ℝ E) q * ∑ r ∈ Finset.range (q + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) r W‖ :=
      fun q W => rawConnLapIter_const (I := I) (M := M) g₀ Fc hFc hcurv q (s + 1) W
    set Di : SmoothCcTensor g₀ 0 (s + 1) :=
      rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
        covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)
      with hDi_def
    set FULL : ℝ := ∑ a ∈ Finset.range (2 * (i + 1) + p),
      ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ with hFULL
    have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hrec :
        rawTensorConnLapIter (I := I) g₀ 0 (s + 1) (i + 1)
              (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s
              (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ s
              (rawTensorConnLapIter (I := I) g₀ 0 s i S) +
            rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Di := by
      have hlapDi :
          rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Di =
            rawTensorConnLapIter (I := I) g₀ 0 (s + 1) (i + 1)
                (covGrad (I := I) (M := M) g₀ 0 s S) -
              rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1)
                (covGrad (I := I) (M := M) g₀ 0 s
                  (rawTensorConnLapIter (I := I) g₀ 0 s i S)) := by
        rw [hDi_def, rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 (s + 1)]
        rw [rawTensorConnLapIter_succ (I := I) g₀ 0 (s + 1) i
          (covGrad (I := I) (M := M) g₀ 0 s S)]
      have hcomm :
          rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1)
              (covGrad (I := I) (M := M) g₀ 0 s
                (rawTensorConnLapIter (I := I) g₀ 0 s i S)) =
            covGrad (I := I) (M := M) g₀ 0 s
                (rawTensorConnLapIter (I := I) g₀ 0 s (i + 1) S) +
              pointwiseTensorCurv (I := I) (M := M) g₀ s
                (rawTensorConnLapIter (I := I) g₀ 0 s i S) := by
        rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)]
        rw [rawTensorConnLapIter_succ (I := I) g₀ 0 s i S]
      rw [hlapDi, hcomm]
      abel
    rw [hrec, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + 1) p]
    refine le_trans (norm_add_le _ _) ?_
    have htermA :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ s
              (rawTensorConnLapIter (I := I) g₀ 0 s i S))‖ ≤
          Fc p * (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) * FULL := by
      have hcurvT := hcurv s p (rawTensorConnLapIter (I := I) g₀ 0 s i S)
      have hmaster_le :
          ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s a
                (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
            (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) * FULL := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun a ha => ?_)
        have hmb := hCmaster a S
        have hsub :
            ∑ b ∈ Finset.range (2 * i + a + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ ≤ FULL := by
          rw [hFULL]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
          intro b hb; rw [Finset.mem_range] at ha hb ⊢; omega
        calc ‖iteratedCovGrad (I := I) g₀ 0 s a
                (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖
            ≤ iterRawLapC Fc (Module.finrank ℝ E) i a * ∑ b ∈ Finset.range (2 * i + a + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 s b S‖ := hmb
          _ ≤ iterRawLapC Fc (Module.finrank ℝ E) i a * FULL :=
              mul_le_mul_of_nonneg_left hsub (hCmaster_nn a)
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ s
                (rawTensorConnLapIter (I := I) g₀ 0 s i S))‖
          ≤ Fc p * ∑ a ∈ Finset.range (p + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 s a
                (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ := hcurvT
        _ ≤ Fc p * ((∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) * FULL) :=
            mul_le_mul_of_nonneg_left hmaster_le (hFc p)
        _ = Fc p * (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) * FULL := by
            ring
    have htermB :
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Di)‖ ≤
          rawLapIterC Fc (Module.finrank ℝ E) p *
            (∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q) * FULL := by
      have hB := hcoefB_bound p Di
      have hih_le :
          ∑ q ∈ Finset.range (p + 3), ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q Di‖ ≤
            (∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q) * FULL := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqb := ih q S
        rw [← hDi_def] at hqb
        have hsub :
            ∑ a ∈ Finset.range (2 * i + q),
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤ FULL := by
          rw [hFULL]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
          intro b hb; rw [Finset.mem_range] at hq hb ⊢; omega
        calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q Di‖
            ≤ lapGradCommC Fc (Module.finrank ℝ E) i q * ∑ a ∈ Finset.range (2 * i + q),
                ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := hqb
          _ ≤ lapGradCommC Fc (Module.finrank ℝ E) i q * FULL :=
              mul_le_mul_of_nonneg_left hsub (hCfun_nn q)
      calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Di)‖
          ≤ rawLapIterC Fc (Module.finrank ℝ E) p * ∑ q ∈ Finset.range (p + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) q Di‖ := hB
        _ ≤ rawLapIterC Fc (Module.finrank ℝ E) p *
              ((∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q) * FULL) :=
            mul_le_mul_of_nonneg_left hih_le (hcoefB_nn p)
        _ = rawLapIterC Fc (Module.finrank ℝ E) p *
              (∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q) * FULL := by
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ s
              (rawTensorConnLapIter (I := I) g₀ 0 s i S))‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + 1) Di)‖
        ≤ Fc p * (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) * FULL +
            rawLapIterC Fc (Module.finrank ℝ E) p *
              (∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q) * FULL :=
          add_le_add htermA htermB
      _ = (Fc p * (∑ a ∈ Finset.range (p + 2), iterRawLapC Fc (Module.finrank ℝ E) i a) +
            rawLapIterC Fc (Module.finrank ℝ E) p *
              (∑ q ∈ Finset.range (p + 3), lapGradCommC Fc (Module.finrank ℝ E) i q)) * FULL := by
          ring

/-- **Class-uniform iterated-Laplacian / gradient commutator (all gradient orders).**  The
`Λ`-uniform, `Fc`-explicit sibling of the private
`exists_rawConnLapIter_covGrad_commutator_l2Norm_le_aux` (`AllOrderGardingConstant.lean:673`):
`‖∇^p([Δ_∇^i, ∇] S)‖ ≤ Cfun(p)·∑_{a<2i+p} ‖∇^a S‖`.  Induction on `i`; the curvature term is the
abstract `hcurv` (its own `Fc`), the master term is `iterRawLap_unif`, and the extra-Laplacian
term reuses `rawConnLapIter_unif` at rank `s+1` — so the constant chain is `Fc`+dimension
explicit, never a `Classical.choose` of a curvature sup. -/
theorem iterLapGradComm_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s i : ℕ) :
    ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s),
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) p
            (rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
                (covGrad (I := I) (M := M) g₀ 0 s S) -
              covGrad (I := I) (M := M) g₀ 0 s
                (rawTensorConnLapIter (I := I) g₀ 0 s i S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (2 * i + p),
            ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  exact ⟨lapGradCommC Fc (Module.finrank ℝ E) i, fun p => lapGradCommC_nonneg hFc i p,
    fun p S => lapGradComm_const (I := I) (M := M) g₀ Fc hFc hcurv s i p S⟩

/-- **Constant-exposed form of `rawConnLapCovComm_unif`** (brick E1): the `p = 0` face of
`lapGradComm_const`, constant `lapGradCommC Fc d i 0`. -/
theorem lapCovComm_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
        covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
      lapGradCommC Fc (Module.finrank ℝ E) i 0 *
        ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  have h := lapGradComm_const (I := I) (M := M) g₀ Fc hFc hcurv s i 0 S
  simpa only [iteratedCovGrad_zero, Nat.add_zero] using h

/-- **Class-uniform iterated-Laplacian / gradient commutator (order 0).**  The `p = 0` face of
`iterLapGradComm_unif`; the `Λ`-uniform, `Fc`-explicit sibling of the public
`exists_rawConnLapIter_covGrad_commutator_l2Norm_le` (`AllOrderGardingConstant.lean:830`).  The
odd-order building block consumed by `jetOdd_unif`. -/
theorem rawConnLapCovComm_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
          covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := by
  exact ⟨lapGradCommC Fc (Module.finrank ℝ E) i 0, lapGradCommC_nonneg hFc i 0,
    fun S => lapCovComm_const (I := I) (M := M) g₀ Fc hFc hcurv s i S⟩

set_option linter.unusedSectionVars false in
/-- Reindex of the covariant-jet norm under a proof of order equality (inline of the private
`IteratedCovGradHsJetBound.norm_iteratedCovGrad_order_eq:596`). -/
private theorem norm_icg_order_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h; rfl

/-- **Constant-exposed form of `jetOdd_unif`** (brick E1): constant
`jetOddC Fc d k = jetEvenC k + ellipticEngC (2k)·((k+1) + (∑_{i ≤ k} lapGradCommC i 0)·jetEvenC k)`. -/
theorem jetOdd_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      jetOddC Fc (Module.finrank ℝ E) k *
        ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  unfold jetOddC
  have hClow_nn : (0 : ℝ) ≤ jetEvenC Fc (Module.finrank ℝ E) k := jetEvenC_nonneg Fc (Module.finrank ℝ E) k
  have hCgard_nn : (0 : ℝ) ≤ ellipticEngC Fc (Module.finrank ℝ E) (2 * k) :=
    ellipticEngC_nonneg Fc (Module.finrank ℝ E) (2 * k)
  have hCcomm_nn : ∀ i, (0 : ℝ) ≤ lapGradCommC Fc (Module.finrank ℝ E) i 0 :=
    fun i => lapGradCommC_nonneg hFc i 0
  have hClow : ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      jetEvenC Fc (Module.finrank ℝ E) k * ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ :=
    jetEven_const (I := I) (M := M) g₀ Fc hFc hcurv s k S
  have hCcomm : ∀ i : ℕ,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
          covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
        lapGradCommC Fc (Module.finrank ℝ E) i 0 *
          ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
    fun i => lapCovComm_const (I := I) (M := M) g₀ Fc hFc hcurv s i S
  have hCcommsum_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0 :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  set Nspec : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccTensorToHs (I := I) (M := M) g₀ s ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def]
    refine ccToHs_norm_mono (I := I) (M := M) g₀ s ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this
  have hlow_le : ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k : ℕ) : ℝ) S‖ ≤ Nspec :=
    hccmono (2 * k) (by omega)
  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤ jetEvenC Fc (Module.finrank ℝ E) k * Nspec := by
    refine le_trans hClow ?_
    exact mul_le_mul_of_nonneg_left hlow_le hClow_nn
  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ ≤
        (1 + lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) =
          covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
                (covGrad (I := I) (M := M) g₀ 0 s S) -
              covGrad (I := I) (M := M) g₀ 0 s
                (rawTensorConnLapIter (I := I) g₀ 0 s i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 s
          (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤ Nspec := by
      refine le_trans (covIter_odd (I := I) (M := M) g₀ s i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 s a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ ≤
          lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S) -
              covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖
          ≤ lapGradCommC Fc (Module.finrank ℝ E) i 0 * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ := hcomm
        _ ≤ lapGradCommC Fc (Module.finrank ℝ E) i 0 * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 s a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ lapGradCommC Fc (Module.finrank ℝ E) i 0 * (jetEvenC Fc (Module.finrank ℝ E) k * Nspec) :=
            mul_le_mul_of_nonneg_left hlowsum (hCcomm_nn i)
        _ = lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 s
            (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S) -
            covGrad (I := I) (M := M) g₀ 0 s (rawTensorConnLapIter (I := I) g₀ 0 s i S)‖
        ≤ Nspec + lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by ring
  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ ≤
      ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖ := by
      have h := icg_comp_norm (I := I) (M := M) g₀ s 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 s S =
          iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 s (1 + 2 * k) S‖ :=
        norm_icg_order_eq (I := I) (M := M) g₀ s (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard' := ellipticLapSum_const (I := I) (M := M) g₀ Fc hFc hcurv (s + 1) k
      (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 s S)
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
            (covGrad (I := I) (M := M) g₀ 0 s S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S)‖
          ≤ ∑ i ∈ Finset.range (k + 1),
              (1 + lapGradCommC Fc (Module.finrank ℝ E) i 0 * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1),
              (Nspec + (lapGradCommC Fc (Module.finrank ℝ E) i 0) * (jetEvenC Fc (Module.finrank ℝ E) k * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 (s + 1) (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 s S)‖
        ≤ ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 (s + 1) i
              (covGrad (I := I) (M := M) g₀ 0 s S)‖ := hgard'
      _ ≤ ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * ((((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec := by
          ring
  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 s j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 s (2 * k + 1) S‖
      ≤ jetEvenC Fc (Module.finrank ℝ E) k * Nspec +
          ellipticEngC Fc (Module.finrank ℝ E) (2 * k) * (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (jetEvenC Fc (Module.finrank ℝ E) k + ellipticEngC Fc (Module.finrank ℝ E) (2 * k) *
          (((k + 1 : ℕ) : ℝ) + (∑ i ∈ Finset.range (k + 1), lapGradCommC Fc (Module.finrank ℝ E) i 0) * jetEvenC Fc (Module.finrank ℝ E) k)) * Nspec := by ring

/-- **Class-uniform odd-order covariant jet ≤ spectral `H^{2k+1}` norm.**  The `Λ`-uniform,
`Fc`-explicit sibling of the private `jet_odd` (`IteratedCovGradHsJetBound.lean:667`).  The top
order `∇^{2k+1}S = ∇^{2k}(∇S)` is controlled by `elliptic_lapSum_unif` at rank `s+1`, each
`Δ_∇^i(∇S)` being converted to the odd-order `Hs`-bounded `∇(Δ_∇^i S)` (`covIter_odd`) up to the
`Fc`-explicit commutator `rawConnLapCovComm_unif`; the lower orders reuse `jetEven_unif`. -/
theorem jetOdd_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g₀ s ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  exact ⟨jetOddC Fc (Module.finrank ℝ E) k, jetOddC_nonneg hFc k,
    fun S => jetOdd_const (I := I) (M := M) g₀ Fc hFc hcurv s k S⟩

/-- **Constant-exposed form of the endpoint `covsum_hs_unif`** (brick E1, hard direction):
`∑_{j ≤ n} ‖∇^j S‖ ≤ covsumHsC Fc d n · ‖ccTensorToHs g₀ s n S‖` with the closed constant
`covsumHsC Fc d n = jetEvenC (n/2)` for even `n` and `jetOddC (n/2)` for odd `n`,
`d = finrank ℝ E`.  Together with `hsCovsum_unif_const` these are the two class-uniform,
constant-exposed `H^n` ↔ covariant-jet endpoints. -/
theorem covsum_hs_unif_const
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s n : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
      covsumHsC Fc (Module.finrank ℝ E) n *
        ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ := by
  classical
  unfold covsumHsC
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hm : n % 2 = 0 := by omega
    have hd : n / 2 = k := by omega
    rw [if_pos hm, hd]
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact jetEven_const (I := I) (M := M) g₀ Fc hFc hcurv s k S
  · have hm : ¬ (n % 2 = 0) := by omega
    have hd : n / 2 = k := by omega
    rw [if_neg hm, hd]
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact jetOdd_const (I := I) (M := M) g₀ Fc hFc hcurv s k S

/-- **Class-uniform covariant `L²` jet ≤ spectral `H^n` norm** (endpoint `covsum_hs_unif`).  The
`Λ`-uniform, `Fc`-explicit sibling of `hsJet_le` (`IteratedCovGradHsJetBound.lean:834`):
`∑_{j ≤ n} ‖∇^j S‖ ≤ C · ‖ccTensorToHs g₀ s n S‖`.  Hard direction; the even case is
`jetEven_unif`, the odd case `jetOdd_unif`.  Together with `hsCovsum_unif` these are the two
`H^n`-norm ↔ covariant-jet endpoints of the class-uniform Sobolev comparison. -/
theorem covsum_hs_unif
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g₀ 0 s,
      ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 s j S‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g₀ s (n : ℝ) S‖ := by
  exact ⟨covsumHsC Fc (Module.finrank ℝ E) n, covsumHsC_nonneg hFc n,
    fun S => covsum_hs_unif_const (I := I) (M := M) g₀ Fc hFc hcurv s n S⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
