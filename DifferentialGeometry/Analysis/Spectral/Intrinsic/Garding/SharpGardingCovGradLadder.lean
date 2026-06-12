import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.AllOrderGardingBootstrap
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Geometry.Connection.Laplacian.RoughLaplacianSecondCovGradL2Bound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

/-!
# The sharp Gårding ladder: spectral order `a` ⟺ covariant jets of order `a`

For a closed Riemannian manifold `(M, g)` and smooth compactly-supported
`(0, 2)`-tensor fields, this file closes the **currency mismatch** between the
two on-disk Sobolev scales at *matching* order:

* the **spectral** scale, `‖S‖²_{Hᵃ,spec} = ∑'_i (1 + λᵢ)ᵃ · cᵢ(S)²` with
  `cᵢ = tensorL2Coeff` the connection-Laplacian eigenbasis coordinates, and
* the **covariant-jet** scale, `∑_{j ≤ a} ‖∇ʲS‖_{L²}`.

The on-disk bootstrap `allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional`
covers only the *even* rungs (`H^{2k}` from `k` Laplacians); the four results
here supply the sharp two-sided ladder at every order:

* **odd Parseval rung** (`covGrad_rawConnLapIter_l2NormSq_eq_tsum_lambda_pow`):
  `‖∇ Δ_∇ʲ S‖²_{L²} = ∑'_i λᵢ^{2j+1} cᵢ(S)²` — an *exact identity*, from the
  rank-generic Green identity and Parseval in the eigenbasis;
* **mixed commutator bound / M3**
  (`iteratedCovGrad_rawConnLapIter_l2Norm_le_covJetSum`):
  `‖∇ᵐ Δ_∇ʲ S‖_{L²} ≤ C(j,m) · ∑_{l ≤ m+2j} ‖∇ˡS‖_{L²}` — induction on `j`
  threading the proven valence-uniform metric-trace bound
  `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` against the
  curvature-commutator defect bound `commutatorDefectBound_holds`;
* **sharp spectral-from-jets / M1** (`tensorSobolevMass_le_covJetSum_sq`):
  `∑'_i (1 + λᵢ)ᵃ cᵢ(S)² ≤ C · (∑_{j ≤ a} ‖∇ʲS‖_{L²})²` at *matching* order
  `a` (binomial expansion of the weight; even powers are iterated-Laplacian
  `L²` norms by Parseval, odd powers are the odd rungs; both reduced to jets
  of order `≤ a` by M3);
* **sharp all-rung Gårding / M2**
  (`iteratedCovGrad_l2Norm_le_sqrt_tensorSobolevMass`):
  `‖∇ᵐS‖_{L²} ≤ C · √(∑'_i (1 + λᵢ)ᵐ cᵢ(S)²)` for **every** `m` — a refined
  ladder bootstrap whose right-hand side is the Laplacian ladder
  `{Δ_∇ⁱ, ∇Δ_∇ⁱ}` (never overshooting to `Δ_∇^{⌈m/2⌉+1}`), so each ladder
  norm has spectral weight `λ^{≤ m}` exactly.

The commutator input `commutatorDefectBound_holds` is fully proven on disk,
so M3, M1 and both Parseval rungs are sorry-free (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`).  M2's ladder bootstrap
additionally threads the per-valence order-`2` Gårding family
`order2GardingFamily_holds`, whose curvature cross-term input
(`exists_abs_curvCrossTerm_l2_bound`, `AllValenceL2DefectBound.lean`) is still
posited; consumers of M2 transitively depend on `sorryAx` through that single
pre-existing node and nothing else.

Finally the **a.e.-in-time sup mass coupling / M4**
(`maxRegDuhamelSolFieldHa1_zeroDatum_spectralMass_ae_le`): for the zero-datum
Duhamel field of a time-`L²` forcing `f`, at almost every time `t` and every
spatial order `σ`, the order-`σ` spectral mass of the field value is bounded
by `2(1 + T)` times the total order-`(σ−1)` forcing mass — the
pointwise-in-time version of the `L²`-maximal-regularity one-derivative gain,
assembled from the per-mode endpoint Cauchy–Schwarz bound and the
uniform-in-`λ` Duhamel kernel mass bound, extended here from continuous to
`L²` per-mode forcings.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; eigenvalues
`λᵢ ≥ 0` of `-Δ_∇`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

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

variable (g : SmoothRiemannianMetric I M)

/-- The covariant-jet sum of order `n`: `∑_{l ≤ n} ‖∇ˡS‖_{L²}`, the
`SmoothCcTensor` seminorms of the iterated covariant gradients up to order
`n`.  This is the jet-side currency of the sharp Gårding ladder. -/
def covJetSum (n : ℕ) (S : SmoothCcTensor g 0 2) : ℝ :=
  ∑ l ∈ Finset.range (n + 1), ‖iteratedCovGrad g 0 2 l S‖

lemma covJetSum_nonneg (n : ℕ) (S : SmoothCcTensor g 0 2) :
    0 ≤ covJetSum (I := I) (M := M) g n S :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma covJetSum_mono {n n' : ℕ} (h : n ≤ n') (S : SmoothCcTensor g 0 2) :
    covJetSum (I := I) (M := M) g n S ≤ covJetSum (I := I) (M := M) g n' S := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
  exact Finset.range_subset_range.mpr (by omega)

lemma le_covJetSum {l n : ℕ} (h : l ≤ n) (S : SmoothCcTensor g 0 2) :
    ‖iteratedCovGrad g 0 2 l S‖ ≤ covJetSum (I := I) (M := M) g n S :=
  Finset.single_le_sum (f := fun l => ‖iteratedCovGrad g 0 2 l S‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

/-- Shifting one Laplacian into the base: `Δ_∇ⁱ (Δ_∇ S) = Δ_∇^{i+1} S`. -/
private lemma lapIter_shift (i : ℕ) (S : SmoothCcTensor g 0 2) :
    rawTensorConnLapIter (I := I) g 0 2 i
        (rawTensorConnLapSmooth (I := I) g 0 2 S) =
      rawTensorConnLapIter (I := I) g 0 2 (i + 1) S := by
  induction i with
  | zero => simp [rawTensorConnLapIter]
  | succ n ihn => rw [rawTensorConnLapIter_succ, ihn, ← rawTensorConnLapIter_succ]

section SpectralRungs

/-- The squared `i`-th eigenbasis coordinate of `Δ_∇ʲ S` is `λᵢ^{2j} · cᵢ(S)²`. -/
private lemma coeff_lapIter_sq (S : SmoothCcTensor g 0 2) (j : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j S)) i) ^ 2 =
      (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 S) i) ^ 2 := by
  rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g S i j, mul_pow, ← pow_mul,
    mul_comm j 2, (even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]

/-- **Summability of the `λ`-power-weighted squared coordinates.**  For every
smooth compactly-supported `(0, 2)`-tensor `S` and every power `k`, the family
`i ↦ λᵢᵏ · cᵢ(S)²` is summable.  Even powers are the squared coordinates of
the iterated Laplacian (square-summable by Bessel/Parseval); odd powers are
dominated by the arithmetic mean of the two adjacent even powers. -/
theorem summable_lambda_pow_mul_coeff_sq (S : SmoothCcTensor g 0 2) (k : ℕ) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
      (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 S) i) ^ 2) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hsum := tensorL2Coeff_summable_sq (I := I) (M := M)
      (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j S))
    refine hsum.congr fun i => ?_
    rw [coeff_lapIter_sq (I := I) (M := M) g S j i, hj, two_mul]
  · have hsum1 := tensorL2Coeff_summable_sq (I := I) (M := M)
      (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j S))
    have hsum2 := tensorL2Coeff_summable_sq (I := I) (M := M)
      (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 (j + 1) S))
    have hdom := (hsum1.add hsum2).mul_left (1 / 2 : ℝ)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
    · have hlam := tensor_lambda_nonneg (I := I) (M := M) i
      positivity
    · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      set c := tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 S) i with hc_def
      rw [coeff_lapIter_sq (I := I) (M := M) g S j i,
        coeff_lapIter_sq (I := I) (M := M) g S (j + 1) i, ← hlam_def, ← hc_def]
      have hk : lam ^ k = lam ^ (2 * j) * lam := by
        rw [hj, pow_succ]
      have hamgm : lam ^ (2 * j) * lam ≤
          (1 / 2) * (lam ^ (2 * j) + lam ^ (2 * (j + 1))) := by
        have h1 : lam ^ (2 * (j + 1)) = lam ^ (2 * j) * lam ^ 2 := by
          rw [← pow_add]; ring_nf
        have h2 : 0 ≤ lam ^ (2 * j) := by positivity
        nlinarith [sq_nonneg (lam - 1), h2, mul_nonneg h2 (sq_nonneg (lam - 1))]
      have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
      calc lam ^ k * c ^ 2 = (lam ^ (2 * j) * lam) * c ^ 2 := by rw [hk]
        _ ≤ ((1 / 2) * (lam ^ (2 * j) + lam ^ (2 * (j + 1)))) * c ^ 2 :=
            mul_le_mul_of_nonneg_right hamgm hc2
        _ = (1 / 2) * (lam ^ (2 * j) * c ^ 2 + lam ^ (2 * (j + 1)) * c ^ 2) := by ring

/-- **The even Parseval rung.**  The squared `L²` norm of the `j`-th iterated
connection Laplacian is the spectral sum `∑'_i λᵢ^{2j} · cᵢ(S)²`. -/
theorem rawConnLapIter_l2NormSq_eq_tsum_lambda_pow (S : SmoothCcTensor g 0 2) (j : ℕ) :
    ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ ^ 2 =
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 S) i) ^ 2 := by
  rw [show ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ =
        ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (rawTensorConnLapIter (I := I) g 0 2 j S)‖ from
      (SmoothCcTensor.norm_toL2 (I := I) (M := M) _).symm,
    ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
      (hCompact (I := I) (M := M) g)]
  exact tsum_congr fun i => coeff_lapIter_sq (I := I) (M := M) g S j i

/-- **The odd Parseval rung** (an exact identity).  The squared `L²` norm of
the covariant gradient of the `j`-th iterated connection Laplacian is the odd
spectral sum:

  `‖∇ Δ_∇ʲ S‖²_{L²} = ∑'_i λᵢ^{2j+1} · cᵢ(S)²`.

By the rank-generic Green identity, `‖∇u‖² = −⟨Δ_∇ u, u⟩_{L²}` for
`u = Δ_∇ʲ S`; expanding the `L²` pairing in the resolvent eigenbasis
(Parseval for the inner product) and applying the coordinate eigen-equation
`cᵢ(Δ_∇ u) = −λᵢ cᵢ(u)` collapses the pairing to the odd spectral sum. -/
theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum_lambda_pow
    (S : SmoothCcTensor g 0 2) (j : ℕ) :
    ‖covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ^ 2 =
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j + 1) *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 S) i) ^ 2 := by
  classical
  set u : SmoothCcTensor g 0 2 := rawTensorConnLapIter (I := I) g 0 2 j S with hu_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g) with hb_def
  have hgreen : ‖covGrad (I := I) (M := M) g 0 2 u‖ ^ 2 =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 u).toFun u.toFun := by
    rw [← real_inner_self_eq_norm_sq (covGrad (I := I) (M := M) g 0 2 u),
      SmoothCcTensor.inner_def (I := I) (M := M)
        (covGrad (I := I) (M := M) g 0 2 u) (covGrad (I := I) (M := M) g 0 2 u)]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g 2 u u
  have hpair : tensorL2Inner (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 u).toFun u.toFun =
      ⟪SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (rawTensorConnLapSmooth (I := I) g 0 2 u),
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) u⟫_ℝ := by
    rw [SmoothCcTensor.inner_toL2 (I := I) (M := M)]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) _ _).symm
  have hparseval : ⟪SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
        (rawTensorConnLapSmooth (I := I) g 0 2 u),
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) u⟫_ℝ =
      ∑' i, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 u)) i *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 u) i := by
    rw [← HilbertBasis.tsum_inner_mul_inner b
      (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
        (rawTensorConnLapSmooth (I := I) g 0 2 u))
      (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) u)]
    refine tsum_congr fun i => ?_
    rw [tensorL2Coeff_eq_inner (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 u)) i,
      tensorL2Coeff_eq_inner (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 u) i, ← hb_def,
      real_inner_comm (b i) (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
        (rawTensorConnLapSmooth (I := I) g 0 2 u))]
  have hterm : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 u)) i *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 u) i =
      - ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j + 1) *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 S) i) ^ 2) := by
    intro i
    rw [rawConnLapSmooth_tensorL2Coeff (I := I) (M := M) g u i, hu_def,
      rawConnLapIter_tensorL2Coeff (I := I) (M := M) g S i j]
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    set c := tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 S) i with hc_def
    have hneg : (-lam) ^ j * (-lam) ^ j = lam ^ (2 * j) := by
      rw [← pow_add, show j + j = 2 * j from by ring,
        (even_two_mul j).neg_pow lam]
    calc - lam * ((-lam) ^ j * c) * ((-lam) ^ j * c)
        = - (((-lam) ^ j * (-lam) ^ j) * (lam * c ^ 2)) := by ring
      _ = - (lam ^ (2 * j) * (lam * c ^ 2)) := by rw [hneg]
      _ = - (lam ^ (2 * j + 1) * c ^ 2) := by rw [pow_succ]; ring
  rw [hgreen, hpair, hparseval, tsum_congr hterm, tsum_neg, neg_neg]

end SpectralRungs

section MixedCommutatorBound

/-- **M3: the mixed iterated-gradient/iterated-Laplacian jet bound.**  For
every Laplacian order `j` there are per-gradient-order constants `C : ℕ → ℝ`
such that for every gradient order `m` and every smooth compactly-supported
`(0, 2)`-tensor `S`,

  `‖∇ᵐ Δ_∇ʲ S‖_{L²} ≤ C m · ∑_{l ≤ m + 2j} ‖∇ˡS‖_{L²}`,

the *matching-order* control of the mixed jets by the pure covariant jets.
Induction on `j`: each Laplacian peels off through the valence-uniform
metric-trace bound `‖Δ_∇ S'‖ ≤ K‖∇²S'‖`
(`exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen`, proven) and the
curvature-commutator defect bound `‖Δ_∇∇ˡS − ∇ˡΔ_∇S‖ ≤ Cc l · ∑_{i≤l+1}‖∇ⁱS‖`
(`commutatorDefectBound_holds`, proven on disk), each
exchange costing two gradient orders — exactly the two orders the removed
Laplacian carries. -/
theorem iteratedCovGrad_rawConnLapIter_l2Norm_le_covJetSum (j : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (m : ℕ) (S : SmoothCcTensor g 0 2),
        ‖iteratedCovGrad g 0 2 m (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ≤
          C m * covJetSum (I := I) (M := M) g (m + 2 * j) S := by
  classical
  obtain ⟨K, hK1, htrace⟩ :=
    exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  obtain ⟨Cc, hCc, hcomm⟩ := commutatorDefectBound_holds (I := I) (M := M) g
  induction j with
  | zero =>
      refine ⟨fun _ => 1, fun _ => zero_le_one, fun m S => ?_⟩
      rw [rawTensorConnLapIter_zero, one_mul]
      exact le_covJetSum (I := I) (M := M) g (by omega) S
  | succ j ihj =>
      obtain ⟨C, hC0, hC⟩ := ihj
      refine ⟨fun m => C m * ∑ l ∈ Finset.range (m + 2 * j + 1), (K + Cc l),
        fun m => mul_nonneg (hC0 m) (Finset.sum_nonneg fun l _ => by
          have := hCc l; linarith), fun m S => ?_⟩
      set ΔS : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 S
        with hΔS_def
      have hshift : rawTensorConnLapIter (I := I) g 0 2 (j + 1) S =
          rawTensorConnLapIter (I := I) g 0 2 j ΔS :=
        (lapIter_shift (I := I) (M := M) g j S).symm
      rw [hshift]
      refine le_trans (hC m ΔS) ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (hC0 m)
      -- Bound each `‖∇ˡ(Δ_∇ S)‖` by `(K + Cc l) · covJetSum (m + 2(j+1)) S`.
      have hperl : ∀ l ∈ Finset.range (m + 2 * j + 1),
          ‖iteratedCovGrad g 0 2 l ΔS‖ ≤
            (K + Cc l) * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S := by
        intro l hl
        rw [Finset.mem_range] at hl
        have hl' : l ≤ m + 2 * j := by omega
        -- Triangle through the commutator defect.
        have htri : ‖iteratedCovGrad g 0 2 l ΔS‖ ≤
            ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                (iteratedCovGrad g 0 2 l S)‖ +
              ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                  (iteratedCovGrad g 0 2 l S) -
                iteratedCovGrad g 0 2 l ΔS‖ := by
          have h := norm_sub_le_norm_sub_add_norm_sub
            (iteratedCovGrad g 0 2 l ΔS)
            (rawTensorConnLapSmooth (I := I) g 0 (2 + l)
              (iteratedCovGrad g 0 2 l S)) 0
          simp only [sub_zero] at h
          calc ‖iteratedCovGrad g 0 2 l ΔS‖
              ≤ ‖iteratedCovGrad g 0 2 l ΔS -
                    rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                      (iteratedCovGrad g 0 2 l S)‖ +
                  ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                    (iteratedCovGrad g 0 2 l S)‖ := h
            _ = ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                    (iteratedCovGrad g 0 2 l S)‖ +
                  ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                      (iteratedCovGrad g 0 2 l S) -
                    iteratedCovGrad g 0 2 l ΔS‖ := by
                rw [norm_sub_rev]; ring
        -- The defect term.
        have hdefect : ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                (iteratedCovGrad g 0 2 l S) -
              iteratedCovGrad g 0 2 l ΔS‖ ≤
            Cc l * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S := by
          refine le_trans (hcomm S l) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCc l)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun _ _ _ => norm_nonneg _
          exact Finset.range_subset_range.mpr (by omega)
        -- The trace term: `‖Δ_∇ ∇ˡS‖ ≤ K · ‖∇^{l+2}S‖`.
        have htraceterm : ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                (iteratedCovGrad g 0 2 l S)‖ ≤
            K * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S := by
          have h0 := htrace (2 + l) (iteratedCovGrad g 0 2 l S)
          rw [← SmoothCcTensor.norm_def (I := I) (M := M)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                (iteratedCovGrad g 0 2 l S)),
            ← SmoothCcTensor.norm_def (I := I) (M := M)
              (covGrad (I := I) (M := M) g 0 (2 + l + 1)
                (covGrad (I := I) (M := M) g 0 (2 + l)
                  (iteratedCovGrad g 0 2 l S)))] at h0
          have hgrad_eq : iteratedCovGrad g 0 2 (l + 2) S =
              covGrad (I := I) (M := M) g 0 (2 + l + 1)
                (covGrad (I := I) (M := M) g 0 (2 + l)
                  (iteratedCovGrad g 0 2 l S)) := rfl
          refine le_trans h0 ?_
          refine mul_le_mul_of_nonneg_left ?_ hK0
          rw [← hgrad_eq]
          exact le_covJetSum (I := I) (M := M) g (by omega) S
        calc ‖iteratedCovGrad g 0 2 l ΔS‖
            ≤ ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                  (iteratedCovGrad g 0 2 l S)‖ +
                ‖rawTensorConnLapSmooth (I := I) g 0 (2 + l)
                    (iteratedCovGrad g 0 2 l S) -
                  iteratedCovGrad g 0 2 l ΔS‖ := htri
          _ ≤ K * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S +
                Cc l * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S :=
              add_le_add htraceterm hdefect
          _ = (K + Cc l) * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S := by
              ring
      calc covJetSum (I := I) (M := M) g (m + 2 * j) ΔS
          = ∑ l ∈ Finset.range (m + 2 * j + 1), ‖iteratedCovGrad g 0 2 l ΔS‖ := rfl
        _ ≤ ∑ l ∈ Finset.range (m + 2 * j + 1),
              (K + Cc l) * covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S :=
            Finset.sum_le_sum hperl
        _ = (∑ l ∈ Finset.range (m + 2 * j + 1), (K + Cc l)) *
              covJetSum (I := I) (M := M) g (m + 2 * (j + 1)) S := by
            rw [← Finset.sum_mul]

/-- **M3, Laplacian instance:** `‖Δ_∇ʲS‖_{L²} ≤ C(j) · ∑_{l ≤ 2j} ‖∇ˡS‖_{L²}`. -/
theorem rawConnLapIter_l2Norm_le_covJetSum (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 2,
      ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ ≤
        C * covJetSum (I := I) (M := M) g (2 * j) S := by
  obtain ⟨C, hC0, hC⟩ :=
    iteratedCovGrad_rawConnLapIter_l2Norm_le_covJetSum (I := I) (M := M) g j
  refine ⟨C 0, hC0 0, fun S => ?_⟩
  have h := hC 0 S
  rwa [iteratedCovGrad_zero, show 0 + 2 * j = 2 * j from by omega] at h

/-- **M3, gradient-of-Laplacian instance (the sharp odd companion):**
`‖∇ Δ_∇ʲS‖_{L²} ≤ C(j) · ∑_{l ≤ 2j+1} ‖∇ˡS‖_{L²}`. -/
theorem covGrad_rawConnLapIter_l2Norm_le_covJetSum (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 2,
      ‖covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ≤
        C * covJetSum (I := I) (M := M) g (2 * j + 1) S := by
  obtain ⟨C, hC0, hC⟩ :=
    iteratedCovGrad_rawConnLapIter_l2Norm_le_covJetSum (I := I) (M := M) g j
  refine ⟨C 1, hC0 1, fun S => ?_⟩
  have h := hC 1 S
  have hgrad_eq : iteratedCovGrad g 0 2 1 (rawTensorConnLapIter (I := I) g 0 2 j S) =
      covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 j S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rwa [hgrad_eq, show 1 + 2 * j = 2 * j + 1 from by omega] at h

end MixedCommutatorBound

section SharpSpectralFromJets

/-- Pointwise weight comparison: `λᵢᵏ ≤ (1 + λᵢ)^σ` for `k ≤ σ` (`σ` a natural
number cast to the real Sobolev exponent). -/
private lemma lambda_pow_le_weight {k m : ℕ} (hkm : k ≤ m)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k ≤
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) := by
  have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  have h1 : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ k :=
    pow_le_pow_left₀ hlam (by linarith) k
  have h2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ k ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m :=
    pow_le_pow_right₀ (one_le_one_add_lambda (I := I) (M := M) i) hkm
  have h3 : tensorSobolevWeight (I := I) (M := M) i (m : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ m := by
    unfold tensorSobolevWeight
    exact Real.rpow_natCast _ m
  rw [h3]
  exact le_trans h1 h2

/-- **M1: the sharp spectral mass from matching-order covariant jets.**  For
every natural Sobolev order `a` there is a constant `C ≥ 0` such that for every
smooth compactly-supported `(0, 2)`-tensor `S`, the order-`a` spectral mass is
summable and bounded by the *matching-order* jet sum:

  `∑'_i (1 + λᵢ)ᵃ · cᵢ(S)²  ≤  C · (∑_{j ≤ a} ‖∇ʲS‖_{L²})²`.

Binomial expansion `(1 + λ)ᵃ = ∑_{k ≤ a} C(a,k) λᵏ`; the even-power spectral
sums are squared iterated-Laplacian `L²` norms (even Parseval rung), the
odd-power sums are squared gradient-of-Laplacian norms (odd Parseval rung),
and both are reduced to jets of order `≤ k ≤ a` by the mixed commutator bound
M3 — never overshooting the order. -/
theorem tensorSobolevMass_le_covJetSum_sq (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 2,
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
          (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 S) i) ^ 2) ∧
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 S) i) ^ 2 ≤
        C * covJetSum (I := I) (M := M) g a S ^ 2 := by
  classical
  -- The mixed commutator constants, per Laplacian order.
  have hQ := fun j =>
    iteratedCovGrad_rawConnLapIter_l2Norm_le_covJetSum (I := I) (M := M) g j
  choose CQ hCQ0 hCQ using hQ
  -- The per-power constant: even `k = 2j` uses `CQ j 0`, odd `k = 2j+1` uses `CQ j 1`.
  set B : ℕ → ℝ := fun k => if k % 2 = 0 then CQ (k / 2) 0 else CQ (k / 2) 1
    with hB_def
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    simp only [hB_def]
    by_cases h : k % 2 = 0
    · rw [if_pos h]; exact hCQ0 (k / 2) 0
    · rw [if_neg h]; exact hCQ0 (k / 2) 1
  refine ⟨∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) * (B k) ^ 2,
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _),
    fun S => ?_⟩
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 S) i with hc_def
  -- Binomial expansion of the weight, termwise.
  have hw : ∀ i, tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (c i) ^ 2 =
      ∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) *
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2) := by
    intro i
    have hweight : tensorSobolevWeight (I := I) (M := M) i (a : ℝ) =
        ∑ k ∈ Finset.range (a + 1),
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (a.choose k : ℝ) := by
      unfold tensorSobolevWeight
      rw [Real.rpow_natCast, add_comm (1 : ℝ),
        add_pow (TensorEigenIdx.lambda (I := I) (M := M) i) 1 a]
      exact Finset.sum_congr rfl fun k _ => by rw [one_pow, mul_one]
    rw [hweight, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Summability of each power family, hence of the weighted family.
  have hsummk : ∀ k ∈ Finset.range (a + 1),
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
        (a.choose k : ℝ) *
          ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2)) :=
    fun k _ =>
      (summable_lambda_pow_mul_coeff_sq (I := I) (M := M) g S k).mul_left _
  have hsumm : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (c i) ^ 2) := by
    refine (summable_sum hsummk).congr fun i => ?_
    exact (hw i).symm
  refine ⟨hsumm, ?_⟩
  -- The per-power spectral sums against the matching-order jet sum.
  have hmassk : ∀ k ∈ Finset.range (a + 1),
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2 ≤
        (B k) ^ 2 * covJetSum (I := I) (M := M) g a S ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hka : k ≤ a := by omega
    have hjet : covJetSum (I := I) (M := M) g k S ≤
        covJetSum (I := I) (M := M) g a S :=
      covJetSum_mono (I := I) (M := M) g hka S
    have hjet0 : 0 ≤ covJetSum (I := I) (M := M) g a S :=
      covJetSum_nonneg (I := I) (M := M) g a S
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- Even power: `∑' λ^{2j} c² = ‖Δ_∇ʲS‖² ≤ (CQ j 0 · jets_{2j})²`.
      have hk2j : k = 2 * j := by omega
      have heq : ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2 =
          ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ ^ 2 := by
        rw [rawConnLapIter_l2NormSq_eq_tsum_lambda_pow (I := I) (M := M) g S j, hk2j]
      have hbound := hCQ j 0 S
      rw [iteratedCovGrad_zero] at hbound
      have hBk : B k = CQ j 0 := by
        simp only [hB_def]
        have h1 : k % 2 = 0 := by omega
        have h2 : k / 2 = j := by omega
        rw [if_pos h1, h2]
      rw [heq, hBk]
      have hnn : 0 ≤ ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ := norm_nonneg _
      have hchain : ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ ≤
          CQ j 0 * covJetSum (I := I) (M := M) g a S := by
        refine le_trans hbound ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCQ0 j 0)
        calc covJetSum (I := I) (M := M) g (0 + 2 * j) S
            = covJetSum (I := I) (M := M) g k S := by rw [hk2j, zero_add]
          _ ≤ covJetSum (I := I) (M := M) g a S := hjet
      calc ‖rawTensorConnLapIter (I := I) g 0 2 j S‖ ^ 2
          ≤ (CQ j 0 * covJetSum (I := I) (M := M) g a S) ^ 2 := by
            have hrhs : 0 ≤ CQ j 0 * covJetSum (I := I) (M := M) g a S :=
              mul_nonneg (hCQ0 j 0) hjet0
            nlinarith [hchain, hnn, hrhs]
        _ = (CQ j 0) ^ 2 * covJetSum (I := I) (M := M) g a S ^ 2 := by ring
    · -- Odd power: `∑' λ^{2j+1} c² = ‖∇Δ_∇ʲS‖² ≤ (CQ j 1 · jets_{2j+1})²`.
      have hk2j : k = 2 * j + 1 := by omega
      have heq : ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2 =
          ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ^ 2 := by
        rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum_lambda_pow
          (I := I) (M := M) g S j, hk2j]
      have hbound := hCQ j 1 S
      have hgrad_eq : iteratedCovGrad g 0 2 1
            (rawTensorConnLapIter (I := I) g 0 2 j S) =
          covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 j S) := by
        rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      rw [hgrad_eq] at hbound
      have hBk : B k = CQ j 1 := by
        simp only [hB_def]
        have h1 : ¬ (k % 2 = 0) := by omega
        have h2 : k / 2 = j := by omega
        rw [if_neg h1, h2]
      rw [heq, hBk]
      have hnn : 0 ≤ ‖covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapIter (I := I) g 0 2 j S)‖ := norm_nonneg _
      have hchain : ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ≤
          CQ j 1 * covJetSum (I := I) (M := M) g a S := by
        refine le_trans hbound ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCQ0 j 1)
        calc covJetSum (I := I) (M := M) g (1 + 2 * j) S
            = covJetSum (I := I) (M := M) g k S := by
              rw [hk2j, show 1 + 2 * j = 2 * j + 1 from by omega]
          _ ≤ covJetSum (I := I) (M := M) g a S := hjet
      calc ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 j S)‖ ^ 2
          ≤ (CQ j 1 * covJetSum (I := I) (M := M) g a S) ^ 2 := by
            have hrhs : 0 ≤ CQ j 1 * covJetSum (I := I) (M := M) g a S :=
              mul_nonneg (hCQ0 j 1) hjet0
            nlinarith [hchain, hnn, hrhs]
        _ = (CQ j 1) ^ 2 * covJetSum (I := I) (M := M) g a S ^ 2 := by ring
  -- Assemble: expand, exchange tsum with the finite binomial sum, bound termwise.
  calc ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (c i) ^ 2
      = ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
          ∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) *
            ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2) :=
        tsum_congr hw
    _ = ∑ k ∈ Finset.range (a + 1),
          ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
            (a.choose k : ℝ) *
              ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2) :=
        Summable.tsum_finsetSum hsummk
    _ = ∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) *
          ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k * (c i) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tsum_mul_left]
    _ ≤ ∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) *
          ((B k) ^ 2 * covJetSum (I := I) (M := M) g a S ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_of_nonneg_left (hmassk k hk) (Nat.cast_nonneg _)
    _ = (∑ k ∈ Finset.range (a + 1), (a.choose k : ℝ) * (B k) ^ 2) *
          covJetSum (I := I) (M := M) g a S ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring

end SharpSpectralFromJets

section SharpLadderGarding

/-- **The Laplacian ladder sum of order `p`:**
`∑_{2i ≤ p} ‖Δ_∇ⁱS‖_{L²} + ∑_{2i+1 ≤ p} ‖∇Δ_∇ⁱS‖_{L²}` — the family of mixed
Laplacian-ladder norms of total differentiation order `≤ p`.  Every term has
spectral weight `λ^{≤ p}` exactly (even and odd Parseval rungs), which is what
makes the ladder the sharp intermediary of the order-`m` Gårding bound. -/
def lapLadderSum (p : ℕ) (S : SmoothCcTensor g 0 2) : ℝ :=
  (∑ i ∈ Finset.range (p / 2 + 1), ‖rawTensorConnLapIter (I := I) g 0 2 i S‖) +
    ∑ i ∈ Finset.range ((p + 1) / 2),
      ‖covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i S)‖

lemma lapLadderSum_nonneg (p : ℕ) (S : SmoothCcTensor g 0 2) :
    0 ≤ lapLadderSum (I := I) (M := M) g p S :=
  add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

lemma lapLadderSum_mono {p q : ℕ} (h : p ≤ q) (S : SmoothCcTensor g 0 2) :
    lapLadderSum (I := I) (M := M) g p S ≤ lapLadderSum (I := I) (M := M) g q S := by
  unfold lapLadderSum
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    exact Finset.range_subset_range.mpr (by omega)
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    exact Finset.range_subset_range.mpr (by omega)

/-- Shifting one Laplacian into the base raises the ladder order by two:
`lapLadderSum p (Δ_∇S) ≤ lapLadderSum (p+2) S`. -/
lemma lapLadderSum_rawConnLap_le (p : ℕ) (S : SmoothCcTensor g 0 2) :
    lapLadderSum (I := I) (M := M) g p (rawTensorConnLapSmooth (I := I) g 0 2 S) ≤
      lapLadderSum (I := I) (M := M) g (p + 2) S := by
  unfold lapLadderSum
  refine add_le_add ?_ ?_
  · have hcongr : ∀ i, ‖rawTensorConnLapIter (I := I) g 0 2 i
          (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ =
        ‖rawTensorConnLapIter (I := I) g 0 2 (i + 1) S‖ := fun i => by
      rw [lapIter_shift (I := I) (M := M) g i S]
    rw [Finset.sum_congr rfl fun i _ => hcongr i]
    have hshift : ∑ i ∈ Finset.range (p / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g 0 2 (i + 1) S‖ =
        ∑ i ∈ Finset.Ico 1 (p / 2 + 2),
          ‖rawTensorConnLapIter (I := I) g 0 2 i S‖ := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr (by norm_num) fun i _ => by ring_nf
    rw [hshift]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    omega
  · have hcongr : ∀ i, ‖covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapIter (I := I) g 0 2 i
            (rawTensorConnLapSmooth (I := I) g 0 2 S))‖ =
        ‖covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapIter (I := I) g 0 2 (i + 1) S)‖ := fun i => by
      rw [lapIter_shift (I := I) (M := M) g i S]
    rw [Finset.sum_congr rfl fun i _ => hcongr i]
    have hshift : ∑ i ∈ Finset.range ((p + 1) / 2),
          ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 (i + 1) S)‖ =
        ∑ i ∈ Finset.Ico 1 ((p + 1) / 2 + 1),
          ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 i S)‖ := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr (by norm_num) fun i _ => by ring_nf
    rw [hshift]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    omega

/-- **The sharp ladder bootstrap.**  For every order `p` there is a constant
`C ≥ 0` with: for every `q ≤ p` and every smooth compactly-supported
`(0, 2)`-tensor `S`,

  `‖∇^q S‖_{L²} ≤ C · lapLadderSum q S`.

The same strong-induction skeleton as the on-disk even bootstrap
`gradOrder_l2Norm_le_lapIter_sum`, but with the *Laplacian-ladder* right-hand
side `{Δ_∇ⁱ, ∇Δ_∇ⁱ}` instead of `{Δ_∇ⁱ}` alone: the order-`q+2` step applies
the per-valence order-`2` Gårding estimate to `∇^qS` and exchanges `Δ_∇` with
`∇^q` through the commutator defect, and the base cases `q ∈ {0, 1}` are the
ladder terms themselves — so for odd `q` the recursion terminates at
`∇Δ_∇^{(q-1)/2}` (total order `q`) and never overshoots to `Δ_∇^{(q+1)/2}`
(total order `q + 1`).  This is the sharpness the even-rung bootstrap lacks. -/
theorem iteratedCovGrad_l2Norm_le_lapLadderSum (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, q ≤ p → ∀ S : SmoothCcTensor g 0 2,
      ‖iteratedCovGrad g 0 2 q S‖ ≤ C * lapLadderSum (I := I) (M := M) g q S := by
  classical
  obtain ⟨Cg, hCg, hgardS⟩ := order2GardingFamily_holds (I := I) (M := M) g
  obtain ⟨Cc, hCc, hcommU⟩ := commutatorDefectBound_holds (I := I) (M := M) g
  induction p with
  | zero =>
      refine ⟨1, zero_le_one, fun q hq S => ?_⟩
      interval_cases q
      rw [iteratedCovGrad_zero, one_mul]
      have h0 : ‖S‖ = ‖rawTensorConnLapIter (I := I) g 0 2 0 S‖ := by
        rw [rawTensorConnLapIter_zero]
      rw [h0]
      refine le_trans ?_ (le_add_of_nonneg_right
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      exact Finset.single_le_sum
        (f := fun i => ‖rawTensorConnLapIter (I := I) g 0 2 i S‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  | succ p ihp =>
      obtain ⟨C, hC0, hC⟩ := ihp
      match p with
      | 0 =>
          -- Orders `q ≤ 1`: both are single ladder terms.
          refine ⟨max C 1, le_trans hC0 (le_max_left _ _), fun q hq S => ?_⟩
          interval_cases q
          · refine le_trans (hC 0 le_rfl S) ?_
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (lapLadderSum_nonneg (I := I) (M := M) g 0 S)
          · have hgrad_eq : iteratedCovGrad g 0 2 1 S =
                covGrad (I := I) (M := M) g 0 2
                  (rawTensorConnLapIter (I := I) g 0 2 0 S) := by
              rw [iteratedCovGrad_succ, iteratedCovGrad_zero,
                rawTensorConnLapIter_zero]
            rw [hgrad_eq]
            have hsingle : ‖covGrad (I := I) (M := M) g 0 2
                  (rawTensorConnLapIter (I := I) g 0 2 0 S)‖ ≤
                lapLadderSum (I := I) (M := M) g 1 S := by
              unfold lapLadderSum
              refine le_trans ?_ (le_add_of_nonneg_left
                (Finset.sum_nonneg fun _ _ => norm_nonneg _))
              exact Finset.single_le_sum
                (f := fun i => ‖covGrad (I := I) (M := M) g 0 2
                  (rawTensorConnLapIter (I := I) g 0 2 i S)‖)
                (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by norm_num))
            calc ‖covGrad (I := I) (M := M) g 0 2
                  (rawTensorConnLapIter (I := I) g 0 2 0 S)‖
                ≤ lapLadderSum (I := I) (M := M) g 1 S := hsingle
              _ = 1 * lapLadderSum (I := I) (M := M) g 1 S := by ring
              _ ≤ max C 1 * lapLadderSum (I := I) (M := M) g 1 S :=
                  mul_le_mul_of_nonneg_right (le_max_right _ _)
                    (lapLadderSum_nonneg (I := I) (M := M) g 1 S)
      | m + 1 =>
          -- The genuine step: target order `p + 1 = m + 2`.
          set sg : ℝ := Real.sqrt (Cg (2 + m)) with hsg_def
          have hsg0 : 0 ≤ sg := Real.sqrt_nonneg _
          set Cnew : ℝ := max C (sg * (2 * C + Cc m * ((m + 2) * C))) with hCnew_def
          have hCnew0 : 0 ≤ Cnew := le_trans hC0 (le_max_left _ _)
          refine ⟨Cnew, hCnew0, fun q hq S => ?_⟩
          rcases Nat.lt_or_ge q (m + 2) with hqlt | hqge
          · -- Inherited orders.
            refine le_trans (hC q (by omega) S) ?_
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (lapLadderSum_nonneg (I := I) (M := M) g q S)
          have hqeq : q = m + 2 := by omega
          subst hqeq
          -- Gårding at valence `2 + m` on `∇^m S`.
          set Sm : SmoothCcTensor g 0 (2 + m) := iteratedCovGrad g 0 2 m S
            with hSm_def
          have hgrad2_eq : iteratedCovGrad g 0 2 (m + 2) S =
              covGrad (I := I) (M := M) g 0 (2 + m + 1)
                (covGrad (I := I) (M := M) g 0 (2 + m) Sm) := by
            rw [hSm_def]; rfl
          have hgard2 := hgardS (2 + m) Sm
          set nHess : ℝ := ‖covGrad (I := I) (M := M) g 0 (2 + m + 1)
            (covGrad (I := I) (M := M) g 0 (2 + m) Sm)‖ with hnHess_def
          set nLap : ℝ := ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) Sm‖
            with hnLap_def
          set nS : ℝ := ‖Sm‖ with hnS_def
          have hnHess0 : 0 ≤ nHess := norm_nonneg _
          have hnLap0 : 0 ≤ nLap := norm_nonneg _
          have hnS0 : 0 ≤ nS := norm_nonneg _
          have hgard_fp : nHess ≤ sg * (nLap + nS) := by
            rw [hsg_def, ← Real.sqrt_sq hnHess0]
            calc Real.sqrt (nHess ^ 2)
                ≤ Real.sqrt (Cg (2 + m) * (nLap ^ 2 + nS ^ 2)) :=
                  Real.sqrt_le_sqrt hgard2
              _ = Real.sqrt (Cg (2 + m)) * Real.sqrt (nLap ^ 2 + nS ^ 2) := by
                  rw [Real.sqrt_mul (hCg (2 + m))]
              _ ≤ Real.sqrt (Cg (2 + m)) * (nLap + nS) := by
                  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
                  rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ nLap + nS)]
                  refine Real.sqrt_le_sqrt ?_
                  nlinarith [mul_nonneg hnLap0 hnS0]
          set L : ℝ := lapLadderSum (I := I) (M := M) g (m + 2) S with hL_def
          have hL0 : 0 ≤ L := lapLadderSum_nonneg (I := I) (M := M) g (m + 2) S
          -- Commutator exchange on `Δ_∇ ∇^m S`.
          have hcomm_m := hcommU S m
          have htri : nLap ≤
              ‖iteratedCovGrad g 0 2 m (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ +
                ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                    (iteratedCovGrad g 0 2 m S) -
                  iteratedCovGrad g 0 2 m
                    (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ := by
            rw [hnLap_def, hSm_def]
            exact norm_le_norm_add_norm_sub'
              (rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                (iteratedCovGrad g 0 2 m S))
              (iteratedCovGrad g 0 2 m (rawTensorConnLapSmooth (I := I) g 0 2 S))
          -- The exchanged main term, by IH at order `m` with base `Δ_∇S`.
          have hmain : ‖iteratedCovGrad g 0 2 m
                (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ ≤ C * L := by
            refine le_trans (hC m (by omega)
              (rawTensorConnLapSmooth (I := I) g 0 2 S)) ?_
            refine mul_le_mul_of_nonneg_left ?_ hC0
            refine le_trans (lapLadderSum_mono (I := I) (M := M) g
              (by omega : m ≤ m) _) ?_
            exact lapLadderSum_rawConnLap_le (I := I) (M := M) g m S
          -- The defect term, by IH at orders `≤ m + 1`.
          have hdefect : ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                  (iteratedCovGrad g 0 2 m S) -
                iteratedCovGrad g 0 2 m
                  (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ ≤
              Cc m * ((m + 2) * C * L) := by
            refine le_trans (hcomm_m) ?_
            refine mul_le_mul_of_nonneg_left ?_ (hCc m)
            have hper : ∀ i ∈ Finset.range (m + 2),
                ‖iteratedCovGrad g 0 2 i S‖ ≤ C * L := by
              intro i hi
              rw [Finset.mem_range] at hi
              refine le_trans (hC i (by omega) S) ?_
              refine mul_le_mul_of_nonneg_left ?_ hC0
              exact lapLadderSum_mono (I := I) (M := M) g (by omega) S
            calc ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i S‖
                ≤ ∑ _i ∈ Finset.range (m + 2), C * L := Finset.sum_le_sum hper
              _ = (m + 2) * (C * L) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  push_cast; ring
              _ = (m + 2) * C * L := by ring
          -- `‖∇^m S‖` itself, by IH at order `m`.
          have hnS_le : nS ≤ C * L := by
            rw [hnS_def, hSm_def]
            refine le_trans (hC m (by omega) S) ?_
            refine mul_le_mul_of_nonneg_left ?_ hC0
            exact lapLadderSum_mono (I := I) (M := M) g (by omega) S
          have hnLap_le : nLap ≤ C * L + Cc m * ((m + 2) * C * L) :=
            le_trans htri (add_le_add hmain hdefect)
          have hfinal : nHess ≤ Cnew * L := by
            have h1 : nHess ≤ sg * (2 * C + Cc m * ((m + 2) * C)) * L := by
              calc nHess ≤ sg * (nLap + nS) := hgard_fp
                _ ≤ sg * ((C * L + Cc m * ((m + 2) * C * L)) + C * L) := by
                    refine mul_le_mul_of_nonneg_left ?_ hsg0
                    exact add_le_add hnLap_le hnS_le
                _ = sg * (2 * C + Cc m * ((m + 2) * C)) * L := by ring
            refine le_trans h1 ?_
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) hL0
          rw [hgrad2_eq]
          exact hfinal

/-- **M2: the sharp all-rung Gårding bound.**  For every order `m` there is a
constant `C ≥ 0` such that for every smooth compactly-supported
`(0, 2)`-tensor `S`,

  `‖∇ᵐS‖_{L²} ≤ C · √(∑'_i (1 + λᵢ)ᵐ · cᵢ(S)²)`,

the order-`m` covariant gradient controlled by the *matching-order* spectral
mass — including the odd rungs the on-disk even bootstrap
(`allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional`) does not reach.  The
ladder bootstrap reduces `‖∇ᵐS‖` to the Laplacian-ladder norms
`{‖Δ_∇ⁱS‖}_{2i ≤ m} ∪ {‖∇Δ_∇ⁱS‖}_{2i+1 ≤ m}`, and each ladder norm is an exact
spectral sum (even/odd Parseval rung) with weight `λ^{≤ m} ≤ (1 + λ)ᵐ`. -/
theorem iteratedCovGrad_l2Norm_le_sqrt_tensorSobolevMass (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 2,
      ‖iteratedCovGrad g 0 2 m S‖ ≤
        C * Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
              (SmoothCcTensor.toL2 S) i) ^ 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := iteratedCovGrad_l2Norm_le_lapLadderSum (I := I) (M := M) g m
  obtain ⟨CM, _hCM0, hCM⟩ := tensorSobolevMass_le_covJetSum_sq (I := I) (M := M) g m
  refine ⟨C * (m + 2), by positivity, fun S => ?_⟩
  set mass : ℝ := ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
    tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 S) i) ^ 2 with hmass_def
  have hmass_summable := (hCM S).1
  have hmass0 : 0 ≤ mass := by
    rw [hmass_def]
    refine tsum_nonneg fun i => ?_
    have := tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ)
    positivity
  -- Each ladder term is bounded by `√mass`.
  have hladder_even : ∀ i, 2 * i ≤ m →
      ‖rawTensorConnLapIter (I := I) g 0 2 i S‖ ≤ Real.sqrt mass := by
    intro i h2i
    have hsq : ‖rawTensorConnLapIter (I := I) g 0 2 i S‖ ^ 2 ≤ mass := by
      rw [rawConnLapIter_l2NormSq_eq_tsum_lambda_pow (I := I) (M := M) g S i,
        hmass_def]
      refine Summable.tsum_le_tsum (fun j => ?_)
        (summable_lambda_pow_mul_coeff_sq (I := I) (M := M) g S (2 * i))
        hmass_summable
      exact mul_le_mul_of_nonneg_right
        (lambda_pow_le_weight (I := I) (M := M) g h2i j) (sq_nonneg _)
    rw [← Real.sqrt_sq (norm_nonneg (rawTensorConnLapIter (I := I) g 0 2 i S))]
    exact Real.sqrt_le_sqrt hsq
  have hladder_odd : ∀ i, 2 * i + 1 ≤ m →
      ‖covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i S)‖ ≤
        Real.sqrt mass := by
    intro i h2i
    have hsq : ‖covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapIter (I := I) g 0 2 i S)‖ ^ 2 ≤ mass := by
      rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum_lambda_pow
        (I := I) (M := M) g S i, hmass_def]
      refine Summable.tsum_le_tsum (fun j => ?_)
        (summable_lambda_pow_mul_coeff_sq (I := I) (M := M) g S (2 * i + 1))
        hmass_summable
      exact mul_le_mul_of_nonneg_right
        (lambda_pow_le_weight (I := I) (M := M) g h2i j) (sq_nonneg _)
    rw [← Real.sqrt_sq (norm_nonneg (covGrad (I := I) (M := M) g 0 2
      (rawTensorConnLapIter (I := I) g 0 2 i S)))]
    exact Real.sqrt_le_sqrt hsq
  -- The ladder sum has at most `m + 2` terms.
  have hladder : lapLadderSum (I := I) (M := M) g m S ≤ (m + 2) * Real.sqrt mass := by
    unfold lapLadderSum
    have h1 : ∑ i ∈ Finset.range (m / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g 0 2 i S‖ ≤
        (m / 2 + 1 : ℕ) * Real.sqrt mass := by
      calc ∑ i ∈ Finset.range (m / 2 + 1), ‖rawTensorConnLapIter (I := I) g 0 2 i S‖
          ≤ ∑ _i ∈ Finset.range (m / 2 + 1), Real.sqrt mass := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.mem_range] at hi
            exact hladder_even i (by omega)
        _ = (m / 2 + 1 : ℕ) * Real.sqrt mass := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ∑ i ∈ Finset.range ((m + 1) / 2),
          ‖covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapIter (I := I) g 0 2 i S)‖ ≤
        ((m + 1) / 2 : ℕ) * Real.sqrt mass := by
      calc ∑ i ∈ Finset.range ((m + 1) / 2),
            ‖covGrad (I := I) (M := M) g 0 2
              (rawTensorConnLapIter (I := I) g 0 2 i S)‖
          ≤ ∑ _i ∈ Finset.range ((m + 1) / 2), Real.sqrt mass := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.mem_range] at hi
            exact hladder_odd i (by omega)
        _ = ((m + 1) / 2 : ℕ) * Real.sqrt mass := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcount : ((m / 2 + 1 : ℕ) : ℝ) + (((m + 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
      have : (m / 2 + 1) + ((m + 1) / 2) ≤ m + 2 := by omega
      exact_mod_cast this
    have hsqrt0 : 0 ≤ Real.sqrt mass := Real.sqrt_nonneg _
    nlinarith [h1, h2, hcount, hsqrt0]
  calc ‖iteratedCovGrad g 0 2 m S‖
      ≤ C * lapLadderSum (I := I) (M := M) g m S := hC m le_rfl S
    _ ≤ C * ((m + 2) * Real.sqrt mass) := mul_le_mul_of_nonneg_left hladder hC0
    _ = C * (m + 2) * Real.sqrt mass := by ring

end SharpLadderGarding

section SupInTimeMassCoupling

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {g' : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ} {T : ℝ}

/-- **The endpoint Cauchy–Schwarz bound for an `L²` per-mode forcing.**  For a
time-`L²` forcing `f`, decay rate `lam` and `0 ≤ t ≤ T`,

  `(perModeConv lam ⇑f t)² ≤ (∫₀ᵗ e^{−2·lam·(t−s)} ds) · ∫₀ᵗ (f s)² ds`.

Same discriminant argument as the continuous-forcing
`perModeConv_endpoint_sq_le`, with the interval integrability of `f²`, of the
kernel times `f`, and of the kernel square supplied by the `L²` structure
(`L²([0,T]) ⊆ L¹`, finite measure) instead of continuity. -/
theorem perModeConv_timeL2_endpoint_sq_le (lam : ℝ) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (perModeConv lam (fun s => f s) t) ^ 2 ≤
      duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hmemIcc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T ∧ t ∈ Set.Icc (0 : ℝ) T :=
    ⟨⟨le_rfl, hT⟩, ⟨ht0, htT⟩⟩
  set k : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s))) with hk_def
  have hconv_eq : perModeConv lam (fun s => f s) t =
      ∫ s in (0 : ℝ)..t, k s * f s := rfl
  set A : ℝ := ∫ s in (0 : ℝ)..t, (f s) ^ 2 with hA
  set B : ℝ := ∫ s in (0 : ℝ)..t, k s * f s with hB
  set C : ℝ := ∫ s in (0 : ℝ)..t, k s ^ 2 with hC
  have hC_eq : C = duhamelKernelSqIntegral lam t := by
    rw [hC]; unfold duhamelKernelSqIntegral
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hk_def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  -- Integrability of the three quadratic-form pieces on `[0, t] ⊆ [0, T]`.
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    Set.uIcc_subset_Icc hmemIcc.1 hmemIcc.2
  have hi_f2 : IntervalIntegrable (fun s => (f s) ^ 2) volume 0 t := by
    have hLp : Integrable (fun s => (f s) ^ 2) (timeMeasure T) := by
      refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f).congr
        (Eventually.of_forall fun s => ?_)
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    have hOn : IntegrableOn (fun s => (f s) ^ 2) (Set.Icc (0 : ℝ) T) volume := hLp
    exact (hOn.mono_set hsub).intervalIntegrable
  have hi_kf : IntervalIntegrable (fun s => k s * f s) volume 0 t := by
    have hbdd := integrableOn_bdd_mul_timeL2 (T := T)
      (k := k) (by rw [hk_def]; fun_prop) f
    exact (hbdd.mono_set hsub).intervalIntegrable
  have hi_k2 : IntervalIntegrable (fun s => k s ^ 2) volume 0 t := by
    refine Continuous.intervalIntegrable ?_ 0 t
    rw [hk_def]; fun_prop
  have hquad : ∀ c : ℝ, 0 ≤ A * (c * c) + (-(2 * B)) * c + C := by
    intro c
    have hintegrand : (fun s => (k s - c * f s) ^ 2)
        = fun s => (c * c) * (f s) ^ 2 + (-(2 * c)) * (k s * f s) + k s ^ 2 := by
      funext s; ring
    have hexpand : (∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2)
        = (c * c) * A + (-(2 * c)) * B + C := by
      rw [hintegrand,
        intervalIntegral.integral_add
          ((hi_f2.const_mul (c * c)).add (hi_kf.const_mul (-(2 * c)))) hi_k2,
        intervalIntegral.integral_add (hi_f2.const_mul (c * c))
          (hi_kf.const_mul (-(2 * c))),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (k s - c * f s) ^ 2 :=
      intervalIntegral.integral_nonneg ht0 fun s _ => sq_nonneg _
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdiscrim : discrim A (-(2 * B)) C ≤ 0 :=
    discrim_le_zero fun c => by nlinarith [hquad c]
  rw [discrim] at hdiscrim
  rw [hC_eq] at hdiscrim
  rw [hconv_eq]
  nlinarith [hdiscrim]

/-- **The per-mode one-derivative endpoint gain for an `L²` forcing.**  For
`0 ≤ lam`, `0 ≤ t ≤ T`,

  `(1 + lam) · (perModeConv lam ⇑f t)² ≤ (T + 1/2) · ‖f‖²`,

the endpoint Cauchy–Schwarz bound against the uniform-in-`λ` kernel mass bound
`(1 + λ)·mass ≤ t + 1/2`, with the time integral of `f²` closed up to the full
squared `L²` norm. -/
theorem one_add_lambda_mul_perModeConv_timeL2_endpoint_sq_le (lam : ℝ)
    (hlam : 0 ≤ lam) (hT : 0 ≤ T) (f : timeL2 ℝ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (1 + lam) * (perModeConv lam (fun s => f s) t) ^ 2 ≤
      (T + 1 / 2) * ‖f‖ ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hcs := perModeConv_timeL2_endpoint_sq_le lam hT f ⟨ht0, htT⟩
  have hkernel : (1 + lam) * duhamelKernelSqIntegral lam t ≤ t + 1 / 2 :=
    one_add_lambda_mul_duhamel_kernel_sq_integral_le hlam ht0
  have hint_le : ∫ s in (0 : ℝ)..t, (f s) ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [TimeSobolev.norm_sq_eq_integral f]
    have heq : ∀ s, ‖f s‖ ^ 2 = (f s) ^ 2 := fun s => by
      rw [Real.norm_eq_abs, sq_abs]
    rw [intervalIntegral.integral_of_le ht0]
    have hIcc : IntegrableOn (fun s => ‖f s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
      have hLp : Integrable (fun s => ‖f s‖ ^ 2) (timeMeasure T) := by
        refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f).congr
          (Eventually.of_forall fun s => ?_)
        simp only [real_inner_self_eq_norm_sq]
      exact hLp
    calc ∫ s in Set.Ioc (0 : ℝ) t, (f s) ^ 2
        = ∫ s in Set.Ioc (0 : ℝ) t, ‖f s‖ ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
          rw [heq s]
      _ ≤ ∫ s in Set.Icc (0 : ℝ) T, ‖f s‖ ^ 2 := by
          refine setIntegral_mono_set hIcc
            (Eventually.of_forall fun s => sq_nonneg _) ?_
          exact HasSubset.Subset.eventuallyLE
            (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hint_nn : 0 ≤ ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
    rw [intervalIntegral.integral_of_le ht0]
    exact setIntegral_nonneg measurableSet_Ioc fun s _ => sq_nonneg _
  have hmass_nn : 0 ≤ duhamelKernelSqIntegral lam t :=
    duhamelKernelSqIntegral_nonneg ht0
  have h1lam : (0:ℝ) ≤ 1 + lam := by linarith
  calc (1 + lam) * (perModeConv lam (fun s => f s) t) ^ 2
      ≤ (1 + lam) * (duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, (f s) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h1lam
    _ = ((1 + lam) * duhamelKernelSqIntegral lam t) * ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
        ring
    _ ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, (f s) ^ 2 :=
        mul_le_mul_of_nonneg_right hkernel hint_nn
    _ ≤ (T + 1 / 2) * ∫ s in (0 : ℝ)..t, (f s) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (by linarith) hint_nn
    _ ≤ (T + 1 / 2) * ‖f‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left hint_le (by linarith)

/-- The spectral weight at `σ` factors through `σ - 1`:
`(1 + λᵢ)^σ = (1 + λᵢ)^{σ-1} · (1 + λᵢ)`. -/
private lemma tensorSobolevWeight_sub_one_mul
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) := by
  have hpos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  unfold tensorSobolevWeight
  rw [show σ = (σ - 1) + 1 from by ring, Real.rpow_add hpos, Real.rpow_one]
  ring_nf

/-- **M4: the a.e.-in-time sup mass coupling of the zero-datum Duhamel field.**
For a time-`L²` forcing `f ∈ L²([0,T]; Hᵃ)` with summable order-`(σ−1)`
per-mode masses, at almost every time `t` the order-`σ` spectral mass of the
`H^{a+1}`-view zero-datum Duhamel field value is summable and bounded by the
total forcing mass one order down:

  `∑'_i (1 + λᵢ)^σ · ((field t).coeff i)² ≤ 2(1 + T) · ∑'_i forcingMass f (σ−1) i`.

This is the pointwise-in-time (sup-in-time, a.e.) version of the
`L²`-maximal-regularity one-derivative gain: a.e., the field's `i`-th
coordinate is the per-mode Duhamel convolution of the forcing's `i`-th
coordinate (zero datum kills the homogeneous part), and the per-mode endpoint
gain `(1 + λᵢ)·(φᵢ(t))² ≤ (T + 1/2)·‖fᵢ‖²` — uniform across the spectrum —
trades exactly one weight factor for the constant `T + 1/2 ≤ 2(1 + T)`. -/
theorem maxRegDuhamelSolFieldHa1_zeroDatum_spectralMass_ae_le
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g' r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g' r s a) T) (σ : ℝ)
    (hsum : Summable (forcingMass (I := I) (M := M) f (σ - 1))) :
    ∀ᵐ t ∂(timeMeasure T),
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          ((maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1
              (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) f t).coeff i) ^ 2) ∧
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s,
          tensorSobolevWeight (I := I) (M := M) i σ *
            ((maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) f t).coeff i) ^ 2 ≤
        2 * (1 + T) *
          ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s,
            forcingMass (I := I) (M := M) f (σ - 1) i := by
  classical
  haveI : Countable (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s) :=
    countable_tensorEigenIdx (I := I) (M := M) h_compact
  set Field := maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) f with hField_def
  -- Per-mode a.e. identification of the field coordinate with the Duhamel
  -- convolution of the forcing coordinate (zero datum: no homogeneous part).
  have hcoeff : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s,
      ∀ᵐ t ∂(timeMeasure T), (Field t).coeff i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => timeModeCoeff (I := I) (M := M) f i u) t := by
    intro i
    have hmode : timeModeCoeff (I := I) (M := M) Field i =
        homModeCoeff (I := I) (M := M) (a := a) (T := T)
            (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) i +
          solModeCoeff (I := I) (M := M) (a := a) hT.le f i := by
      rw [hField_def, maxRegDuhamelSolFieldHa1, timeModeCoeff_add (I := I) (M := M),
        maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a)
          (T := T) hT.le _ i,
        maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
          (h_compact := h_compact) (a := a) hT hT1 f i]
    have hfield_coe := timeModeCoeff_coeFn (I := I) (M := M) Field i
    have haddcoe := Lp.coeFn_add
      (homModeCoeff (I := I) (M := M) (a := a) (T := T)
        (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) i)
      (solModeCoeff (I := I) (M := M) (a := a) hT.le f i)
    have hhom0 : (homModeCoeff (I := I) (M := M) (a := a) (T := T)
          (0 : tensorHs (I := I) (M := M) g' r s (a + 2)) i :
            ℝ → ℝ) =ᵐ[timeMeasure T] fun _ => (0 : ℝ) := by
      have h1 := TimeSobolev.coeFn_ofContinuousOn (X := ℝ) (T := T)
        (f := fun u => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u) *
          (0 : tensorHs (I := I) (M := M) g' r s (a + 2)).coeff i)
        (Continuous.continuousOn (by fun_prop))
      refine h1.trans (Eventually.of_forall fun u => ?_)
      simp
    have hsol := perModeConvL2_coeFn (TensorEigenIdx.lambda (I := I) (M := M) i)
      (tensor_lambda_nonneg (I := I) (M := M) i) hT.le
      (timeModeCoeff (I := I) (M := M) f i)
    filter_upwards [hfield_coe, haddcoe, hhom0, hsol] with t h1 h2 h3 h4
    rw [← h1, hmode, h2, Pi.add_apply, h3, zero_add]
    exact h4
  rw [← ae_all_iff] at hcoeff
  filter_upwards [hcoeff, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htcoeff htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  -- The per-mode endpoint bound, weighted.
  have hper : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s,
      tensorSobolevWeight (I := I) (M := M) i σ * ((Field t).coeff i) ^ 2 ≤
        (T + 1 / 2) * forcingMass (I := I) (M := M) f (σ - 1) i := by
    intro i
    rw [htcoeff i, tensorSobolevWeight_sub_one_mul (I := I) (M := M) i σ]
    have hgain := one_add_lambda_mul_perModeConv_timeL2_endpoint_sq_le
      (TensorEigenIdx.lambda (I := I) (M := M) i)
      (tensor_lambda_nonneg (I := I) (M := M) i) hT.le
      (timeModeCoeff (I := I) (M := M) f i) htmem'
    have hw_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (σ - 1) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1)
    calc tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => timeModeCoeff (I := I) (M := M) f i u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => timeModeCoeff (I := I) (M := M) f i u) t) ^ 2) := by ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            ((T + 1 / 2) * ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hgain hw_nn
      _ = (T + 1 / 2) * forcingMass (I := I) (M := M) f (σ - 1) i := by
          rw [forcingMass]; ring
  have hsumm : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g' r s =>
      tensorSobolevWeight (I := I) (M := M) i σ * ((Field t).coeff i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) hper (hsum.mul_left (T + 1 / 2))
    have := tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    positivity
  refine ⟨hsumm, ?_⟩
  have htsum_le : ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        ((Field t).coeff i) ^ 2 ≤
      ∑' i, (T + 1 / 2) * forcingMass (I := I) (M := M) f (σ - 1) i :=
    Summable.tsum_le_tsum hper hsumm (hsum.mul_left (T + 1 / 2))
  rw [tsum_mul_left] at htsum_le
  refine le_trans htsum_le ?_
  have hforcing_nn : 0 ≤ ∑' i, forcingMass (I := I) (M := M) f (σ - 1) i :=
    tsum_nonneg fun i => forcingMass_nonneg (I := I) (M := M) f (σ - 1) i
  have hconst : T + 1 / 2 ≤ 2 * (1 + T) := by linarith [hT.le]
  exact mul_le_mul_of_nonneg_right hconst hforcing_nn

end SupInTimeMassCoupling

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
