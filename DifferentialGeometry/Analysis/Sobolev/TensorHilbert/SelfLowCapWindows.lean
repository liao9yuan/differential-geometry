import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GradCapArms
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Lc0VBCapWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Low1KerRadiusFree
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRicciPairing

/-!
# The five summands of `selfLow_split` in the `∇P`-capped currency

`selfLow_split` writes the zero-arm self-action integrand as

`rhsSelfLow = (-2)•ricciGoodLow + (deTurckLieCovDerivArmField − edgeLiePairFam)
  + lc0VB + lc0AMix + lc0Riem`,

and `selfLow_jet` must bound its `L²` jets by the state's own jets through order
`i + 1` only.  Three of the five summands are quadratic in the connection
difference (`ricciGoodLow`'s `A·A` and `∇A ⋆ ∇T` arms, `lc0VB`, `lc0AMix`), so
the ordinary radius-free currency lands one order over budget; the capped
currency of `GradCapAtgw`/`GradCapArms` recovers the order.

This module produces the capped window `HasCapWin g₀ P · K` of each summand.  In
every case the recipe is the same and mechanical:

* every factor of the product tree has an ordinary radius-free window at
  `bP`-offset at most `+2` — one derivative of the state — and enters the capped
  currency through `capOfArm` (or `capOfBnd` when it is state-free);
* the tree is then reassembled with `capApp`/`capAdd`/`capSmul`/`capReindex`,
  all of which preserve the capped level `i + 1`;
* `capJet` integrates the result into the `range (i + 2)` budget.

Nothing about the geometry of the summands is re-proved: the arm windows are the
ones the radius-free layer already supplies, and the structural identities
(`lc0Riem_eq_app`, `amix_refold_rf`, `aaKerSplit`, `lieCov_residual`) are the
ones already committed.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LieCorr0Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### `lc0Riem`: the fixed-curvature summand -/

set_option linter.unusedVariables false in
/-- **`lc0Riem` in the capped currency.**

`lc0Riem = -(lc0RiemLive ⋆ lc0RiemPass)` with a live cometric arm costing no
derivative of the state and a state-free passenger, so this summand is honest
already in the radius-free currency; the capped statement is produced only so
that all five summands speak the same language at the assembly. -/
theorem lc0RiemCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (lc0Riem (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := rfns_iCG_cometricCastG0_atgw_rf (I := I) (M := M) g₀ hδ₀
  choose SPass hSPass_nn hSPass using
    (fun l : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 2 (4 + l)
      (iteratedCovGrad (I := I) g₀ 2 4 l (lc0RiemPass (I := I) g₀)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KLive : ℕ → ℝ := fun i => fr * Kcg i * shiftConst Λ (i + 1) with hKLive_def
  have hKLive_nn : ∀ i, 0 ≤ KLive i := fun i =>
    mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i)) (shiftConst_nn hΛ0 _)
  refine ⟨foldConst (E := E) 0 0 KLive SPass,
    fun i => foldConst_nn (u := 0) (v := 0) hKLive_nn hSPass_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  -- the live cometric arm: offset `+1`, weakened to `+2`, then shifted
  have hLive : HasCapWin (I := I) (M := M) g₀ P
      (lc0RiemLive (I := I) (M := M) g₀ g₁) KLive := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _
      (fun i => mul_nonneg hfr_nn (hKcg_nn i)) (fun m y => ?_)
    have hbnn := gridBase_nn (I := I) (M := M) g₀ P y
    refine le_trans (lc0RiemLive_rfns_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hfr_nn
    refine le_trans (hcg g₁ P htie hδ_le hδ0 hδ m y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKcg_nn m)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _ hbnn (by omega)
  -- the state-free passenger
  have hPass : HasCapWin (I := I) (M := M) g₀ P (lc0RiemPass (I := I) g₀) SPass :=
    capOfBnd (I := I) (M := M) g₀ P _ hSPass_nn (fun l y => hSPass l y)
  refine capCongr (I := I) (M := M) g₀ P (lc0Riem_eq_app (I := I) (M := M) g₀ g₁) ?_
  exact capNeg (I := I) (M := M) g₀ P
    (capApp (I := I) (M := M) g₀ P _ _ hKLive_nn hSPass_nn hLive hPass)

/-! ### `lc0AMix`: the five-factor mixed summand -/

set_option linter.unusedVariables false in
/-- **`lc0AMix` in the capped currency.**

`amix_refold_rf` writes the summand as two copies of the five-factor product
`trace ⋆ trace ⋆ mcd ⋆ trace ⋆ mcd`.  The three traces cost no derivative of the
state, the two lowered connection differences cost one each — so the summand is
quadratic in `∇P` and its radius-free window `b4_amix_atgw` sits at
`atgw bP (i + 3)`, one level over budget.  Shifting each of the five factors
first and only then folding recovers the level: every factor lands at
`atgw b'P (i + 1)` and the folds preserve that. -/
theorem lc0AMixCap (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P
          (lc0AMix (I := I) (M := M) g₀ g₁ g_bg) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Ctr2, hCtr2_nn, htr2⟩ := trace_grid_rf (I := I) (M := M) 2 g₀ hδ₀
  obtain ⟨Ctr3, hCtr3_nn, htr3⟩ := trace_grid_rf (I := I) (M := M) 3 g₀ hδ₀
  obtain ⟨Ctr4, hCtr4_nn, htr4⟩ := trace_grid_rf (I := I) (M := M) 4 g₀ hδ₀
  obtain ⟨Km0, hKm0_nn, hm0⟩ :=
    b4_mcd_atgw (I := I) (M := M) g₀ g₀ hδ₀ (Real.sqrt_nonneg Λ)
  obtain ⟨KmB, hKmB_nn, hmB⟩ :=
    b4_mcd_atgw (I := I) (M := M) g₀ g_bg hδ₀ (Real.sqrt_nonneg Λ)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KT2 : ℕ → ℝ := fun i => Ctr2 i * shiftConst Λ (i + 1) with hKT2_def
  set KT3 : ℕ → ℝ := fun i => Ctr3 i * shiftConst Λ (i + 1) with hKT3_def
  set KT4 : ℕ → ℝ := fun i => Ctr4 i * shiftConst Λ (i + 1) with hKT4_def
  set KM0 : ℕ → ℝ := fun i => fr ^ 2 * (Km0 i * shiftConst Λ (i + 1)) with hKM0_def
  set KMB : ℕ → ℝ := fun i => fr ^ 3 * (KmB i * shiftConst Λ (i + 1)) with hKMB_def
  have hKT2_nn : ∀ i, 0 ≤ KT2 i := fun i =>
    mul_nonneg (hCtr2_nn i) (shiftConst_nn hΛ0 _)
  have hKT3_nn : ∀ i, 0 ≤ KT3 i := fun i =>
    mul_nonneg (hCtr3_nn i) (shiftConst_nn hΛ0 _)
  have hKT4_nn : ∀ i, 0 ≤ KT4 i := fun i =>
    mul_nonneg (hCtr4_nn i) (shiftConst_nn hΛ0 _)
  have hKM0_nn : ∀ i, 0 ≤ KM0 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (mul_nonneg (hKm0_nn i) (shiftConst_nn hΛ0 _))
  have hKMB_nn : ∀ i, 0 ≤ KMB i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 3) (mul_nonneg (hKmB_nn i) (shiftConst_nn hΛ0 _))
  set Ktail : ℕ → ℝ := foldConst (E := E) 0 0 KT3 KM0 with hKtail_def
  have hKtail_nn : ∀ i, 0 ≤ Ktail i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKT3_nn hKM0_nn i
  set Kmid : ℕ → ℝ := foldConst (E := E) 0 0 KMB Ktail with hKmid_def
  have hKmid_nn : ∀ i, 0 ≤ Kmid i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKMB_nn hKtail_nn i
  set Ktr4 : ℕ → ℝ := foldConst (E := E) 0 0 KT4 Kmid with hKtr4_def
  have hKtr4_nn : ∀ i, 0 ≤ Ktr4 i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKT4_nn hKmid_nn i
  set Khalf : ℕ → ℝ := foldConst (E := E) 0 0 KT2 Ktr4 with hKhalf_def
  have hKhalf_nn : ∀ i, 0 ≤ Khalf i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKT2_nn hKtr4_nn i
  refine ⟨fun i => 16 * Khalf i, fun i => by have := hKhalf_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
      (P.toSection y) ≤ Real.sqrt Λ ^ 2 := by
    intro y
    rw [Real.sq_sqrt hΛ0]
    simpa using hP0 y
  -- the three moving traces: offset `+1`, weakened to `+2`, then shifted
  have htrace : ∀ (p : ℕ) (C : ℕ → ℝ), (∀ i, 0 ≤ C i) →
      (∀ (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) k) →
      ∀ σ : Equiv.Perm (Fin (p + 2)),
        HasCapWin (I := I) (M := M) g₀ P (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ)
          (fun i => C i * shiftConst Λ (i + 1)) := by
    intro p C hC hbd σ
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hC (fun i y => ?_)
    have hbnn := gridBase_nn (I := I) (M := M) g₀ P y
    refine le_trans (hbd σ i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC i)
    have hwin : (∑ k ∈ Finset.range (i + 1),
          Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y)) k) =
        Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i + 1) := rfl
    rw [hwin]
    exact Combinatorics.antidiagonalTupleGridWindow_mono _ hbnn (by omega)
  have hT2 : ∀ σ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σ) KT2 :=
    htrace 2 Ctr2 hCtr2_nn (fun σ i x => htr2 g₁ P htie hδ_le hδ0 hδ σ i x)
  have hT3 : HasCapWin (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ) KT3 :=
    htrace 3 Ctr3 hCtr3_nn (fun σ i x => htr3 g₁ P htie hδ_le hδ0 hδ σ i x) _
  have hT4 : HasCapWin (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1) KT4 :=
    htrace 4 Ctr4 hCtr4_nn (fun σ i x => htr4 g₁ P htie hδ_le hδ0 hδ σ i x) _
  -- the two lowered connection differences, extended into their slots
  have hmcd : ∀ (gb : SmoothRiemannianMetric I M) (Km : ℕ → ℝ), (∀ i, 0 ≤ Km i) →
      (∀ (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
          Km n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)) →
      HasCapWin (I := I) (M := M) g₀ P
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gb)
        (fun i => Km i * shiftConst Λ (i + 1)) := by
    intro gb Km hKm hbd
    exact capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hKm (fun i y => hbd i y)
  have hM0 : HasCapWin (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)) KM0 :=
    capIter (I := I) (M := M) g₀ P 2
      (hmcd g₀ Km0 hKm0_nn (fun n x => hm0 g₁ P htie hδ_le hδ0 hδ hsup n x))
  have hMB : HasCapWin (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)) KMB :=
    capIter (I := I) (M := M) g₀ P 3
      (hmcd g_bg KmB hKmB_nn (fun n x => hmB g₁ P htie hδ_le hδ0 hδ hsup n x))
  -- the four nested folds
  have hhalf : ∀ σ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P
        (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g_bg σ) Khalf := by
    intro σ
    have htail := capApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀))
      hKT3_nn hKM0_nn hT3 hM0
    have hmid := capApp (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)) _
      hKMB_nn hKtail_nn hMB htail
    have htr4' := capApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1) _
      hKT4_nn hKmid_nn hT4 hmid
    exact capApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σ) _ hKT2_nn hKtr4_nn (hT2 σ) htr4'
  refine capCongr (I := I) (M := M) g₀ P
    (amix_refold_rf (I := I) (M := M) g₀ g₁ g_bg) ?_
  have hsum := capAdd (I := I) (M := M) g₀ P
    (hhalf lieCorr0AMixPerm2) (hhalf (lc0SwapPermRF * lieCorr0AMixPerm2))
  have hfin := capSmul (I := I) (M := M) g₀ P (2 : ℝ) hsum
  refine capMono (I := I) (M := M) g₀ P (fun i => ?_) hfin
  have := hKhalf_nn i
  nlinarith [this]

/-! ### `ricciAAArm`: the connection-difference-quadratic Ricci arm

`ricciAAKer` is a SINGLE arm which is itself quadratic in the connection
difference, so shifting its folded window is not sharp — the shift is sharp only
when every grid entry of the bound carries a factor.  The two arms have to be
exposed first.  These are the six pieces of the kernel; the split is the public
re-derivation of the `private` `aaKer_eq` of the read-only low-base action
module, and each piece is `permCoeff ⋆ (insertion ⋆ innerInsertion)` with both
insertions carrying exactly one derivative of the state. -/

private def aaP3201 : Equiv.Perm (Fin 4) := ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩
private def aaP2301 : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩
private def aaP3102 : Equiv.Perm (Fin 4) := ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩
private def aaP1302 : Equiv.Perm (Fin 4) := ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩
private def aaP1203 : Equiv.Perm (Fin 4) := ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩
private def aaP2103 : Equiv.Perm (Fin 4) := ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩
private def aaP102 : Equiv.Perm (Fin 3) := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
private def aaP120 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

/-- The two-arm core of a quadratic Ricci kernel piece, with the inner insertion
read through a slot permutation. -/
def aaCoreP (g₀ g₁ : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 4))
    (ρ' : Equiv.Perm (Fin 3)) : SmoothCcTensor g₀ 2 4 :=
  appCcRS (I := I) (M := M) g₀ 2 4 4 (permCoeff (I := I) (M := M) g₀ ρ)
    (appCcRS (I := I) (M := M) g₀ 2 3 4
      (connDiffContrInsertionField (I := I) g₀ g₁)
      (appCcRS (I := I) (M := M) g₀ 2 3 3 (permCoeff (I := I) (M := M) g₀ ρ')
        (connDiffContrInsertionInnerField (I := I) g₀ g₁)))

/-- The two-arm core of a quadratic Ricci kernel piece, with the inner insertion
read directly. -/
def aaCore (g₀ g₁ : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 2 4 :=
  appCcRS (I := I) (M := M) g₀ 2 4 4 (permCoeff (I := I) (M := M) g₀ ρ)
    (appCcRS (I := I) (M := M) g₀ 2 3 4
      (connDiffContrInsertionField (I := I) g₀ g₁)
      (connDiffContrInsertionInnerField (I := I) g₀ g₁))

/-- **Public two-arm split of the quadratic Ricci kernel.**

`ricciAAKer` is the sum of six slot-reindexed two-arm cores, each an insertion
against an inner insertion.  Public re-derivation of the `private` `aaKer_eq`;
this is what lets the base shift be applied per arm, which is the only way the
quadratic kernel enters the `range (i + 2)` budget. -/
theorem aaKerSplit (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciAAKer (I := I) (M := M) g₀ g₁ =
      aaCoreP (I := I) (M := M) g₀ g₁ aaP3201 aaP102 +
        reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (aaCoreP (I := I) (M := M) g₀ g₁ aaP2301 aaP102) innerCoreInPerm10 +
        aaCoreP (I := I) (M := M) g₀ g₁ aaP3102 aaP120 +
        reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (aaCore (I := I) (M := M) g₀ g₁ aaP1302) innerCoreInPerm10 +
        aaCore (I := I) (M := M) g₀ g₁ aaP1203 +
        reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (aaCoreP (I := I) (M := M) g₀ g₁ aaP2103 aaP120) innerCoreInPerm10 := rfl

set_option linter.unusedVariables false in
/-- **`ricciAAArm` in the capped currency.**

The four-trace cast costs no derivative of the state; the kernel is six copies
of a product of two arms each carrying one.  Shifting the two insertions
separately — which `aaKerSplit` is what makes possible — puts every factor at
level `i + 1` in the jets of `∇P`, and the folds preserve it. -/
theorem ricciAACap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P
          (ricciAAArm (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Cins, hCins_nn, hins⟩ := insertAtgw (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := rfns_iCG_connDiffSection_atgw_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kft, hKft_nn, hft⟩ := fourTrAtgw (I := I) (M := M) g₀ hδ₀
  choose S4 hS4_nn hS4 using
    (fun (ρ : Equiv.Perm (Fin 4)) (i : ℕ) =>
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
        (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ ρ)))
  choose S3 hS3_nn hS3 using
    (fun (ρ : Equiv.Perm (Fin 3)) (i : ℕ) =>
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
        (iteratedCovGrad (I := I) g₀ 3 3 i (permCoeff (I := I) (M := M) g₀ ρ)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set SP4 : ℕ → ℝ := fun i => ∑ ρ : Equiv.Perm (Fin 4), S4 ρ i with hSP4_def
  set SP3 : ℕ → ℝ := fun i => ∑ ρ : Equiv.Perm (Fin 3), S3 ρ i with hSP3_def
  have hSP4_nn : ∀ i, 0 ≤ SP4 i := fun i => Finset.sum_nonneg (fun ρ _ => hS4_nn ρ i)
  have hSP3_nn : ∀ i, 0 ≤ SP3 i := fun i => Finset.sum_nonneg (fun ρ _ => hS3_nn ρ i)
  set KIns : ℕ → ℝ := fun i => Cins i * shiftConst Λ (i + 1) with hKIns_def
  have hKIns_nn : ∀ i, 0 ≤ KIns i := fun i =>
    mul_nonneg (hCins_nn i) (shiftConst_nn hΛ0 _)
  set KInn : ℕ → ℝ := fun i => fr * (Ccd i * shiftConst Λ (i + 1)) with hKInn_def
  have hKInn_nn : ∀ i, 0 ≤ KInn i := fun i =>
    mul_nonneg hfr_nn (mul_nonneg (hCcd_nn i) (shiftConst_nn hΛ0 _))
  set KIC : ℕ → ℝ := foldConst (E := E) 0 0 SP3 KInn with hKIC_def
  have hKIC_nn : ∀ i, 0 ≤ KIC i := fun i =>
    foldConst_nn (u := 0) (v := 0) hSP3_nn hKInn_nn i
  set KMA : ℕ → ℝ := foldConst (E := E) 0 0 KIns KIC with hKMA_def
  have hKMA_nn : ∀ i, 0 ≤ KMA i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKIns_nn hKIC_nn i
  set KMB : ℕ → ℝ := foldConst (E := E) 0 0 KIns KInn with hKMB_def
  have hKMB_nn : ∀ i, 0 ≤ KMB i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKIns_nn hKInn_nn i
  set KA : ℕ → ℝ := foldConst (E := E) 0 0 SP4 KMA with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    foldConst_nn (u := 0) (v := 0) hSP4_nn hKMA_nn i
  set KB : ℕ → ℝ := foldConst (E := E) 0 0 SP4 KMB with hKB_def
  have hKB_nn : ∀ i, 0 ≤ KB i := fun i =>
    foldConst_nn (u := 0) (v := 0) hSP4_nn hKMB_nn i
  set KQ : ℕ → ℝ := fun i => KA i + KB i with hKQ_def
  have hKQ_nn : ∀ i, 0 ≤ KQ i := fun i => by
    have := hKA_nn i; have := hKB_nn i; simp only [hKQ_def]; linarith
  set KFT : ℕ → ℝ := fun i => Kft i * shiftConst Λ (i + 1) with hKFT_def
  have hKFT_nn : ∀ i, 0 ≤ KFT i := fun i =>
    mul_nonneg (hKft_nn i) (shiftConst_nn hΛ0 _)
  have hK94_nn : ∀ i, 0 ≤ 94 * KQ i := fun i => by have := hKQ_nn i; linarith
  refine ⟨foldConst (E := E) 0 0 KFT (fun i => 94 * KQ i),
    fun i => foldConst_nn (u := 0) (v := 0) hKFT_nn hK94_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  -- the two permutation coefficients, state-free
  have hP4 : ∀ ρ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) SP4 := by
    intro ρ
    refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
      (capOfBnd (I := I) (M := M) g₀ P _ (fun i => hS4_nn ρ i) (fun i x => hS4 ρ i x))
    exact Finset.single_le_sum (f := fun r => S4 r i)
      (fun r _ => hS4_nn r i) (Finset.mem_univ ρ)
  have hP3 : ∀ ρ : Equiv.Perm (Fin 3),
      HasCapWin (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) SP3 := by
    intro ρ
    refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
      (capOfBnd (I := I) (M := M) g₀ P _ (fun i => hS3_nn ρ i) (fun i x => hS3 ρ i x))
    exact Finset.single_le_sum (f := fun r => S3 r i)
      (fun r _ => hS3_nn r i) (Finset.mem_univ ρ)
  -- the two insertions, each carrying one derivative of the state
  have hIns : HasCapWin (I := I) (M := M) g₀ P
      (connDiffContrInsertionField (I := I) g₀ g₁) KIns :=
    capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCins_nn
      (fun l y => hins g₁ P htie hδ_le hδ0 hδ l y)
  have hInn : HasCapWin (I := I) (M := M) g₀ P
      (connDiffContrInsertionInnerField (I := I) g₀ g₁) KInn := by
    have hcdcap : HasCapWin (I := I) (M := M) g₀ P
        (connDiffSection (I := I) g₁ g₀)
        (fun i => Ccd i * shiftConst Λ (i + 1)) :=
      capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCcd_nn
        (fun l y => hcd g₁ P htie hδ_le hδ0 hδ l y)
    refine capCongr (I := I) (M := M) g₀ P
      (connDiffContrInsertionInnerField_eq_reindex_slotExtend (I := I) (M := M) g₀ g₁) ?_
    exact capReindex (I := I) (M := M) g₀ P innerCoreInPerm10
      (capSlotExt (I := I) (M := M) g₀ P hcdcap)
  -- the two shapes
  have hShapeA : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasCapWin (I := I) (M := M) g₀ P (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') KA := by
    intro ρ ρ'
    exact capApp (I := I) (M := M) g₀ P _ _ hSP4_nn hKMA_nn (hP4 ρ)
      (capApp (I := I) (M := M) g₀ P _ _ hKIns_nn hKIC_nn hIns
        (capApp (I := I) (M := M) g₀ P _ _ hSP3_nn hKInn_nn (hP3 ρ') hInn))
  have hShapeB : ∀ ρ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) KB := by
    intro ρ
    exact capApp (I := I) (M := M) g₀ P _ _ hSP4_nn hKMB_nn (hP4 ρ)
      (capApp (I := I) (M := M) g₀ P _ _ hKIns_nn hKInn_nn hIns hInn)
  have hA' : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasCapWin (I := I) (M := M) g₀ P (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') KQ :=
    fun ρ ρ' => capMono (I := I) (M := M) g₀ P
      (fun i => by have := hKB_nn i; simp only [hKQ_def]; linarith) (hShapeA ρ ρ')
  have hB' : ∀ ρ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) KQ :=
    fun ρ => capMono (I := I) (M := M) g₀ P
      (fun i => by have := hKA_nn i; simp only [hKQ_def]; linarith) (hShapeB ρ)
  -- the six pieces, summed
  have hKer : HasCapWin (I := I) (M := M) g₀ P
      (ricciAAKer (I := I) (M := M) g₀ g₁) (fun i => 94 * KQ i) := by
    refine capCongr (I := I) (M := M) g₀ P
      (aaKerSplit (I := I) (M := M) g₀ g₁) ?_
    have hsum := capAdd (I := I) (M := M) g₀ P
      (capAdd (I := I) (M := M) g₀ P
        (capAdd (I := I) (M := M) g₀ P
          (capAdd (I := I) (M := M) g₀ P
            (capAdd (I := I) (M := M) g₀ P (hA' aaP3201 aaP102)
              (capReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' aaP2301 aaP102)))
            (hA' aaP3102 aaP120))
          (capReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hB' aaP1302)))
        (hB' aaP1203))
      (capReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' aaP2103 aaP120))
    refine capMono (I := I) (M := M) g₀ P (fun i => ?_) hsum
    exact le_of_eq (by ring)
  -- the four-trace cast, offset `+1`, weakened and shifted
  have hFT : HasCapWin (I := I) (M := M) g₀ P
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁) KFT := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hKft_nn (fun n y => ?_)
    have hbnn := gridBase_nn (I := I) (M := M) g₀ P y
    refine le_trans (hft g₁ P htie hδ_le hδ0 hδ n y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKft_nn n)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _ hbnn (by omega)
  exact capApp (I := I) (M := M) g₀ P _ _ hKFT_nn hK94_nn hFT hKer

end DifferentialGeometry.Integral.Connection

end
