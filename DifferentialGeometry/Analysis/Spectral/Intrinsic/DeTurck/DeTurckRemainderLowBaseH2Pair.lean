import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2Cov

/-!
# The `H²` pairwise estimate for the zero-order low-base coefficient

`DeTurckRemainderLowBaseLip` produces the pairwise modulus for the transparent
zero-arm self-action only at the `H¹` level, and with a `(1+A+A²)⁴` envelope in
the third-jet size `A`.  Every downstream consumer of the low-regularity
Ricci--DeTurck fixed point (the third arm of the tame three-arm estimate, and
`MemLp A1 2` in time) admits only a factor which is *linear* in the `H³` size.

This module records the `H²` level of that chain in the critical orientation
`(B0 R · D3 + B1 R · D2 + B1 R · A · D2 + B2 R · N)²`, i.e. linear in the
third-jet size `A` and linear in the third-jet difference `D3`, matching the
corrected `UNIF_N_PRO_RULING` second-order arms at the `a = 2` rung.

The admissible modulus class is
`(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²`
with `A` the third-jet size of either state, `A4` the fourth-jet size of either
state (allowed **linearly**, as an endpoint tame factor), and `D2, D3, D4, N`
the second/third/fourth-jet and spectral differences.  Every difference slot
carries either an `A`-degree `≤ 1` or an `A4`-degree `≤ 1` coefficient; `A4²`,
`D4·A4` and any `A`-degree `≥ 2` against a difference are excluded.

Classes 4 and 5 are proved here; class 3 (`vbH2Pair`) is proved in the
sibling module `DeTurckRemainderLowBaseH2VB`, which also carries the shared
`H²` jet algebra (`jetInterp3`, `appH2`, `amixScalar`, the slot/reindex/trace
transfer layer), and class 2 (`lieCovH2Pair`) in
`DeTurckRemainderLowBaseH2Cov`.  Class 1 still carries a passenger which is
quadratic in `A` (`ricciAAKer`) whose re-pairing needs in addition a *sharper*
`aaKer_bdd_h2`: the existing bound is lossy by `A²` in the norm, and re-pairing
it as it stands produces the forbidden `A4²`.  Class 1 is therefore stated here
in the ruling's orientation and left with `sorry`; see the same-name `.md`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ### The five-class telescope at fixed path parameter

`selfLow_parts` and `selfLow_sub_parts` are private to
`DeTurckRemainderLowBaseLip`; both are level-agnostic identities and are
re-established here from the public producers. -/

private theorem selfParts
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            LowBaseInternal.ricciGoodLow
              (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
            edgeLiePairFam (I := I) (M := M) g T hδ hδZ
              lieRefoldQ lieRefoldEps s)) +
        lc0VB (I := I) (M := M) g gm) +
        lc0AMix (I := I) (M := M) g gm g) +
        lc0Riem (I := I) (M := M) g gm := by
  rw [LowBaseInternal.selfLow_good
    (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let Q := edgeLiePairFam (I := I) (M := M) g T hδ hδZ
    lieRefoldQ lieRefoldEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
            lieCorr0Field (I := I) (M := M) g gm g - Q =
        (deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g) +
          lc0Riem (I := I) (M := M) g gm) := by
    rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
    rw [← tail_base_split (I := I) (M := M) g gm g]
    abel
  calc
    _ = (-2 : ℝ) •
          LowBaseInternal.ricciGoodLow
            (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorr0Field (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) •
          LowBaseInternal.ricciGoodLow
            (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g) +
          lc0Riem (I := I) (M := M) g gm)) := by
      rw [hlie]
    _ = _ := by
      simp only [sub_self, zero_add, add_zero]
      abel

private theorem selfSubParts
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδT hδZ s -
      LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g U hδU hδZ s =
      (((((-2 : ℝ) •
            (LowBaseInternal.ricciGoodLow (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hδT hδZ s) (s • T) -
              LowBaseInternal.ricciGoodLow (I := I) (M := M) g
                (realizedFam (I := I) g U 0 hδU hδZ s) (s • U)) +
          ((deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g T hδT hδZ
              lieRefoldQ lieRefoldEps s) -
          (deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g U hδU hδZ
              lieRefoldQ lieRefoldEps s))) +
        (lc0VB (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) -
          lc0VB (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s))) +
        (lc0AMix (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g -
          lc0AMix (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g)) +
        (lc0Riem (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) -
          lc0Riem (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s))) := by
  rw [selfParts (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    selfParts (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  dsimp only
  module


/-! ### A tame `H³` product used by the Ricci class

The ordinary `H³` algebra estimate puts three derivatives on both factors.
For the inverse-metric resolvent telescope below that would create a spurious
quadratic high-state factor.  At the fixed three-dimensional rung we instead
differentiate the application once and use the already proved `H²` algebra
estimate on the two Leibniz terms. -/

private theorem gradSq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

private theorem gradH2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 3 S := by
  have h0 := gradSq (I := I) (M := M) g r s 0 S
  have h1 := gradSq (I := I) (M := M) g r s 1 S
  have h2 := gradSq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖S‖]

private theorem jet3Grad
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 3 S ≤
      lowJetSq (I := I) (M := M) g 2 S +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g r s S) := by
  have h0 := gradSq (I := I) (M := M) g r s 0 S
  have h1 := gradSq (I := I) (M := M) g r s 1 S
  have h2 := gradSq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg
    ‖iteratedCovGrad (I := I) g r s 1 S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 2 S‖]

omit [BoundarylessManifold I M] in
private theorem h3TameSc
    {c0 c1 c2 fr X Y : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hfr : 0 ≤ fr) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    c0 * X + 2 * (c1 * X + c2 * fr * Y) ≤
      (c0 + 2 * (c1 + c2 * fr)) * (X + Y) := by
  have h0Y : 0 ≤ c0 * Y := mul_nonneg hc0 hY
  have h1Y : 0 ≤ 2 * c1 * Y :=
    mul_nonneg (mul_nonneg (by norm_num) hc1) hY
  have h2X : 0 ≤ 2 * c2 * fr * X :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc2) hfr) hX
  nlinarith only [h0Y, h1Y, h2X]

set_option maxHeartbeats 1600000 in
private theorem appH3Tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * (lowJetSq (I := I) (M := M) g 3 Φ *
              lowJetSq (I := I) (M := M) g 2 W +
            lowJetSq (I := I) (M := M) g 2 Φ *
              lowJetSq (I := I) (M := M) g 3 W) := by
  obtain ⟨C0, hC0, h0⟩ :=
    appH2 (I := I) (M := M) hDim g p r c
  obtain ⟨C1, hC1, h1⟩ :=
    appH2 (I := I) (M := M) hDim g p r (c + 1)
  obtain ⟨C2, hC2, h2⟩ :=
    appH2 (I := I) (M := M) hDim g p (r + 1) (c + 1)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := C0 + 2 * (C1 + C2 * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0
      (mul_nonneg (by norm_num) (add_nonneg hC1 (mul_nonneg hC2 hfr)))
  refine ⟨C, hC, ?_⟩
  intro Φ W
  let Y : SmoothCcTensor g p c :=
    appCcRS (I := I) (M := M) g p r c Φ W
  let A : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
  let B : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g p r W)
  let X : ℝ := lowJetSq (I := I) (M := M) g 3 Φ *
    lowJetSq (I := I) (M := M) g 2 W
  let Z : ℝ := lowJetSq (I := I) (M := M) g 2 Φ *
    lowJetSq (I := I) (M := M) g 3 W
  have hΦ23 := jetMono (I := I) (M := M) g
    (by omega : 2 ≤ 3) Φ
  have hΦ2 := jetNn (I := I) (M := M) (m := 2) g Φ
  have hW2 := jetNn (I := I) (M := M) (m := 2) g W
  have hΦ3 := jetNn (I := I) (M := M) (m := 3) g Φ
  have hW3 := jetNn (I := I) (M := M) (m := 3) g W
  have hX : 0 ≤ X := mul_nonneg hΦ3 hW2
  have hZ : 0 ≤ Z := mul_nonneg hΦ2 hW3
  have hY2 :
      lowJetSq (I := I) (M := M) g 2 Y ≤ C0 * X := by
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          C0 * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [Y] using h0 Φ W
      _ ≤ C0 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦ23 hC0) hW2
      _ = C0 * X := by simp only [X]; ring
  have hA2 :
      lowJetSq (I := I) (M := M) g 2 A ≤ C1 * X := by
    calc
      lowJetSq (I := I) (M := M) g 2 A ≤
          C1 * lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [A] using
          h1 (covGrad (I := I) (M := M) g r c Φ) W
      _ ≤ C1 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (gradH2 (I := I) (M := M) g Φ) hC1) hW2
      _ = C1 * X := by simp only [X]; ring
  have hB2 :
      lowJetSq (I := I) (M := M) g 2 B ≤ C2 * fr * Z := by
    calc
      lowJetSq (I := I) (M := M) g 2 B ≤
          C2 * lowJetSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        simpa only [B] using
          h2 (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g p r W)
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [fr] using
              slotH2 (I := I) (M := M) g r c Φ) hC2)
          (jetNn (I := I) (M := M) g
            (covGrad (I := I) (M := M) g p r W))
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left
          (gradH2 (I := I) (M := M) g W)
          (mul_nonneg hC2 (mul_nonneg hfr hΦ2))
      _ = C2 * fr * Z := by simp only [Z]; ring
  have hgrad :
      lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) ≤
        2 * (C1 * X + C2 * fr * Z) := by
    rw [show covGrad (I := I) (M := M) g p c Y = A + B by
      simpa only [Y, A, B] using
        covGrad_appCcRS_eq (I := I) (M := M) g p r c Φ W]
    exact (jetAdd (I := I) (M := M) g 2 A B).trans
      (mul_le_mul_of_nonneg_left (add_le_add hA2 hB2) (by norm_num))
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) =
      lowJetSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ lowJetSq (I := I) (M := M) g 2 Y +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) :=
      jet3Grad (I := I) (M := M) g Y
    _ ≤ C0 * X + 2 * (C1 * X + C2 * fr * Z) :=
      add_le_add hY2 hgrad
    _ ≤ C * (X + Z) := by
      simpa only [C] using h3TameSc hC0 hC1 hC2 hfr hX hZ
    _ = C * (lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W +
          lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 3 W) := by
      simp only [X, Z]


private theorem endoSlotL2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endoSlotJet
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endoSlotL2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem sharpSlot0
    (g gm : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g gm =
      slotInsertEndoCc (I := I) (M := M) g 0
        (fullRaisedEndoField (I := I) (M := M) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g gm x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g gm x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g gm).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) gm x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (gInvRaisedEndo (I := I) g gm x w) =
      gm.inner x (inverseMetricSharpFib (I := I) gm x om)
        (gInvRaisedEndo (I := I) g gm x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) gm x om
      (gInvRaisedEndo (I := I) g gm x w)).symm]
  rw [show gInvRaisedEndo (I := I) g gm x w =
      inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w) from by
    rw [gInvRaisedEndo_apply]]
  rw [gm.symm x (inverseMetricSharpFib (I := I) gm x om)
    (inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) gm x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) gm x om)]

set_option linter.unusedVariables false in
private theorem sharpH3
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (sharpFlatEndoCc (I := I) g gm) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 3, hFlow0 3, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [lowJetSq, Nat.reduceAdd] using
    (hFlow gm P htie hδ_le hδ0 hδ hsup).2 3 (by omega)

set_option linter.unusedVariables false in
private theorem fullSlotH3
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharpH3 (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
      fr * lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g gm)) := by
      simpa only [fr, pow_one] using
        endoSlotJet (I := I) (M := M) g 1 3
          (fullRaisedEndoField (I := I) (M := M) g gm)
    _ = fr * lowJetSq (I := I) (M := M) g 3
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharpSlot0 (I := I) (M := M) g gm]
    _ ≤ fr * (K₀ *
        (1 + lowJetSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private theorem perturbJet
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    lowJetSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g 1
          (symmRaiseEndo (I := I) (M := M) g D)) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g m D := by
  have h0 :
      lowJetSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g D)) =
        lowJetSq (I := I) (M := M) g m D := by
    rw [insert_symmRaise_eq (I := I) (M := M) g D]
    calc
      lowJetSq (I := I) (M := M) g m
          (cometricRaiseSlot0Field (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D))) =
        lowJetSq (I := I) (M := M) g m
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D)) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D)) q]
      _ = lowJetSq (I := I) (M := M) g m
          (symmS (I := I) (M := M) g D) := by
        unfold lowJetSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D) q]
      _ = lowJetSq (I := I) (M := M) g m D := by rw [hD]
  have hslot := endoSlotJet (I := I) (M := M) g 1 m
    (symmRaiseEndo (I := I) (M := M) g D)
  rw [h0] at hslot
  simpa only [pow_one] using hslot

omit [BoundarylessManifold I M] in
private theorem jetNeg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (-S) =
      lowJetSq (I := I) (M := M) g m S := by
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    jetSmul (I := I) (M := M) g m (-1 : ℝ) S

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
private theorem fullPairH3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT) -
            slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gU)) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bh, hBh, hbdd⟩ :=
    fullSlot_bdd_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kh, hKh, hh3⟩ :=
    fullSlotH3 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C2, hC2, happ2⟩ :=
    appH2 (I := I) (M := M) hDim g 2 2 2
  obtain ⟨C3, hC3, happ3⟩ :=
    appH3Tame (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  let Z3 : ℝ → ℝ := fun R =>
    C3 ^ 2 * fr * (Bh R) ^ 4
  let Z2 : ℝ → ℝ := fun R =>
    C3 * Kh * fr * (Bh R) ^ 2 * (C2 + C3)
  let Z : ℝ → ℝ := fun R => Z3 R + Z2 R
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ3 : ∀ R : ℝ, 0 ≤ Z3 R := by
    intro R
    dsimp only [Z3]
    positivity
  have hZ2 : ∀ R : ℝ, 0 ≤ Z2 R := by
    intro R
    dsimp only [Z2]
    positivity
  have hZ : ∀ R : ℝ, 0 ≤ Z R := by
    intro R
    exact add_nonneg (hZ3 R) (hZ2 R)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let LT : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gT)
  let LU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gU)
  let P : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
  let X : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2 P LT
  let Y : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2 LU X
  let H3 : ℝ := Kh * (1 + A ^ 2)
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub,
      symmS_eq_self_of_ccTensorBilin_symm
        (I := I) (M := M) g T hT,
      symmS_eq_self_of_ccTensorBilin_symm
        (I := I) (M := M) g U hU]
  have hLT2 :
      lowJetSq (I := I) (M := M) g 2 LT ≤ (Bh R) ^ 2 := by
    simpa only [LT] using
      hbdd gT T hT hTtie hδT_le hδT0 hδT R hR hT2
  have hLU2 :
      lowJetSq (I := I) (M := M) g 2 LU ≤ (Bh R) ^ 2 := by
    simpa only [LU] using
      hbdd gU U hU hUtie hδU_le hδU0 hδU R hR hU2
  have hLT3 :
      lowJetSq (I := I) (M := M) g 3 LT ≤ H3 := by
    calc
      lowJetSq (I := I) (M := M) g 3 LT ≤
          Kh * (1 + lowJetSq (I := I) (M := M) g 3 T) := by
        simpa only [LT] using
          hh3 gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ H3 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hKh
  have hLU3 :
      lowJetSq (I := I) (M := M) g 3 LU ≤ H3 := by
    calc
      lowJetSq (I := I) (M := M) g 3 LU ≤
          Kh * (1 + lowJetSq (I := I) (M := M) g 3 U) := by
        simpa only [LU] using
          hh3 gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ H3 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hKh
  have hP2 :
      lowJetSq (I := I) (M := M) g 2 P ≤ fr * D2 ^ 2 := by
    refine (by
      simpa only [P, fr] using
        perturbJet (I := I) (M := M) g 2 (T - U) hsymm).trans ?_
    exact mul_le_mul_of_nonneg_left hTU2 hfr
  have hP3 :
      lowJetSq (I := I) (M := M) g 3 P ≤ fr * D3 ^ 2 := by
    refine (by
      simpa only [P, fr] using
        perturbJet (I := I) (M := M) g 3 (T - U) hsymm).trans ?_
    exact mul_le_mul_of_nonneg_left hTU3 hfr
  have hH3 : 0 ≤ H3 := mul_nonneg hKh (by positivity)
  have hX2 :
      lowJetSq (I := I) (M := M) g 2 X ≤
        C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 X ≤
          C2 * lowJetSq (I := I) (M := M) g 2 P *
            lowJetSq (I := I) (M := M) g 2 LT := by
        simpa only [X] using happ2 P LT
      _ ≤ C2 * (fr * D2 ^ 2) *
            lowJetSq (I := I) (M := M) g 2 LT := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP2 hC2)
          (jetNn (I := I) (M := M) (m := 2) g LT)
      _ ≤ C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hLT2
          (mul_nonneg hC2 (mul_nonneg hfr (sq_nonneg D2)))
  have hX3 :
      lowJetSq (I := I) (M := M) g 3 X ≤
        C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 +
          (fr * D2 ^ 2) * H3) := by
    calc
      lowJetSq (I := I) (M := M) g 3 X ≤
          C3 * (lowJetSq (I := I) (M := M) g 3 P *
              lowJetSq (I := I) (M := M) g 2 LT +
            lowJetSq (I := I) (M := M) g 2 P *
              lowJetSq (I := I) (M := M) g 3 LT) := by
        simpa only [X] using happ3 P LT
      _ ≤ C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 +
          (fr * D2 ^ 2) * H3) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hP3 hLT2
            (jetNn (I := I) (M := M) (m := 2) g LT)
            (mul_nonneg hfr (sq_nonneg D3)))
          (mul_le_mul hP2 hLT3
            (jetNn (I := I) (M := M) (m := 3) g LT)
            (mul_nonneg hfr (sq_nonneg D2)))
  have hY3 :
      lowJetSq (I := I) (M := M) g 3 Y ≤
        C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 +
              (fr * D2 ^ 2) * H3))) := by
    calc
      lowJetSq (I := I) (M := M) g 3 Y ≤
          C3 * (lowJetSq (I := I) (M := M) g 3 LU *
              lowJetSq (I := I) (M := M) g 2 X +
            lowJetSq (I := I) (M := M) g 2 LU *
              lowJetSq (I := I) (M := M) g 3 X) := by
        simpa only [Y] using happ3 LU X
      _ ≤ C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 +
              (fr * D2 ^ 2) * H3))) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hLU3 hX2
            (jetNn (I := I) (M := M) (m := 2) g X) hH3)
          (mul_le_mul hLU2 hX3
            (jetNn (I := I) (M := M) (m := 3) g X)
            (sq_nonneg (Bh R)))
  have hYfold :
      lowJetSq (I := I) (M := M) g 3 Y ≤
        Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
    have heq :
        C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 +
              (fr * D2 ^ 2) * H3))) =
        Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) := by
      simp only [H3, Z3, Z2]
      ring
    rw [heq] at hY3
    refine hY3.trans ?_
    calc
      Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) ≤
          Z3 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) +
            Z2 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right
              (mul_nonneg (by positivity) (sq_nonneg D2)))
            (hZ3 R))
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (sq_nonneg D3))
            (hZ2 R))
      _ = Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        simp only [Z]
        ring
  have hlin :
      D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 ≤
        (D3 + D2 + A * D2) ^ 2 := by
    calc
      D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 =
          (D3 ^ 2 + D2 ^ 2) + (A * D2) ^ 2 := by ring
      _ ≤ (D3 + D2) ^ 2 + (A * D2) ^ 2 := by
        exact add_le_add_right (sqAdd2 hD3 hD2) _
      _ ≤ (D3 + D2 + A * D2) ^ 2 :=
        sqAdd2 (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hBsq : (B R) ^ 2 = Z R := by
    simpa only [B] using Real.sq_sqrt (hZ R)
  have hslot :
      LT - LU =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    have hdiff :
        fullRaisedEndoField (I := I) (M := M) g gT -
            fullRaisedEndoField (I := I) (M := M) g gU =
          gInvDiffRaisedEndoField (I := I) g gT -
            gInvDiffRaisedEndoField (I := I) g gU := by
      apply ContMDiffSection.ext
      intro x
      rw [ContMDiffSection.coe_sub, Pi.sub_apply,
        ContMDiffSection.coe_sub, Pi.sub_apply]
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        fullRaisedEndoField_apply, fullRaisedEndoField_apply,
        show gInvDiffRaisedEndoField (I := I) g gT x =
          gInvDiffRaisedEndo (I := I) g gT x from rfl,
        show gInvDiffRaisedEndoField (I := I) g gU x =
          gInvDiffRaisedEndo (I := I) g gU x from rfl,
        gInvRaisedEndo_eq_diff_add_id (I := I) g gT x v,
        gInvRaisedEndo_eq_diff_add_id (I := I) g gU x v]
      abel
    simp only [LT, LU]
    rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU,
      ← slotInsertEndoCc_sub, ← slotInsertEndoCc_sub, hdiff]
  rw [show
      slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gT) -
          slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU) =
        LT - LU from rfl,
    hslot,
    invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    jetNeg (I := I) (M := M) g 3]
  have hYmain :
      lowJetSq (I := I) (M := M) g 3 Y ≤
        Z R * (D3 + D2 + A * D2) ^ 2 :=
    hYfold.trans (mul_le_mul_of_nonneg_left hlin (hZ R))
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU))
          (appCcRS (I := I) (M := M) g 2 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))
            (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT)))) =
      lowJetSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ Z R * (D3 + D2 + A * D2) ^ 2 := hYmain
    _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
      rw [mul_pow, hBsq]


/-! ### The five classes at the `H²` level

Each class lemma bounds one summand of `selfSubParts` in `lowJetSq 2` with the
admissible modulus of the corrected ruling. -/
set_option linter.unusedVariables false in
/-- **Class 1** — the symmetrized first-order Ricci coefficient
`ricciGoodLow` along the realized family.

Remaining sub-steps (mirror `good_pair_h1`, Lip:9611, at `J2`):
1. `aaKer_bdd_h2_sharp`: the existing `aaKer_bdd_h2` (Lip:8451) envelope
   `B R·(1+A+A²)⁴` is lossy by `A²` in the norm.  Rebuild it as
   `J2 (ricciAAKer) ≤ (B' R·(1+A)²)²` by bounding each block with
   `appRS_h2_h2_h2` against the two *sharp* connection factors
   (`mcd_h2_bdd`-shaped `(B R(1+A))²`, `wXi_self_tame`-shaped `(B R·A)²`).
2. `aaKer_pair_h2` (H² sibling of `aaKer_pair_h1`, Lip:8654) and
   `dagLow_pair_h2` (of `dagLow_pair_h1`, Lip:8045).
3. Re-pair: `Δfourtrace ⊗ aaKer` gives `N·(1+A)²`; instantiate the sharp
   producer at `A' := √(C·R·A4)` — legitimate by `jetInterp3` — and use
   `√(R·A4) ≤ (R + A4)/2`, landing in the `A4·N` arm.  `ΔaaKer` is
   `(1+A)·D3`-shaped, i.e. the first arm.
4. Publicize from Lip: `fourtrace_bdd_h2`, `fourtrace_pair_h2`,
   `aaKer_bdd_h2`, `dagLow_bdd_h2`, `refold_h2_lip`, `inputSymm_h1`. -/
private theorem goodH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (LowBaseInternal.ricciGoodLow (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) (s • T) -
            LowBaseInternal.ricciGoodLow (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) (s • U)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
  sorry

set_option maxHeartbeats 6400000 in
set_option linter.unusedVariables false in
/-- **Class 4, one half.**  The unsymmetrized five-factor half of `lc0AMix`
obeys the admissible second-order modulus.

The chain is `Tr₂ · Tr₄ · Ext³mcd · Tr₃ · Ext²mcd`, so it carries *two*
connection-difference factors.  Each of them is bounded by `mcd_h2_bdd` in the
form `(Bm R (1+A))`, which against a difference would give the inadmissible
`A`-degree `2`.  Both are therefore re-paired through `jetInterp3`: the third
jet of the realized perturbation is re-read as `√(C·R·A4)`, so that
`(1+√(C R A4))⁴ ≤ 8(1 + (C R A4)²)` is `A4`-linear in the square root scale.
The `A·D2` slot of `mcd_pair_h2` is fed with `D2 := D3` (legitimate since
`J2 (T-U) ≤ J3 (T-U)`), turning it into the admissible `A4·D3` arm. -/
private theorem amixHalfH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (σlast : Equiv.Perm (Fin 4)),
      lowJetSq (I := I) (M := M) g 2
          (lc0AMixHalfRF (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g σlast -
            lc0AMixHalfRF (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g σlast) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca1, hCa1, happ1⟩ := appH2 (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Ca2, hCa2, happ2⟩ := appH2 (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ca3, hCa3, happ3⟩ := appH2 (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca4, hCa4, happ4⟩ := appH2 (I := I) (M := M) hDim g 2 5 3
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt3, Ct3, hρt3, hCt3, htp3⟩ :=
    LowBaseInternal.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt4, Ct4, hρt4, hCt4, htp4⟩ :=
    LowBaseInternal.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb3, Bt3, hρb3, hBt3, htb3⟩ :=
    LowBaseInternal.trace3_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb4, Bt4, hρb4, hBt4, htb4⟩ :=
    LowBaseInternal.trace4_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    LowBaseInternal.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    LowBaseInternal.mcd_h2_bdd (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cip, hCip, hinterp⟩ := jetInterp3 (I := I) (M := M) g 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  have hfr3 : (0 : ℝ) ≤ fr ^ 3 := pow_nonneg hfr 3
  set ρ : ℝ := min (min ρt2 (min ρt3 ρt4)) (min ρb2 (min ρb3 ρb4))
    with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt2 (lt_min hρt3 hρt4))
      (lt_min hρb2 (lt_min hρb3 hρb4))
  let S5b : ℝ → ℝ := fun R => fr ^ 2 * (Bm R) ^ 2
  let E3b : ℝ → ℝ := fun R => fr ^ 3 * (Bm R) ^ 2
  let S4b : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * S5b R
  let S3b : ℝ → ℝ := fun R => Ca3 * E3b R * S4b R
  let S2b : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * S3b R
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let D5c : ℝ → ℝ := fun R => fr ^ 2 * M5 R
  let E3d : ℝ → ℝ := fun R => fr ^ 3 * M5 R
  let K4 : ℝ → ℝ := fun R => Ca4 * Ct3 ^ 2 * S5b R
  let K5 : ℝ → ℝ := fun R => Ca4 * Bt3 ^ 2 * D5c R
  let K3 : ℝ → ℝ := fun R => Ca3 * E3d R * S4b R
  let K34 : ℝ → ℝ := fun R => Ca3 * E3b R * (2 * (K4 R + K5 R))
  let K2 : ℝ → ℝ := fun R => Ca2 * Ct4 ^ 2 * S3b R
  let K23 : ℝ → ℝ := fun R => Ca2 * Bt4 ^ 2 * (2 * (K3 R + K34 R))
  let K1 : ℝ → ℝ := fun R => Ca1 * Ct2 ^ 2 * S2b R
  let K12 : ℝ → ℝ := fun R => Ca1 * Bt2 ^ 2 * (2 * (K2 R + K23 R))
  let Bh : ℝ → ℝ := fun R => 2 * (K1 R + K12 R)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hS5b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S5b R := fun R hR =>
    mul_nonneg hfr2 (sq_nonneg _)
  have hE3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3b R := fun R hR =>
    mul_nonneg hfr3 (sq_nonneg _)
  have hS4b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hS3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR)) (hS4b R hR)
  have hS2b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simp only [M5]
    linarith
  have hD5c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D5c R := fun R hR =>
    mul_nonneg hfr2 (hM5 R hR)
  have hE3d : ∀ R : ℝ, 0 ≤ R → 0 ≤ E3d R := fun R hR =>
    mul_nonneg hfr3 (hM5 R hR)
  have hK4 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K4 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hK5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K5 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hD5c R hR)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3d R hR)) (hS4b R hR)
  have hK34 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K34 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (hE3b R hR))
      (by
        have := hK4 R hR
        have := hK5 R hR
        linarith)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hK23 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K23 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _))
      (by
        have := hK3 R hR
        have := hK34 R hR
        linarith)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _)) (hS2b R hR)
  have hK12 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K12 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _))
      (by
        have := hK2 R hR
        have := hK23 R hR
        linarith)
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    have := hK1 R hR
    have := hK12 R hR
    simp only [Bh]
    linarith
  refine ⟨ρ, B0, B1, hρ0,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs σlast
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP4 : lowJetSq (I := I) (M := M) g 4 P ≤ A4 ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 4) g T) hs2).trans hT4
  have hQ4 : lowJetSq (I := I) (M := M) g 4 Q ≤ A4 ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 4) g U) hs2).trans hU4
  have hPQ3 : lowJetSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (jetMono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  -- the interpolated third-jet size of the two states
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hP3i : lowJetSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp P R A4 hR hA4 hP2 hP4
  have hQ3i : lowJetSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp Q R A4 hR hA4 hQ2 hQ4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg N]
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg D3]
  -- the two connection-difference factors
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmU g with hmU
  have hmbT : lowJetSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmbU : lowJetSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmpd : lowJetSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    have hstep : (B0m R * D3 + B1m R * D3 + B1m R * a * D3) ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 +
          2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) := by
      have hre : B0m R * D3 + B1m R * D3 + B1m R * a * D3 =
          (B0m R + B1m R) * D3 + B1m R * a * D3 := by ring
      rw [hre]
      refine (sqTwo ((B0m R + B1m R) * D3) (B1m R * a * D3)).trans (le_of_eq ?_)
      ring
    refine hstep.trans ?_
    have hA2D : a ^ 2 * D3 ^ 2 ≤ pl2 * u := by
      have h1 : a ^ 2 * D3 ^ 2 ≤ pl2 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
      have h2 : pl2 * D3 ^ 2 ≤ pl2 * u :=
        mul_le_mul_of_nonneg_left hD3le hpl20
      linarith
    have e1 : 2 * (B0m R + B1m R) ^ 2 * D3 ^ 2 ≤
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD3u (by positivity)
    have e2 : 2 * (B1m R) ^ 2 * (a ^ 2 * D3 ^ 2) ≤
        2 * (B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    have hM5eq : M5 R * (pl2 * u) =
        2 * (B0m R + B1m R) ^ 2 * (pl2 * u) +
          2 * (B1m R) ^ 2 * (pl2 * u) := by
      simp only [M5]
      ring
    rw [hM5eq]
    linarith
  -- trace moduli (ρ-cascade)
  have hρc : ρ ≤ ρt2 ∧ ρ ≤ ρt3 ∧ ρ ≤ ρt4 ∧ ρ ≤ ρb2 ∧ ρ ≤ ρb3 ∧
      ρ ≤ ρb4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.1
  have htp3' := htrp 3 Ct3 ρt3 htp3 hCt3 hρc.2.1
  have htp4' := htrp 4 Ct4 ρt4 htp4 hCt4 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2.1
  have htb3' := htrb 3 Bt3 ρb3 htb3 hρc.2.2.2.2.1
  have htb4' := htrb 4 Bt4 ρb4 htb4 hρc.2.2.2.2.2
  -- stack abbreviations
  set S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdT with hS5Tdef
  set S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdU with hS5Udef
  set S4T : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3
      (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ) S5T
    with hS4Tdef
  set S4U : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3
      (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) S5U
    with hS4Udef
  set E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdT with hE3Tdef
  set E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdU with hE3Udef
  set S3T : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3T S4T with hS3Tdef
  set S3U : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3U S4U with hS3Udef
  set S2T : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4
      (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1) S3T
    with hS2Tdef
  set S2U : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4
      (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) S3U
    with hS2Udef
  have hHalfT : lc0AMixHalfRF (I := I) (M := M) g gmT g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmT 2 σlast) S2T := rfl
  have hHalfU : lc0AMixHalfRF (I := I) (M := M) g gmU g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2U := rfl
  -- bounded chain, T-state
  have hS5T2 : lowJetSq (I := I) (M := M) g 2 S5T ≤ S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        slotH2 (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdT) :=
        mul_le_mul_of_nonneg_left
          (slotH2 (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * pl2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmbT hfr) hfr
      _ = S5b R * pl2 := by
        simp only [S5b]
        ring
  have hE3T2 : lowJetSq (I := I) (M := M) g 2 E3T ≤ E3b R * pl2 := by
    rw [hE3Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdT))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        slotH2 (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (slotH2 (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slotH2 (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbT hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hE3U2 : lowJetSq (I := I) (M := M) g 2 E3U ≤ E3b R * pl2 := by
    rw [hE3Udef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdU))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        slotH2 (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (slotH2 (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slotH2 (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbU hfr) hfr) hfr
      _ = E3b R * pl2 := by
        simp only [E3b]
        ring
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hS4T2 : lowJetSq (I := I) (M := M) g 2 S4T ≤ S4b R * pl2 := by
    rw [hS4Tdef]
    refine (happ4 _ S5T).trans ?_
    have htr := (trJet (I := I) (M := M) g gmT 3 2
      LieCorr0Core.lieCorr0AMixPermQ).le.trans htb3'.1
    calc
      Ca4 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ) *
        lowJetSq (I := I) (M := M) g 2 S5T ≤
        Ca4 * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4) hS5T2
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa4 (sq_nonneg _))
      _ = S4b R * pl2 := by
        simp only [S4b]
        ring
  have hS3T2 : lowJetSq (I := I) (M := M) g 2 S3T ≤
      S3b R * (pl2 * pl2) := by
    rw [hS3Tdef]
    refine (happ3 E3T S4T).trans ?_
    calc
      Ca3 * lowJetSq (I := I) (M := M) g 2 E3T *
        lowJetSq (I := I) (M := M) g 2 S4T ≤
        Ca3 * (E3b R * pl2) * (S4b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hE3T2 hCa3) hS4T2
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa3 (mul_nonneg (hE3b R hR) hpl20))
      _ = S3b R * (pl2 * pl2) := by
        simp only [S3b]
        ring
  have hS2T2 : lowJetSq (I := I) (M := M) g 2 S2T ≤
      S2b R * (pl2 * pl2) := by
    rw [hS2Tdef]
    refine (happ2 _ S3T).trans ?_
    have htr := (trJet (I := I) (M := M) g gmT 4 2
      LieCorr0Core.lieCorr0AMixPerm1).le.trans htb4'.1
    calc
      Ca2 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1) *
        lowJetSq (I := I) (M := M) g 2 S3T ≤
        Ca2 * Bt4 ^ 2 * (S3b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa2) hS3T2
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa2 (sq_nonneg _))
      _ = S2b R * (pl2 * pl2) := by
        simp only [S2b]
        ring
  -- level-5 difference
  have hdel5 : S5T - S5U =
      slotExtend (I := I) (M := M) g 1 4
        (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) := by
    rw [hS5Tdef, hS5Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdU =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdU) from rfl,
      slotExtend_sub, slotExtend_sub]
  have hd5 : lowJetSq (I := I) (M := M) g 2 (S5T - S5U) ≤
      D5c R * (pl2 * u) := by
    rw [hdel5]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) :=
        slotH2 (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2 (mcdT - mcdU)) :=
        mul_le_mul_of_nonneg_left
          (slotH2 (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * (M5 R * (pl2 * u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmpd hfr) hfr
      _ = D5c R * (pl2 * u) := by
        simp only [D5c]
        ring
  -- level-4 difference
  have hdel4 : S4T - S4U =
      appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
            lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          S5T +
        appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          (S5T - S5U) := by
    rw [hS4Tdef, hS4Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have htrd3 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
        lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) ≤
      Ct3 ^ 2 * u := by
    rw [trSub, reindexJet]
    exact htp3'
  have hd4 : lowJetSq (I := I) (M := M) g 2 (S4T - S4U) ≤
      2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
    rw [hdel4]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
            lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          S5T) ≤ K4 R * (pl2 * u) := by
      refine (happ4 _ S5T).trans ?_
      calc
        Ca4 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
              lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) *
          lowJetSq (I := I) (M := M) g 2 S5T ≤
          Ca4 * (Ct3 ^ 2 * u) * (S5b R * pl2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htrd3 hCa4) hS5T2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa4 (mul_nonneg (sq_nonneg _) hu0))
        _ = K4 R * (pl2 * u) := by
          simp only [K4]
          ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          (S5T - S5U)) ≤ K5 R * (pl2 * u) := by
      refine (happ4 _ _).trans ?_
      have htr := (trJet (I := I) (M := M) g gmU 3 2
        LieCorr0Core.lieCorr0AMixPermQ).le.trans htb3'.2
      calc
        Ca4 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) *
          lowJetSq (I := I) (M := M) g 2 (S5T - S5U) ≤
          Ca4 * Bt3 ^ 2 * (D5c R * (pl2 * u)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htr hCa4) hd5
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa4 (sq_nonneg _))
        _ = K5 R * (pl2 * u) := by
          simp only [K5]
          ring
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
        linarith [h1, h2]
  -- level-3 difference
  have hdel3 : S3T - S3U =
      appCcRS (I := I) (M := M) g 2 3 6 (E3T - E3U) S4T +
        appCcRS (I := I) (M := M) g 2 3 6 E3U (S4T - S4U) := by
    rw [hS3Tdef, hS3Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have hdelE3 : E3T - E3U =
      slotExtend (I := I) (M := M) g 2 5
        (slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) := by
    rw [hE3Tdef, hE3Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) from rfl,
      slotExtend_sub, slotExtend_sub, slotExtend_sub]
  have hdE32 : lowJetSq (I := I) (M := M) g 2 (E3T - E3U) ≤
      E3d R * (pl2 * u) := by
    rw [hdelE3]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        slotH2 (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (slotH2 (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr *
          lowJetSq (I := I) (M := M) g 2 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slotH2 (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * (M5 R * (pl2 * u)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmpd hfr) hfr) hfr
      _ = E3d R * (pl2 * u) := by
        simp only [E3d]
        ring
  have hd3 : lowJetSq (I := I) (M := M) g 2 (S3T - S3U) ≤
      2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)) := by
    rw [hdel3]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 3 6 (E3T - E3U) S4T) ≤
        K3 R * ((pl2 * pl2) * u) := by
      refine (happ3 (E3T - E3U) S4T).trans ?_
      calc
        Ca3 * lowJetSq (I := I) (M := M) g 2 (E3T - E3U) *
          lowJetSq (I := I) (M := M) g 2 S4T ≤
          Ca3 * (E3d R * (pl2 * u)) * (S4b R * pl2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hdE32 hCa3) hS4T2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa3 (mul_nonneg (hE3d R hR) hpl2u))
        _ = K3 R * ((pl2 * pl2) * u) := by
          simp only [K3]
          ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 3 6 E3U (S4T - S4U)) ≤
        K34 R * ((pl2 * pl2) * u) := by
      refine (happ3 E3U _).trans ?_
      calc
        Ca3 * lowJetSq (I := I) (M := M) g 2 E3U *
          lowJetSq (I := I) (M := M) g 2 (S4T - S4U) ≤
          Ca3 * (E3b R * pl2) *
            (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hE3U2 hCa3) hd4
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa3 (mul_nonneg (hE3b R hR) hpl20))
        _ = Ca3 * E3b R * (2 * (K4 R + K5 R)) * ((pl2 * pl2) * u) := by
          ring
        _ = K34 R * ((pl2 * pl2) * u) := by
          simp only [K34]
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (K3 R * ((pl2 * pl2) * u) +
          K34 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  -- level-2 difference
  have hdel2 : S2T - S2U =
      appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
            lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          S3T +
        appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          (S3T - S3U) := by
    rw [hS2Tdef, hS2Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have htrd4 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
        lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) ≤
      Ct4 ^ 2 * u := by
    rw [trSub, reindexJet]
    exact htp4'
  have hd2 : lowJetSq (I := I) (M := M) g 2 (S2T - S2U) ≤
      2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)) := by
    rw [hdel2]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
            lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          S3T) ≤ K2 R * ((pl2 * pl2) * u) := by
      refine (happ2 _ S3T).trans ?_
      calc
        Ca2 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
              lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) *
          lowJetSq (I := I) (M := M) g 2 S3T ≤
          Ca2 * (Ct4 ^ 2 * u) * (S3b R * (pl2 * pl2)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htrd4 hCa2) hS3T2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa2 (mul_nonneg (sq_nonneg _) hu0))
        _ = K2 R * ((pl2 * pl2) * u) := by
          simp only [K2]
          ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          (S3T - S3U)) ≤ K23 R * ((pl2 * pl2) * u) := by
      refine (happ2 _ _).trans ?_
      have htr := (trJet (I := I) (M := M) g gmU 4 2
        LieCorr0Core.lieCorr0AMixPerm1).le.trans htb4'.2
      calc
        Ca2 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) *
          lowJetSq (I := I) (M := M) g 2 (S3T - S3U) ≤
          Ca2 * Bt4 ^ 2 * (2 * (K3 R * ((pl2 * pl2) * u) +
            K34 R * ((pl2 * pl2) * u))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htr hCa2) hd3
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa2 (sq_nonneg _))
        _ = K23 R * ((pl2 * pl2) * u) := by
          simp only [K23]
          ring
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (K2 R * ((pl2 * pl2) * u) +
          K23 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  -- the half itself
  have htrd2 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
        lc0TraceRF (I := I) (M := M) g gmU 2 σlast) ≤
      Ct2 ^ 2 * u := by
    rw [trSub, reindexJet]
    exact htp2'
  have hdel1 : lc0AMixHalfRF (I := I) (M := M) g gmT g σlast -
      lc0AMixHalfRF (I := I) (M := M) g gmU g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
            lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2T +
        appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmU 2 σlast)
          (S2T - S2U) := by
    rw [hHalfT, hHalfU, appCcRS_sub_left, appCcRS_sub_right]
    module
  have hhalf : lowJetSq (I := I) (M := M) g 2
      (lc0AMixHalfRF (I := I) (M := M) g gmT g σlast -
        lc0AMixHalfRF (I := I) (M := M) g gmU g σlast) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hdel1]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
            lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2T) ≤
        K1 R * ((pl2 * pl2) * u) := by
      refine (happ1 _ S2T).trans ?_
      calc
        Ca1 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
              lc0TraceRF (I := I) (M := M) g gmU 2 σlast) *
          lowJetSq (I := I) (M := M) g 2 S2T ≤
          Ca1 * (Ct2 ^ 2 * u) * (S2b R * (pl2 * pl2)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htrd2 hCa1) hS2T2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa1 (mul_nonneg (sq_nonneg _) hu0))
        _ = K1 R * ((pl2 * pl2) * u) := by
          simp only [K1]
          ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmU 2 σlast)
          (S2T - S2U)) ≤ K12 R * ((pl2 * pl2) * u) := by
      refine (happ1 _ _).trans ?_
      have htr := (trJet (I := I) (M := M) g gmU 2 2
        σlast).le.trans htb2'.2
      calc
        Ca1 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmU 2 σlast) *
          lowJetSq (I := I) (M := M) g 2 (S2T - S2U) ≤
          Ca1 * Bt2 ^ 2 * (2 * (K2 R * ((pl2 * pl2) * u) +
            K23 R * ((pl2 * pl2) * u))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htr hCa1) hd2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa1 (sq_nonneg _))
        _ = K12 R * ((pl2 * pl2) * u) := by
          simp only [K12]
          ring
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (K1 R * ((pl2 * pl2) * u) +
          K12 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hhalf.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact amixScalar (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **Class 4** — the mixed connection--cometric zero head `lc0AMix`.  Proved.

`amix_refold_rf` writes `lc0AMix` as `2 •` the sum of the two half products
`Tr₂ · Tr₄ · Ext³mcd · Tr₃ · Ext²mcd`, symmetrized by `lc0SwapPermRF`; each half
is estimated by `amixHalfH2Pair` and the two halves are added.

The five-factor telescope carries *two* connection-difference factors, so the
naive bounded chain is `(1+A)²` against a difference — outside the arm class.
Both are re-paired through `jetInterp3`; see `amixHalfH2Pair` for the
orientation.  No publicization from `DeTurckRemainderLowBaseLip` was needed:
`trace{2,3,4}_pair_h2 / _h2_bdd`, `mcd_pair_h2`, `mcd_h2_bdd` and
`appRS_h2_h2_h2` are all public, and the `H¹` chain's private slot/reindex/
product helpers are re-derived above from the public `rfns` layer. -/
private theorem amixH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (lc0AMix (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            lc0AMix (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
 by
  obtain ⟨ρ, Bp0, Bp1, hρ, hBp0, hBp1, hhalf⟩ :=
    amixHalfH2Pair (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => 4 * Bp0 R, fun R => 4 * Bp1 R, hρ,
    fun R hR => by
      have := hBp0 R hR
      linarith,
    fun R hR => by
      have := hBp1 R hR
      linarith, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hh1 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn hs
    LieCorr0Core.lieCorr0AMixPerm2
  have hh2 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn hs
    (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2)
  rw [amix_refold_rf (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδT hδZ s) g,
    amix_refold_rf (I := I) (M := M) g
      (realizedFam (I := I) g U 0 hδU hδZ s) g]
  have hform :
      lc0AMixFormRF (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδT hδZ s) g -
        lc0AMixFormRF (I := I) (M := M) g
          (realizedFam (I := I) g U 0 hδU hδZ s) g =
      (2 : ℝ) •
        ((lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g
              LieCorr0Core.lieCorr0AMixPerm2 -
          lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g
              LieCorr0Core.lieCorr0AMixPerm2) +
        (lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g
              (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2) -
          lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g
              (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))) := by
    simp only [lc0AMixFormRF]
    module
  rw [hform, jetSmul]
  have hadd := jetAdd (I := I) (M := M) g 2
    (lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδT hδZ s) g
          LieCorr0Core.lieCorr0AMixPerm2 -
      lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g U 0 hδU hδZ s) g
          LieCorr0Core.lieCorr0AMixPerm2)
    (lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδT hδZ s) g
          (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2) -
      lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g U 0 hδU hδZ s) g
          (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))
  calc
    (2 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
      (2 : ℝ) ^ 2 * (2 * (lowJetSq (I := I) (M := M) g 2 _ +
        lowJetSq (I := I) (M := M) g 2 _)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (2 : ℝ) ^ 2 * (2 *
        ((Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
            Bp1 R * A4 * (D3 + N)) ^ 2 +
          (Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
            Bp1 R * A4 * (D3 + N)) ^ 2)) := by
      have := add_le_add hh1 hh2
      linarith
    _ = (4 * Bp0 R * (1 + A) * (D4 + D3 + D2 + N) +
        4 * Bp1 R * A4 * (D3 + N)) ^ 2 := by
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Class 5** — the curvature passenger `lc0Riem`.  Proved: only the spectral difference enters, with an `A`-free constant. -/
private theorem riemH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (lc0Riem (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) -
            lc0Riem (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
 by
  obtain ⟨ρ, C, hρ, hC, hriem⟩ := riem_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, fun _ => C, fun _ => 0, hρ,
    fun _ _ => hC, fun _ _ => le_refl 0, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn)
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  refine (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
  have hstep : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      C * N := mul_le_mul_of_nonneg_left hPQn hC
  refine (pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg _)) hstep 2).trans ?_
  have hbig : C * N ≤ C * (1 + A) * (D4 + D3 + D2 + N) + 0 * A4 * (D3 + N) := by
    have hin : N ≤ (1 + A) * (D4 + D3 + D2 + N) := by
      nlinarith [mul_nonneg hA hD4, mul_nonneg hA hD3,
        mul_nonneg hA hD2, mul_nonneg hA hN, hD2, hD3, hD4]
    have := mul_le_mul_of_nonneg_left hin hC
    nlinarith [this]
  exact pow_le_pow_left₀ (mul_nonneg hC hN) hbig 2


/-! ### The master telescope and its path integral -/

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **The five-class `H²` master telescope.**  On a common small spectral `H²`
ball the transparent self-action family difference obeys the admissible
second-order modulus of the corrected ruling: every difference slot carries a
coefficient of `A`-degree `≤ 1` or `A4`-degree `≤ 1`. -/
theorem selfLow_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (LowBaseInternal.rhsSelfLow (I := I) (M := M)
              g g T hδT hδZ s -
            LowBaseInternal.rhsSelfLow (I := I) (M := M)
              g g U hδU hδZ s) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨ρg, G0, G1, hρg, hG0, hG1, hgood⟩ :=
    goodH2Pair (I := I) (M := M) hDim g
  obtain ⟨ρl, L0, L1, hρl, hL0, hL1, hlie⟩ :=
    lieCovH2Pair (I := I) (M := M) hDim g
  obtain ⟨ρv, V0, V1, hρv, hV0, hV1, hvb⟩ :=
    vbH2Pair (I := I) (M := M) hDim g
  obtain ⟨ρa, W0, W1, hρa, hW0, hW1, hamix⟩ :=
    amixH2Pair (I := I) (M := M) hDim g
  obtain ⟨ρr, C0, C1, hρr, hC0, hC1, hriem⟩ :=
    riemH2Pair (I := I) (M := M) hDim g
  set ρ : ℝ := min (min ρg ρl) (min ρv (min ρa ρr)) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρg hρl) (lt_min hρv (lt_min hρa hρr))
  let MB0 : ℝ → ℝ := fun R => 8 * G0 R + 4 * (L0 R + V0 R + W0 R + C0 R)
  let MB1 : ℝ → ℝ := fun R => 8 * G1 R + 4 * (L1 R + V1 R + W1 R + C1 R)
  refine ⟨ρ, MB0, MB1, hρ0, ?_, ?_, ?_⟩
  · intro R hR
    have e1 := hG0 R hR
    have e2 := hL0 R hR
    have e3 := hV0 R hR
    have e4 := hW0 R hR
    have e5 := hC0 R hR
    simp only [MB0]
    linarith
  · intro R hR
    have e1 := hG1 R hR
    have e2 := hL1 R hR
    have e3 := hV1 R hR
    have e4 := hW1 R hR
    have e5 := hC1 R hR
    simp only [MB1]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hρc : ρ ≤ ρg ∧ ρ ≤ ρl ∧ ρ ≤ ρv ∧ ρ ≤ ρa ∧ ρ ≤ ρr := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  have hXg := hgood T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.1) (hUn.trans hρc.1) hTUn hs
  have hXl := hlie T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.1) (hUn.trans hρc.2.1) hTUn hs
  have hXv := hvb T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.1) (hUn.trans hρc.2.2.1) hTUn hs
  have hXa := hamix T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.2.1) (hUn.trans hρc.2.2.2.1) hTUn hs
  have hXr := hriem T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.2.2) (hUn.trans hρc.2.2.2.2) hTUn hs
  rw [selfSubParts (I := I) (M := M) g T U hT hU
    hδ_lt hδT hδU hδZ hs]
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set Y1 : SmoothCcTensor g 2 2 :=
    LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmT (s • T) -
      LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmU (s • U)
    with hY1
  set Y2 : SmoothCcTensor g 2 2 :=
    (deTurckLieCovDerivArmField (I := I) (M := M) g gmT g -
        edgeLiePairFam (I := I) (M := M) g T hδT hδZ
          lieRefoldQ lieRefoldEps s) -
      (deTurckLieCovDerivArmField (I := I) (M := M) g gmU g -
        edgeLiePairFam (I := I) (M := M) g U hδU hδZ
          lieRefoldQ lieRefoldEps s) with hY2
  set Y3 : SmoothCcTensor g 2 2 :=
    lc0VB (I := I) (M := M) g gmT -
      lc0VB (I := I) (M := M) g gmU with hY3
  set Y4 : SmoothCcTensor g 2 2 :=
    lc0AMix (I := I) (M := M) g gmT g -
      lc0AMix (I := I) (M := M) g gmU g with hY4
  set Y5 : SmoothCcTensor g 2 2 :=
    lc0Riem (I := I) (M := M) g gmT -
      lc0Riem (I := I) (M := M) g gmU with hY5
  set Zg : ℝ := G0 R * (1 + A) * (D4 + D3 + D2 + N) +
    G1 R * A4 * (D3 + N) with hZg
  set Zl : ℝ := L0 R * (1 + A) * (D4 + D3 + D2 + N) +
    L1 R * A4 * (D3 + N) with hZl
  set Zv : ℝ := V0 R * (1 + A) * (D4 + D3 + D2 + N) +
    V1 R * A4 * (D3 + N) with hZv
  set Za : ℝ := W0 R * (1 + A) * (D4 + D3 + D2 + N) +
    W1 R * A4 * (D3 + N) with hZa
  set Zr : ℝ := C0 R * (1 + A) * (D4 + D3 + D2 + N) +
    C1 R * A4 * (D3 + N) with hZr
  have hZgn : 0 ≤ Zg := by
    have h0 := hG0 R hR
    have h1 := hG1 R hR
    have e1 : 0 ≤ G0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) this
    have e2 : 0 ≤ G1 R * A4 * (D3 + N) := by
      have : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) this
    rw [hZg]
    linarith
  have hZln : 0 ≤ Zl := by
    have h0 := hL0 R hR
    have h1 := hL1 R hR
    have e1 : 0 ≤ L0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) this
    have e2 : 0 ≤ L1 R * A4 * (D3 + N) := by
      have : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) this
    rw [hZl]
    linarith
  have hZvn : 0 ≤ Zv := by
    have h0 := hV0 R hR
    have h1 := hV1 R hR
    have e1 : 0 ≤ V0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) this
    have e2 : 0 ≤ V1 R * A4 * (D3 + N) := by
      have : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) this
    rw [hZv]
    linarith
  have hZan : 0 ≤ Za := by
    have h0 := hW0 R hR
    have h1 := hW1 R hR
    have e1 : 0 ≤ W0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) this
    have e2 : 0 ≤ W1 R * A4 * (D3 + N) := by
      have : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) this
    rw [hZa]
    linarith
  have hZrn : 0 ≤ Zr := by
    have h0 := hC0 R hR
    have h1 := hC1 R hR
    have e1 : 0 ≤ C0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) this
    have e2 : 0 ≤ C1 R * A4 * (D3 + N) := by
      have : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) this
    rw [hZr]
    linarith
  have hj1 : lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • Y1) ≤
      (2 * Zg) ^ 2 := by
    rw [jetSmul]
    have h4 : ((-2 : ℝ)) ^ 2 = 4 := by norm_num
    have he : (2 * Zg) ^ 2 = 4 * Zg ^ 2 := by ring
    rw [h4, he]
    linarith [hXg]
  have h12 : lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • Y1 + Y2) ≤
      2 * ((2 * Zg) ^ 2 + Zl ^ 2) := by
    have hadd := jetAdd (I := I) (M := M) g 2 ((-2 : ℝ) • Y1) Y2
    linarith [hj1, hXl, hadd]
  have h123 : lowJetSq (I := I) (M := M) g 2
      (((-2 : ℝ) • Y1 + Y2) + Y3) ≤
      2 * (2 * ((2 * Zg) ^ 2 + Zl ^ 2) + Zv ^ 2) := by
    have hadd := jetAdd (I := I) (M := M) g 2 ((-2 : ℝ) • Y1 + Y2) Y3
    linarith [h12, hXv, hadd]
  have h1234 : lowJetSq (I := I) (M := M) g 2
      ((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) ≤
      2 * (2 * (2 * ((2 * Zg) ^ 2 + Zl ^ 2) + Zv ^ 2) + Za ^ 2) := by
    have hadd := jetAdd (I := I) (M := M) g 2
      (((-2 : ℝ) • Y1 + Y2) + Y3) Y4
    linarith [h123, hXa, hadd]
  have hfin : lowJetSq (I := I) (M := M) g 2
      (((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) + Y5) ≤
      2 * (2 * (2 * (2 * ((2 * Zg) ^ 2 + Zl ^ 2) + Zv ^ 2) + Za ^ 2) +
        Zr ^ 2) := by
    have hadd := jetAdd (I := I) (M := M) g 2
      ((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) Y5
    linarith [h1234, hXr, hadd]
  refine hfin.trans ?_
  have h2g : (0 : ℝ) ≤ 2 * Zg := by linarith
  have hsq : (2 * Zg) ^ 2 + Zl ^ 2 + Zv ^ 2 + Za ^ 2 + Zr ^ 2 ≤
      (2 * Zg + Zl + Zv + Za + Zr) ^ 2 := by
    have e1 := sqAdd2 (a := 2 * Zg) (b := Zl) h2g hZln
    have e2 := sqAdd2 (a := 2 * Zg + Zl) (b := Zv) (by linarith) hZvn
    have e3 := sqAdd2 (a := 2 * Zg + Zl + Zv) (b := Za) (by linarith) hZan
    have e4 := sqAdd2 (a := 2 * Zg + Zl + Zv + Za) (b := Zr)
      (by linarith) hZrn
    linarith
  have hexp : 2 * (2 * (2 * (2 * ((2 * Zg) ^ 2 + Zl ^ 2) + Zv ^ 2) +
        Za ^ 2) + Zr ^ 2) ≤
      16 * ((2 * Zg) ^ 2 + Zl ^ 2 + Zv ^ 2 + Za ^ 2 + Zr ^ 2) := by
    have p1 : (0 : ℝ) ≤ Zv ^ 2 := sq_nonneg _
    have p2 : (0 : ℝ) ≤ Za ^ 2 := sq_nonneg _
    have p3 : (0 : ℝ) ≤ Zr ^ 2 := sq_nonneg _
    linarith
  refine hexp.trans ?_
  have hmul : 16 * ((2 * Zg) ^ 2 + Zl ^ 2 + Zv ^ 2 + Za ^ 2 + Zr ^ 2) ≤
      16 * (2 * Zg + Zl + Zv + Za + Zr) ^ 2 := by linarith
  refine hmul.trans (le_of_eq ?_)
  simp only [MB0, MB1]
  rw [hZg, hZl, hZv, hZa, hZr]
  ring

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **The `H²` tame bound for the pairwise `C0` coefficient difference.**  The
path integral of `selfLow_pair_h2`; the `C0` half of `lowA1_pair_tame`. -/
theorem c0Diff_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 2
          (lowC0Diff (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hker⟩ :=
    selfLow_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδT hδZ s -
      LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g U hδU hδZ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjoint :=
    threeArmJoint_sub (I := I) (M := M) g _ _
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  set Btot : ℝ := B0 R * (1 + A) * (D4 + D3 + D2 + N) +
    B1 R * A4 * (D3 + N) with hBtot
  have hBn : 0 ≤ Btot := by
    have h0 := hB0 R hR
    have h1 := hB1 R hR
    have e1 : 0 ≤ B0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have hs1 : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) hs1
    have e2 : 0 ≤ B1 R * A4 * (D3 + N) := by
      have hs2 : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) hs2
    rw [hBtot]
    linarith
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 2 (Φ s) ≤ Btot ^ 2 := by
    intro s hs
    rw [hBtot]
    exact hker T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
      hTn hUn hTUn hs
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 2 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := Btot) hBn
    (by
      intro t ht
      simpa only [lowJetSq, Nat.reduceAdd] using hpoint t ht)
  have hfin : lowJetSq (I := I) (M := M) g 2
      (lowC0Diff (I := I) (M := M) g T U hδ_lt hδT hδU hδZ) ≤
      Btot ^ 2 := by
    simpa only [lowJetSq, lowC0Diff, Φ, S, Nat.reduceAdd] using hpath
  exact hfin

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
