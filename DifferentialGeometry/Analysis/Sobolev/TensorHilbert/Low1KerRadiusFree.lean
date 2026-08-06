import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciOrder1RadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0CoeffDiffRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound

/-!
# Radius-free grid currency for the order-one low-base integrand

The order-one path integrand of the low-base split is

`rhsLow1Coeff g₀ g_bg T T' s
  = (-2) • linearizedRicciConnDiffOrder1CoeffField g₀ g₁ + deTurckLieArm1Coeff g₀ g₁ g_bg`,

with `g₁` the realized metric along the radial segment.  Both summands are
**linear** in the connection difference — that is what separates the order-one
coefficient from the order-zero one, where the `A·A` arm is quadratic — so both
carry an `antidiagonalTupleGridWindow` bound at offset `+2`, i.e. one derivative
of the state, with no Sobolev ball and no order gate.

This module produces those two windows:

* `ricci1Atgw` — the Ricci arm `appCcRS (fourTrace) (order-1 kernel)`, folded from
  the outer factor's `+1` window (`fourTrAtgw`) against `ricciKerAtgw`'s `+2`.
* `lieA1Atgw` — the DeTurck Lie arm at the frozen background `g_bg = g₀`, folded
  piecewise from `dltcAtgw` (`+1`) against the three `Ψ` factors' `+2` windows.

The `+1` window of the two outer trace factors has a common source: both
`ricciCometricFourTraceCastG0` and `deTurckLieTraceCoeff` are slot reindexings of
`ricciArmPrincipalCoeffPure`, whose window is `pureAtgw`.  The only genuinely new
`Ψ` is `lieArm1PsiB`; it is the moving-metric-lowered connection difference
raised and slot-permuted, so its window comes from `b4_mcd_atgw` through the
sign identity `metricConnDiffLoweredCc_eq_neg_kappa`.

Every statement here is radius-free and gate-free, which is what the all-order
jet tower `c1_jet_tower` needs and what the flat ball-uniform producers cannot
give.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Sign and scalar bookkeeping -/

omit [BoundarylessManifold I M] in
private lemma l1IcgSmul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma l1RfnsNeg (g : SmoothRiemannianMetric I M) {r s : ℕ} (l : ℕ) (x : M)
    (X : SmoothCcTensor g r s) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l (-X)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l X).toSection x) := by
  have hneg : (-X) = (-1 : ℝ) • X := by rw [neg_smul, one_smul]
  rw [hneg, l1IcgSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, riemannianFiberNormSq_smul]
  norm_num

/-! ### The `+1` window of the outer trace factors -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the pure Ricci principal coefficient.**

`|∇ˡ(ricciArmPrincipalCoeffPure g₀ g₁)|²(x) ≤ Kp l · atgw(bP)(l + 1)`.

Offset `+1`: the coefficient is the background double trace plus one endomorphism
insertion built from the inverse-metric difference, and the difference costs no
derivative of the state.  This is the valence-`(4,2)` sibling of
`rfns_iCG_cometricCastG0_atgw_rf`. -/
theorem pureAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kp : ℕ → ℝ, (∀ l, 0 ≤ Kp l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 2 l
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kp l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  set Φ : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + i)
      (iteratedCovGrad (I := I) g₀ 4 2 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KW : ℕ → ℝ := fun q => fr ^ 3 * C_base q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q => mul_nonneg (pow_nonneg hfr_nn 3) (hC_base_nn q)
  refine ⟨fun l => 2 * SΦ l + 2 * foldConst (E := E) 0 0 SΦ KW l,
    fun l => by
      have h1 := hSΦ_nn l
      have h2 := foldConst_nn (E := E) (u := 0) (v := 0) hSΦ_nn hKW_nn l
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set bP : ℕ → ℝ := gridBase (I := I) (M := M) g₀ P x with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j := gridBase_nn (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow bP (l + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow bP hbP_nn (by omega)
  set W : SmoothCcTensor g₀ 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 3 (gInvDiffRaisedEndoField (I := I) g₀ g₁) with hW_def
  -- the constant outer factor is a window at offset `0`
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i' Φ).toSection y) ≤
        SΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hSΦ i' y) (le_mul_of_one_le_right (hSΦ_nn i') hy)
  -- the endomorphism-insertion arm is a window at offset `0`
  have hWw : ∀ (q : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) y
          ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection y) ≤
        KW q * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) := by
    intro q y
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 3
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) q y
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q y
    have hgrideq : (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
          ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) y
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection y)) =
        Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P y) q := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid
          (gridBase (I := I) (M := M) g₀ P y) q ≤
        Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _
        (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) y
            ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection y)
        ≤ fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) y
            ((iteratedCovGrad (I := I) g₀ 1 1 q
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ 3 * (C_base q * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P y) q) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn 3)
      _ ≤ fr ^ 3 * (C_base q * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgw (hC_base_nn q)) (pow_nonneg hfr_nn 3)
      _ = KW q * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) := by rw [hKW_def]; ring
  have hB := atgwFold (I := I) (M := M) g₀ (p := 4) (a := 4) (b := 2) 0 0 Φ W P
    hSΦ_nn hKW_nn hΦw hWw l x
  have hid : ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁ =
      Φ + appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W := by
    have h := ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
    rw [← hΦ_def, ← hW_def] at h
    exact h
  rw [hid, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ 4 2 l Φ +
        iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 4 2 l Φ).toSection x +
        (iteratedCovGrad (I := I) g₀ 4 2 l
          (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 4 2 l Φ).toSection x) ≤ SΦ l := hSΦ l x
  have hAw : SΦ l ≤ SΦ l * Combinatorics.antidiagonalTupleGridWindow bP (l + 1) :=
    le_mul_of_one_le_right (hSΦ_nn l) hone
  have hBw : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 4 2 l
        (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x) ≤
      foldConst (E := E) 0 0 SΦ KW l *
        Combinatorics.antidiagonalTupleGridWindow bP (l + 1) := by
    have hidx : l + 0 + 0 + 1 = l + 1 := by omega
    rw [hbP_def]
    rw [hidx] at hB
    exact hB
  nlinarith [hA, hAw, hBw]

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the Ricci four-trace cast.**

`|∇ⁿ(ricciCometricFourTraceCastG0 g₀ g₁)|²(x) ≤ K n · atgw(bP)(n + 1)`.  This is
the `diagonalProductGrid` producer of `RicciConnDiffOrder0KernelJetGrid` read in
window currency: the window at level `n + 1` *is* the grid sum over
`range (n + 1)`. -/
theorem fourTrAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kft : ℕ → ℝ, (∀ n, 0 ≤ Kft n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          Kft n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 1) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  have h := hC g₁ P htie hδ_le hδ0 hδ n x
  have hwin : (∑ k ∈ Finset.range (n + 1),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
      Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (n + 1) := rfl
  rwa [hwin] at h

set_option linter.unusedSectionVars false in
/-- **The DeTurck Lie trace coefficient is a slot reindexing of the pure Ricci
principal coefficient.**  Both are the moving cometric double trace read through
a fixed source-slot permutation; only the permutation differs. -/
theorem dltcEqPure (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  rfl

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the DeTurck Lie trace coefficient.**

`|∇ˡ(deTurckLieTraceCoeff g₀ g₁ σ)|²(x) ≤ Kp l · atgw(bP)(l + 1)`, at the same
constant as `pureAtgw` because the reindexing is a fibre isometry at every jet
order. -/
theorem dltcAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kp : ℕ → ℝ, (∀ l, 0 ≤ Kp l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 2 l
              (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ)).toSection x) ≤
          Kp l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  obtain ⟨Kp, hKp_nn, hp⟩ := pureAtgw (I := I) (M := M) g₀ hδ₀
  refine ⟨Kp, hKp_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ σ l x
  rw [dltcEqPure (I := I) (M := M) g₀ g₁ σ,
    rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) σ l x]
  exact hp g₁ P htie hδ_le hδ0 hδ l x

/-! ### The Ricci arm -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the order-one Ricci coefficient
field.**

`|∇ⁿ(linearizedRicciConnDiffOrder1CoeffField g₀ g₁)|²(x) ≤ K n · atgw(bP)(n + 2)`.

The coefficient is the four-trace cast applied to the order-one kernel; the cast
costs no derivative of the state (`fourTrAtgw`, offset `+1`) and the kernel costs
exactly one (`ricciKerAtgw`, offset `+2`), so the Leibniz fold lands at `+2` —
the `range (i + 2)` budget of the `C1` jet tower. -/
theorem ricci1Atgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kr : ℕ → ℝ, (∀ n, 0 ≤ Kr n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kr n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kft, hKft_nn, hft⟩ := fourTrAtgw (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kker, hKker_nn, hker⟩ := ricciKerAtgw (I := I) (M := M) g₀ hδ₀
  refine ⟨fun n => foldConst (E := E) 0 1 Kft Kker n,
    fun n => foldConst_nn (E := E) hKft_nn hKker_nn n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection y) ≤
        Kft i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have h := hft g₁ P htie hδ_le hδ0 hδ i' y
    have hidx : i' + 0 + 1 = i' + 1 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 4 l
            (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection y) ≤
        Kker l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 1 + 1) := by
    intro l y
    have h := hker g₁ P htie hδ_le hδ0 hδ l y
    have hidx : l + 1 + 1 = l + 2 := by omega
    rw [hidx]
    exact h
  have hfold := atgwFold (I := I) (M := M) g₀ (p := 3) (a := 4) (b := 2) 0 1
    (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
    (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) P
    hKft_nn hKker_nn hΦw hWw n x
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS (I := I) (M := M) g₀ g₁]
  have hidx : n + 0 + 1 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  exact hfold

/-! ### The `Ψ` factors of the Lie arm -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for `sharpFlatEndoCc`.**

`|∇ˡ(sharpFlatEndoCc g₀ g₁)|²(x) ≤ S l · atgw(bP)(l + 1)`: the endomorphism is the
identity plus an inverse-metric difference, so it costs no derivative of the
state. -/
theorem sfEndoAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ksf : ℕ → ℝ, (∀ l, 0 ≤ Ksf l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Ksf l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ :=
    CurvatureCoefficientDifferenceJetTower.exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
      (I := I) (M := M) g₀ hδ₀
  refine ⟨S, hS_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  refine le_trans (hS g₁ P htie hδ_le hδ0 hδ l x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hS_nn l)
  exact Combinatorics.antidiagonalTupleGrid_le_window _
    (gridBase_nn (I := I) (M := M) g₀ P x) (by omega)

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the moving-lowered connection
difference, raised and slot-permuted.**

This is the `Ψ`-shaped factor of `lieArm1PsiB`: raising slot `0` and permuting
slots are fibre isometries at every jet order, so the window is the one
`b4_mcd_atgw` supplies for `metricConnDiffLoweredCc`, at offset `+2`. -/
theorem kappaAtgw (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kκ : ℕ → ℝ, (∀ l, 0 ≤ Kκ l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
                (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
                  (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) ≤
          Kκ l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := b4_mcd_atgw (I := I) (M := M) g₀ g_bg hδ₀ hΛ₀0
  refine ⟨Kmcd, hKmcd_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup l x
  have hraise : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 2 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)) l x]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      lieArm1RhoSlot0 (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) l x
  have hsign : lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg =
      -metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg := by
    rw [metricConnDiffLoweredCc_eq_neg_kappa (I := I) (M := M) g₀ g₁ g_bg, neg_neg]
  rw [hraise, hsign,
    l1RfnsNeg (I := I) (M := M) g₀ l x (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g_bg)]
  have h := hmcd g₁ P htie hδ_le hδ0 hδ hsup l x
  have hbase : (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) =
      gridBase (I := I) (M := M) g₀ P x := rfl
  rwa [hbase] at h

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for `lieArm1PsiB`.**

`|∇ⁿ(lieArm1PsiB g₀ g₁ g_bg)|²(x) ≤ K n · atgw(bP)(n + 2)`.  `lieArm1PsiB` is the
moving-lowered connection difference (offset `+2`) composed with the sharp-flat
endomorphism (offset `+1` — no derivative of the state), so the fold stays at
`+2`. -/
theorem psiBAtgw (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kψ : ℕ → ℝ, (∀ n, 0 ≤ Kψ n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kψ n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kκ, hKκ_nn, hκ⟩ := kappaAtgw (I := I) (M := M) g₀ g_bg hδ₀ hΛ₀0
  obtain ⟨Ksf, hKsf_nn, hsf⟩ := sfEndoAtgw (I := I) (M := M) g₀ hδ₀
  refine ⟨fun n => foldConst (E := E) 1 0 Kκ Ksf n,
    fun n => foldConst_nn (E := E) hKκ_nn hKsf_nn n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 1 2 i'
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
                (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))).toSection y) ≤
        Kκ i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i' + 1 + 1) := by
    intro i' y
    have h := hκ g₁ P htie hδ_le hδ0 hδ hsup i' y
    have hidx : i' + 1 + 1 = i' + 2 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection y) ≤
        Ksf l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 0 + 1) := by
    intro l y
    have h := hsf g₁ P htie hδ_le hδ0 hδ l y
    have hidx : l + 0 + 1 = l + 1 := by omega
    rw [hidx]
    exact h
  have hfold := atgwFold (I := I) (M := M) g₀ (p := 1) (a := 1) (b := 2) 1 0
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
    (sharpFlatEndoCc (I := I) g₀ g₁) P hKκ_nn hKsf_nn hΦw hWw n x
  have hidx : n + 1 + 0 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  rw [hdef]
  exact hfold

set_option linter.unusedSectionVars false in
/-- At the frozen background the `lieArm1` background arm is the plain connection
difference. -/
theorem bgCcEqConn (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g₀ = connDiffSection (I := I) g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

/-! ### The Lie arm -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for one `lieArm1Piece`.**

Given a `Ψ` factor with an offset-`+2` window, the piece
`reindex (appCcRS (deTurckLieTraceCoeff σ') (slotExtend² Ψ)) ρ` again has an
offset-`+2` window: the reindexing and the two slot extensions are fibre
isometries up to dimension factors, and the trace coefficient costs no
derivative of the state. -/
theorem pieceAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (Kψ : ℕ → ℝ) (hKψ_nn : ∀ l, 0 ≤ Kψ l) :
    ∃ Kpc : ℕ → ℝ, (∀ n, 0 ≤ Kpc n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (Ψ : SmoothCcTensor g₀ 1 2),
        (∀ (l : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y) ≤
          Kψ l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (l + 2)) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ)).toSection x) ≤
          Kpc n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kp, hKp_nn, hp⟩ := dltcAtgw (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun n => foldConst (E := E) 0 1 Kp (fun l => fr * (fr * Kψ l)) n,
    fun n => foldConst_nn (E := E) hKp_nn
      (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKψ_nn l))) n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ Ψ hΨ σ' ρ n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection y) ≤
        Kp i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have h := hp g₁ P htie hδ_le hδ0 hδ σ' i' y
    have hidx : i' + 0 + 1 = i' + 1 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection y) ≤
        fr * (fr * Kψ l) * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 1 + 1) := by
    intro l y
    have hidx : l + 1 + 1 = l + 2 := by omega
    rw [hidx]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ) l y) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2 Ψ l y) hfr_nn) ?_
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y))
        ≤ fr * (fr * (Kψ l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (l + 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hΨ l y) hfr_nn) hfr_nn
      _ = fr * (fr * Kψ l) * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (l + 2) := by ring
  have hfold := atgwFold (I := I) (M := M) g₀ (p := 3) (a := 4) (b := 2) 0 1
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
    (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)) P
    hKp_nn (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKψ_nn l))) hΦw hWw n x
  have hidx : n + 0 + 1 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  have hdef : lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (appCcRS (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 2 _ ρ n x]
  exact hfold

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the order-one DeTurck Lie
coefficient at the frozen background.**

`|∇ⁿ(deTurckLieArm1Coeff g₀ g₁ g₀)|²(x) ≤ K n · atgw(bP)(n + 2)`.

`deTurckLieArm1Coeff_eq_lieArm1Piece_sum` writes the coefficient as fourteen
`lieArm1Piece`s over three `Ψ` factors.  At `g_bg = g₀` two of them collapse to
`connDiffSection g₁ g₀`; the third is `lieArm1PsiB`.  All three carry offset-`+2`
windows, so the whole arm does. -/
theorem lieA1Atgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kl : ℕ → ℝ, (∀ n, 0 ≤ Kl n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          Kl n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := rfns_iCG_connDiffSection_atgw_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kψ, hKψ_nn, hψ⟩ := psiBAtgw (I := I) (M := M) g₀ g₀ hδ₀ hΛ₀0
  set KΨ : ℕ → ℝ := fun l => Kcd l + Kψ l with hKΨ_def
  have hKΨ_nn : ∀ l, 0 ≤ KΨ l := fun l => by
    have := hKcd_nn l; have := hKψ_nn l; simp only [hKΨ_def]; linarith
  obtain ⟨Kpc, hKpc_nn, hpc⟩ := pieceAtgw (I := I) (M := M) g₀ hδ₀ KΨ hKΨ_nn
  refine ⟨fun n => 1138 * Kpc n, fun n => by have := hKpc_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set bW : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (gridBase (I := I) (M := M) g₀ P x) (n + 2) with hbW_def
  have hbW_nn : 0 ≤ bW :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg _
      (gridBase_nn (I := I) (M := M) g₀ P x) _
  -- the two `Ψ` factors, both at offset `+2` with the common constant `KΨ`
  have hΨcd : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    have h := hcd g₁ P htie hδ_le hδ0 hδ l y
    have hbase : (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y)) =
        gridBase (I := I) (M := M) g₀ P y := rfl
    rw [hbase] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Combinatorics.antidiagonalTupleGridWindow_nonneg _
        (gridBase_nn (I := I) (M := M) g₀ P y) _)
    have := hKψ_nn l
    simp only [hKΨ_def]; linarith
  have hΨpsi : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g₀)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    refine le_trans (hψ g₁ P htie hδ_le hδ0 hδ hsup l y) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Combinatorics.antidiagonalTupleGridWindow_nonneg _
        (gridBase_nn (I := I) (M := M) g₀ P y) _)
    have := hKcd_nn l
    simp only [hKΨ_def]; linarith
  have hΨbg : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g₀)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    rw [bgCcEqConn (I := I) (M := M) g₀ g₁]
    exact hΨcd l y
  -- the fibre jet functional at order `n`, and its two-subadditivity
  set F : SmoothCcTensor g₀ 3 2 → ℝ := fun X =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n X).toSection x) with hF_def
  have hFnn : ∀ X, 0 ≤ F X := fun X => riemannianFiberNormSq_nonneg _ _ _ _ _
  have hFadd : ∀ X Y : SmoothCcTensor g₀ 3 2, F (X + Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    simp only [hF_def]
    rw [iteratedCovGrad_add (I := I) g₀ 3 2 n X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (2 + n) x _ _
  have hFneg : ∀ X : SmoothCcTensor g₀ 3 2, F (-X) = F X := by
    intro X
    simp only [hF_def]
    exact l1RfnsNeg (I := I) (M := M) g₀ n x X
  have hFsub : ∀ X Y : SmoothCcTensor g₀ 3 2, F (X - Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    have h := hFadd X (-Y)
    rw [hFneg Y] at h
    rwa [sub_eq_add_neg]
  -- every piece is bounded by the same window
  have hpiece : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
      (Ψ : SmoothCcTensor g₀ 1 2),
      (∀ (l : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 2)) →
      F (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ) ≤ Kpc n * bW := by
    intro σ' ρ Ψ hΨ
    exact hpc g₁ P htie hδ_le hδ0 hδ Ψ hΨ σ' ρ n x
  set A : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g₀) with hA_def
  set B1 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hB1_def
  set B2 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g₀) with hB2_def
  set B3 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hB3_def
  set B4 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀) with hB4_def
  set B5 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀) with hB5_def
  set B6 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hB6_def
  set C1 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hC1_def
  set C2 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g₀) with hC2_def
  set C3 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hC3_def
  set C4 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀) with hC4_def
  set C5 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀) with hC5_def
  set C6 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀) with hC6_def
  set D : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀) with hD_def
  have hAb : F A ≤ Kpc n * bW := hpiece _ _ _ hΨbg
  have hB1b : F B1 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB2b : F B2 ≤ Kpc n * bW := hpiece _ _ _ hΨpsi
  have hB3b : F B3 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB4b : F B4 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB5b : F B5 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB6b : F B6 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC1b : F C1 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC2b : F C2 ≤ Kpc n * bW := hpiece _ _ _ hΨpsi
  have hC3b : F C3 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC4b : F C4 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC5b : F C5 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC6b : F C6 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hDb : F D ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  -- cascade the two-subadditivity along the recorded bracketing
  have e1 := hFadd B1 B2
  have e2 := hFsub (B1 + B2) B3
  have e3 := hFsub (B1 + B2 - B3) B4
  have e4 := hFsub (B1 + B2 - B3 - B4) B5
  have e5 := hFsub (B1 + B2 - B3 - B4 - B5) B6
  have f1 := hFadd C1 C2
  have f2 := hFsub (C1 + C2) C3
  have f3 := hFsub (C1 + C2 - C3) C4
  have f4 := hFsub (C1 + C2 - C3 - C4) C5
  have f5 := hFsub (C1 + C2 - C3 - C4 - C5) C6
  have g1 := hFadd A (B1 + B2 - B3 - B4 - B5 - B6)
  have g2 := hFadd (A + (B1 + B2 - B3 - B4 - B5 - B6))
    (C1 + C2 - C3 - C4 - C5 - C6)
  have g3 := hFadd (A + (B1 + B2 - B3 - B4 - B5 - B6) +
    (C1 + C2 - C3 - C4 - C5 - C6)) D
  have hsum : F (A + (B1 + B2 - B3 - B4 - B5 - B6) +
      (C1 + C2 - C3 - C4 - C5 - C6) + D) ≤ 1138 * (Kpc n * bW) := by
    linarith [hAb, hB1b, hB2b, hB3b, hB4b, hB5b, hB6b,
      hC1b, hC2b, hC3b, hC4b, hC5b, hC6b, hDb]
  have hexp : deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀ =
      A + (B1 + B2 - B3 - B4 - B5 - B6) + (C1 + C2 - C3 - C4 - C5 - C6) + D :=
    deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g₀
  show F (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀) ≤ _
  rw [hexp]
  refine hsum.trans ?_
  rw [hbW_def]
  exact le_of_eq (by ring)

/-! ### The full order-one integrand -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the order-one low-base integrand.**

`|∇ⁿ((-2) • ricci₁ + lieArm₁)|²(x) ≤ K n · atgw(bP)(n + 2)`: both arms are linear
in the connection difference, so the whole integrand costs exactly one derivative
of the state.  Integrating this against `atgwToJet` at offset `w = 2` is the
`range (i + 2)` budget of `c1_jet_tower`. -/
theorem low1Atgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              ((-2 : ℝ) • linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁ +
                deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          K n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kr, hKr_nn, hr⟩ := ricci1Atgw (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kl, hKl_nn, hl⟩ := lieA1Atgw (I := I) (M := M) g₀ hδ₀ hΛ₀0
  refine ⟨fun n => 8 * Kr n + 2 * Kl n,
    fun n => by have := hKr_nn n; have := hKl_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set R : SmoothCcTensor g₀ 3 2 :=
    linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁ with hR_def
  set L : SmoothCcTensor g₀ 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀ with hL_def
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (gridBase (I := I) (M := M) g₀ P x) (n + 2) with hW_def
  have hRb : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x) ≤ Kr n * W :=
    hr g₁ P htie hδ_le hδ0 hδ n x
  have hLb : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n L).toSection x) ≤ Kl n * W :=
    hl g₁ P htie hδ_le hδ0 hδ hsup n x
  have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n ((-2 : ℝ) • R)).toSection x) =
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x) := by
    rw [l1IcgSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, riemannianFiberNormSq_smul]
    norm_num
  rw [iteratedCovGrad_add (I := I) g₀ 3 2 n ((-2 : ℝ) • R) L,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (2 + n) x _ _) ?_
  rw [hsm]
  calc 2 * (4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x)) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 2 n L).toSection x)
      ≤ 2 * (4 * (Kr n * W)) + 2 * (Kl n * W) := by linarith [hRb, hLb]
    _ = (8 * Kr n + 2 * Kl n) * W := by ring

end DifferentialGeometry.Integral.Connection

end
