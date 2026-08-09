import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.TameMarkWin
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SelfLowCapWindows

/-!
# The quadratic zero-order arms with their `∇P` factors kept explicit

`SelfLowCapWindows.lean` produces each `selfLow_split` summand's window in the
`∇P`-**capped** currency.  That currency spends both caps inside `shiftConst`, so
its constants have `Λ`-degree growing with the order — fatal for the tame
deliverable, which needs a constant affine in `‖∇P‖²_∞`.

This module re-derives the same trees in the **marked** currency of
`TameMarkWin.lean`, where the two `∇P` factors of a quadratic arm stay visible
and **no cap is spent at all**: the resulting constants are state-free.

Currently covered: the `A·A` arm `ricciAAArm` (`ricciAAMark`).  The chain is a
one-for-one re-run of `ricciAACap` with `capOfArm ↦ mkOfTop`:

```
connDiffSection      topSeparated  -->  u = 1   (mkOfTop; NO cap)
  slotExtend ×2, reindex           -->  u = 1   (insertion field)
  slotExtend ×1, reindex           -->  u = 1   (inner insertion field)
permCoeff (Fin 3 / Fin 4)          -->  u = 0   (mkOfBnd)
  aaCoreP / aaCore = perm ⋆ (Ins ⋆ (perm ⋆ Inn))
                                   -->  u = 2   (mkApp: the marks ADD)
ricciAAKer = Σ six pieces          -->  u = 2   (mkAdd, mkReindex)
fourTraceCast                      -->  u = 0   (mkOfWin, offset `+1`)
ricciAAArm = cast ⋆ ricciAAKer     -->  u = 2   ✓
```

The load-bearing input is `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`:
it already presents `∇ʲ(connDiffSection)` as `Ktop·|∇^{j+1}P|²` plus residual
monomials `|∇^{j-k}P|²·grid(k+1)`, every one of which carries an EXPLICIT jet of
the state of order at least one and has total weight exactly `j + 1`.  That is a
once-marked window; the ordinary `atgw bP (j+2)` window of the same arm is not,
because it also admits the bare constant and the unaccompanied top jet.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### The connection difference, once marked -/

set_option linter.unusedVariables false in
/-- **The connection difference carries an explicit `∇P` factor.**

`|∇ʲ(connDiffSection g₁ g₀)|²(x) ≤ Kcd j · markGrid (bP x) 1 j`: every monomial
of the bound has an explicit factor `|∇^cP|²` with `c ≥ 1` and total weight
exactly `j + 1`.  This is `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
read in the marked currency, and it is the entry point of the whole tame chain —
`rfns_iCG_connDiffSection_atgw_rf`, the same arm's ordinary window, has thrown
the mark away. -/
theorem connDiffMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kcd : ℕ → ℝ, (∀ j, 0 ≤ Kcd j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P
          (connDiffSection (I := I) g₁ g₀) 1 Kcd := by
  classical
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hts⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => 2 * Ktop + (2 * Kc j) * j, fun j => by
    have := hKc_nn j; positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  refine mkOfTop (I := I) (M := M) g₀ P _ (Ktop := 2 * Ktop) (by linarith)
    (Kc := fun j => 2 * Kc j) (fun j => by have := hKc_nn j; linarith) ?_
  intro j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  obtain ⟨h1, h2⟩ := hts g₁ P htie hδ_le hδ0 hδ j x
  have hsplit_eq :
      (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x =
        Hd.toSection x +
          (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x := by
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]; abel
  rw [hsplit_eq]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
    (Hd.toSection x) _) ?_
  have h1' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Ktop * gridBase (I := I) (M := M) g₀ P x (j + 1) := h1
  have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) ≤
      Kc j * ∑ k ∈ Finset.range j,
        gridBase (I := I) (M := M) g₀ P x (j - k) *
          Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) (k + 1) := h2
  linarith [h1', h2']

/-! ### The `A·A` arm -/

set_option linter.unusedVariables false in
/-- **The `A·A` Ricci arm in the marked currency: two explicit `∇P` factors.**

`|∇ⁱ(ricciAAArm g₀ g₁)|²(x) ≤ K i · markGrid (bP x) 2 i` with `K` **state-free** —
no `Λ` and no Sobolev radius appear anywhere in the statement.  Every monomial of
the bound carries two explicit jets of the state of order at least one and has
total weight at most `i + 2`, so the out-of-budget single jet `|∇^{i+2}P|²` does
not occur.

Compare `ricciAACap`, whose constant is `foldConst` of `shiftConst Λ (i+1)`
factors — `Λ`-degree `3(i+1)`, i.e. degree `6(i+1)` in `‖T‖_{H³}`.  The degree is
gone here because no monomial is ever re-based: the marks are carried, not
paid. -/
theorem ricciAAMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P
          (ricciAAArm (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connDiffMark (I := I) (M := M) g₀ hδ₀
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
  set KInn : ℕ → ℝ := fun i => fr * Kcd i with hKInn_def
  have hKInn_nn : ∀ i, 0 ≤ KInn i := fun i => mul_nonneg hfr_nn (hKcd_nn i)
  set KIns : ℕ → ℝ := fun i => fr * (fr * Kcd i) with hKIns_def
  have hKIns_nn : ∀ i, 0 ≤ KIns i := fun i =>
    mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKcd_nn i))
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
  have hK94_nn : ∀ i, 0 ≤ 94 * KQ i := fun i => by have := hKQ_nn i; linarith
  refine ⟨foldConst (E := E) 0 0 Kft (fun i => 94 * KQ i),
    fun i => foldConst_nn (u := 0) (v := 0) hKft_nn hK94_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hcdP := hcd g₁ P htie hδ_le hδ0 hδ
  -- the two permutation coefficients, state-free, unmarked
  have hP4 : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) 0 SP4 := by
    intro ρ
    refine mkMono (I := I) (M := M) g₀ P (fun i => ?_)
      (mkOfBnd (I := I) (M := M) g₀ P _ (fun i => hS4_nn ρ i) (fun i x => hS4 ρ i x))
    exact Finset.single_le_sum (f := fun r => S4 r i)
      (fun r _ => hS4_nn r i) (Finset.mem_univ ρ)
  have hP3 : ∀ ρ : Equiv.Perm (Fin 3),
      HasMarkWin (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) 0 SP3 := by
    intro ρ
    refine mkMono (I := I) (M := M) g₀ P (fun i => ?_)
      (mkOfBnd (I := I) (M := M) g₀ P _ (fun i => hS3_nn ρ i) (fun i x => hS3 ρ i x))
    exact Finset.single_le_sum (f := fun r => S3 r i)
      (fun r _ => hS3_nn r i) (Finset.mem_univ ρ)
  -- the two insertions, each once marked
  have hInn : HasMarkWin (I := I) (M := M) g₀ P
      (connDiffContrInsertionInnerField (I := I) g₀ g₁) 1 KInn := by
    refine mkCongr (I := I) (M := M) g₀ P
      (connDiffContrInsertionInnerField_eq_reindex_slotExtend (I := I) (M := M) g₀ g₁) ?_
    exact mkReindex (I := I) (M := M) g₀ P innerCoreInPerm10
      (mkSlotExt (I := I) (M := M) g₀ P hcdP)
  have hIns : HasMarkWin (I := I) (M := M) g₀ P
      (connDiffContrInsertionField (I := I) g₀ g₁) 1 KIns := by
    refine mkCongr (I := I) (M := M) g₀ P
      (connDiffContrInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁) ?_
    exact mkReindex (I := I) (M := M) g₀ P coreInPerm201
      (mkSlotExt (I := I) (M := M) g₀ P (mkSlotExt (I := I) (M := M) g₀ P hcdP))
  -- the two shapes, each twice marked
  have hShapeA : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasMarkWin (I := I) (M := M) g₀ P
        (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') 2 KA := by
    intro ρ ρ'
    have hinner : HasMarkWin (I := I) (M := M) g₀ P
        (appCcRS (I := I) (M := M) g₀ 2 3 3 (permCoeff (I := I) (M := M) g₀ ρ')
          (connDiffContrInsertionInnerField (I := I) g₀ g₁)) 1 KIC := by
      simpa using mkApp (I := I) (M := M) g₀ P _ _ hSP3_nn hKInn_nn (hP3 ρ') hInn
    have hmid : HasMarkWin (I := I) (M := M) g₀ P
        (appCcRS (I := I) (M := M) g₀ 2 3 4
          (connDiffContrInsertionField (I := I) g₀ g₁)
          (appCcRS (I := I) (M := M) g₀ 2 3 3 (permCoeff (I := I) (M := M) g₀ ρ')
            (connDiffContrInsertionInnerField (I := I) g₀ g₁))) 2 KMA := by
      simpa using mkApp (I := I) (M := M) g₀ P _ _ hKIns_nn hKIC_nn hIns hinner
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hSP4_nn hKMA_nn (hP4 ρ) hmid
  have hShapeB : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) 2 KB := by
    intro ρ
    have hmid : HasMarkWin (I := I) (M := M) g₀ P
        (appCcRS (I := I) (M := M) g₀ 2 3 4
          (connDiffContrInsertionField (I := I) g₀ g₁)
          (connDiffContrInsertionInnerField (I := I) g₀ g₁)) 2 KMB := by
      simpa using mkApp (I := I) (M := M) g₀ P _ _ hKIns_nn hKInn_nn hIns hInn
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hSP4_nn hKMB_nn (hP4 ρ) hmid
  have hA' : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasMarkWin (I := I) (M := M) g₀ P (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') 2 KQ :=
    fun ρ ρ' => mkMono (I := I) (M := M) g₀ P
      (fun i => by have := hKB_nn i; simp only [hKQ_def]; linarith) (hShapeA ρ ρ')
  have hB' : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) 2 KQ :=
    fun ρ => mkMono (I := I) (M := M) g₀ P
      (fun i => by have := hKA_nn i; simp only [hKQ_def]; linarith) (hShapeB ρ)
  -- the six pieces, summed
  have hKer : HasMarkWin (I := I) (M := M) g₀ P
      (ricciAAKer (I := I) (M := M) g₀ g₁) 2 (fun i => 94 * KQ i) := by
    refine mkCongr (I := I) (M := M) g₀ P
      (aaKerSplit (I := I) (M := M) g₀ g₁) ?_
    refine mkMono (I := I) (M := M) g₀ P ?_
      (mkAdd (I := I) (M := M) g₀ P
        (mkAdd (I := I) (M := M) g₀ P
          (mkAdd (I := I) (M := M) g₀ P
            (mkAdd (I := I) (M := M) g₀ P
              (mkAdd (I := I) (M := M) g₀ P (hA' _ _)
                (mkReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' _ _)))
              (hA' _ _))
            (mkReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hB' _)))
          (hB' _))
        (mkReindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' _ _)))
    intro i
    exact le_of_eq (by ring)
  -- the four-trace cast: no derivative of the state, unmarked
  have hFT : HasMarkWin (I := I) (M := M) g₀ P
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁) 0 Kft :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun n y => hft g₁ P htie hδ_le hδ0 hδ n y)
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hKft_nn hK94_nn hFT hKer

set_option linter.unusedVariables false in
/-- **The `A·A` arm's tame `L²` jet bound — the deliverable shape.**

```
‖∇ⁱ(ricciAAArm g₀ g₁)‖²  ≤  (K₀ i + K₂ i · ‖P‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲP‖²)
```

with `K₀, K₂` constants of the background metric and the order alone — chosen
BEFORE the state, no Sobolev radius `R₀`, no opaque cap, no Galerkin index, and
exactly ONE power of `‖P‖²_{H³}` (here written explicitly as
`∑_{j < 3} ‖∇^{1+j}P‖²`, the jet form `gradCapLin` produces).

The two inputs are the marked window `ricciAAMark` (state-free constants, the two
`∇P` factors explicit) and the tame integration `markJet`; the `∇P` cap is spent
exactly once, at the very end, through `gradCapLin`.  The only hypothesis on the
state beyond the standard fibre-operator bound is the δ-anchor `|P|_∞ ≤ 1`, which
at `finrank = 3` is implied by `‖P‖_∞ ≤ finrank/3`.

Compare `ricciAACap`-then-`capJet`: same left-hand side, but a constant of
`Λ`-degree `3(i+1)`, i.e. degree `6(i+1)` in `‖P‖_{H³}`. -/
theorem ricciAAJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (ricciAAArm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KA, hKA_nn, hAA⟩ := ricciAAMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KA i * K0' i, fun i => KA i * K0' i * cg,
    fun i => mul_nonneg (hKA_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKA_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (ricciAAArm (I := I) (M := M) g₀ g₁) hKA_nn
    (hAA g₁ P htie hδ_le hδ0 hδ) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

end DifferentialGeometry.Integral.Connection

end

