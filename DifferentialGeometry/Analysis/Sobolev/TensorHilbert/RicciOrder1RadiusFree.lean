import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AtgwArmFold

/-!
# Radius-free grid currency for the order-one Ricci kernel

The order-one arm of the linearized Ricci operator is *linear* in the
connection difference — `kernelField_eq_neg_arm_combination` exhibits
`linearizedRicciConnDiffOrder1KernelField g₀ g₁` as five slot-permuted copies of
the single insertion field `connDiffContrInsertionField g₀ g₁`, each carrying
exactly one `connDiffSection`.  That is what separates it from the order-zero
arm, where the `A·A` term is quadratic and no radius-free bound exists.

This module converts that structure into the `antidiagonalTupleGridWindow`
currency that the radius-free composer `AtgwArmFold` consumes:

* `permAppEqRs` — the public bridge `appCcRS (slotPermCc σ) S = rsDomDomCongrSection σ S`
  (`permApp_eq_rs` lives `private` inside the read-only low-base action file).
* `ricci1Split` — the split rewritten with `rsDomDomCongrSection` in place of
  the `appCcRS`/`slotPermCc` pair, which is the form whose fibre jets are a
  pointwise *isometry* of the original's.
* `ricciKerAtgw` — the resulting radius-free pointwise window, at offset `+2`.

Offset `+2` (not `+3`) is the whole point: the kernel costs exactly one
derivative of the state, so folding it against an order-zero-capped arm lands on
`range (i + 2)`, the budget the low-base `C1` jet tower spends.
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

set_option linter.unusedSectionVars false in
/-- **Applying the parallel slot-permutation field is the slot permutation.**

Public re-derivation of the `private` `permApp_eq_rs` of the read-only low-base
action module.  It is what lets a permuted arm be recognised as a fibre isometry
of its argument at every jet order. -/
theorem permAppEqRs (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    appCcRS (I := I) (M := M) g r s s
        (slotPermCc (I := I) (M := M) g σ) S =
      rsDomDomCongrSection (I := I) (M := M) g r s σ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  rw [appCcRS_toSection, ContinuousLinearMap.comp_apply,
    rsDomDomCongrSection_toSection]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) σ x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (S.toSection x)) D)
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    toModel_rsDomDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- **The order-one Ricci kernel as five slot permutations of one insertion.**

`ricci1Split` is `kernelField_eq_neg_arm_combination` with the
`appCcRS`/`slotPermCc` pairs collapsed to `rsDomDomCongrSection`, which is the
form in which each summand is a *pointwise fibre isometry* of
`connDiffContrInsertionField g₀ g₁` at every covariant jet order. -/
theorem ricci1Split (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁ =
      -(reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0312
            (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0213
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120
        + rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm2301
            (connDiffContrInsertionField (I := I) g₀ g₁)
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1302
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1203
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120) := by
  rw [kernelField_eq_neg_arm_combination (I := I) (M := M) g₀ g₁]
  simp only [permAppEqRs]

omit [BoundarylessManifold I M] in
private lemma icgSmul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma rfnsSmul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
/-- Negation is a pointwise fibre isometry at every jet order. -/
private lemma rfnsNegIcg (g : SmoothRiemannianMetric I M) {r s : ℕ} (l : ℕ) (x : M)
    (X : SmoothCcTensor g r s) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l (-X)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l X).toSection x) := by
  have hneg : (-X) = (-1 : ℝ) • X := by
    rw [neg_smul, one_smul]
  rw [hneg, icgSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, rfnsSmul]
  norm_num

set_option linter.unusedSectionVars false in
/-- The permuted/reindexed kernel arms are pointwise fibre isometries of the
insertion field at every jet order. -/
private lemma rfnsArmEq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 4 l
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) :=
  rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 4 σ
    (connDiffContrInsertionField (I := I) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ
      (connDiffContrInsertionField (I := I) g₀ g₁))
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the order-one insertion field.**

`|∇ˡ(connDiffContrInsertionField g₀ g₁)|²(x) ≤ Cins l · atgw(bP)(l + 2)`: the
insertion is a reindexed double slot extension of `connDiffSection`, so it
inherits the connection difference's offset `+2` window at the cost of two
dimension factors. -/
theorem insertAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Cins : ℕ → ℝ, (∀ l, 0 ≤ Cins l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 4 l
              (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
          Cins l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := rfns_iCG_connDiffSection_atgw_rf (I := I) (M := M) g₀ hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨fun l => (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Ccd l),
    fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCcd_nn l)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  rw [connDiffContrInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (slotExtend (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
    coreInPerm201 l x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) l x) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
      (connDiffSection (I := I) g₁ g₀) l x) hfr_nn) ?_
  have hgb : Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (l + 2) =
      Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := rfl
  rw [hgb]
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) with hW_def
  calc (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x))
      ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (Ccd l * W)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hcd g₁ P htie hδ_le hδ0 hδ l x) hfr_nn) hfr_nn
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * Ccd l) * W := by ring

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the order-one Ricci kernel.**

`|∇ˡ(linearizedRicciConnDiffOrder1KernelField g₀ g₁)|²(x) ≤ Kk l · atgw(bP)(l + 2)`.

The kernel is five permuted copies of the insertion field, so the offset stays
at `+2` — one derivative of the state — and only a fixed combinatorial factor
(`46`, from four binary applications of `2`-subadditivity) is paid. -/
theorem ricciKerAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kk : ℕ → ℝ, (∀ l, 0 ≤ Kk l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 4 l
              (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection x) ≤
          Kk l * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Cins, hCins_nn, hins⟩ := insertAtgw (I := I) (M := M) g₀ hδ₀
  refine ⟨fun l => 46 * Cins l, fun l => by have := hCins_nn l; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set O : SmoothCcTensor g₀ 3 4 := connDiffContrInsertionField (I := I) g₀ g₁ with hO_def
  set A0 : SmoothCcTensor g₀ 3 4 :=
    reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0312 O) kInPerm102 with hA0_def
  set A1 : SmoothCcTensor g₀ 3 4 :=
    reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm0213 O) kInPerm120 with hA1_def
  set A2 : SmoothCcTensor g₀ 3 4 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm2301 O with hA2_def
  set A3 : SmoothCcTensor g₀ 3 4 :=
    reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1302 O) kInPerm102 with hA3_def
  set A4 : SmoothCcTensor g₀ 3 4 :=
    reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 kOutPerm1203 O) kInPerm120 with hA4_def
  -- abbreviation for the pointwise fibre jet of a `(3,4)` field at order `l`
  set F : SmoothCcTensor g₀ 3 4 → ℝ := fun X =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 3 4 l X).toSection x) with hF_def
  have hFnn : ∀ X, 0 ≤ F X := fun X => riemannianFiberNormSq_nonneg _ _ _ _ _
  have hFadd : ∀ X Y : SmoothCcTensor g₀ 3 4, F (X + Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    simp only [hF_def]
    rw [iteratedCovGrad_add (I := I) g₀ 3 4 l X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (4 + l) x _ _
  -- every arm has the insertion field's fibre jet
  have harm : ∀ (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      F (reindexCoeffGen (I := I) (M := M) g₀ 3 4
        (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ O) ρ) = F O := by
    intro σ ρ
    simp only [hF_def]
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
      (rsDomDomCongrSection (I := I) (M := M) g₀ 3 4 σ O) ρ l x]
    exact rfnsArmEq (I := I) (M := M) g₀ g₁ σ l x
  have h0 : F A0 = F O := harm _ _
  have h1 : F A1 = F O := harm _ _
  have h2 : F A2 = F O := rfnsArmEq (I := I) (M := M) g₀ g₁ kOutPerm2301 l x
  have h3 : F A3 = F O := harm _ _
  have h4 : F A4 = F O := harm _ _
  have hOnn : 0 ≤ F O := hFnn O
  have hsum : F (A0 + A1 + A2 + A3 + A4) ≤ 46 * F O := by
    have s01 := hFadd A0 A1
    have s012 := hFadd (A0 + A1) A2
    have s0123 := hFadd (A0 + A1 + A2) A3
    have s01234 := hFadd (A0 + A1 + A2 + A3) A4
    rw [h0, h1] at s01
    rw [h2] at s012
    rw [h3] at s0123
    rw [h4] at s01234
    linarith
  have hker : F (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) =
      F (A0 + A1 + A2 + A3 + A4) := by
    rw [ricci1Split (I := I) (M := M) g₀ g₁]
    simp only [hF_def, ← hO_def, ← hA0_def, ← hA1_def, ← hA2_def, ← hA3_def, ← hA4_def]
    exact rfnsNegIcg (I := I) (M := M) g₀ l x (A0 + A1 + A2 + A3 + A4)
  show F (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) ≤ _
  rw [hker]
  refine hsum.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hins g₁ P htie hδ_le hδ0 hδ l x) (by norm_num)

end DifferentialGeometry.Integral.Connection

end
