import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.TameArmJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0VBRefold

/-!
# The `lieCorr0` summands with their `∇P` factors kept explicit

`SelfLowCapWindows.lean` produces the `lieCorr0` summands of `selfLow_split` in
the `∇P`-**capped** currency, whose constants have `Λ`-degree growing with the
order.  `TameArmJets.lean` re-derives the Ricci `A·A` arm in the **marked**
currency of `TameMarkWin.lean`, where the two `∇P` factors of a quadratic arm
stay visible and no cap is spent.  This module does the same for the two
`lieCorr0` summands that are quadratic in the connection difference, `lc0VB` and
`lc0AMix`, and for the linear one, `lc0Riem`.

The entry point of both quadratic chains is the **marked `wXi`**.  At the base
background the tree already proves that `wXi` has no state-free part:
`wXi_self_eq` says `wXi g₀ g₁ g₀ = connDiffLoweredCc g₀ g₁` *as tensors*, so the
`T`-free per-order constant that `rfns_iCG_wXi_atgw_rf` folds for the `g_bg` half
vanishes identically at the `lc0VB`/`lc0AMix` call sites.  Composing that with
the valence bridge `connLow_rfns` and the marked connection difference
`connDiffMark` gives `wXi` a once-marked window with **state-free** constants.

```
wXi g₀ g₁ g₀ = connDiffLoweredCc g₀ g₁     -->  u = 1   (wXiMark)
  mcd = wXi + ½Φ_A ⋆ wXi + ½Φ_B ⋆ wXi      -->  u = 1   (mcdMark; Φ is `F(P)`, u = 0)
  wOmega = cometricCast ⋆ wXi              -->  u = 1   (wOmegaMark)
  ipLowCc (wOmega)                         -->  u = 1   (ipLowMark)
vbMcdArm                                   -->  u = 1   (dominated by mcd)
  lc0VBPass = vbMcdArm ⋆ ipLowCc(wOmega)   -->  u = 2   (marks ADD)
lc0RiemLive                                -->  u = 0   (mkOfWin, offset `+1`)
  lc0VB = 2 · lc0RiemLive ⋆ lc0VBPass      -->  u = 2   ✓
lc0AMix = 2·(half + half), each half
  = trace ⋆ trace ⋆ mcd ⋆ trace ⋆ mcd      -->  u = 2   ✓  (at `g_bg = g₀`)
lc0Riem = -(lc0RiemLive ⋆ lc0RiemPass)     -->  u = 0      (linear; no `∇P` at all)
```

The only hypothesis beyond the standard fibre-operator bound is the δ-anchor
`|P|_∞ ≤ 1`, needed because the `mcd` correction operator `b4Phi` carries an
order-zero factor of the state; at `finrank = 3` it is implied by
`‖P‖_∞ ≤ finrank/3`.

**`lc0AMix` is stated at `g_bg = g₀` only, and this is sharp.**  At a general
DeTurck background `wXi g₀ g₁ g_bg = connDiffLoweredCc g₀ g₁ −
connDiffLoweredCc g₀ g_bg` retains a state-free summand, so the `mcd(·, g_bg)`
factor of the five-factor product is only `u = 0` and the summand is *affine*,
not quadratic, in `∇P`.  `g_bg = g₀` is what the consumer
(`ShortTime/LowRegBgH2.lean`) uses.
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

/-! ### The lowered connection difference at the base background, once marked -/

set_option linter.unusedVariables false in
/-- **`wXi` at the base background carries an explicit `∇P` factor.**

`|∇ⁱ(wXi g₀ g₁ g₀)|²(x) ≤ Kcd i · markGrid (bP x) 1 i`, with `Kcd` **state-free**
— the same constant `connDiffMark` produces, because at `g_bg = g₀` the two
tensors are literally equal (`wXi_self_eq`) and their fibre jets agree with those
of `connDiffSection` (`connLow_rfns`).

Compare `rfns_iCG_wXi_atgw_rf`, which weakens this to the unmarked
`atgw bP (i + 2)` window AND folds a `T`-free per-order constant for the `g_bg`
half — here that constant is not merely small, it is absent: the `g_bg` half is
the zero tensor. -/
theorem wXiMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P (wXi (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connDiffMark (I := I) (M := M) g₀ hδ₀
  refine ⟨Kcd, hKcd_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  refine mkCongr (I := I) (M := M) g₀ P (wXi_self_eq (I := I) (M := M) g₀ g₁) ?_
  intro i x
  rw [connLow_rfns (I := I) (M := M) g₀ g₁ i x]
  exact hcd g₁ P htie hδ_le hδ0 hδ i x

set_option linter.unusedVariables false in
/-- **The `g₁`-lowered connection difference at the base background, once
marked.**

`b4_mcd_eq` writes it as `wXi + ½ Φ_A ⋆ wXi + ½ Φ_B ⋆ wXi`, where the correction
operator `Φ` is built from the state with **no** derivative — an `F(P)`-type
coefficient, entering unmarked through its `atgw bP (l + 1)` window.  So the
whole arm inherits `wXi`'s single mark.

The δ-anchor `|P|_∞ ≤ 1` is what makes the constant state-free: `b4_phi_atgw`'s
constant is affine in `Λ₀²`, and it is evaluated at `Λ₀ = 1`. -/
theorem mcdMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P
          (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := wXiMark (I := I) (M := M) g₀ hδ₀
  choose Kphi hKphi_nn hphi using
    (fun σ : Equiv.Perm (Fin 5) =>
      b4_phi_atgw (I := I) (M := M) g₀ σ (Λ₀ := 1) zero_le_one)
  set SPhi : ℕ → ℝ := fun i => ∑ σ : Equiv.Perm (Fin 5), Kphi σ i with hSPhi_def
  have hSPhi_nn : ∀ i, 0 ≤ SPhi i := fun i =>
    Finset.sum_nonneg (fun σ _ => hKphi_nn σ i)
  have hsingle : ∀ (σ : Equiv.Perm (Fin 5)) (n : ℕ), Kphi σ n ≤ SPhi n := by
    intro σ n
    simp only [hSPhi_def]
    exact Finset.single_le_sum (f := fun r => Kphi r n)
      (fun r _ => hKphi_nn r n) (Finset.mem_univ σ)
  have hF_nn : ∀ i, 0 ≤ foldConst (E := E) 0 0 SPhi Kwx i := fun i =>
    foldConst_nn (u := 0) (v := 0) hSPhi_nn hKwx_nn i
  refine ⟨fun i => 2 * Kwx i +
      2 * (2 * ((1 / 2 : ℝ) ^ 2 * foldConst (E := E) 0 0 SPhi Kwx i) +
        2 * ((1 / 2 : ℝ) ^ 2 * foldConst (E := E) 0 0 SPhi Kwx i)), fun i => by
    have := hKwx_nn i; have := hF_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hWX : HasMarkWin (I := I) (M := M) g₀ P
      (wXi (I := I) (M := M) g₀ g₁ g₀) 1 Kwx := hwx g₁ P htie hδ_le hδ0 hδ
  have hbnn : ∀ y : M, ∀ j, 0 ≤ gridBase (I := I) (M := M) g₀ P y j :=
    fun y => gridBase_nn (I := I) (M := M) g₀ P y
  -- the correction terms, stated for a generic operator so `b4Phi` is never named
  have hcorr : ∀ Φ : SmoothCcTensor g₀ 3 3,
      (∀ (n : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + n) y
            ((iteratedCovGrad (I := I) g₀ 3 3 n Φ).toSection y) ≤
          SPhi n * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (n + 1)) →
      HasMarkWin (I := I) (M := M) g₀ P
        (appCc (I := I) (M := M) g₀ 3 3 Φ (wXi (I := I) (M := M) g₀ g₁ g₀)) 1
        (foldConst (E := E) 0 0 SPhi Kwx) := by
    intro Φ hwin
    rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 3 3]
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hSPhi_nn hKwx_nn
      (mkOfWin (I := I) (M := M) g₀ P _ hwin) hWX
  refine mkCongr (I := I) (M := M) g₀ P
    (b4_mcd_eq (I := I) (M := M) g₀ g₁ g₀ P htie) ?_
  refine mkAdd (I := I) (M := M) g₀ P hWX
    (mkAdd (I := I) (M := M) g₀ P
      (mkSmul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
        (hcorr _ (fun n y => le_trans (hphi _ P hsup n y)
          (mul_le_mul_of_nonneg_right (hsingle _ n)
            (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _)))))
      (mkSmul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
        (hcorr _ (fun n y => le_trans (hphi _ P hsup n y)
          (mul_le_mul_of_nonneg_right (hsingle _ n)
            (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _))))))

/-! ### The `wOmega` covector and its interior product -/

set_option linter.unusedVariables false in
/-- **The `g₀`-lowered DeTurck covector at the base background, once marked.**

`wOmega = cometricCastG0 ⋆ wXi`; the moving cometric cast costs no derivative of
the state (its radius-free window sits at `bP`-offset `+1`), so the product keeps
`wXi`'s single mark. -/
theorem wOmegaMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P
          (wOmega (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := wXiMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := rfns_iCG_cometricCastG0_atgw_rf (I := I) (M := M) g₀ hδ₀
  refine ⟨foldConst (E := E) 0 0 Kcg Kwx,
    fun i => foldConst_nn (u := 0) (v := 0) hKcg_nn hKwx_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hCast : HasMarkWin (I := I) (M := M) g₀ P
      (cometricCastG0 (I := I) g₀ g₁) 0 Kcg :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun l y => hcg g₁ P htie hδ_le hδ0 hδ l y)
  refine mkCongr (I := I) (M := M) g₀ P
    (show wOmega (I := I) (M := M) g₀ g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (wXi (I := I) (M := M) g₀ g₁ g₀) from by
      rw [appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 3 1, wOmega]) ?_
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hKcg_nn hKwx_nn hCast
    (hwx g₁ P htie hδ_le hδ0 hδ)

set_option linter.unusedVariables false in
/-- **The interior product preserves the mark count.**

`rfns_icg_ipLow_le` bounds `∇ˡ(ipLowCc g₀ om)` by the jets of `om` up to order
`l`; the marked window is monotone in its level, so the whole sum collapses onto
level `l` and the mark count is untouched.  The trace factor is `∇`-parallel and
state-free, so it contributes no mark. -/
theorem ipLowMark (g₀ : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ l, 0 ≤ c l) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {u : ℕ} (om : SmoothCcTensor g₀ 0 1)
        {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
        HasMarkWin (I := I) (M := M) g₀ P om u K →
        HasMarkWin (I := I) (M := M) g₀ P (ipLowCc (I := I) (M := M) g₀ om) u
          (fun l => c l * ∑ m ∈ Finset.range (l + 1), K m) := by
  classical
  obtain ⟨c, hc_nn, hip⟩ := rfns_icg_ipLow_le (I := I) (M := M) g₀
  refine ⟨c, hc_nn, ?_⟩
  intro P u om K hK hom l x
  refine le_trans (hip om l x) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hc_nn l)
  have hbnn : ∀ j, 0 ≤ gridBase (I := I) (M := M) g₀ P x j :=
    gridBase_nn (I := I) (M := M) g₀ P x
  calc (∑ m ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 1 m om).toSection x))
      ≤ ∑ m ∈ Finset.range (l + 1),
          K m * Combinatorics.markGrid (gridBase (I := I) (M := M) g₀ P x) u l := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        refine le_trans (hom m x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hK m)
        exact Combinatorics.markGrid_mono _ hbnn u
          (by rw [Finset.mem_range] at hm; omega)
    _ = (∑ m ∈ Finset.range (l + 1), K m) *
          Combinatorics.markGrid (gridBase (I := I) (M := M) g₀ P x) u l := by
        rw [Finset.sum_mul]

/-! ### `lc0VB`: the vector-bilinear summand -/

set_option linter.unusedVariables false in
/-- **`lc0VB` in the marked currency: two explicit `∇P` factors.**

`|∇ⁱ(lc0VB g₀ g₁)|²(x) ≤ K i · markGrid (bP x) 2 i` with `K` **state-free** — no
`Λ`, no Sobolev radius.  The two marks are the two connection differences of the
product `lc0RiemLive ⋆ (vbMcdArm ⋆ ipLowCc (wOmega))`: `vbMcdArm` is dominated by
the lowered connection difference `mcd`, and `wOmega` is the cometric trace of
`wXi`; the live cometric arm and the interior-product trace carry no derivative
of the state.

Compare `lc0VBCapAtgw`, whose constant is a `foldConst` of `shiftConst Λ (i+1)`
factors.  The δ-anchor `|P|_∞ ≤ 1` enters only through `mcdMark`. -/
theorem lc0VBMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P (lc0VB (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := mcdMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨KΩ, hKΩ_nn, hΩ⟩ := wOmegaMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨cip, hcip_nn, hip⟩ := ipLowMark (I := I) (M := M) g₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := rfns_iCG_cometricCastG0_atgw_rf (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun m => fr * Kmcd m with hKA_def
  have hKA_nn : ∀ m, 0 ≤ KA m := fun m => mul_nonneg hfr_nn (hKmcd_nn m)
  set KB : ℕ → ℝ := fun l => cip l * ∑ m ∈ Finset.range (l + 1), KΩ m with hKB_def
  have hKB_nn : ∀ l, 0 ≤ KB l :=
    fun l => mul_nonneg (hcip_nn l) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))
  set KC : ℕ → ℝ := fun m => fr * Kcg m with hKC_def
  have hKC_nn : ∀ m, 0 ≤ KC m := fun m => mul_nonneg hfr_nn (hKcg_nn m)
  set KPass : ℕ → ℝ := foldConst (E := E) 0 0 KA KB with hKPass_def
  have hKPass_nn : ∀ n, 0 ≤ KPass n := fun n =>
    foldConst_nn (u := 0) (v := 0) hKA_nn hKB_nn n
  refine ⟨fun i => (2 : ℝ) ^ 2 * foldConst (E := E) 0 0 KC KPass i, fun i => by
    have := foldConst_nn (E := E) (u := 0) (v := 0) hKC_nn hKPass_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  -- the head of the passenger, dominated by `mcd`
  have hA : HasMarkWin (I := I) (M := M) g₀ P (vbMcdArm (I := I) (M := M) g₀ g₁) 1 KA := by
    intro m y
    refine le_trans (vbMcdArm_rfns_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKA_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hmcd g₁ P htie hδ_le hδ0 hδ hP0 m y) hfr_nn
  -- the interior-product tail of the passenger
  have hB : HasMarkWin (I := I) (M := M) g₀ P
      (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀)) 1 KB :=
    hip P _ hKΩ_nn (hΩ g₁ P htie hδ_le hδ0 hδ)
  -- the live cometric arm, no derivative of the state
  have hC : HasMarkWin (I := I) (M := M) g₀ P
      (lc0RiemLive (I := I) (M := M) g₀ g₁) 0 KC := by
    refine mkOfWin (I := I) (M := M) g₀ P _ (fun m y => ?_)
    refine le_trans (lc0RiemLive_rfns_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKC_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcg g₁ P htie hδ_le hδ0 hδ m y) hfr_nn
  -- the two folds
  have hPass : HasMarkWin (I := I) (M := M) g₀ P
      (lc0VBPass (I := I) (M := M) g₀ g₁) 2 KPass := by
    refine mkCongr (I := I) (M := M) g₀ P (vbSplit (I := I) (M := M) g₀ g₁) ?_
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hKA_nn hKB_nn hA hB
  refine mkCongr (I := I) (M := M) g₀ P (lc0VB_eq_app (I := I) (M := M) g₀ g₁) ?_
  refine mkSmul (I := I) (M := M) g₀ P (2 : ℝ) ?_
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hKC_nn hKPass_nn hC hPass

set_option linter.unusedVariables false in
/-- **`lc0VB`'s tame `L²` jet bound — the deliverable shape.**

```
‖∇ⁱ(lc0VB g₀ g₁)‖²  ≤  (K₀ i + K₂ i · ‖P‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲP‖²)
```

with `K₀, K₂` constants of the background metric and the order alone — chosen
BEFORE the state, no Sobolev radius `R₀`, no opaque cap, no Galerkin index, and
exactly ONE power of `‖P‖²_{H³}`.  The same shape as `ricciAAJet`, produced the
same way: the marked window `lc0VBMark` plus the tame integration `markJet`, the
`∇P` cap being spent exactly once at the end through `gradCapLin`.

Compare `lc0VBCapJet`: same left-hand side and the same `range (i + 2)` budget,
but with a constant of `Λ`-degree growing linearly in `i`. -/
theorem lc0VBJet (hDim : Module.finrank ℝ E = 3)
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
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0VB (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KV, hKV_nn, hVB⟩ := lc0VBMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KV i * K0' i, fun i => KV i * K0' i * cg,
    fun i => mul_nonneg (hKV_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKV_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
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
    (lc0VB (I := I) (M := M) g₀ g₁) hKV_nn
    (hVB g₁ P htie hδ_le hδ0 hδ hP0) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

/-! ### `lc0AMix`: the five-factor mixed summand -/

set_option linter.unusedVariables false in
/-- **`lc0AMix` at the base background, in the marked currency.**

`amix_refold_rf` writes the summand as two copies of the five-factor product
`trace ⋆ trace ⋆ mcd ⋆ trace ⋆ mcd`.  The three moving traces carry no derivative
of the state (offset `+1` windows, unmarked); the two lowered connection
differences carry one each, and the marks add through the four folds, so the
summand is genuinely twice marked with **state-free** constants.

`g_bg = g₀` is not a convenience: at a general DeTurck background
`wXi g₀ g₁ g_bg = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀ g_bg` keeps a
state-free summand, the outer `mcd` factor is then only `u = 0`, and `lc0AMix` is
affine — not quadratic — in `∇P`.  The consumer (`ShortTime/LowRegBgH2.lean`)
uses `g_bg = g₀`. -/
theorem lc0AMixMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P
          (lc0AMix (I := I) (M := M) g₀ g₁ g₀) 2 K := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := mcdMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ctr2, hCtr2_nn, htr2⟩ := trace_grid_rf (I := I) (M := M) 2 g₀ hδ₀
  obtain ⟨Ctr3, hCtr3_nn, htr3⟩ := trace_grid_rf (I := I) (M := M) 3 g₀ hδ₀
  obtain ⟨Ctr4, hCtr4_nn, htr4⟩ := trace_grid_rf (I := I) (M := M) 4 g₀ hδ₀
  set KM2 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 2 * Kmcd i with hKM2_def
  set KM3 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 3 * Kmcd i with hKM3_def
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKM2_nn : ∀ i, 0 ≤ KM2 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKmcd_nn i)
  have hKM3_nn : ∀ i, 0 ≤ KM3 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 3) (hKmcd_nn i)
  set Ktail : ℕ → ℝ := foldConst (E := E) 0 0 Ctr3 KM2 with hKtail_def
  have hKtail_nn : ∀ i, 0 ≤ Ktail i := fun i =>
    foldConst_nn (u := 0) (v := 0) hCtr3_nn hKM2_nn i
  set Kmid : ℕ → ℝ := foldConst (E := E) 0 0 KM3 Ktail with hKmid_def
  have hKmid_nn : ∀ i, 0 ≤ Kmid i := fun i =>
    foldConst_nn (u := 0) (v := 0) hKM3_nn hKtail_nn i
  set Ktr4 : ℕ → ℝ := foldConst (E := E) 0 0 Ctr4 Kmid with hKtr4_def
  have hKtr4_nn : ∀ i, 0 ≤ Ktr4 i := fun i =>
    foldConst_nn (u := 0) (v := 0) hCtr4_nn hKmid_nn i
  set Khalf : ℕ → ℝ := foldConst (E := E) 0 0 Ctr2 Ktr4 with hKhalf_def
  have hKhalf_nn : ∀ i, 0 ≤ Khalf i := fun i =>
    foldConst_nn (u := 0) (v := 0) hCtr2_nn hKtr4_nn i
  refine ⟨fun i => (2 : ℝ) ^ 2 * (2 * Khalf i + 2 * Khalf i), fun i => by
    have := hKhalf_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hmcdP : HasMarkWin (I := I) (M := M) g₀ P
      (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) 1 Kmcd :=
    hmcd g₁ P htie hδ_le hδ0 hδ hP0
  -- the three moving traces: no derivative of the state
  have htrace : ∀ (p : ℕ) (C : ℕ → ℝ),
      (∀ (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (gridBase (I := I) (M := M) g₀ P x) k) →
      ∀ σ : Equiv.Perm (Fin (p + 2)),
        HasMarkWin (I := I) (M := M) g₀ P
          (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ) 0 C := by
    intro p C hbd σ
    exact mkOfWin (I := I) (M := M) g₀ P _ (fun i y => hbd σ i y)
  have hT2 : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σ) 0 Ctr2 :=
    htrace 2 Ctr2 (fun σ i x => htr2 g₁ P htie hδ_le hδ0 hδ σ i x)
  have hT3 : HasMarkWin (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ) 0 Ctr3 :=
    htrace 3 Ctr3 (fun σ i x => htr3 g₁ P htie hδ_le hδ0 hδ σ i x) _
  have hT4 : HasMarkWin (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1) 0 Ctr4 :=
    htrace 4 Ctr4 (fun σ i x => htr4 g₁ P htie hδ_le hδ0 hδ σ i x) _
  -- the two lowered connection differences, extended into their slots
  have hM2 : HasMarkWin (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)) 1 KM2 := by
    rw [hKM2_def]
    exact mkIter (I := I) (M := M) g₀ P 2 hmcdP
  have hM3 : HasMarkWin (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)) 1 KM3 := by
    rw [hKM3_def]
    exact mkIter (I := I) (M := M) g₀ P 3 hmcdP
  -- the four nested folds
  have hhalf : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P
        (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀ σ) 2 Khalf := by
    intro σ
    have htail := mkApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀))
      hCtr3_nn hKM2_nn hT3 hM2
    have hmid := mkApp (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)) _
      hKM3_nn hKtail_nn hM3 htail
    have htr4' := mkApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1) _
      hCtr4_nn hKmid_nn hT4 hmid
    simpa using mkApp (I := I) (M := M) g₀ P
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σ) _ hCtr2_nn hKtr4_nn (hT2 σ) htr4'
  refine mkCongr (I := I) (M := M) g₀ P
    (amix_refold_rf (I := I) (M := M) g₀ g₁ g₀) ?_
  exact mkSmul (I := I) (M := M) g₀ P (2 : ℝ)
    (mkAdd (I := I) (M := M) g₀ P (hhalf lieCorr0AMixPerm2)
      (hhalf (lc0SwapPermRF * lieCorr0AMixPerm2)))

set_option linter.unusedVariables false in
/-- **`lc0AMix`'s tame `L²` jet bound at the base background — the deliverable
shape.**

```
‖∇ⁱ(lc0AMix g₀ g₁ g₀)‖²  ≤  (K₀ i + K₂ i · ‖P‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲP‖²)
```

Constants BEFORE the state, no Sobolev radius, no opaque cap, exactly one power
of `‖P‖²_{H³}`.  Compare `lc0AMixCap`, whose constant carries `shiftConst Λ`
factors from all five arms. -/
theorem lc0AMixJet (hDim : Module.finrank ℝ E = 3)
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
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0AMix (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KX, hKX_nn, hAM⟩ := lc0AMixMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KX i * K0' i, fun i => KX i * K0' i * cg,
    fun i => mul_nonneg (hKX_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKX_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
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
    (lc0AMix (I := I) (M := M) g₀ g₁ g₀) hKX_nn
    (hAM g₁ P htie hδ_le hδ0 hδ hP0) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

/-! ### `lc0Riem`: the fixed-curvature summand -/

set_option linter.unusedVariables false in
/-- **`lc0Riem` in the marked currency: no derivative of the state at all.**

`lc0Riem = −(lc0RiemLive ⋆ lc0RiemPass)`: the live cometric arm costs no
derivative of the state (window at `bP`-offset `+1`) and the passenger is
state-free, so the summand is *linear* and enters at `u = 0`.  Its tame bound
therefore needs no `∇P` cap whatsoever (`lc0RiemJet`, `K₂ = 0`). -/
theorem lc0RiemMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P (lc0Riem (I := I) (M := M) g₀ g₁) 0 K := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := rfns_iCG_cometricCastG0_atgw_rf (I := I) (M := M) g₀ hδ₀
  choose SPass hSPass_nn hSPass using
    (fun l : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 2 (4 + l)
      (iteratedCovGrad (I := I) g₀ 2 4 l (lc0RiemPass (I := I) g₀)))
  set KC : ℕ → ℝ := fun m => (Module.finrank ℝ E : ℝ) * Kcg m with hKC_def
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKC_nn : ∀ m, 0 ≤ KC m := fun m => mul_nonneg hfr_nn (hKcg_nn m)
  refine ⟨foldConst (E := E) 0 0 KC SPass,
    fun i => foldConst_nn (u := 0) (v := 0) hKC_nn hSPass_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hLive : HasMarkWin (I := I) (M := M) g₀ P
      (lc0RiemLive (I := I) (M := M) g₀ g₁) 0 KC := by
    refine mkOfWin (I := I) (M := M) g₀ P _ (fun m y => ?_)
    refine le_trans (lc0RiemLive_rfns_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKC_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcg g₁ P htie hδ_le hδ0 hδ m y) hfr_nn
  have hPass : HasMarkWin (I := I) (M := M) g₀ P (lc0RiemPass (I := I) g₀) 0 SPass :=
    mkOfBnd (I := I) (M := M) g₀ P _ hSPass_nn (fun l y => hSPass l y)
  refine mkCongr (I := I) (M := M) g₀ P (lc0Riem_eq_app (I := I) (M := M) g₀ g₁) ?_
  refine mkNeg (I := I) (M := M) g₀ P ?_
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hKC_nn hSPass_nn hLive hPass

set_option linter.unusedVariables false in
/-- **`lc0Riem`'s tame `L²` jet bound — the deliverable shape with `K₂ = 0`.**

```
‖∇ⁱ(lc0Riem g₀ g₁)‖²  ≤  K₀ i · (1 + ∑_{j < i+2} ‖∇ʲP‖²)
```

no `‖P‖²_{H³}` factor at all, because the summand is linear in the connection
difference.  Compare `lc0Riem_perOrder_rf`, which is radius-free but lands on
`range (i + 3)` — one order over what `selfLow_jet` may spend; the marked
currency recovers the order for free, since an unmarked window is already at
`atgw bP (i + 1)`. -/
theorem lc0RiemJet (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0Riem (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          K0 i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KR, hKR_nn, hRiem⟩ := lc0RiemMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet0 (I := I) (M := M) g₀
  refine ⟨fun i => KR i * K0' i,
    fun i => mul_nonneg (hKR_nn i) (hK0'_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  exact hjet P hP0 (lc0Riem (I := I) (M := M) g₀ g₁) hKR_nn
    (hRiem g₁ P htie hδ_le hδ0 hδ) i

end DifferentialGeometry.Integral.Connection

end
