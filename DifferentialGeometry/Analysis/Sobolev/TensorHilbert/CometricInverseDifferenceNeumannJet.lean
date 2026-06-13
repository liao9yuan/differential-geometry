import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceCovariantSection
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricCrossContractionCalculus
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound

/-! # The family-uniform cometric inverse-difference covariant Neumann jet

For two smooth Riemannian metrics `g₁`, `g₀` on a closed (compact, boundaryless) smooth manifold
`(M, g₀)` modelled on a real inner-product space `E`, the `g₀`-metrically-lowered cometric inverse
difference `cometricInverseDiffSection g₁ g₀ : SmoothCcTensor g₀ 0 2`
(`CometricInverseDifferenceCovariantSection.lean`) carries the cometric difference `g₁⁻¹ − g₀⁻¹` as a
covariant `(0, 2)`-section.  This file delivers its **order-`p` family-uniform covariant Neumann jet
bound**

```
‖∇^p (cometricInverseDiffSection g₁ g₀)‖² ≤ C · ∑_{l ≤ p+1} ‖∇^l T₁‖²,
```

uniformly over the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{p+3+a}`-bounded (`2a > finrank + 4`) perturbation family
(`g₁.inner = g₀.inner + ccTensorBilinSymm g₀ T₁`).  This is the inverse-Gram analog of the
connection-difference jet `exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`.

## The route — resolvent split plus `(1 − 2δ)` self-absorption

The section-level resolvent Koszul identity
`cometricInverseDiffSection g₁ g₀ = −realizeSymmCcTensor g₀ T₁ − crossCometricSection g₁ g₀ T₁`
(`cometricInverseDiffSection_eq_neg_realizeSymm_sub_cross`) carries a *clean linear part*
`−realizeSymmCcTensor g₀ T₁` (the perturbation itself, `L²` jet-bounded unconditionally by the
`≤ p`-jet of `T₁`, `realizeSymm_iteratedCovGrad_normSq_le_jetSum`) minus a *fibre-small cross
correction* `crossCometricSection g₁ g₀ T₁`, whose order-`p` covariant jet self-couples against the
inverse-difference section through the `δ`-coupled cross-jet brick
`cometricCrossSection_iteratedCovGrad_rfns_le` (`‖∇^p crossCometric‖² ≤ δ·‖∇^p cometricInverseDiff‖²
+ jet`).  Writing `L = ‖∇^p cometricInverseDiffSection‖²`, the `2`-subadditivity of the squared norm
over the split gives `L ≤ 2·jet + 2·(δ·L + jet)`, so the recursion term `2δ·L` moves to the left and
divides out (`1 − 2δ > 0` since `δ < 1/2`), giving the family-uniform jet bound.

This mirrors the `(4 − 8δ)` self-absorption Young split of the connection-difference jet
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`, adapted to the `(0, 2)`
output and the simpler resolvent split (the clean linear part is unconditional, no mutual recursion).

## The genuine deep content (the one posited cross-jet brick)

The `δ`-coupled cross-jet brick `cometricCrossSection_iteratedCovGrad_rfns_le` is the genuine
contraction-native frontier: its base case (order `0`) is the sharp `δ²` operator bound
`riemannianFiberNormSq_crossCometricSection_le_sq_cometricInverseDiff` (sorry-free), and the cross
contraction `crossCometricSection` is the `(0, 2)`-cross parallel cometric contraction
`cometricParallelContraction g₀ (realizeSymm T₁) (permute c[1,0] cometricInverseDiff)`
(`cometricParallelContraction_eq_cometricCrossSection`, sorry-free in
`CometricCrossContractionCalculus`).  Lifting the order-`0` sharp bound to the order-`p` jet through the
operator-reduced covariant Leibniz of the parallel contraction is the cometric analog of the posited
`(0, 3)` grid `crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le` (the
operator-reconciliation + binomial telescope under cometric trace annihilation); it is posited here as
the single child, mirroring the `(0, 3)` state. -/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Two small `L²`-jet algebra helpers (file-local) -/

set_option linter.unusedSectionVars false in
/-- **Squared `L²`-norm scaling of an iterated covariant jet.**  `‖∇^j (c • S)‖² = c² · ‖∇^j S‖²`. -/
private lemma iteratedCovGrad_normSq_smul (g₀ : SmoothRiemannianMetric I M) (s j : ℕ) (c : ℝ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (c • S)‖ ^ 2 =
      c ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2 := by
  rw [iteratedCovGrad_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

set_option linter.unusedSectionVars false in
/-- **`2`-subadditivity of the squared `L²` norm on a difference of iterated covariant jets.**
`‖∇^j (S - T)‖² ≤ 2 ‖∇^j S‖² + 2 ‖∇^j T‖²`. -/
private lemma iteratedCovGrad_normSq_sub_le (g₀ : SmoothRiemannianMetric I M) (s j : ℕ)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j (S - T)‖ ^ 2 ≤
      2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S‖ ^ 2
        + 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 := by
  rw [PDE.RicciFlow.iteratedCovGrad_sub]
  set A := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j S with hA
  set Bb := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s j T with hBb
  have h := norm_sub_sq_real A Bb
  have hcs2 := abs_real_inner_le_norm A Bb
  have hcs := neg_le_abs (@inner ℝ _ _ A Bb)
  nlinarith [h, hcs, hcs2, sq_nonneg (‖A‖ - ‖Bb‖), norm_nonneg A, norm_nonneg Bb]

/-! ## The `δ`-coupled cross-jet brick (the one posited child) -/

set_option linter.unusedSectionVars false in
/-- **(POSITED CHILD — the `δ`-coupled cometric cross-correction covariant jet brick, the
operator-reconciliation + binomial telescope under cometric trace annihilation.)**

On the fibre-small ball (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) and the Sobolev
`H^{p+3+a}` ball, the squared metric `L²` norm of the order-`p` covariant gradient of the cometric
cross-correction section `crossCometricSection g₁ g₀ T₁` (the resolvent correction `h ⌟ D`,
`h = ccTensorBilinSymm g₀ T₁`, `D = gInvDiffRaisedEndo g₀ g₁`) is dominated by the **fibre-small-absorbed**
principal term `δ · ‖∇^p cometricInverseDiffSection‖²` plus a perturbation `≤ (p+1)`-jet term:

```
‖∇^p crossCometricSection g₁ g₀ T₁‖²
  ≤ δ · ‖∇^p cometricInverseDiffSection g₁ g₀‖² + Ccross · ∑_{l ≤ p+1} ‖∇^l T₁‖².
```

This is the `(0, 2)` analog of the `(0, 3)` cross-correction jet brick
`crossCorrectionSection_iteratedCovGrad_rfns_le`.  Its genuine content is the
operator-reduced covariant Leibniz of the `(0, 2)`-cross parallel cometric contraction
`crossCometricSection = cometricParallelContraction g₀ (realizeSymm T₁) (permute c[1,0]
cometricInverseDiffSection)` (`cometricParallelContraction_eq_cometricCrossSection`, sorry-free): the
order-`p` jet of the contraction is the slot-extended cometric operator on `∇^p` of the bare product;
the **top** cell `∇^0 h ⌟ ∇^p D` is absorbed via the fibre-smallness (the sharp order-`0` `δ²` bound
`riemannianFiberNormSq_crossCometricSection_le_sq_cometricInverseDiff` lifted to the top jet through the
`g₀`-lowering parallel isometry `∇₀ g₀ = 0`), the **lower** binomial cells `∇^i h ⌟ ∇^q D` (`q < p`)
folded into the `≤ (p+1)`-jet of `T₁` by the Gagliardo–Nirenberg interpolation and the inductive control
of the lower covariant gradients of the inverse-difference section.  Lifting the order-`0` sharp bound to
the order-`p` jet is the cometric analog of the posited `(0, 3)` rest-peel grid
`crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le` (the operator-reconciliation + bare-
product binomial telescope under cometric trace annihilation); it is posited here as the single child,
mirroring the `(0, 3)` state.

**Non-vacuity.**  Carries the `δ`-coupled principal `δ·‖∇^p cometricInverseDiffSection‖²` (the
recursion term the headline self-absorbs) plus the `T₁`-jets.  At `p = 0` it specializes to the sharp
order-`0` bound `‖crossCometric‖² ≤ δ·‖cometricInverseDiff‖² + Ccross·∑_{l≤1}‖∇^l T₁‖²` (which the
order-`0` `δ²` brick, `δ² ≤ δ` on `δ ≤ 1`, already establishes).  At `T₁ = 0`,
`ccTensorBilinSymm g₀ 0 = 0`, so `crossCometricSection = 0` and the bound is `0 ≤ 0`.  Its body is
`sorry`: the operator-reconciliation + bare-product binomial telescope under the cometric trace
annihilation. -/
theorem cometricCrossSection_iteratedCovGrad_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (crossCometricSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Ccross * ∑ l ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 :=
  sorry

/-! ## The headline — the family-uniform cometric inverse-difference covariant Neumann jet -/

set_option linter.unusedSectionVars false in
/-- **The family-uniform cometric inverse-difference covariant Neumann jet bound.**

For a closed Riemannian manifold `(M, g₀)`, an order `p`, a fibre-smallness parameter `δ < 1/2`, and a
Sobolev ball radius `B`, there is a single nonnegative constant `C` such that for every realized metric
`g₁ = g₀ + ccTensorBilinSymm g₀ T₁` whose perturbation `T₁` is fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`) and `H^{p+3+a}`-bounded (`2a > finrank + 4`), the
intrinsic squared metric `L²` norm of the order-`p` covariant gradient of the `g₀`-metrically-lowered
cometric inverse-difference section `cometricInverseDiffSection g₁ g₀` is dominated by the `≤ (p+1)`-jet
of `T₁`:
```
‖∇^p (cometricInverseDiffSection g₁ g₀)‖² ≤ C · ∑_{l ≤ p+1} ‖∇^l T₁‖².
```

This is the inverse-Gram analog of the connection-difference jet
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`.

Proved by the **resolvent split plus `(1 − 2δ)` self-absorption**: the section-level resolvent identity
`cometricInverseDiffSection = −realizeSymm T₁ − crossCometricSection`
(`cometricInverseDiffSection_eq_neg_realizeSymm_sub_cross`), under `∇^p`, with the `2`-subadditivity
`iteratedCovGrad_normSq_sub_le` over the (negated) split, the **clean-linear arm**
`realizeSymm_iteratedCovGrad_normSq_le_jetSum` (the perturbation jet, unconditional), and the
**`δ`-coupled cross brick** `cometricCrossSection_iteratedCovGrad_rfns_le`, whose `δ·L` recursion term
(`L = ‖∇^p cometricInverseDiffSection‖²`) is moved to the left and divided out
(`1 − 2δ > 0` since `δ < 1/2`).

**Non-vacuity.**  The bound is a genuine jet bound (a `C = 0` witness forces `∇^p cometricInverseDiff = 0`
for every fibre-small `T₁`, false whenever `g₁ ≠ g₀`).  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so
`g₁ = g₀`, `cometricInverseDiffSection g₀ g₀ = 0`, and the bound is `0 ≤ 0`. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_cometricInverseDiffSection_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          C * ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
  classical
  have hden : 0 < 1 - 2 * δ := by linarith
  -- The clean-linear arm: `‖∇^p realizeSymm‖² ≤ Crz · ∑_{l ≤ p} ‖∇^l T₁‖²`.
  obtain ⟨Crz, hCrz0, hCrz⟩ := realizeSymm_iteratedCovGrad_normSq_le_jetSum (I := I) g₀ p
  -- The `δ`-coupled cross brick (the single posited child).
  obtain ⟨Cc, hCc0, hCc⟩ := cometricCrossSection_iteratedCovGrad_rfns_le (I := I) g₀ p δ hδ0 hδ1 B a ha
  refine ⟨(2 * Crz + 2 * Cc) / (1 - 2 * δ), ?_, ?_⟩
  · positivity
  intro T₁ g₁ hr hfib hball
  set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
    (cometricInverseDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
  set Rz := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 with hRzdef
  set Cr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
    (crossCometricSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hCrdef
  set S := ∑ l ∈ Finset.range (p + 1 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSdef
  set Sp := ∑ l ∈ Finset.range (p + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSpdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
  have hSpnn : 0 ≤ Sp := Finset.sum_nonneg fun l _ => by positivity
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  -- `Sp ≤ S` (range (p+1) ⊆ range (p+1+1)).
  have hSpS : Sp ≤ S := by
    rw [hSpdef, hSdef]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega : p + 1 ≤ p + 1 + 1)) fun l _ _ => by positivity
  -- The section-level resolvent split, under `∇^p`:
  -- `cometricInverseDiff = (−realizeSymm) − crossCometric`.
  have hsplit : cometricInverseDiffSection (I := I) g₁ g₀ =
      (-realizeSymmCcTensor (I := I) g₀ T₁) - crossCometricSection (I := I) g₁ g₀ T₁ :=
    cometricInverseDiffSection_eq_neg_realizeSymm_sub_cross (I := I) g₁ g₀ T₁ hr
  -- `2`-subadditivity over the split: `L ≤ 2 ‖∇^p (−realizeSymm)‖² + 2 Cr = 2 Rz + 2 Cr`.
  have hsub : L ≤ 2 * Rz + 2 * Cr := by
    rw [hLdef, hsplit]
    have hle := iteratedCovGrad_normSq_sub_le (I := I) g₀ 2 p
      (-realizeSymmCcTensor (I := I) g₀ T₁) (crossCometricSection (I := I) g₁ g₀ T₁)
    -- `‖∇^p (−realizeSymm)‖² = ‖∇^p realizeSymm‖² = Rz`.
    have hneg : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
          (-realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 = Rz := by
      rw [show (-realizeSymmCcTensor (I := I) g₀ T₁)
          = ((-1 : ℝ)) • realizeSymmCcTensor (I := I) g₀ T₁ from by rw [neg_one_smul]]
      rw [iteratedCovGrad_normSq_smul, hRzdef]; norm_num
    rw [hneg, ← hCrdef] at hle
    exact hle
  -- The clean-linear arm and the cross brick.
  have hRz_le : Rz ≤ Crz * Sp := hCrz T₁
  have hCr_le : Cr ≤ δ * L + Cc * S := hCc T₁ g₁ hr hfib hball
  -- Fold `Sp ≤ S` into the clean-linear arm.
  have hRz_le' : Rz ≤ Crz * S := le_trans hRz_le (mul_le_mul_of_nonneg_left hSpS hCrz0)
  -- Close: `(1 − 2δ) L ≤ (2 Crz + 2 Cc) S`, divide.
  have hkey : (1 - 2 * δ) * L ≤ (2 * Crz + 2 * Cc) * S := by
    nlinarith [hsub, hRz_le', hCr_le, hSnn, hLnn, hCrz0, hCc0]
  rw [hLdef] at hkey ⊢
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  rw [← hLdef] at hkey ⊢
  nlinarith [hkey]

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
