import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GradCapAtgw

/-!
# Arm calculus for the `∇P`-capped grid currency

`GradCapAtgw.lean` supplies the `Λ₁` cap, the base shift `atgwShift`/`armShift`
and the capped integration step `atgwCapToJet`.  What the five summands of
`selfLow_split` need on top of that is a *calculus*: every arm of the zero-order
DeTurck/Ricci integrand is assembled from a handful of operations — `appCcRS`,
`+`, `-`, `•`, slot reindexing, slot extension — and each operation has to carry
the capped window along.

The predicate

`HasCapWin g₀ P X K  ↔  ∀ i x, |∇ⁱX|²(x) ≤ K i · atgw (gridBase g₀ (∇P) x) (i+1)`

is the invariant.  Its key property is that it is **closed under `appCcRS`**
(`capApp`), because a fold at offsets `(0,0)` of two shifted arms is again at
offset `0` in the shifted base.  That is what makes the whole integrand — an
arbitrary tree of products of once-differentiated arms — land at level `n + 1`
in the jets of `∇P`, hence on the `range (n + 2)` budget after `capJet`.

Entry points:

* `capOfArm` — the bridge in: any arm with the ordinary radius-free window at
  `bP`-offset `+2` (one derivative of the state) enters, at the price of
  `shiftConst`.
* `capOfBnd` — a state-free (constant) arm enters for free.
* `capApp`, `capAdd`, `capSub`, `capSmul`, `capNeg`, `capReindex`, `capDdc`,
  `capSlotExt`, `capIter`, `capMono` — the calculus.
* `capJet` — the bridge out: `‖∇ⁿX‖² ≤ K · (1 + ∑_{j<n+2} ‖∇ʲP‖²)`.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### The invariant -/

/-- **The `∇P`-capped grid window of an arm.**

`X`'s order-`i` pointwise fibre jet is bounded by `K i` times the antidiagonal
grid window of level `i + 1` in the jets of `∇P`.  Every arm of the zero-order
integrand that carries at most one derivative of the state satisfies this once
the two caps `|P|, |∇P| ≤ Λ` are spent, and the property is preserved by the
whole product/linear calculus below. -/
def HasCapWin (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) (K : ℕ → ℝ) : Prop :=
  ∀ (i : ℕ) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
      K i * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1)

set_option linter.unusedSectionVars false in
/-- The shifted grid window at level `i + 1` is at least one. -/
private lemma oneLeCapW (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (i : ℕ) :
    (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) :=
  Combinatorics.one_le_antidiagonalTupleGridWindow _
    (gridBase_nn (I := I) (M := M) g₀ _ x) (by omega)

set_option linter.unusedSectionVars false in
/-- The shifted grid window at level `i + 1` is nonnegative. -/
private lemma nnCapW (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (i : ℕ) :
    (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) :=
  le_trans zero_le_one (oneLeCapW (I := I) (M := M) g₀ P x i)

/-! ### Bridges in -/

set_option linter.unusedVariables false in
/-- **Bridge in from the radius-free currency.**

An arm carrying exactly one derivative of the state has the ordinary window
`K i · atgw bP (i + 2)`.  Against the two caps this is a capped window, the
grid level dropping from `i + 2` to `i + 1` because the base is now `∇P`. -/
theorem capOfArm (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ} (hK : ∀ i, 0 ≤ K i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        K i * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (i + 2)) :
    HasCapWin (I := I) (M := M) g₀ P X (fun i => K i * shiftConst Λ (i + 1)) := by
  intro i x
  simpa using armShift (I := I) (M := M) g₀ P hΛ1 hP0 hP1 X hK 0
    (fun j y => by simpa using hX j y) i x

set_option linter.unusedVariables false in
/-- **Bridge in for a state-free arm.**  A uniformly bounded arm — a fixed
tensor, a permutation coefficient, a background curvature — has a capped window
at its own bound, because the grid window is at least one. -/
theorem capOfBnd (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {S : ℕ → ℝ} (hS : ∀ i, 0 ≤ S i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤ S i) :
    HasCapWin (I := I) (M := M) g₀ P X S := by
  intro i x
  exact le_trans (hX i x)
    (le_mul_of_one_le_right (hS i) (oneLeCapW (I := I) (M := M) g₀ P x i))

set_option linter.unusedSectionVars false in
/-- A single grid entry of the shifted base sits inside its own window. -/
private lemma capBaseLe (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    gridBase (I := I) (M := M) g₀ P x (j + 1) ≤
      Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
  classical
  set b : ℕ → ℝ := gridBase (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ k, 0 ≤ b k := gridBase_nn (I := I) (M := M) g₀ P x
  have hb' : ∀ k, 0 ≤ (fun k => b (k + 1)) k := fun k => hb _
  have hsingle := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le
    (fun k => b (k + 1)) hb' 0 j hj
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one, zero_add] at hsingle
  refine le_trans hsingle ?_
  rw [← gradBase_fun (I := I) (M := M) g₀ P x]
  exact Combinatorics.antidiagonalTupleGrid_le_window _ hb' (by omega)

set_option linter.unusedSectionVars false in
/-- **The perturbation itself is capped.**

`|∇ⁱP|²` is `|∇P|`'s grid entry of weight `i - 1` for `i ≥ 1`, and the two
pointwise caps cover the two exceptional orders `i = 0, 1`.  This is the bridge
that lets an arm which is *linear in `P` itself* — the curvature head
`lrCurvF g₀ P` of the Palatini residual — enter the capped currency. -/
theorem capOfP (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ) :
    HasCapWin (I := I) (M := M) g₀ P P (fun _ => Λ) := by
  classical
  intro i x
  have hone := oneLeCapW (I := I) (M := M) g₀ P x i
  have hnn := nnCapW (I := I) (M := M) g₀ P x i
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hgoal : gridBase (I := I) (M := M) g₀ P x i ≤
      Λ * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
    match i with
    | 0 => exact le_trans (hP0 x) (le_mul_of_one_le_right hΛ0 hone)
    | 1 => exact le_trans (hP1 x) (le_mul_of_one_le_right hΛ0 hone)
    | (k + 2) =>
        have h := capBaseLe (I := I) (M := M) g₀ P x (i := k + 2) (j := k + 1)
          (by omega) (by omega)
        nlinarith [h, hnn]
  exact hgoal

set_option linter.unusedSectionVars false in
/-- **One derivative of the perturbation is capped, on the order-one cap
alone.**  `∇P` is the very base of the capped currency, so its `i`-th jet is the
grid entry of weight `i`; only the order-zero exception needs `|∇P| ≤ Λ`. -/
theorem capOfDP (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ) :
    HasCapWin (I := I) (M := M) g₀ P (covGrad (I := I) (M := M) g₀ 0 2 P) (fun _ => Λ) := by
  classical
  intro i x
  have hone := oneLeCapW (I := I) (M := M) g₀ P x i
  have hnn := nnCapW (I := I) (M := M) g₀ P x i
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i P x]
  have hgoal : gridBase (I := I) (M := M) g₀ P x (i + 1) ≤
      Λ * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
    match i with
    | 0 => exact le_trans (hP1 x) (le_mul_of_one_le_right hΛ0 hone)
    | (k + 1) =>
        have h := capBaseLe (I := I) (M := M) g₀ P x (i := k + 1) (j := k + 1)
          (by omega) (by omega)
        nlinarith [h, hnn]
  exact hgoal

/-! ### The calculus -/

set_option linter.unusedVariables false in
/-- **The capped window is closed under `appCcRS`.**

Two arms at offset `0` in the shifted base fold to an arm at offset `0` in the
shifted base: `atgwFold` at `(u, v) = (0, 0)` lands at level `n + 0 + 0 + 1`.
This is the reason a whole product tree of once-differentiated arms stays inside
the `range (n + 2)` budget. -/
theorem capApp (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {p a b : ℕ} (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    {KΦ KW : ℕ → ℝ} (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : HasCapWin (I := I) (M := M) g₀ P Φ KΦ)
    (hW : HasCapWin (I := I) (M := M) g₀ P W KW) :
    HasCapWin (I := I) (M := M) g₀ P (appCcRS (I := I) (M := M) g₀ p a b Φ W)
      (foldConst (E := E) 0 0 KΦ KW) := by
  intro n x
  simpa using atgwFold (I := I) (M := M) g₀ (u := 0) (v := 0) Φ W
    (iteratedCovGrad (I := I) g₀ 0 2 1 P) hKΦ hKW
    (fun i' y => by simpa using hΦ i' y) (fun l y => by simpa using hW l y) n x

set_option linter.unusedSectionVars false in
/-- Weakening the constant of a capped window. -/
theorem capMono (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K K' : ℕ → ℝ}
    (hKK : ∀ i, K i ≤ K' i) (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P X K' := by
  intro i x
  exact le_trans (hX i x)
    (mul_le_mul_of_nonneg_right (hKK i) (nnCapW (I := I) (M := M) g₀ P x i))

set_option linter.unusedSectionVars false in
/-- The capped window transports along an equality of arms. -/
theorem capCongr (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (hXY : Y = X)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P Y K := by
  rw [hXY]; exact hX

set_option linter.unusedSectionVars false in
/-- Two-subadditivity of the capped window. -/
theorem capAdd (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X KX)
    (hY : HasCapWin (I := I) (M := M) g₀ P Y KY) :
    HasCapWin (I := I) (M := M) g₀ P (X + Y) (fun i => 2 * KX i + 2 * KY i) := by
  intro i x
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (X + Y)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i Y).toSection x) := by
    rw [iteratedCovGrad_add (I := I) g₀ r c i X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r (c + i) x _ _
  refine hsplit.trans ?_
  have h1 := hX i x
  have h2 := hY i x
  nlinarith [h1, h2, nnCapW (I := I) (M := M) g₀ P x i]

set_option linter.unusedSectionVars false in
/-- Scalar multiples: the constant picks up `c ^ 2`. -/
theorem capSmul (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (t : ℝ)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (t • X) (fun i => t ^ 2 * K i) := by
  intro i x
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (t • X)).toSection x) =
      t ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) (M := M) g₀ r c i t X,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul (I := I) (M := M) g₀ r (c + i) x t _]
  rw [heq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) (sq_nonneg t)

set_option linter.unusedSectionVars false in
/-- Negation is a capped-window isometry. -/
theorem capNeg (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (-X) K := by
  have hneg : (-X) = (-1 : ℝ) • X := by rw [neg_smul, one_smul]
  rw [hneg]
  refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
    (capSmul (I := I) (M := M) g₀ P (-1 : ℝ) hX)
  norm_num

set_option linter.unusedSectionVars false in
/-- Differences of capped arms. -/
theorem capSub (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X KX)
    (hY : HasCapWin (I := I) (M := M) g₀ P Y KY) :
    HasCapWin (I := I) (M := M) g₀ P (X - Y) (fun i => 2 * KX i + 2 * KY i) := by
  have h := capAdd (I := I) (M := M) g₀ P hX (capNeg (I := I) (M := M) g₀ P hY)
  rwa [← sub_eq_add_neg] at h

set_option linter.unusedSectionVars false in
/-- Source-slot reindexing is a capped-window isometry. -/
theorem capReindex (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (ρ : Equiv.Perm (Fin r))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P
      (reindexCoeffGen (I := I) (M := M) g₀ r c X ρ) K := by
  intro i x
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r c X ρ i x]
  exact hX i x

set_option linter.unusedSectionVars false in
/-- Output-slot permutation is a capped-window isometry. -/
theorem capDdc (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P
      (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X) K := by
  intro i x
  rw [rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r c σ X
    (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X)
    (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x]
  exact hX i x

set_option linter.unusedSectionVars false in
/-- Output-slot permutation of a purely covariant arm is a capped-window
isometry.  This is the `(0, s)` sibling of `capDdc`: `domDomCongrSection` is the
form the Palatini normal forms use, `rsDomDomCongrSection` the form the pair
traces use. -/
theorem capDdc0 (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {c : ℕ} {X : SmoothCcTensor g₀ 0 c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (domDomCongrSection (I := I) g₀ σ X) K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ X i x]
  exact hX i x

set_option linter.unusedSectionVars false in
/-- One slot extension costs one dimension factor. -/
theorem capSlotExt (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (slotExtend (I := I) (M := M) g₀ r c X)
      (fun i => (Module.finrank ℝ E : ℝ) * K i) := by
  intro i x
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r c X i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) hfr

set_option linter.unusedSectionVars false in
/-- Iterated slot extension costs a power of the dimension. -/
theorem capIter (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (w : ℕ)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (slotExtendIter (I := I) (M := M) g₀ r c w X)
      (fun i => (Module.finrank ℝ E : ℝ) ^ w * K i) := by
  induction w with
  | zero => simpa using hX
  | succ w ih =>
      have hrec : slotExtendIter (I := I) (M := M) g₀ r c (w + 1) X =
          slotExtend (I := I) (M := M) g₀ (r + w) (c + w)
            (slotExtendIter (I := I) (M := M) g₀ r c w X) := rfl
      have h := capSlotExt (I := I) (M := M) g₀ P ih
      rw [← hrec] at h
      refine capMono (I := I) (M := M) g₀ P (fun i => ?_) h
      simp only [pow_succ]
      ring_nf
      exact le_of_eq rfl

/-! ### The bridge out -/

set_option linter.unusedVariables false in
/-- **Bridge out: the capped window integrates into the `range (n + 2)` budget.**

`atgwCapToJet` at `w = 1`.  This is the whole point of the capped currency: an
arm quadratic in `∇P` spends the same `L²` jet budget as a linear one, provided
the pointwise cap `|∇P| ≤ Λ` is available — which the `H^{a+2}` ball supplies
through `gradCapOfBall` at the gate `1 ≤ a`. -/
theorem capJet (g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ) →
        ∀ {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
          HasCapWin (I := I) (M := M) g₀ P X K →
          ∀ n : ℕ,
            ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
              K n * (∑ k ∈ Finset.range (n + 1), Kint k) *
                (1 + ∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    atgwCapToJet (I := I) (M := M) g₀ (Λ₁ := Real.sqrt Λ) (Real.sqrt_nonneg Λ)
  refine ⟨Kint, hKint_nn, ?_⟩
  intro P hP1 r c X K hK hX n
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Real.sqrt Λ ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛ0]
    simpa using hP1 x
  exact hint P hcap r c n 1 X (K n) (hK n) (fun x => by simpa using hX n x)

end DifferentialGeometry.Integral.Connection

end
