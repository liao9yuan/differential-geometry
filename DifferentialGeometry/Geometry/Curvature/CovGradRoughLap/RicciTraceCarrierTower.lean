import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.DiffCurvatureGenuineTower

/-!
# The Ricci-trace carrier graded-jet primitive

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the graded
curvature-jet bound for the **Ricci-trace carrier** `ricTraceSection g s S = appCc (ricSlotOpField g s)
(∇S)` (the term-`(IV)` `Ric(∇S)` contraction of the order-`2` rough-Laplacian commutator defect, the
operator-field action of the *fixed* smooth leading-slot raised-Ricci operator field on `∇S =
covGrad g 0 s S`).

## The fixed raised-Ricci `Ric·` tower

`ricSlotOpField g s` is a *fixed* smooth rank-preserving `(s + 1, s + 1)`-operator field (built from `g`
and `Ric`), so the carrier is the order-`0` action `appCc (Φ₀ (s + 1)) (∇S)` of that fixed field on
`∇S`. Differentiating the fixed-field action `p` times (the exact covariant-Leibniz remainder, isolating
only the differentiated coefficient) defines the order-`p` raised-Ricci operator `ricTraceDiffOp g p n`,
a rank-preserving tower `SmoothCcTensor g 0 n → SmoothCcTensor g 0 (n + p)` whose order-`0` base is the
fixed-field action `appCc (Φ₀ n) W` (with `Φ₀ (s + 1) = ricSlotOpField g s`, `Φ₀ 0 = 0`).

Because the base coefficient `Φ₀` is a *fixed* smooth section, the tower's operator-field normal form
(`NormalForm`, `OperatorFieldDifferentiatedTowerNormalForm`) expresses each `ricTraceDiffOp g p n W` as a
finite sum of operator-field actions of the fixed smooth coefficients `∇^{≤ p} Φ₀` on the covariant jets
`∇^{≤ p} W` of the contracted section, so its iterated covariant gradient is order-controlled by the
order-`≤ p` jet of `W`; the operator-field covariant-Leibniz double grid then envelopes all iterated
gradients.

## Main result

* `ricTraceSection_gradedCurvJet` — there is a valence/order-dependent nonnegative constant family
  `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and every smooth compactly-supported
  `(0, s)`-tensor `S`, the Ricci-trace carrier `ricTraceSection g s S` is a **graded** curvature jet of
  `S` of lowest order `1` and base width `1`:
  ```
  rfns(∇^k (ricTraceSection g s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
  ```
  The section enters at order `1` (not `0`) because the carrier already contracts the *gradient* `∇S`;
  the field is bounded with all its iterated covariant gradients (the entire graded family), exactly the
  re-differentiable jet the order-`m` curvature-jet induction consumes for the Ricci-trace leg.

## Convention

Geometer convention; all fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq`
(`rfns`). The construction stays intrinsic: `appCc` operator-field actions, `covGrad` covariant
gradients, and `rfns` fibre norms only — no moving-frame extraction, no chart-frame jet.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast (HEq form).** Inlined generic helper. -/
private theorem rfns_toSection_heq_congr_ric (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The intrinsic
squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. (Inlined generic helper, the rfns
mirror of `iteratedCovGrad_covGrad_comm_heq'`.) -/
private theorem rfns_iteratedCovGrad_covGrad_comm_ric (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_ric g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m W) x

/-- **The fixed rank-preserving raised-Ricci operator field `Φ₀ n`.** At rank `n = s + 1` it is the
leading-slot raised-Ricci operator field `ricSlotOpField g s` (a fixed smooth `(s + 1, s + 1)`-operator
field); at rank `n = 0` it is the zero operator field. The order-`0` base of the differentiated
raised-Ricci tower is the fixed-field action `appCc (Φ₀ n) W` of this field. -/
private noncomputable def ricSlotOpFieldShift (g : SmoothRiemannianMetric I M) :
    ∀ n : ℕ, SmoothCcTensor g (n + 0) (n + 0)
  | 0 => 0
  | (s + 1) => ricSlotOpField (I := I) (M := M) g s

/-- **The order-`p` differentiated raised-Ricci `Ric·` operator.** Acting on a smooth compactly-supported
`(0, n)`-tensor section `W`, the `p`-times covariantly-differentiated action of the fixed raised-Ricci
operator field `Φ₀ n`, defined recursively as the exact covariant-Leibniz remainder:

* `p = 0`: the order-`0` action `appCc (Φ₀ n) W`;
* `p + 1`: `∇(op p n W) − (rank-cast) op p (n + 1) (∇W)` — the differentiated-coefficient remainder (the
  input section's derivative `∇W` cancels), rank-cast `(n + 1) + p = n + 1 + p`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`. The base coefficient `Φ₀ n`
is a *fixed* smooth section, so the differentiated tower differentiates only the curvature coefficient,
never a frame jet; the contracted section `W` enters at order `0`. -/
noncomputable def ricTraceDiffOp
    (g : SmoothRiemannianMetric I M) :
    ∀ (p n : ℕ), SmoothCcTensor g 0 n → SmoothCcTensor g 0 (n + p)
  | 0, n => fun W =>
      appCc (I := I) (M := M) g (n + 0) (n + 0)
        (ricSlotOpFieldShift (I := I) (M := M) g n) W
  | (p + 1), n => fun W =>
      covGrad (I := I) (M := M) g 0 (n + p)
          (ricTraceDiffOp g p n W) -
        castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
          (ricTraceDiffOp g p (n + 1) (covGrad (I := I) (M := M) g 0 n W))

/-- **The order-`0` differentiated raised-Ricci operator is the action of the fixed field `Φ₀ n`.** -/
private theorem ricTraceDiffOp_zero_eq_appCc (g : SmoothRiemannianMetric I M) (n : ℕ)
    (W : SmoothCcTensor g 0 n) :
    ricTraceDiffOp (I := I) (M := M) g 0 n W =
      appCc (I := I) (M := M) g (n + 0) (n + 0)
        (ricSlotOpFieldShift (I := I) (M := M) g n) W := rfl

/-- **The order-`0` raised-Ricci operator at rank `s + 1`, applied to `∇S`, is the Ricci-trace carrier.**
By definition `ricTraceDiffOp g 0 (s + 1) (∇S) = appCc (ricSlotOpField g s) (∇S) = ricTraceSection g s
S`. -/
theorem ricTraceDiffOp_zero_covGrad_eq_ricTraceSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ricTraceDiffOp (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S) =
      ricTraceSection (I := I) (M := M) g s S := rfl

/-- **The exact single-step covariant Leibniz of the differentiated raised-Ricci `Ric·` tower.** By the
recursive definition, `∇(op p n W)` splits exactly into the higher-order remainder `op (p + 1) n W` and
the rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. -/
theorem covGrad_ricTraceDiffOp_eq
    (g : SmoothRiemannianMetric I M) (p n : ℕ) (W : SmoothCcTensor g 0 n) :
    covGrad (I := I) (M := M) g 0 (n + p) (ricTraceDiffOp (I := I) (M := M) g p n W) =
      ricTraceDiffOp (I := I) (M := M) g (p + 1) n W +
        castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
          (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
            (covGrad (I := I) (M := M) g 0 n W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (n + p)
      (ricTraceDiffOp (I := I) (M := M) g p n W) -
      castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
        (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
          (covGrad (I := I) (M := M) g 0 n W))) + _
  rw [sub_add_cancel]

/-- **The per-order, per-rank section-proportional fibre envelope for the differentiated raised-Ricci
`Ric·` tower, in jet form.** For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative
envelope family `kappa : ℕ → ℕ → ℝ` such that for every order `p`, rank `n`, smooth compactly-supported
`(0, n)`-tensor `W`, and base point `x`,
```
rfns(ricTraceDiffOp g p n W)(x) ≤ kappa p n · ∑_{q < p + 1} rfns(∇^q W)(x).
```
The tower's order-`0` base is the action of the fixed smooth field `Φ₀ n`, so the operator-field normal
form holds at every order (`normalForm_of_base`), whence the jet envelope (`exists_jet_bound_of_normalForm`):
each `∇^{≤ p} Φ₀` coefficient is a fixed smooth field, uniformly fibre-operator-bounded over the compact
`M`. -/
private theorem exists_proportional_ricTraceDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p n, 0 ≤ kappa p n) ∧
      ∀ (p n : ℕ) (W : SmoothCcTensor g 0 n) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (n + p) x
            ((ricTraceDiffOp (I := I) (M := M) g p n W).toSection x) ≤
          kappa p n * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
              ((iteratedCovGrad g 0 n q W).toSection x) := by
  classical
  have hNF : ∀ (p n : ℕ),
      NormalForm (I := I) (M := M) g (ricTraceDiffOp (I := I) (M := M) g) p n :=
    fun p => normalForm_of_base (I := I) (M := M) g
      (ricTraceDiffOp (I := I) (M := M) g)
      (covGrad_ricTraceDiffOp_eq (I := I) (M := M) g)
      (fun n => ricSlotOpFieldShift (I := I) (M := M) g n)
      (fun n W => ricTraceDiffOp_zero_eq_appCc (I := I) (M := M) g n W) p
  choose kap hkap_nn hkap using fun p n =>
    exists_jet_bound_of_normalForm (I := I) (M := M) g
      (ricTraceDiffOp (I := I) (M := M) g) p n (hNF p n)
  exact ⟨kap, hkap_nn, hkap⟩

/-! ## The iterated-gradient grid for the differentiated raised-Ricci `Ric·` tower -/

/-- A `range`-sum shift bookkeeping helper. -/
private lemma sum_range_shift_le_ric (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

/-- **The binomial covariant-Leibniz `rfns` double grid for the differentiated raised-Ricci `Ric·`
tower.** For every gradient order `j`, differentiation order `p`, base rank `n`, section `W`, and point
`x`, the intrinsic squared fibre norm of `∇^j(op p n W)` is bounded by the binomial jet grid
```
rfns(∇^j(op p n W))(x) ≤ 4^j · gridWindowSum kappa p n j · ∑_{q < p + j + 1} rfns(∇^q W)(x),
```
proved by the binomial covariant-Leibniz induction on `j` over the tower's exact single-step Leibniz
`covGrad_ricTraceDiffOp_eq` and the per-order jet envelope `exists_proportional_ricTraceDiffOp`. -/
private theorem rfns_iteratedCovGrad_ricTraceDiffOp_grid
    (g : SmoothRiemannianMetric I M)
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p n, 0 ≤ kappa p n)
    (hrfns : ∀ (p n : ℕ) (W : SmoothCcTensor g 0 n) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (n + p) x
          ((ricTraceDiffOp (I := I) (M := M) g p n W).toSection x) ≤
        kappa p n * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
            ((iteratedCovGrad g 0 n q W).toSection x)) (j : ℕ) :
    ∀ (p n : ℕ) (W : SmoothCcTensor g 0 n) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((n + p) + j) x
          ((iteratedCovGrad g 0 (n + p) j
            (ricTraceDiffOp (I := I) (M := M) g p n W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p n j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
              ((iteratedCovGrad g 0 n q W).toSection x) := by
  induction j with
  | zero =>
      intro p n W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p n 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
                ((iteratedCovGrad g 0 n q W).toSection x) =
          kappa p n * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
                ((iteratedCovGrad g 0 n q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns p n W x
  | succ j ih =>
      intro p n W x
      set K : ℝ := gridWindowSum kappa p n (j + 1) with hK_def
      set Sm : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
          ((iteratedCovGrad g 0 n q W).toSection x) with hSm_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p n (j + 1)
      have hSm_nn : 0 ≤ Sm := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (n + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((n + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (n + p) (j + 1)
              (ricTraceDiffOp (I := I) (M := M) g p n W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((n + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((n + p) + 1) j
              (covGrad g 0 (n + p)
                (ricTraceDiffOp (I := I) (M := M) g p n W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_ric g 0 (n + p) j
          (ricTraceDiffOp (I := I) (M := M) g p n W) x).symm]
      rw [covGrad_ricTraceDiffOp_eq (I := I) (M := M) g p n W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((n + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((n + p) + 1) j
            (ricTraceDiffOp (I := I) (M := M) g (p + 1) n W)).toSection x)
          ((iteratedCovGrad g 0 ((n + p) + 1) j
            (castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
              (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
                (covGrad g 0 n W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) n j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (n + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
          ((iteratedCovGrad g 0 n q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (n + (q + 1)) x
          ((iteratedCovGrad g 0 n (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((n + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (n + (p + 1)) j
              (ricTraceDiffOp (I := I) (M := M) g (p + 1) n W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) n W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (n + 1) (covGrad g 0 n W) x
      have hBshift : gridWindowSum kappa p (n + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((n + 1) + q) x
                ((iteratedCovGrad g 0 (n + 1) q (covGrad g 0 n W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_ric g 0 n q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((n + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((n + 1) + p) j
              (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
                (covGrad g 0 n W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p n j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p n j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ Sm := by
        rw [hsA_def, hSm_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ Sm := by
        rw [hsB_def, hSm_def]
        refine le_trans (sum_range_shift_le_ric (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
            ((iteratedCovGrad g 0 n q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (n + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) n j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (n + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (n + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (n + (q + 1)) x _
      have hprodA : kA * sA ≤ K * Sm := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * Sm := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * Sm) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * Sm) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p n (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (n + q) x
                ((iteratedCovGrad g 0 n q W).toSection x) := by
        rw [hK_def, hSm_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((n + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((n + p) + 1) j
              (castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
                (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
                  (covGrad g 0 n W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((n + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((n + 1) + p) j
              (ricTraceDiffOp (I := I) (M := M) g p (n + 1)
                (covGrad g 0 n W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (n + 1) + p = n + (p + 1))
          (ricTraceDiffOp (I := I) (M := M) g p (n + 1) (covGrad g 0 n W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-- **The graded curvature-jet bound for the Ricci-trace carrier `ricTraceSection`.** For a closed
smooth Riemannian manifold `(M, g)` there is a valence/order-dependent nonnegative constant family
`c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and every smooth compactly-supported
`(0, s)`-tensor `S`, the Ricci-trace carrier `ricTraceSection g s S = appCc (ricSlotOpField g s) (∇S)`
(the term-`(IV)` `Ric(∇S)` contraction) is a **graded** curvature jet of `S` of lowest order `1` and
base width `1`:

```
rfns(∇^k (ricTraceSection g s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
```

This is the foundational order-`1`/width-`1` graded curvature-jet primitive for the fourth (Ricci-trace)
carrier of the order-`2` rough-Laplacian commutator defect — the missing carrier the three-term split
failed to hold — bounded with ALL its iterated covariant gradients, exactly the re-differentiable jet the
order-`m` curvature-jet induction consumes.

**Proof.** `ricTraceSection g s S = ricTraceDiffOp g 0 (s + 1) (∇S)` is the order-`0` base of the
differentiated raised-Ricci `Ric·` tower applied to `∇S = covGrad g 0 s S`, the operator-field action of
the *fixed* smooth coefficient `Φ₀ (s + 1) = ricSlotOpField g s`. The at-point covariant-Leibniz double
grid `rfns_iteratedCovGrad_ricTraceDiffOp_grid` at differentiation order `p = 0` and rank `s + 1`,
section `∇S`, bounds `∇^k` of that base by `4^k · gridWindowSum kappa 0 (s + 1) k · ∑_{q < k + 1}
rfns(∇^q (∇S))`; commuting the front gradient (`rfns_iteratedCovGrad_covGrad_comm_ric`) turns
`rfns(∇^q (∇S))` into `rfns(∇^{q + 1} S)`, so the contracted-order range is `1 … k + 1`, i.e. the
section enters at order `1` (width `1`). The constant family is the engine's single-sum constant
`c s k := √(4^k · gridWindowSum kappa 0 (s + 1) k)`, frame-free since the per-order envelope is.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(ricTraceSection g s S)(x) = 0` at `k = 0`, i.e.
the Ricci-trace contraction `Ric(∇S)` vanishes; false on a non-flat manifold (`Ric ≠ 0`) for a
non-parallel `S` (`∇S ≠ 0`). The constant family is genuinely positive. -/
theorem ricTraceSection_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g S (c s) 1 1
          (ricTraceSection (I := I) (M := M) g s S) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_ricTraceDiffOp (I := I) (M := M) g
  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s' + 1) k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 (s + 1) k)
  -- The graded predicate at the order-`0` base of the differentiated raised-Ricci `Ric·` tower applied
  -- to `∇S`.
  change riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + k) x
        ((iteratedCovGrad g 0 (s + 1) k
          (ricTraceSection (I := I) (M := M) g s S)).toSection x) ≤
      (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k)) ^ 2 *
        ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
            ((iteratedCovGrad g 0 s (i + 1) S).toSection x)
  rw [hcsq]
  -- The at-point grid for the raised-Ricci tower, differentiation order `p = 0`, rank `s + 1`, section
  -- `∇S = covGrad g 0 s S`.
  have hgrid := rfns_iteratedCovGrad_ricTraceDiffOp_grid (I := I) (M := M) g
    kappa hkappa_nn hkappa k 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) x
  -- The order-`0` base on `∇S` is `ricTraceSection g s S`; the windows collapse to `range (k + 1)`.
  rw [ricTraceDiffOp_zero_covGrad_eq_ricTraceSection (I := I) (M := M) g s S] at hgrid
  -- Normalize the contracted-order window in `hgrid`: `range (0 + k + 1) = range (k + 1)`.
  rw [Nat.zero_add] at hgrid
  refine le_trans (le_of_eq ?_) (hgrid.trans (le_of_eq ?_))
  · -- LHS rank reassociation `(s + 1 + 0) + k = (s + 1) + k`.
    norm_num
  · -- RHS: re-express each `rfns(∇^q (∇S))` as `rfns(∇^{q + 1} S)` and re-index the window
    -- `range (k + 1) = range (1 + k)`.
    have hsum : ∑ q ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + q) x
            ((iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
        ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
            ((iteratedCovGrad g 0 s (i + 1) S).toSection x) := by
      rw [show (k + 1) = (1 + k) from by omega]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      exact rfns_iteratedCovGrad_covGrad_comm_ric g 0 s q S x
    rw [hsum]

end Connection
end Integral
end DifferentialGeometry

end
