import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDiffCurvTraceSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJet

/-!
# The intrinsic differentiated-curvature graded-jet primitive

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
foundational graded curvature-jet bound for the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` (the `(∇R) S` field, the
operator-field action of the covariant derivative of the frame-free curvature operator field on `S`).

## The differentiated `(∇R)·` tower

`genuineDiffCurvSection g s S` is the operator-field action `appCc Ψ₀ S` of the *fixed* smooth
`(s, s + 1)`-operator field `Ψ₀ := covGrad (curvOpField g s)` on `S`. Differentiating that action `p`
times (the exact covariant-Leibniz remainder, isolating only the differentiated coefficient) defines the
order-`p` differentiated `(∇R)·` operator `diffCurvGenuineDiffOp g p s`, a rank-raising tower
`SmoothCcTensor g 0 s → SmoothCcTensor g 0 (s + 1 + p)` whose order-`0` base is
`genuineDiffCurvSection g s S`.

Because the base coefficient `Ψ₀` is a *fixed* smooth section (built from `g, R, ∇R`), the tower's normal
form expresses each `diffCurvGenuineDiffOp g p s W` as a finite sum of operator-field actions of the
fixed smooth coefficients `∇^{≤ p} Ψ₀` on the covariant jets `∇^{≤ p} W` of the contracted section, so
its iterated covariant gradient is order-controlled by the order-`≤ p` jet of `W`; the operator-field
covariant-Leibniz double grid then envelopes all iterated gradients.

## Main result

* `genuineDiffCurvSection_gradedCurvJet` — there is a valence/order-dependent nonnegative constant family
  `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and every smooth compactly-supported
  `(0, s)`-tensor `S`, the differentiated-curvature section `genuineDiffCurvSection g s S` is a **graded**
  curvature jet of `S` of lowest order `0` and base width `1`:
  ```
  rfns(∇^k (genuineDiffCurvSection g s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 0} S)(x).
  ```
  The differentiation is entirely on the curvature factor, so the section enters at order `0`; the field
  is bounded with all its iterated covariant gradients (the entire graded family), exactly the
  re-differentiable jet the order-`m` curvature-jet induction consumes.

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

/-- **The fixed differentiated-curvature operator field `Ψ₀ s = ∇(Φ₀ s)`.** The covariant gradient of
the frame-free curvature operator field `curvOpField g s`, a fixed smooth `(s, s + 1)`-operator field
whose operator-field action on a `(0, s)`-tensor `S` is the differentiated-curvature section
`genuineDiffCurvSection g s S = appCc (Ψ₀ s) S` (the `(∇R) S` field). -/
private noncomputable def diffCurvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0 + 1) :=
  covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)

/-- **The order-`p` differentiated `(∇R)·` curvature operator.** Acting on a smooth compactly-supported
`(0, r)`-tensor section `W`, the `p`-times covariantly-differentiated action of the fixed
differentiated-curvature operator field `Ψ₀ r = ∇(Φ₀ r)`, defined recursively as the exact
covariant-Leibniz remainder:

* `p = 0`: the order-`0` action `appCc (Ψ₀ r) W = genuineDiffCurvSection g r W`;
* `p + 1`: `∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` — the differentiated-coefficient remainder (the
  input section's derivative `∇W` cancels), rank-cast `(r + 1) + (p + 1) = r + 1 + (p + 1)`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`. The base coefficient `Ψ₀ r`
is a *fixed* smooth section, so the differentiated tower differentiates only the curvature coefficient,
never a frame jet; the section enters at order `0`. -/
noncomputable def diffCurvGenuineDiffOp
    (g : SmoothRiemannianMetric I M) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p)
  | 0, r => fun W =>
      appCc (I := I) (M := M) g (r + 0) (r + 0 + 1)
        (diffCurvOpField (I := I) (M := M) g r) W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + 1 + p)
          (diffCurvGenuineDiffOp g p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
          (diffCurvGenuineDiffOp g p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

/-- **The order-`0` differentiated `(∇R)·` operator is the differentiated-curvature section.** By
definition `diffCurvGenuineDiffOp g 0 s S = appCc (Ψ₀ s) S = genuineDiffCurvSection g s S`. -/
theorem diffCurvGenuineDiffOp_zero_eq_genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    diffCurvGenuineDiffOp (I := I) (M := M) g 0 s S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl

/-- **The order-`0` differentiated `(∇R)·` operator is the action of the fixed field `Ψ₀ r`.** The
base-rank operator-field-action factorisation: `diffCurvGenuineDiffOp g 0 r W = appCc (Ψ₀ r) W`. -/
private theorem diffCurvGenuineDiffOp_zero_eq_appCc (g : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g 0 r) :
    diffCurvGenuineDiffOp (I := I) (M := M) g 0 r W =
      appCc (I := I) (M := M) g (r + 0) (r + 0 + 1) (diffCurvOpField (I := I) (M := M) g r) W := rfl

/-- **The exact single-step covariant Leibniz of the differentiated `(∇R)·` tower.** By the recursive
definition, `∇(op p r W)` splits exactly into the higher-order remainder `op (p + 1) r W` and the
rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. -/
theorem covGrad_diffCurvGenuineDiffOp_eq
    (g : SmoothRiemannianMetric I M) (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + 1 + p) (diffCurvGenuineDiffOp (I := I) (M := M) g p r W) =
      diffCurvGenuineDiffOp (I := I) (M := M) g (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
          (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + 1 + p)
      (diffCurvGenuineDiffOp (I := I) (M := M) g p r W) -
      castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
        (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

/-- **The operator-field normal form of the differentiated `(∇R)·` tower at order `p`, rank `r`.** The
order-`p` tower value `op p r W` decomposes as a finite sum of operator-field actions of fixed smooth
operator fields `Ψ k : SmoothCcTensor g (r + k) (r + 1 + p)` on the covariant jets `∇^k W` of the
contracted section, `k < p + 1` (the rank-raising analogue of `NormalForm`, output rank `r + 1 + p`). -/
private def NormalFormRaise (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p))
    (p r : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g (r + k) (r + 1 + p),
    ∀ W : SmoothCcTensor g 0 r,
      op p r W =
        ∑ k ∈ Finset.range (p + 1),
          appCc (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k) (iteratedCovGrad g 0 r k W)

/-- **The gradient of a rank-raising normal-form sum expands termwise.** -/
private theorem covGrad_normalFormRaise_sum (g : SmoothRiemannianMetric I M) (p r : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (r + k) (r + 1 + p)) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + 1 + p)
        (∑ k ∈ Finset.range (p + 1),
          appCc (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k) (iteratedCovGrad g 0 r k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (appCc (I := I) (M := M) g (r + k) (r + 1 + (p + 1))
            (covGrad (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k)) (iteratedCovGrad g 0 r k W) +
          appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
            (slotExtend (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k))
            (iteratedCovGrad g 0 r (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCc_eq (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k) (iteratedCovGrad g 0 r k W)]
  rw [show covGrad (I := I) (M := M) g 0 (r + k) (iteratedCovGrad g 0 r k W) =
      iteratedCovGrad g 0 r (k + 1) W from (iteratedCovGrad_succ g 0 r k W).symm]
  rfl

/-- **The rank-cast lower-tower normal form on `∇W` re-expressed in canonical jets (rank-raising).**
The output-rank-`(r + 1) + 1 + p` analogue of `castRankCc_appCc_iteratedCovGrad_covGrad`. -/
private theorem castRankCc_appCc_iteratedCovGrad_covGrad_raise (g : SmoothRiemannianMetric I M)
    (p r k : ℕ)
    (Ψ : SmoothCcTensor g ((r + 1) + k) ((r + 1) + 1 + p)) (W : SmoothCcTensor g 0 r) :
    castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
        (appCc (I := I) (M := M) g ((r + 1) + k) ((r + 1) + 1 + p) Ψ
          (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))) =
      appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
        (castSrcCc g (r + 1 + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
          (castRankCc_db g ((r + 1) + k) (by omega : (r + 1) + 1 + p = r + 1 + (p + 1)) Ψ))
        (iteratedCovGrad g 0 r (k + 1) W) := by
  rw [appCc_castRankCc_db g (by omega : (r + 1) + k = r + (k + 1))
    (by omega : (r + 1) + 1 + p = r + 1 + (p + 1)) Ψ
    (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g 0 r k W)
  exact castRankCc_db_heq g 0 (by omega : (r + 1) + k = r + (k + 1))
    (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W))

/-- **The rank-raising normal form propagates up the differentiated tower.** -/
private theorem normalFormRaise_succ (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p))
    (covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + 1 + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
            (op p (r + 1) (covGrad g 0 r W)))
    (p : ℕ) (hp : ∀ r, NormalFormRaise (I := I) (M := M) g op p r) (r : ℕ) :
    NormalFormRaise (I := I) (M := M) g op (p + 1) r := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp r
  obtain ⟨Ψr1, hΨr1⟩ := hp (r + 1)
  set Tk : (k : ℕ) → SmoothCcTensor g (r + (k + 1)) (r + 1 + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g (r + k) (r + 1 + p) (Ψr k) -
      castSrcCc g (r + 1 + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
        (castRankCc_db g ((r + 1) + k) (by omega : (r + 1) + 1 + p = r + 1 + (p + 1)) (Ψr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g (r + 0) (r + 1 + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1))
          else 0)
          + Tk k, ?_⟩
  intro W
  have hrec : op (p + 1) r W =
      covGrad g 0 (r + 1 + p) (op p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
          (op p (r + 1) (covGrad g 0 r W)) := by
    rw [covGrad_op p r W]; abel
  rw [hrec, hΨr W]
  rw [covGrad_normalFormRaise_sum (I := I) (M := M) g p r Ψr W]
  rw [hΨr1 (covGrad g 0 r W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
          (appCc (I := I) (M := M) g ((r + 1) + k) ((r + 1) + 1 + p) (Ψr1 k)
            (iteratedCovGrad g 0 (r + 1) k (covGrad g 0 r W)))) =
      ∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (castSrcCc g (r + 1 + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
            (castRankCc_db g ((r + 1) + k) (by omega : (r + 1) + 1 + p = r + 1 + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 r (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCc_iteratedCovGrad_covGrad_raise (I := I) (M := M) g p r k (Ψr1 k) W)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    appCc (I := I) (M := M) g (r + j) (r + 1 + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g (r + 0) (r + 1 + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g 0 r j W)) (p + 1)]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          ((if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 r (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCc_add_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (slotExtend (I := I) (M := M) g (r + k) (r + 1 + p) (Ψr k))
          (iteratedCovGrad g 0 r (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (castSrcCc g (r + 1 + (p + 1)) (by omega : (r + 1) + k = r + (k + 1))
            (castRankCc_db g ((r + 1) + k) (by omega : (r + 1) + 1 + p = r + 1 + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 r (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCc_sub_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 r (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        appCc (I := I) (M := M) g (r + (k + 1)) (r + 1 + (p + 1))
          (covGrad (I := I) (M := M) g (r + (k + 1)) (r + 1 + p) (Ψr (k + 1)))
          (iteratedCovGrad g 0 r (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCc_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
  rw [Finset.sum_range_succ' (fun k =>
    appCc (I := I) (M := M) g (r + k) (r + 1 + (p + 1))
      (covGrad (I := I) (M := M) g (r + k) (r + 1 + p) (Ψr k)) (iteratedCovGrad g 0 r k W)) p]
  abel

/-- **The order-`0` base factorisation is the order-`0` rank-raising normal form.** -/
private theorem normalFormRaise_zero (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p))
    (r : ℕ) (Φ₀ : SmoothCcTensor g (r + 0) (r + 0 + 1))
    (hbase : ∀ W : SmoothCcTensor g 0 r,
      op 0 r W = appCc (I := I) (M := M) g (r + 0) (r + 0 + 1) Φ₀ W) :
    NormalFormRaise (I := I) (M := M) g op 0 r := by
  refine ⟨fun k => match k with | 0 => Φ₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl

/-- **The rank-raising operator-field normal form holds at every order.** A recursively-differentiated
rank-raising tower `op` whose single-step covariant Leibniz is the exact remainder (`covGrad_op`) and
whose order-`0` base is a fixed-operator-field action at every rank (`hbase`) admits the operator-field
normal form at every order `p` and rank `r`. -/
private theorem normalFormRaise_of_base (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p))
    (covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + 1 + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
            (op p (r + 1) (covGrad g 0 r W)))
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0 + 1))
    (hbase : ∀ (r : ℕ) (W : SmoothCcTensor g 0 r),
      op 0 r W = appCc (I := I) (M := M) g (r + 0) (r + 0 + 1) (Φ₀ r) W)
    (p : ℕ) : ∀ r : ℕ, NormalFormRaise (I := I) (M := M) g op p r := by
  induction p with
  | zero => exact fun r => normalFormRaise_zero (I := I) (M := M) g op r (Φ₀ r) (hbase r)
  | succ p ih => exact fun r => normalFormRaise_succ (I := I) (M := M) g op covGrad_op p ih r

/-- **The per-order, per-rank jet envelope of the rank-raising differentiated tower from its normal
form.** If `op p r` admits the rank-raising operator-field normal form, then its intrinsic squared fibre
norm is bounded, uniformly over the compact `M`, by a nonnegative constant times the order-`≤ p`
covariant jet of the contracted section. -/
private theorem exists_jet_bound_of_normalFormRaise (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + 1 + p))
    (p r : ℕ) (hNF : NormalFormRaise (I := I) (M := M) g op p r) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1 + p) x ((op p r W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := hNF
  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k)
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
    ((iteratedCovGrad g 0 r k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + k) x _
  rw [hΨ W, SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 (r + 1 + p) x
    (Finset.range (p + 1))
    (fun k => (appCc (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k)
      (iteratedCovGrad g 0 r k W)).toSection x)) ?_
  rw [Finset.card_range]
  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1 + p) x
          ((appCc (I := I) (M := M) g (r + k) (r + 1 + p) (Ψ k)
            (iteratedCovGrad g 0 r k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_
  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

/-- **The per-order, per-rank section-proportional fibre envelope for the differentiated `(∇R)·`
tower, in jet form.** For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative envelope
family `kappa : ℕ → ℕ → ℝ` such that for every order `p`, rank `r`, smooth compactly-supported
`(0, r)`-tensor `W`, and base point `x`,
```
rfns(diffCurvGenuineDiffOp g p r W)(x) ≤ kappa p r · ∑_{q < p + 1} rfns(∇^q W)(x).
```
The tower's order-`0` base is the action of the fixed smooth field `Ψ₀ r = ∇(Φ₀ r)`, so the rank-raising
operator-field normal form holds at every order (`normalFormRaise_of_base`), whence the jet envelope
(`exists_jet_bound_of_normalFormRaise`): each `∇^{≤ p} Ψ₀` coefficient is a fixed smooth field, uniformly
fibre-operator-bounded over the compact `M`. -/
private theorem exists_proportional_diffCurvGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1 + p) x
            ((diffCurvGenuineDiffOp (I := I) (M := M) g p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  have hNF : ∀ (p r : ℕ),
      NormalFormRaise (I := I) (M := M) g (diffCurvGenuineDiffOp (I := I) (M := M) g) p r :=
    fun p => normalFormRaise_of_base (I := I) (M := M) g
      (diffCurvGenuineDiffOp (I := I) (M := M) g)
      (covGrad_diffCurvGenuineDiffOp_eq (I := I) (M := M) g)
      (fun r => diffCurvOpField (I := I) (M := M) g r)
      (fun r W => diffCurvGenuineDiffOp_zero_eq_appCc (I := I) (M := M) g r W) p
  choose kap hkap_nn hkap using fun p r =>
    exists_jet_bound_of_normalFormRaise (I := I) (M := M) g
      (diffCurvGenuineDiffOp (I := I) (M := M) g) p r (hNF p r)
  exact ⟨kap, hkap_nn, hkap⟩

/-! ## The iterated-gradient grid for the differentiated `(∇R)·` tower -/

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast (HEq form).** Inlined generic helper. -/
private theorem rfns_toSection_heq_congr_raise (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The intrinsic
squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. (Inlined generic helper, the rfns
mirror of `iteratedCovGrad_covGrad_comm_heq'`.) -/
private theorem rfns_iteratedCovGrad_covGrad_comm_raise (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_raise g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m W) x

/-- A `range`-sum shift bookkeeping helper. -/
private lemma sum_range_shift_le_raise (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

/-- **The binomial covariant-Leibniz `rfns` double grid for the differentiated `(∇R)·` tower.** For
every gradient order `j`, differentiation order `p`, base rank `r`, section `W`, and point `x`, the
intrinsic squared fibre norm of `∇^j(op p r W)` is bounded by the binomial jet grid
```
rfns(∇^j(op p r W))(x) ≤ 4^j · gridWindowSum kappa p r j · ∑_{q < p + j + 1} rfns(∇^q W)(x),
```
the rank-raising analogue of `rfns_iteratedCovGrad_grid`, proved by the same binomial covariant-Leibniz
induction on `j` over the tower's exact single-step Leibniz `covGrad_diffCurvGenuineDiffOp_eq` and the
per-order jet envelope `exists_proportional_diffCurvGenuineDiffOp`. -/
private theorem rfns_iteratedCovGrad_diffCurvGenuineDiffOp_grid
    (g : SmoothRiemannianMetric I M)
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p r, 0 ≤ kappa p r)
    (hrfns : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 1 + p) x
          ((diffCurvGenuineDiffOp (I := I) (M := M) g p r W).toSection x) ≤
        kappa p r * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x)) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1 + p) + j) x
          ((iteratedCovGrad g 0 (r + 1 + p) j
            (diffCurvGenuineDiffOp (I := I) (M := M) g p r W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns p r W x
  | succ j ih =>
      intro p r W x
      set K : ℝ := gridWindowSum kappa p r (j + 1) with hK_def
      set Sm : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hSm_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p r (j + 1)
      have hSm_nn : 0 ≤ Sm := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1 + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + 1 + p) (j + 1)
              (diffCurvGenuineDiffOp (I := I) (M := M) g p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1 + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + 1 + p) + 1) j
              (covGrad g 0 (r + 1 + p)
                (diffCurvGenuineDiffOp (I := I) (M := M) g p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_raise g 0 (r + 1 + p) j
          (diffCurvGenuineDiffOp (I := I) (M := M) g p r W) x).symm]
      rw [covGrad_diffCurvGenuineDiffOp_eq (I := I) (M := M) g p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + 1 + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + 1 + p) + 1) j
            (diffCurvGenuineDiffOp (I := I) (M := M) g (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + 1 + p) + 1) j
            (castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
              (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
                (covGrad g 0 r W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (r + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1 + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + 1 + (p + 1)) j
              (diffCurvGenuineDiffOp (I := I) (M := M) g (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad g 0 r W) x
      have hBshift : gridWindowSum kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_raise g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + 1 + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + 1 + p) j
              (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
                (covGrad g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ Sm := by
        rw [hsA_def, hSm_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ Sm := by
        rw [hsB_def, hSm_def]
        refine le_trans (sum_range_shift_le_raise (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _
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
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hSm_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1 + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + 1 + p) + 1) j
              (castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
                (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
                  (covGrad g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + 1 + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + 1 + p) j
              (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1)
                (covGrad g 0 r W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (r + 1) + 1 + p = r + 1 + (p + 1))
          (diffCurvGenuineDiffOp (I := I) (M := M) g p (r + 1) (covGrad g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-- **The graded curvature-jet bound for the differentiated-curvature section `genuineDiffCurvSection`.**
For a closed smooth Riemannian manifold `(M, g)` there is a valence/order-dependent nonnegative constant
family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and every smooth compactly-supported
`(0, s)`-tensor `S`, the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` (the `(∇R) S` field) is a **graded**
curvature jet of `S` of lowest order `0` and base width `1`:

```
rfns(∇^k (genuineDiffCurvSection g s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 0} S)(x).
```

This is the foundational order-`0`/width-`1` graded curvature-jet primitive (the `(∇R) S` carrier
bounded with ALL its iterated covariant gradients) the order-`m` curvature-jet induction consumes for the
differentiated-curvature leg.

**Proof.** `genuineDiffCurvSection g s S = diffCurvGenuineDiffOp g 0 s S` is the order-`0` base of the
differentiated `(∇R)·` tower, the operator-field action of the *fixed* smooth coefficient
`Ψ₀ s = ∇(Φ₀ s)`. The at-point covariant-Leibniz double grid
`rfns_iteratedCovGrad_diffCurvGenuineDiffOp_grid` at differentiation order `p = 0` (whose per-order jet
envelope `exists_proportional_diffCurvGenuineDiffOp` comes from the tower's rank-raising operator-field
normal form) bounds `∇^k` of that base by `4^k · gridWindowSum kappa 0 s k · ∑_{q < k + 1} rfns(∇^q S)`;
the contracted-order range `q < k + 1 = 1 + k` is the differentiation entering entirely on the curvature
factor, so the section enters at order `0` (width `1`). The constant family is the engine's single-sum
constant `c s k := √(4^k · gridWindowSum kappa 0 s k)`, frame-free since the per-order envelope is.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(genuineDiffCurvSection g s S)(x) = 0` at
`k = 0`, i.e. the differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` vanishes; false on a non-flat
manifold (`∇R ≠ 0`) for a non-parallel `S`. The constant family is genuinely positive. -/
theorem genuineDiffCurvSection_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g S (c s) 0 1
          (genuineDiffCurvSection (I := I) (M := M) g s S) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_diffCurvGenuineDiffOp (I := I) (M := M) g
  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s' k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 s k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 s k)
  -- The graded predicate at the order-`0` base of the differentiated `(∇R)·` tower.
  change riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + k) x
        ((iteratedCovGrad g 0 (s + 1) k
          (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x) ≤
      (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s k)) ^ 2 *
        ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 0)) x
            ((iteratedCovGrad g 0 s (i + 0) S).toSection x)
  rw [hcsq]
  -- The at-point grid for the differentiated `(∇R)·` tower, differentiation order `p = 0`, section `S`.
  have hgrid := rfns_iteratedCovGrad_diffCurvGenuineDiffOp_grid (I := I) (M := M) g
    kappa hkappa_nn hkappa k 0 s S x
  -- The order-`0` base is `genuineDiffCurvSection g s S`; the windows collapse to `range (k + 1)`.
  rw [diffCurvGenuineDiffOp_zero_eq_genuineDiffCurvSection (I := I) (M := M) g s S] at hgrid
  -- Normalize the contracted-order window in `hgrid`: `range (0 + k + 1) = range (k + 1)`.
  rw [Nat.zero_add] at hgrid
  refine le_trans (le_of_eq ?_) (hgrid.trans (le_of_eq ?_))
  · -- LHS rank reassociation `(s + 1 + 0) + k = (s + 1) + k`.
    norm_num
  · -- RHS: re-index the target window `range (1 + k) = range (k + 1)`, `i + 0 = i`.
    have hsum : ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 0)) x
            ((iteratedCovGrad g 0 s (i + 0) S).toSection x) =
        ∑ q ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
            ((iteratedCovGrad g 0 s q S).toSection x) := by
      rw [Nat.add_comm 1 k]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Nat.add_zero]
    rw [hsum, mul_assoc]

end Connection
end Integral
end DifferentialGeometry

end
