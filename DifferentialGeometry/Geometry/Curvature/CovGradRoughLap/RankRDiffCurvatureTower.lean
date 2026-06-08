import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRPureRCurvatureTower

/-!
# The frame-free differentiated `(∇R)·` curvature tower at contravariant valence `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-valence-`r` lift of the intrinsic differentiated-curvature graded-jet tower
`diffCurvGenuineDiffOp` (`DiffCurvatureGenuineTower`), the `(∇R) S` operator-field carrier of the
order-`2` rough-Laplacian / covariant-gradient commutator defect.  The rank-`0` tower is hard-locked to
contravariant rank `0`: its order-`0` base is the operator-field action `appCc (∇Φ₀ r) W` of the fixed
smooth differentiated-curvature operator field `Ψ₀ r := ∇(Φ₀ r)` (`diffCurvOpField`,
`covGrad (curvOpField g r)`), where the contravariant-rank-`0`-locked action `appCc` and the
rank-`0`-locked curvature operator field `curvOpField` both carry a literal contravariant `0`.

This file rebuilds the entire tower **at a fixed but generic contravariant valence `r`** (R7 — extend,
do not duplicate) through the contravariant-valence-`r` operator-field calculus `appCcRS`
(`OperatorFieldCovariantCalculusRS`), so the contravariant-rank-`r` curvature-jet tower of the order-`2`
commutator defect can consume the same intrinsic graded curvature-jet packaging the rank-`0` tower
consumes, exactly as `RankRPureRCurvatureTower` lifts the pure-Riemann tower to valence `r`.

The construction differs from rank `0` in exactly one index: every `0` in the contravariant slot of the
operator-field action becomes `r` (`appCc → appCcRS g r`).  The recursive single-step covariant Leibniz
remainder, the operator-field normal form, the per-order/per-width proportional fibre envelope, and the
binomial covariant-Leibniz `rfns` grid all port verbatim with `appCc` replaced by `appCcRS g r`.

## What is proved vs. posited

* the **order-`p` differentiated operator** `diffCurvGenuineDiffOpRS` is the exact covariant-Leibniz
  remainder, so the single-step Leibniz field `covGrad_diffCurvGenuineDiffOpRS_eq` holds *by
  `sub_add_cancel`* — *proved*; the rank-raising operator-field normal form (`NormalFormRaiseRS`) and the
  binomial covariant-Leibniz `rfns` grid `rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid` are *proved*
  outright through the `appCcRS` calculus, with no posit of their own;
* the **rank-`r` curvature operator field** `exists_curvOpFieldRS` — the smooth operator-field section
  whose `appCcRS` action realises the order-`0` moving-centre pure-Riemann curvature endomorphism
  `genuinePureRDiffOpRS g r 0 rr` at valence `r` — is the verbatim contravariant-valence-`r` mirror of
  the rank-`0` curvature operator field `exists_pureRGenuineDiffOp_base_appCc` (whose own rank-`0`
  realisation bottoms on the atomic moving-frame freeze node), absent sorry-free at valence `r`, posited
  here as one precise true child;
* the **per-order, per-width frame-free proportional fibre envelope**
  `exists_proportional_diffCurvGenuineDiffOpRS` is *proved* outright as the verbatim
  contravariant-valence-`r` mirror of the rank-`0` `exists_proportional_diffCurvGenuineDiffOp`: the
  rank-raising operator-field normal form (`NormalFormRaiseRS`) holds at every order because the order-`0`
  base is a fixed-coefficient `appCcRS` action, and the uniform `appCcRS` fibre bound
  `exists_uniform_riemannianFiberNormSq_appCcRS_le` (`OperatorFieldCovariantCalculusRS`) accumulates the
  jet envelope — no envelope posit of its own.

Consumers transitively depend on `sorryAx` through the single posited node `exists_curvOpFieldRS`.

The `(∇R) S` carrier `diffCurvSectionRS g r s S := diffCurvGenuineDiffOpRS g r 0 s S` is the order-`0`
base; its iterated-gradient grid bound of lowest order `0` and width `1`
(`exists_diffCurvSectionRS_iteratedCovGrad_grid_bound`, the raw fibre-inequality form) is *proved* from
the `rfns` grid, exactly the rank-`r` mirror of the rank-`0` `genuineDiffCurvSection_gradedCurvJet`.  The
downstream consumer `OrderSeparatedCurvatureJetRS` (which imports this file and owns the
`IsGradedCurvJetRS` predicate) packages it as the graded curvature jet
`exists_diffCurvSectionRS_gradedCurvJet`.

Because the `(∇R)·` tower genuinely *raises* the covariant rank by one at order `0` (it carries the
codomain `rr + 1 + p`, not `rr + p`), it is **not** a rank-preserving `DiffBilinOpRS` (whose order-`0`
operator preserves the rank); the binomial covariant-Leibniz grid is therefore built directly here
through the rank-raising normal form, exactly as the rank-`0` differentiated-curvature tower
`DiffCurvatureGenuineTower` builds its own raising grid rather than a `DiffBilinOp` instance.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`.  The construction stays
intrinsic: `appCcRS` operator-field actions, `covGrad` covariant gradients, and `rfns` fibre norms only —
no moving-frame extraction, no chart-frame jet.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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

/-! ## The rank-`r` curvature operator field and the differentiated coefficient -/

set_option linter.unusedVariables false in
/-- **The rank-`r` curvature operator field (posited general-valence curvature child).** For a closed
smooth Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is a family of fixed
smooth `(rr, rr)`-operator fields `Φ : ∀ rr, SmoothCcTensor g (rr + 0) (rr + 0)` whose
contravariant-valence-`r` operator-field action `appCcRS` recovers the order-`0` moving-centre
pure-Riemann curvature endomorphism `genuinePureRDiffOpRS g r 0 rr W` at every width `rr`:
```
appCcRS g r (rr + 0) (rr + 0) (Φ rr) W = genuinePureRDiffOpRS g r 0 rr W.
```

**Why this is TRUE.** This is the verbatim contravariant-valence-`r` mirror of the rank-`0` curvature
operator field `exists_pureRGenuineDiffOp_base_appCc` (`FrozenFramePureRCurvatureTower`), whose own
rank-`0` realisation packages the order-`0` moving-frame pure-Riemann endomorphism fibre as the operator
field `Φ₀ r` and bottoms on the atomic moving-frame freeze node disclosed there.  At valence `r` the
order-`0` moving-centre endomorphism `genuinePureRDiffOpRS g r 0 rr` (`RankRPureRCurvatureTower`) is the
genuine `g`-metric curvature trace, but the smooth `appCcRS`-operator-field realisation
(`riemannSec`-uncurry of the bundled curvature operator `riemannOp (tensorCov g rr rr)` as a fixed
`SmoothCcTensor g rr rr` section, frame-free) uses the rank-`0`-locked moving-frame freeze, absent
sorry-free at valence `r`, so this curvature operator field is posited here as one precise true child.
Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate `Φ ≡ 0` is rejected on any non-flat manifold: at `rr = m + 1` and a
section `W` whose slot-`0` reading carries a non-zero pure-Riemann contraction, the right-hand
`genuinePureRDiffOpRS g r 0 (m + 1) W` is the genuine moving-frame trace `∑ᵢ R(Bᵢ, ·)(slot0_{Bᵢ} W)`,
genuinely nonzero (`R ≠ 0`), while `appCcRS g r _ _ 0 W = 0`; the operator field must carry the genuine
curvature operator and is genuinely nonzero. -/
theorem exists_curvOpFieldRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Φ : ∀ rr : ℕ, SmoothCcTensor g (rr + 0) (rr + 0),
      ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
        appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0) (Φ rr) W =
          genuinePureRDiffOpRS (I := I) (M := M) g r 0 rr W := by
  sorry

/-- **The rank-`r` curvature operator field `Φ₀ rr`.** The `Classical.choose` witness of
`exists_curvOpFieldRS`: the fixed smooth `(rr, rr)`-operator field whose `appCcRS` action recovers the
order-`0` moving-centre pure-Riemann curvature endomorphism at valence `r`. The valence-`r` mirror of
`curvOpField`. -/
noncomputable def curvOpFieldRS (g : SmoothRiemannianMetric I M) (r rr : ℕ) :
    SmoothCcTensor g (rr + 0) (rr + 0) :=
  (Classical.choose (exists_curvOpFieldRS (I := I) (M := M) g r)) rr

/-- **The curvature operator base spec for `curvOpFieldRS`.** The `appCcRS` action of the rank-`r`
curvature operator field on a `(r, rr)`-tensor `W` recovers the order-`0` moving-centre pure-Riemann
curvature endomorphism `genuinePureRDiffOpRS g r 0 rr W`. The valence-`r` mirror of
`appCc_curvOpField_eq_pureRGenuineDiffOp`. -/
theorem appCcRS_curvOpFieldRS_eq_genuinePureRDiffOpRS
    (g : SmoothRiemannianMetric I M) (r rr : ℕ) (W : SmoothCcTensor g r rr) :
    appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0) (curvOpFieldRS (I := I) (M := M) g r rr) W =
      genuinePureRDiffOpRS (I := I) (M := M) g r 0 rr W :=
  Classical.choose_spec (exists_curvOpFieldRS (I := I) (M := M) g r) rr W

/-- **The fixed differentiated-curvature operator field `Ψ₀ rr = ∇(Φ₀ rr)` at valence `r`.** The
covariant gradient of the rank-`r` curvature operator field `curvOpFieldRS g r rr`, a fixed smooth
`(rr, rr + 1)`-operator field whose `appCcRS` action on a `(r, rr)`-tensor `W` is the differentiated-
curvature carrier `(∇R) W`. The valence-`r` mirror of `diffCurvOpField`. -/
noncomputable def diffCurvOpFieldRS (g : SmoothRiemannianMetric I M) (r rr : ℕ) :
    SmoothCcTensor g (rr + 0) (rr + 0 + 1) :=
  covGrad (I := I) (M := M) g (rr + 0) (rr + 0) (curvOpFieldRS (I := I) (M := M) g r rr)

/-! ## The order-`p` differentiated `(∇R)·` tower at valence `r` -/

/-- **The order-`p` differentiated `(∇R)·` curvature operator at valence `r`.** Acting on a smooth
compactly-supported `(r, rr)`-tensor section `W`, the `p`-times covariantly-differentiated action of the
fixed differentiated-curvature operator field `Ψ₀ rr = ∇(Φ₀ rr)`, defined recursively as the exact
covariant-Leibniz remainder:

* `p = 0`: the order-`0` action `appCcRS (Ψ₀ rr) W` (the `(∇R) W` carrier);
* `p + 1`: `∇(op p rr W) − (rank-cast) op p (rr + 1) (∇W)` — the differentiated-coefficient remainder
  (the input section's derivative `∇W` cancels), rank-cast `(rr + 1) + 1 + p = rr + 1 + (p + 1)`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`. The base coefficient `Ψ₀ rr`
is a *fixed* smooth section, so the differentiated tower differentiates only the curvature coefficient,
never a frame jet; the section enters at order `0`. The valence-`r` mirror of `diffCurvGenuineDiffOp`. -/
noncomputable def diffCurvGenuineDiffOpRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p)
  | 0, rr => fun W =>
      appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0 + 1)
        (diffCurvOpFieldRS (I := I) (M := M) g r rr) W
  | (p + 1), rr => fun W =>
      covGrad (I := I) (M := M) g r (rr + 1 + p)
          (diffCurvGenuineDiffOpRS g r p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineDiffOpRS g r p (rr + 1) (covGrad (I := I) (M := M) g r rr W))

/-- **The order-`0` differentiated `(∇R)·` operator is the action of the fixed field `Ψ₀ rr`.** The
base-rank operator-field-action factorisation: `diffCurvGenuineDiffOpRS g r 0 rr W = appCcRS (Ψ₀ rr) W`.
The valence-`r` mirror of `diffCurvGenuineDiffOp_zero_eq_appCc`. -/
theorem diffCurvGenuineDiffOpRS_zero_eq_appCcRS (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W : SmoothCcTensor g r rr) :
    diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 rr W =
      appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0 + 1)
        (diffCurvOpFieldRS (I := I) (M := M) g r rr) W := rfl

/-- **The exact single-step covariant Leibniz of the differentiated `(∇R)·` tower at valence `r`.** By
the recursive definition, `∇(op p rr W)` splits exactly into the higher-order remainder `op (p + 1) rr W`
and the rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. The valence-`r` mirror of
`covGrad_diffCurvGenuineDiffOp_eq`. -/
theorem covGrad_diffCurvGenuineDiffOpRS_eq (g : SmoothRiemannianMetric I M) (r p rr : ℕ)
    (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + 1 + p)
        (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W) =
      diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W +
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
            (covGrad (I := I) (M := M) g r rr W)) := by
  change _ = (covGrad (I := I) (M := M) g r (rr + 1 + p)
      (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W) -
      castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
        (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
          (covGrad (I := I) (M := M) g r rr W))) + _
  rw [sub_add_cancel]

/-! ## The rank-raising operator-field normal form at valence `r` -/

/-- **The operator-field normal form of the differentiated `(∇R)·` tower at order `p`, valence `r`,
width `rr`.** The order-`p` tower value `op p rr W` decomposes as a finite sum of operator-field actions
of fixed smooth operator fields `Ψ k : SmoothCcTensor g (rr + k) (rr + 1 + p)` on the covariant jets
`∇^k W` of the contracted `(r, rr)`-section, `k < p + 1` (the rank-raising analogue of `NormalFormRS`,
output rank `rr + 1 + p`). The valence-`r` mirror of `NormalFormRaise`. -/
private def NormalFormRaiseRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
    (p rr : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + 1 + p),
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k) (iteratedCovGrad g r rr k W)

set_option linter.unusedSectionVars false in
/-- **The gradient of a rank-raising normal-form sum expands termwise at valence `r`.** -/
private theorem covGrad_normalFormRaiseRS_sum (g : SmoothRiemannianMetric I M) (r p rr : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + 1 + p)) (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + 1 + p)
        (∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k) (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + (p + 1))
            (covGrad (I := I) (M := M) g (rr + k) (rr + 1 + p) (Ψ k)) (iteratedCovGrad g r rr k W) +
          appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
            (slotExtend (I := I) (M := M) g (rr + k) (rr + 1 + p) (Ψ k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k) (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl

set_option linter.unusedSectionVars false in
/-- **The rank-cast lower-tower normal form on `∇W` re-expressed in canonical jets (rank-raising), at
valence `r`.** The output-rank-`(rr + 1) + 1 + p` analogue of `castRankCc_appCcRS_iteratedCovGrad_covGrad`. -/
private theorem castRankCc_appCcRS_iteratedCovGrad_covGrad_raise (g : SmoothRiemannianMetric I M)
    (r p rr k : ℕ)
    (Ψ : SmoothCcTensor g ((rr + 1) + k) ((rr + 1) + 1 + p)) (W : SmoothCcTensor g r rr) :
    castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
        (appCcRS (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + 1 + p) Ψ
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
        (castSrcCc g (rr + 1 + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
          (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1)) Ψ))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appCcRS_castRankCc_db g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1)) Ψ
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))

set_option linter.unusedSectionVars false in
/-- **The rank-raising normal form propagates up the differentiated tower at valence `r`.** -/
private theorem normalFormRaiseRS_succ (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + 1 + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormRaiseRS (I := I) (M := M) g r op p rr) (rr : ℕ) :
    NormalFormRaiseRS (I := I) (M := M) g r op (p + 1) rr := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp rr
  obtain ⟨Ψr1, hΨr1⟩ := hp (rr + 1)
  set Tk : (k : ℕ) → SmoothCcTensor g (rr + (k + 1)) (rr + 1 + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g (rr + k) (rr + 1 + p) (Ψr k) -
      castSrcCc g (rr + 1 + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
        (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1)) (Ψr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + 1 + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1))
          else 0)
          + Tk k, ?_⟩
  intro W
  have hrec : op (p + 1) rr W =
      covGrad g r (rr + 1 + p) (op p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hΨr W]
  rw [covGrad_normalFormRaiseRS_sum (I := I) (M := M) g r p rr Ψr W]
  rw [hΨr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (appCcRS (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + 1 + p) (Ψr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (castSrcCc g (rr + 1 + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCcRS_iteratedCovGrad_covGrad_raise (I := I) (M := M) g r p rr k (Ψr1 k) W)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    appCcRS (I := I) (M := M) g r (rr + j) (rr + 1 + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + 1 + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          ((if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCcRS_add_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (slotExtend (I := I) (M := M) g (rr + k) (rr + 1 + p) (Ψr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (castSrcCc g (rr + 1 + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castRankCc_db g ((rr + 1) + k) (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCcRS_sub_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        appCcRS (I := I) (M := M) g r (rr + (k + 1)) (rr + 1 + (p + 1))
          (covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + 1 + p) (Ψr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + (p + 1))
      (covGrad (I := I) (M := M) g (rr + k) (rr + 1 + p) (Ψr k)) (iteratedCovGrad g r rr k W)) p]
  abel

set_option linter.unusedSectionVars false in
/-- **The order-`0` base factorisation is the order-`0` rank-raising normal form at valence `r`.** -/
private theorem normalFormRaiseRS_zero (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
    (rr : ℕ) (Φ₀ : SmoothCcTensor g (rr + 0) (rr + 0 + 1))
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0 + 1) Φ₀ W) :
    NormalFormRaiseRS (I := I) (M := M) g r op 0 rr := by
  refine ⟨fun k => match k with | 0 => Φ₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl

set_option linter.unusedSectionVars false in
/-- **The rank-raising operator-field normal form holds at every order at valence `r`.** A
recursively-differentiated rank-raising tower `op` whose single-step covariant Leibniz is the exact
remainder (`covGrad_op`) and whose order-`0` base is a fixed-operator-field action at every width
(`hbase`) admits the operator-field normal form at every order `p` and width `rr`. The valence-`r`
mirror of `normalFormRaise_of_base`. -/
private theorem normalFormRaiseRS_of_base (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + 1 + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (Φ₀ : ∀ rr : ℕ, SmoothCcTensor g (rr + 0) (rr + 0 + 1))
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = appCcRS (I := I) (M := M) g r (rr + 0) (rr + 0 + 1) (Φ₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormRaiseRS (I := I) (M := M) g r op p rr := by
  induction p with
  | zero => exact fun rr => normalFormRaiseRS_zero (I := I) (M := M) g r op rr (Φ₀ rr) (hbase rr)
  | succ p ih => exact fun rr => normalFormRaiseRS_succ (I := I) (M := M) g r op covGrad_op p ih rr

set_option linter.unusedSectionVars false in
/-- **The per-order, per-width jet envelope of the rank-raising differentiated tower from its normal
form at valence `r`.** If `op p rr` admits the rank-raising operator-field normal form, then its
intrinsic squared fibre norm is bounded, uniformly over the compact `M`, by a nonnegative constant times
the order-`≤ p` covariant jet of the contracted section. The valence-`r` mirror of
`exists_jet_bound_of_normalFormRaise`. -/
private theorem exists_jet_bound_of_normalFormRaiseRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + 1 + p))
    (p rr : ℕ) (hNF : NormalFormRaiseRS (I := I) (M := M) g r op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := hNF
  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k)
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _
  rw [hΨ W, SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + 1 + p) x
    (Finset.range (p + 1))
    (fun k => (appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]
  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
          ((appCcRS (I := I) (M := M) g r (rr + k) (rr + 1 + p) (Ψ k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
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

/-- **The per-order, per-width section-proportional fibre envelope for the differentiated `(∇R)·` tower
at valence `r`, in jet form.** For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant
valence `r` there is a nonnegative envelope family `kappa : ℕ → ℕ → ℝ` such that for every order `p`,
width `rr`, smooth compactly-supported `(r, rr)`-tensor `W`, and base point `x`,
```
rfns(diffCurvGenuineDiffOpRS g r p rr W)(x) ≤ kappa p rr · ∑_{q < p + 1} rfns(∇^q W)(x).
```
The tower's order-`0` base is the action of the fixed smooth field `Ψ₀ rr = ∇(Φ₀ rr)`, so the
rank-raising operator-field normal form holds at every order (`normalFormRaiseRS_of_base`), whence the
jet envelope (`exists_jet_bound_of_normalFormRaiseRS`): each `∇^{≤ p} Ψ₀` coefficient is a fixed smooth
field, uniformly fibre-operator-bounded over the compact `M`.  The valence-`r` mirror of the rank-`0`
`exists_proportional_diffCurvGenuineDiffOp` — *proved* outright off the posited curvature operator field
`exists_curvOpFieldRS` (transited through the order-`0` base), with no envelope posit of its own. -/
theorem exists_proportional_diffCurvGenuineDiffOpRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p rr, 0 ≤ kappa p rr) ∧
      ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
            ((diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  have hNF : ∀ (p rr : ℕ),
      NormalFormRaiseRS (I := I) (M := M) g r (diffCurvGenuineDiffOpRS (I := I) (M := M) g r) p rr :=
    fun p => normalFormRaiseRS_of_base (I := I) (M := M) g r
      (diffCurvGenuineDiffOpRS (I := I) (M := M) g r)
      (covGrad_diffCurvGenuineDiffOpRS_eq (I := I) (M := M) g r)
      (fun rr => diffCurvOpFieldRS (I := I) (M := M) g r rr)
      (fun rr W => diffCurvGenuineDiffOpRS_zero_eq_appCcRS (I := I) (M := M) g r rr W) p
  choose kap hkap_nn hkap using fun p rr =>
    exists_jet_bound_of_normalFormRaiseRS (I := I) (M := M) g r
      (diffCurvGenuineDiffOpRS (I := I) (M := M) g r) p rr (hNF p rr)
  exact ⟨kap, hkap_nn, hkap⟩

/-! ## The iterated-gradient grid for the differentiated `(∇R)·` tower at valence `r` -/

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast at valence `r` (HEq form).** -/
private theorem rfns_toSection_heq_congr_raiseRS (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form) at valence `r`.**
The intrinsic squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_raiseRS (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_raiseRS g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g r s m W) x

set_option linter.unusedSectionVars false in
/-- A `range`-sum shift bookkeeping helper. -/
private lemma sum_range_shift_le_raiseRS (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

/-- **The binomial covariant-Leibniz `rfns` double grid for the differentiated `(∇R)·` tower at valence
`r`.** For every gradient order `j`, differentiation order `p`, base width `rr`, section `W`, and point
`x`, the intrinsic squared fibre norm of `∇^j(op p rr W)` is bounded by the binomial jet grid
```
rfns(∇^j(op p rr W))(x) ≤ 4^j · gridWindowSum kappa p rr j · ∑_{q < p + j + 1} rfns(∇^q W)(x),
```
the valence-`r` rank-raising analogue of `rfns_iteratedCovGrad_grid`, proved by the same binomial
covariant-Leibniz induction on `j` over the tower's exact single-step Leibniz
`covGrad_diffCurvGenuineDiffOpRS_eq` and the per-order jet envelope (supplied as the hypotheses
`kappa`/`hrfns`). The valence-`r` mirror of `rfns_iteratedCovGrad_diffCurvGenuineDiffOp_grid`. -/
private theorem rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p rr, 0 ≤ kappa p rr)
    (hrfns : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + 1 + p) x
          ((diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W).toSection x) ≤
        kappa p rr * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
            ((iteratedCovGrad g r rr q W).toSection x)) (j : ℕ) :
    ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + p) + j) x
          ((iteratedCovGrad g r (rr + 1 + p) j
            (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p rr j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  induction j with
  | zero =>
      intro p rr W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p rr 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) =
          kappa p rr * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns p rr W x
  | succ j ih =>
      intro p rr W x
      set K : ℝ := gridWindowSum kappa p rr (j + 1) with hK_def
      set Sm : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
          ((iteratedCovGrad g r rr q W).toSection x) with hSm_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p rr (j + 1)
      have hSm_nn : 0 ≤ Sm := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + p) + (j + 1)) x
            ((iteratedCovGrad g r (rr + 1 + p) (j + 1)
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
            ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
              (covGrad g r (rr + 1 + p)
                (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_raiseRS g r (rr + 1 + p) j
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p rr W) x).symm]
      rw [covGrad_diffCurvGenuineDiffOpRS_eq (I := I) (M := M) g r p rr W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
          ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
            (diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W)).toSection x)
          ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
            (castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) rr j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (rr + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
          ((iteratedCovGrad g r rr q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + (q + 1)) x
          ((iteratedCovGrad g r rr (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1 + (p + 1)) + j) x
            ((iteratedCovGrad g r (rr + 1 + (p + 1)) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r (p + 1) rr W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) rr W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (rr + 1) (covGrad g r rr W) x
      have hBshift : gridWindowSum kappa p (rr + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g r ((rr + 1) + q) x
                ((iteratedCovGrad g r (rr + 1) q (covGrad g r rr W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_raiseRS g r rr q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1) + 1 + p) + j) x
            ((iteratedCovGrad g r ((rr + 1) + 1 + p) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p rr j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p rr j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ Sm := by
        rw [hsA_def, hSm_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ Sm := by
        rw [hsB_def, hSm_def]
        refine le_trans (sum_range_shift_le_raiseRS (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
            ((iteratedCovGrad g r rr q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) rr j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (rr + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + (q + 1)) x _
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
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p rr (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
                ((iteratedCovGrad g r rr q W).toSection x) := by
        rw [hK_def, hSm_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1 + p) + 1) + j) x
            ((iteratedCovGrad g r ((rr + 1 + p) + 1) j
              (castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
                (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                  (covGrad g r rr W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g r (((rr + 1) + 1 + p) + j) x
            ((iteratedCovGrad g r ((rr + 1) + 1 + p) j
              (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1)
                (covGrad g r rr W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g r (by omega : (rr + 1) + 1 + p = rr + 1 + (p + 1))
          (diffCurvGenuineDiffOpRS (I := I) (M := M) g r p (rr + 1) (covGrad g r rr W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-! ## The `(∇R) S` carrier section and its graded curvature jet at valence `r` -/

/-- **The frame-free differentiated-curvature `(∇R) S` carrier section at valence `r`.** The order-`0`
base of the differentiated `(∇R)·` tower: the operator-field action `appCcRS (Ψ₀ s) S` of the fixed
differentiated-curvature operator field on the smooth compactly-supported `(r, s)`-tensor `S`, a smooth
compactly-supported `(r, s + 1)`-tensor. The valence-`r` mirror of `genuineDiffCurvSection`. -/
noncomputable def diffCurvSectionRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r (s + 1) :=
  diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S

/-- **The `(∇R) S` carrier is the order-`0` base of the differentiated `(∇R)·` tower.** By definition. -/
theorem diffCurvSectionRS_eq_diffCurvGenuineDiffOpRS_zero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    diffCurvSectionRS (I := I) (M := M) g r s S =
      diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S := rfl

set_option linter.unusedSectionVars false in
/-- **The differentiated-curvature `(∇R) S` carrier iterated-gradient grid at valence `r`.** For a closed
smooth Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is a valence/order-
dependent nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every
smooth compactly-supported `(r, s)`-tensor `S`, every gradient order `k` and every point `x`, the
`k`-fold iterated covariant gradient of the gauge-glued tensorial differentiated-curvature carrier
`diffCurvSectionRS g r s S` (the `(∇R) S` contraction) is fibre-bounded by the truncated contracted-order
window `0 … k` of the iterated gradients of `S`:
```
rfns(∇^k (diffCurvSectionRS g r s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 0} S)(x).
```
This is the contravariant-valence-`r` mirror of the rank-`0`
`genuineDiffCurvSection_gradedCurvJet` (the `(∇R) S` graded jet of lowest order `0` and width `1`), in
the *raw fibre-inequality* form (it does not reference the downstream predicate `IsGradedCurvJetRS`, which
lives in the consumer `OrderSeparatedCurvatureJetRS` that imports this file), exactly as
`exists_GcurvSectionRS_iteratedCovGrad_grid_bound` is the raw form of the pure-Riemann section's grid.

**Proof.** `diffCurvSectionRS g r s S = diffCurvGenuineDiffOpRS g r 0 s S` is the order-`0` base of the
differentiated `(∇R)·` tower. The at-point covariant-Leibniz double grid
`rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid` at differentiation order `p = 0` (whose per-order jet
envelope `exists_proportional_diffCurvGenuineDiffOpRS` comes from the tower's rank-raising operator-field
normal form) bounds `∇^k` of that base by `4^k · gridWindowSum kappa 0 s k · ∑_{q < k + 1} rfns(∇^q S)`;
the contracted-order range `q < k + 1 = 1 + k` is the differentiation entering entirely on the curvature
factor, so the section enters at order `0` (width `1`). The constant family is the engine's single-sum
constant `c s k := √(4^k · gridWindowSum kappa 0 s k)`. Consumers transitively depend on `sorryAx`
through the single posited node `exists_curvOpFieldRS`.

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` (where `∇^0(diffCurvSectionRS g r s S) =
diffCurvSectionRS g r s S`) forces `rfns(diffCurvSectionRS g r s S)(x) = 0`, i.e. the differentiated-
curvature contraction `(∇R) S` vanishes; *false* on a non-flat manifold (`∇R ≠ 0`) for a non-parallel
`S`. The constant family is genuinely positive. -/
theorem exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + k) x
            ((iteratedCovGrad g r (s + 1) k
              (diffCurvSectionRS (I := I) (M := M) g r s S)).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 0)) x
              ((iteratedCovGrad g r s (i + 0) S).toSection x) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_diffCurvGenuineDiffOpRS (I := I) (M := M) g r
  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s' k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 s k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 s k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 s k)
  rw [hcsq]
  -- The at-point grid for the differentiated `(∇R)·` tower, differentiation order `p = 0`, section `S`.
  have hgrid := rfns_iteratedCovGrad_diffCurvGenuineDiffOpRS_grid (I := I) (M := M) g r
    kappa hkappa_nn hkappa k 0 s S x
  -- The order-`0` base is `diffCurvSectionRS g r s S`; the windows collapse to `range (k + 1)`.
  rw [show (diffCurvGenuineDiffOpRS (I := I) (M := M) g r 0 s S) =
      diffCurvSectionRS (I := I) (M := M) g r s S from rfl] at hgrid
  -- Normalize the contracted-order window in `hgrid`: `range (0 + k + 1) = range (k + 1)`.
  rw [Nat.zero_add] at hgrid
  refine le_trans (le_of_eq ?_) (hgrid.trans (le_of_eq ?_))
  · -- LHS rank reassociation `(s + 1 + 0) + k = (s + 1) + k`.
    norm_num
  · -- RHS: re-index the target window `range (1 + k) = range (k + 1)`, `i + 0 = i`.
    have hsum : ∑ i ∈ Finset.range (1 + k),
          riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 0)) x
            ((iteratedCovGrad g r s (i + 0) S).toSection x) =
        ∑ q ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g r (s + q) x
            ((iteratedCovGrad g r s q S).toSection x) := by
      rw [Nat.add_comm 1 k]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Nat.add_zero]
    rw [hsum, mul_assoc]

end Connection
end Integral
end DifferentialGeometry

end
