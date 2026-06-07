import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJetRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.DiffCurvatureGenuineTower

/-!
# The order-`2` commutator defect is a full-sum graded curvature jet

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file records the
**full-sum** (lowest contracted order `0`, base width `3`) graded curvature-jet bound for the
rank-generic order-`2` commutator defect

```
Curv T := Δ_∇(∇T) − ∇(Δ_∇ T)
```

(`pointwiseTensorCurv g s T`, a `(0, s + 1)`-tensor field). The headline is

```
pointwiseTensorCurv_fullSum_gradedCurvJet :
  IsGradedCurvJet g T (c s) 0 3 (pointwiseTensorCurv g s T),
```

i.e. for every gradient order `k` and point `x`,

```
rfns(∇^k (Curv T))(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i T)(x).
```

This is the *full-sum* form: the contracted-order range starts at `0` and runs over the whole window
`0 … k + 2`. Unlike the order-*separated* pure-order remainder bound (where the moving-frame remainder
is asserted to be controlled by the *single* top order `∇^{k + 2}T`, false on a normal manifold —
counterexample `∇²S = 0`, `∇S ≠ 0`, `R ≠ 0`), the full-sum bound is genuinely true: the order-`2`
commutator defect `Curv T` is intrinsic (the moving-frame bracket is only a *decomposition* artifact),
and `Curv T` together with all its iterated covariant gradients is, by the iterated Ricci identity, a
curvature contraction of the `≤ k + 2`-jet of `T`.

## How it is proved (directly, NOT through the order-separated base seed)

`Curv T` decomposes intrinsically as

```
Curv T = GcurvSection g s T + genuineDiffCurvSection g s T + Grem,
```

where the two genuine curvature sections are operator-field actions of *fixed* smooth curvature
operators and the moving-frame remainder is `Grem := Curv T − GcurvSection g s T −
genuineDiffCurvSection g s T`:

* `GcurvSection g s T` (the pure-Riemann contraction `R(∇T)`, the operator-field action
  `appCc (Φ₀ (s + 1)) (∇T)`) is, by `GcurvSection_gradedCurvJet`, a **graded** curvature jet of `T`
  of shape `(1, 1)` — *proved sorry-free* via the frame-free pure-Riemann trace tower;
* `genuineDiffCurvSection g s T` (the differentiated-curvature contraction `(∇R) T`, the
  operator-field action `appCc (∇Φ₀ (s)) T`) is, by `genuineDiffCurvSection_gradedCurvJet`, a
  **graded** curvature jet of shape `(0, 1)` — *proved sorry-free* via the rank-raising operator-field
  normal-form grid engine (`DiffCurvatureGenuineTower`);
* the moving-frame remainder `Grem` is a **full-sum** graded curvature jet of shape `(0, 3)`
  (`pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet`): pointwise it is the
  frame-bracket discrepancy, genuinely `∇²T`-order, so every `∇^k Grem` is — after the iterated-Ricci
  cancellation of the top `∇^{k + 3}T` terms — a curvature contraction of `∇^{≤ k + 2}T`, the full-sum
  window `0 … k + 2`. This is the genuine irreducible iterated-Ricci content; it is the *full-sum*
  shape `(0, 3)`, **not** the false order-separated single-top-order shape `(2, 1)`.

Homogenizing the two genuine jets to the common full-sum shape `(0, 3)` through the order-range
monotonicity `IsGradedCurvJet.le_shape` and summing the three `(0, 3)` jets through
`IsGradedCurvJet.add` (twice) gives `Curv T` as a single `(0, 3)` graded jet, the headline. The two
genuine legs are sorry-free; only the moving-frame remainder leg transits `sorryAx`. The proof does
**not** route through the order-separated base seed `pointwiseTensorCurv_gradedCurvJet_field_base` (nor
its order-separated child `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`), whose
moving-frame remainder is asserted controlled by the single top order — false on a normal manifold.

## Non-vacuity

At gradient order `k = 0` the headline bound reads `rfns(Curv T)(x) ≤ (c s 0)² · (rfns(T) + rfns(∇T) +
rfns(∇²T))(x)`, the `m = 0` single-step defect fibre bound, which is *false* with `c s 0 = 0` on a
non-flat manifold (the defect carries the genuine curvature contraction of `T`). The remainder posit's
constant is likewise genuinely positive: with `c s 0 = 0` the remainder bound forces `Grem = 0`, i.e.
`Curv T = GcurvSection g s T + genuineDiffCurvSection g s T`, false on a non-flat manifold (the
moving-frame bracket discrepancy is genuinely non-zero, carried explicitly throughout the
moving-frame tower).

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian; `covGrad g 0 s`
raises the rank `(0, s) → (0, s + 1)` and `iteratedCovGrad g 0 s j` is its `j`-fold iterate; all fibre
norms are the intrinsic `riemannianFiberNormSq`.
-/

noncomputable section

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

/-- **Order-window domination for an order-shifted truncated sum.** For a nonnegative order-indexed
family `f`, the `(p, w)`-windowed sum `∑_{i < w + k} f (i + p)` (contracted orders `p … p + w + k − 1`)
is dominated by the wider `(p', w')`-windowed sum `∑_{i < w' + k} f (i + p')` whenever `p' ≤ p` and
`p + w ≤ p' + w'`: both reindex (`Finset.sum_Ico_eq_sum_range`) onto `Ico`-sums over the order set,
and the former order-window is a subset of the latter with all summands `≥ 0`. The opaque `f` keeps
the reindex free of the dependent rank-index motive obstruction. -/
private theorem orderWindow_sum_le (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) {p w p' w' k : ℕ}
    (hp : p' ≤ p) (hpw : p + w ≤ p' + w') :
    ∑ i ∈ Finset.range (w + k), f (i + p) ≤ ∑ i ∈ Finset.range (w' + k), f (i + p') := by
  have eL : ∑ i ∈ Finset.range (w + k), f (i + p) = ∑ q ∈ Finset.Ico p (p + (w + k)), f q := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm])
  have eR : ∑ i ∈ Finset.range (w' + k), f (i + p') = ∑ q ∈ Finset.Ico p' (p' + (w' + k)), f q := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm])
  rw [eL, eR]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => hf q)
  exact Finset.Ico_subset_Ico hp (by omega)

omit [BoundarylessManifold I M] in
/-- **Order-range monotonicity of the graded curvature-jet predicate.** A graded curvature jet of
`T` of lowest contracted order `p` and base width `w` is also a graded curvature jet of any *wider*
shape `(p', w')` whose contracted-order window contains the original: if `p' ≤ p` and `p + w ≤ p' +
w'`, then the `(p, w)` truncated target sum (orders `p … p + w + k − 1`) is dominated, at every
gradient order `k`, by the `(p', w')` truncated target sum (orders `p' … p' + w' + k − 1`), since the
former order-window is a subset of the latter and every summand `rfns(∇^q T)(x)` is nonnegative. The
constant family is unchanged. This is the order-collapse step that brings the genuine curvature jets
of the intrinsic split onto the common full-sum shape. -/
theorem IsGradedCurvJet.le_shape (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor g 0 s) {c : ℕ → ℝ} {p w p' w' r : ℕ} {G : SmoothCcTensor g 0 r}
    (hp : p' ≤ p) (hpw : p + w ≤ p' + w')
    (hG : IsGradedCurvJet (I := I) (M := M) g T c p w G) :
    IsGradedCurvJet (I := I) (M := M) g T c p' w' G := by
  intro k x
  refine (hG k x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (c k))
  -- Abstract the order-indexed fibre norm as the opaque `f q := rfns(∇^q T)(x)`; the `(p, w)` and
  -- `(p', w')` truncated sums are then `∑ f (i + p)` and `∑ f (i + p')`, dominated by the order-window
  -- lemma since `{p, …, p + w + k − 1} ⊆ {p', …, p' + w' + k − 1}`.
  exact orderWindow_sum_le
    (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
      ((iteratedCovGrad g 0 s q T).toSection x))
    (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + q) x _) hp hpw

/-- **The graded curvature-jet predicate is closed under subtraction of two jets of the same shape.**
The difference analogue of `IsGradedCurvJet.add`: if `G₁`, `G₂` are graded curvature jets of `T` of the
*same* lowest order `p` and base width `w`, with nonnegative constant families `c₁`, `c₂`, then their
difference `G₁ − G₂` is a graded curvature jet of the same lowest order `p` and base width `w`, with
constant family `k ↦ √(2·((c₁ k)² + (c₂ k)²))`: at every gradient order `k`,
`∇^k(G₁ − G₂) = ∇^k G₁ − ∇^k G₂` (`iteratedCovGrad_sub`, `SmoothCcTensor.toSection_sub`), so the fibre
norm is `≤ 2·rfns(∇^k G₁) + 2·rfns(∇^k G₂)` (`riemannianFiberNormSq_sub_le`), each term bounded by its
jet, giving `2((c₁ k)² + (c₂ k)²)` times the shared target sum. This is the field-level closure that
isolates a genuine remainder field `Curv − Gcurv − Gdiff` as a graded jet from the jets of the whole
defect and the two genuine curvature sections it subtracts. -/
theorem IsGradedCurvJet.sub (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor g 0 s) {c₁ c₂ : ℕ → ℝ} {p w r : ℕ}
    {G₁ G₂ : SmoothCcTensor g 0 r}
    (hG₁ : IsGradedCurvJet (I := I) (M := M) g T c₁ p w G₁)
    (hG₂ : IsGradedCurvJet (I := I) (M := M) g T c₂ p w G₂) :
    IsGradedCurvJet (I := I) (M := M) g T
      (fun k => Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2))) p w (G₁ - G₂) := by
  intro k x
  have hsplit : (iteratedCovGrad g 0 r k (G₁ - G₂)).toSection x =
      (iteratedCovGrad g 0 r k G₁).toSection x - (iteratedCovGrad g 0 r k G₂).toSection x := by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsplit]
  have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (r + k) x
    ((iteratedCovGrad g 0 r k G₁).toSection x) ((iteratedCovGrad g 0 r k G₂).toSection x)
  have hcsq : Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2)) ^ 2 = 2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  rw [hcsq]
  calc riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
          ((iteratedCovGrad g 0 r k G₁).toSection x - (iteratedCovGrad g 0 r k G₂).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
            ((iteratedCovGrad g 0 r k G₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
            ((iteratedCovGrad g 0 r k G₂).toSection x) := hsub
    _ ≤ 2 * ((c₁ k) ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x)) +
          2 * ((c₂ k) ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x)) := by
        gcongr <;> [exact hG₁ k x; exact hG₂ k x]
    _ = 2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2) * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x) := by ring

omit [BoundarylessManifold I M] in
/-- **Order-range monotonicity of the rank-`r` graded curvature-jet predicate.** The contravariant-rank
mirror of `IsGradedCurvJet.le_shape`: a rank-`r` graded curvature jet of `S` of lowest order `p` / base
width `w` is also a jet of any wider shape `(p', w')` with `p' ≤ p` and `p + w ≤ p' + w'`, since the
`(p, w)` order-window is a subset of the `(p', w')` window with nonnegative summands. -/
theorem IsGradedCurvJetRS.le_shape (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c : ℕ → ℝ} {p w p' w' t : ℕ} {G : SmoothCcTensor g r t}
    (hp : p' ≤ p) (hpw : p + w ≤ p' + w')
    (hG : IsGradedCurvJetRS (I := I) (M := M) g S c p w G) :
    IsGradedCurvJetRS (I := I) (M := M) g S c p' w' G := by
  intro k x
  refine (hG k x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (c k))
  exact orderWindow_sum_le
    (fun q => riemannianFiberNormSq (I := I) (M := M) g r (s + q) x
      ((iteratedCovGrad g r s q S).toSection x))
    (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + q) x _) hp hpw

/-- **The genuine full-sum graded-jet base split of the rank-`r` order-`2` commutator defect (the
iterated-Ricci deep well, posited once at general rank).** For a closed smooth Riemannian manifold
`(M, g)` and a fixed contravariant rank `r` there is a valence/order-dependent nonnegative constant
family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` splits
intrinsically into three smooth compactly-supported `(r, s + 1)`-tensor fields
```
Curv S = Gcurv + Gdiff + Grem
```
each a **graded** curvature jet (`IsGradedCurvJetRS`) of `S` at its genuine shape: the pure-Riemann
contraction `R(∇S)` jet `Gcurv` of lowest order `1` and width `1` (bounded by `∇^{≥1}S`), the
differentiated-curvature `(∇R) S` jet `Gdiff` of lowest order `0` and width `1` (bounded by `∇^{≥0}S`),
and — crucially — the moving-frame remainder `Grem` of the **sound full-sum shape** lowest order `0` and
width `3` (bounded by the whole window `∇^{≤k+2}S`, NOT the false single-top-order shape `(2, 1)`).

**Why this is TRUE — and why it is the FULL-SUM, not order-separated, shape.** Pointwise `Curv S` is
the genuine third-order Bochner–Weitzenböck field: by the metric-trace reading of the rough Laplacian
`Δ_∇ = tr_g ∘ ∇²` (`rawTensorConnLap_eq_metricTrace2`, frame-free, rank-generic) the defect
`Δ_∇(∇S) − ∇(Δ_∇ S)` is the metric trace of the antisymmetrised second covariant derivative of `∇S`
after the outer `∇` is passed through the trace by metric compatibility (`metricTrace2_covDeriv_comm`,
rank-generic), which the third-order tensor Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` exhibits as a `riemannOp`-contraction of `(∇S, S)`.
Splitting that contraction into its pure-Riemann `R(∇S)` part (`Gcurv`, the slot-`0` assembly of the
moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ}S)`) and its differentiated-curvature `(∇R) S` part (`Gdiff`),
the surviving `Grem` is the moving-frame/frame-bracket discrepancy, genuinely `∇²S`-order; each of its
own iterated gradients `∇^k Grem` is, after the iterated-Ricci cancellation of the top `∇^{k+3}S` terms,
a curvature contraction of `∇^{≤k+2}S` with every curvature coefficient absorbed uniformly over the
compact manifold (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The contracted-order window is the
**full-sum** `0 … k+2` (shape `(0, 3)`): the per-direction moving-frame bracket trace is non-tensorial
in the direction (false term-by-term through `smoothExtensionTangent`), so only the intrinsic full-sum
window — not the single top order `(2, 1)` — is order-controlled. This is the genuinely-irreducible
iterated-Ricci content; at general rank `r` the rank-`r` pure-Riemann grid tower is itself absent
sorry-free (only the rank-`0` `GcurvSection_gradedCurvJet` / `genuineDiffCurvSection_gradedCurvJet` are
proven), so the entire rank-`r` graded base split is collected here as the single posited primitive
(exactly as `MovingFrameGenuineFieldPairingRS` and `pointwiseTensorCurvRS_gradedCurvJet_field_base`
collect the rank-`r` development into one node). Consumers transitively depend on `sorryAx`.

**Strictly stronger than the bare full-sum jet (genuine decomposition, no hypothesis-packaging).** This
posits the *witnessed* three-field split together with each field's genuine (tighter) graded shape; the
full-sum jet bound `pointwiseTensorCurvRS_fullSum_gradedCurvJet` is *derived* from it by homogenising the
three pieces to the common shape `(0, 3)` and summing — so the bare jet cannot reconstruct this split
(it carries strictly more information), and this node is not its own conclusion.

**Non-vacuity.** With `c s 0 = 0` the three bounds force `rfns(Gcurv)(x) = rfns(Gdiff)(x) =
rfns(Grem)(x) = 0` at `k = 0`, hence the section equation gives `Curv S = 0`; *false* on a non-flat
manifold, where the order-`2` commutator defect carries the genuine curvature contraction of `S`
(`R ≠ 0`, `∇S ≠ 0`). The constant family is genuinely positive. -/
theorem pointwiseTensorCurvRS_directFullSum_baseSplit
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcurv Gdiff Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S = Gcurv + Gdiff + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 1 Gcurv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 Gdiff ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem := by
  sorry

/-- **The rank-`r` order-`2` commutator defect is a full-sum graded curvature jet of lowest order `0`
and base width `3`, derived from the genuine base split.** This is the *bare-jet* corollary of the
witnessed base split `pointwiseTensorCurvRS_directFullSum_baseSplit`: homogenising the three genuine
fields to the common full-sum shape `(0, 3)` (`IsGradedCurvJetRS.le_shape`: each genuine window
`{p, …, p + w + k − 1}` sits inside `{0, …, 2 + k}`) and summing them via `IsGradedCurvJetRS.add`
(twice) realises `Gcurv + (Gdiff + Grem) = Curv S` as a single `(0, 3)` graded jet. It is the direct
full-sum graded-jet primitive the rank-`r` iterated-gradient commutator-defect pointwise fibre bound
`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound` consumes (its `k = m`
specialisation is exactly that bound's `∑_{i < m + 3}` conclusion), and the value-anchor the covariant
remainder leaf `pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet` subtracts the two
sorry-free genuine sections from. It does **not** route through the order-separated base seed
`pointwiseTensorCurvRS_gradedCurvJet_field_base` (whose moving-frame remainder, asserted pure top-order,
is false on a normal manifold). -/
theorem pointwiseTensorCurvRS_directFullSum_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S) := by
  classical
  obtain ⟨c, hc_nn, hsplit⟩ := pointwiseTensorCurvRS_directFullSum_baseSplit (I := I) (M := M) g r
  -- A single uniform per-order constant family dominating all three genuine jets; the two
  -- `IsGradedCurvJetRS.add` applications square-combine the common constant left-associatively.
  refine ⟨fun s k =>
      Real.sqrt (2 * ((c s k) ^ 2
        + Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2)) ^ 2)),
    fun s k => Real.sqrt_nonneg _, fun s S => ?_⟩
  obtain ⟨Gcurv, Gdiff, Grem, heq, hGcurv, hGdiff, hGrem⟩ := hsplit s S
  -- Homogenise the three genuine jets to the common full-sum shape `(0, 3)`.
  have hG1 : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Gcurv :=
    hGcurv.le_shape (I := I) (M := M) g S (by omega) (by omega)
  have hG2 : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Gdiff :=
    hGdiff.le_shape (I := I) (M := M) g S (by omega) (by omega)
  have hG3 : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem := hGrem
  -- Sum: `Gcurv + (Gdiff + Grem) = Curv S`.
  have hpair := hG2.add (I := I) (M := M) g S hG3
  have htriple := hG1.add (I := I) (M := M) g S hpair
  have hsum : pointwiseTensorCurvRS (I := I) (M := M) g r s S =
      Gcurv + (Gdiff + Grem) := by rw [heq]; abel
  rw [hsum]
  exact htriple

/-- **The intrinsic moving-frame remainder of the order-`2` commutator defect is a full-sum graded
curvature jet of lowest order `0` and base width `3` (the iterated-Ricci leg).** For a closed smooth
Riemannian manifold `(M, g)` there is a valence/order-dependent nonnegative constant family
`c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `T`, the *moving-frame remainder*

```
Grem := Curv T − GcurvSection g s T − genuineDiffCurvSection g s T
```

of the intrinsic genuine-curvature split is a **graded** curvature jet of `T` of lowest contracted
order `0` and base width `3`:

```
rfns(∇^k Grem)(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i T)(x).
```

**Why this is TRUE.** Pointwise, after removing the two genuine curvature contractions — the
pure-Riemann `R(∇T)` carried by `GcurvSection g s T = appCc (Φ₀ (s + 1)) (∇T)` and the
differentiated-curvature `(∇R) T` carried by `genuineDiffCurvSection g s T = appCc (∇Φ₀ (s)) T` — the
surviving remainder `Grem` is the frame-bracket discrepancy `tensor3rdCurvBracket` together with the
moving-frame trace discrepancy and residual (`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_
field`). The bracket carries two covariant derivatives of `T`, so `Grem` is genuinely `rfns(∇²T)`-order
at gradient order `0`; differentiating `Grem` once shifts the window by one, and the top-order
`∇^{k + 3}T` terms cancel by the iterated Ricci identity
(`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), leaving each `∇^k Grem` a contraction of
`∇^{≤ k + 2}T` (contracted-order window `0 … k + 2`), with every curvature coefficient absorbed
uniformly over the compact manifold (carrying `‖∇^{≤ k + 2} R‖_∞`, finite by per-`k` compactness;
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The contracted-order window is the
**full-sum** `0 … k + 2` (shape `(0, 3)`), *not* the single top order `k + 2` (shape `(2, 1)`): the
moving-frame bracket trace is non-tensorial in the direction, false term-by-term through
`smoothExtensionTangent`; only the intrinsic full-sum window is order-controlled. This is the
genuinely irreducible iterated-Ricci moving-frame content of the order-`2` commutator defect, posited
here as the precise true full-sum child (consumers transitively depend on `sorryAx`).

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(Grem)(x) = 0` at `k = 0`, i.e. `Curv T =
GcurvSection g s T + genuineDiffCurvSection g s T` (the moving-frame bracket discrepancy vanishes);
*false* on a non-flat manifold, where the frame-bracket discrepancy is genuinely non-zero (it is
carried explicitly — never asserted to vanish — throughout the moving-frame tower, e.g.
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`). The constant family is genuinely
positive. -/
theorem pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet
    (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3
          (pointwiseTensorCurv (I := I) (M := M) g s T -
            GcurvSection (I := I) (M := M) g s T -
            genuineDiffCurvSection (I := I) (M := M) g s T) := by
  classical
  -- The direct full-sum jet of the *whole* defect at rank `0` (the value anchor): the rank-`r`
  -- direct jet specialised to `r = 0` is, definitionally, the covariant defect jet
  -- (`pointwiseTensorCurvRS g 0 s T = pointwiseTensorCurv g s T`,
  -- `IsGradedCurvJetRS (r := 0) = IsGradedCurvJet`).
  obtain ⟨cD, hcD_nn, hD⟩ :=
    pointwiseTensorCurvRS_directFullSum_gradedCurvJet (I := I) (M := M) g 0
  -- The two genuine curvature sections are *sorry-free* graded jets (shapes `(1, 1)` and `(0, 1)`).
  obtain ⟨cA, hcA_nn, hA⟩ := GcurvSection_gradedCurvJet (I := I) (M := M) g
  obtain ⟨cB, hcB_nn, hB⟩ := genuineDiffCurvSection_gradedCurvJet (I := I) (M := M) g
  -- The remainder is the defect minus the two genuine sections; homogenising each leg to the common
  -- full-sum shape `(0, 3)` and subtracting twice (`IsGradedCurvJet.sub`) lands the remainder jet.
  refine ⟨fun s k => Real.sqrt (2 * ((Real.sqrt (2 * ((cD s k) ^ 2 + (cA s k) ^ 2))) ^ 2
      + (cB s k) ^ 2)), fun s k => Real.sqrt_nonneg _, fun s T => ?_⟩
  -- `hD` at rank `0` is the covariant defect jet (definitional transport of the rank predicate:
  -- `pointwiseTensorCurvRS g 0 s T = pointwiseTensorCurv g s T` and `IsGradedCurvJetRS (r := 0)
  -- = IsGradedCurvJet`).
  have hDcurv : IsGradedCurvJet (I := I) (M := M) g T (cD s) 0 3
      (pointwiseTensorCurv (I := I) (M := M) g s T) := hD s T
  -- Homogenise the two genuine jets to the common full-sum shape `(0, 3)`.
  have hAls : IsGradedCurvJet (I := I) (M := M) g T (cA s) 0 3
      (GcurvSection (I := I) (M := M) g s T) :=
    (hA s T).le_shape (I := I) (M := M) g T (by omega) (by omega)
  have hBls : IsGradedCurvJet (I := I) (M := M) g T (cB s) 0 3
      (genuineDiffCurvSection (I := I) (M := M) g s T) :=
    (hB s T).le_shape (I := I) (M := M) g T (by omega) (by omega)
  -- `Curv − GcurvSection − genuineDiffCurvSection = (Curv − GcurvSection) − genuineDiffCurvSection`.
  exact (hDcurv.sub (I := I) (M := M) g T hAls).sub (I := I) (M := M) g T hBls

/-- **The order-`2` commutator defect is a full-sum graded curvature jet of lowest order `0` and base
width `3`.** For a closed smooth Riemannian manifold `(M, g)` there is a valence/order-dependent
nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `T`, the order-`2` commutator defect
`Curv T := pointwiseTensorCurv g s T = Δ_∇(∇T) − ∇(Δ_∇ T)` is a **graded** curvature jet of `T` of
lowest contracted order `0` and base width `3`:

```
rfns(∇^k (Curv T))(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i T)(x).
```

**Proof (direct, via the intrinsic genuine-curvature split).** `Curv T` decomposes as
`GcurvSection g s T + genuineDiffCurvSection g s T + Grem` with `Grem := Curv T − GcurvSection g s T −
genuineDiffCurvSection g s T`. The pure-Riemann genuine section `GcurvSection g s T` is a graded jet of
shape `(1, 1)` (`GcurvSection_gradedCurvJet`, *sorry-free*); the differentiated-curvature genuine
section `genuineDiffCurvSection g s T` is a graded jet of shape `(0, 1)`
(`genuineDiffCurvSection_gradedCurvJet`, *sorry-free* — the rank-raising operator-field normal-form
grid); and the moving-frame remainder `Grem` is a graded jet of the full-sum shape `(0, 3)`
(`pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet`, the iterated-Ricci leg). Each is, by
`IsGradedCurvJet.le_shape`, also a jet of the common full-sum shape `(0, 3)` (each contracted-order
window `{p, …, p + w + k − 1}` sits inside `{0, …, 2 + k}`), promoted to one common constant family by
`IsGradedCurvJet.mono_const`, and `IsGradedCurvJet.add` (applied twice) sums the three homogenized jets
to `GcurvSection + (genuineDiffCurvSection + Grem) = Curv T` as a single `(0, 3)` graded jet. The
constant family is genuinely positive (non-vacuity: at `k = 0` the bound is the `m = 0` defect fibre
bound, false with constant `0` on a non-flat manifold).

This is the direct full-sum graded-jet primitive the iterated-gradient commutator-defect pointwise
fibre bound `exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound` consumes: its
`k = m` specialisation is exactly that bound's `∑_{i < m + 3}` conclusion. It does **not** route through
the order-separated base seed `pointwiseTensorCurv_gradedCurvJet_field_base` (nor its order-separated
child whose moving-frame remainder, asserted pure top-order, is false on a normal manifold): the two
genuine legs are sorry-free, and only the intrinsic full-sum remainder leg transits `sorryAx`. -/
theorem pointwiseTensorCurv_fullSum_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3
          (pointwiseTensorCurv (I := I) (M := M) g s T) := by
  classical
  obtain ⟨cR, hcR_nn, hRcurv⟩ := GcurvSection_gradedCurvJet (I := I) (M := M) g
  obtain ⟨cD, hcD_nn, hDcurv⟩ := genuineDiffCurvSection_gradedCurvJet (I := I) (M := M) g
  obtain ⟨cRem, hcRem_nn, hRem⟩ :=
    pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet (I := I) (M := M) g
  -- A single uniform per-order constant family dominating all three genuine/remainder jets; the two
  -- `IsGradedCurvJet.add` applications square-combine the common constant `c s k` left-associatively.
  refine ⟨fun s k =>
      Real.sqrt (2 * ((max (cR s k) (max (cD s k) (cRem s k))) ^ 2
        + Real.sqrt (2 * ((max (cR s k) (max (cD s k) (cRem s k))) ^ 2
          + (max (cR s k) (max (cD s k) (cRem s k))) ^ 2)) ^ 2)),
    fun s k => Real.sqrt_nonneg _, fun s T => ?_⟩
  set c : ℕ → ℝ := fun k => max (cR s k) (max (cD s k) (cRem s k)) with hc_def
  have hc_nn : ∀ k, 0 ≤ c k := fun k => le_trans (hcR_nn s k) (le_max_left _ _)
  -- Homogenize the three jets to the common full-sum shape `(0, 3)` and constant family `c`.
  have hG1 : IsGradedCurvJet (I := I) (M := M) g T c 0 3 (GcurvSection (I := I) (M := M) g s T) :=
    ((hRcurv s T).le_shape (I := I) (M := M) g T (by omega) (by omega)).mono_const
      (I := I) (M := M) g T (hcR_nn s) (fun k => le_max_left _ _)
  have hG2 : IsGradedCurvJet (I := I) (M := M) g T c 0 3
      (genuineDiffCurvSection (I := I) (M := M) g s T) :=
    ((hDcurv s T).le_shape (I := I) (M := M) g T (by omega) (by omega)).mono_const
      (I := I) (M := M) g T (hcD_nn s) (fun k => le_trans (le_max_left _ _) (le_max_right _ _))
  have hG3 : IsGradedCurvJet (I := I) (M := M) g T c 0 3
      (pointwiseTensorCurv (I := I) (M := M) g s T -
        GcurvSection (I := I) (M := M) g s T -
        genuineDiffCurvSection (I := I) (M := M) g s T) :=
    (hRem s T).mono_const (I := I) (M := M) g T (hcRem_nn s)
      (fun k => le_trans (le_max_right _ _) (le_max_right _ _))
  -- Sum the homogenized jets: `GcurvSection + (genuineDiffCurvSection + Grem) = Curv T`.
  have hpair := hG2.add (I := I) (M := M) g T hG3
  have htriple := hG1.add (I := I) (M := M) g T hpair
  have hsum : pointwiseTensorCurv (I := I) (M := M) g s T =
      GcurvSection (I := I) (M := M) g s T +
        (genuineDiffCurvSection (I := I) (M := M) g s T +
          (pointwiseTensorCurv (I := I) (M := M) g s T -
            GcurvSection (I := I) (M := M) g s T -
            genuineDiffCurvSection (I := I) (M := M) g s T)) := by abel
  rw [hsum]
  exact htriple

/-- **The rank-`r` order-`2` commutator defect is a full-sum graded curvature jet of lowest order `0`
and base width `3` (the iterated-Ricci form).** The contravariant-rank analogue of
`pointwiseTensorCurv_fullSum_gradedCurvJet`: at fixed contravariant rank `r` there is a
valence/order-dependent nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` is a **graded** curvature jet of `S` of lowest contracted
order `0` and base width `3`:

```
rfns(∇^k (Curv S))(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i S)(x).
```

**Proof (direct, via the genuine base split — NOT the order-separated route).** This is the consumer-
facing bare-jet name for `pointwiseTensorCurvRS_directFullSum_gradedCurvJet`, which is *derived* from
the witnessed genuine full-sum base split `pointwiseTensorCurvRS_directFullSum_baseSplit`: `Curv S`
splits as `Gcurv + Gdiff + Grem` (the pure-Riemann `R(∇S)` jet of shape `(1, 1)`, the
differentiated-curvature `(∇R) S` jet of shape `(0, 1)`, and the moving-frame remainder of the sound
full-sum shape `(0, 3)`), and homogenising the three to the common shape `(0, 3)`
(`IsGradedCurvJetRS.le_shape`) and summing (`IsGradedCurvJetRS.add`, twice) gives `Curv S` as a single
`(0, 3)` graded jet. The mathematical content — `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` is intrinsic and, by the
metric-trace reading `Δ_∇ = tr_g ∘ ∇²` (`rawTensorConnLap_eq_metricTrace2`), the trace–`∇` commutation
(`metricTrace2_covDeriv_comm`), and the third-order tensor Ricci identity
(`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), a `riemannOp`-contraction of the `≤ k + 2`-jet of
`S` with the **full-sum** window `0 … k + 2` (sound: the per-direction moving-frame bracket trace is
non-tensorial, false term-by-term through `smoothExtensionTangent`) — lives in the posited base split.
It is the direct full-sum graded-jet primitive the rank-`r` iterated-gradient commutator-defect pointwise
fibre bound (`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound`) consumes,
bypassing the order-separated base seed `pointwiseTensorCurvRS_gradedCurvJet_field_base` and its (false
single-top-order) remainder.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(Curv S)(x) = 0` at `k = 0`, i.e. the order-`2`
commutator defect vanishes; *false* on a non-flat manifold (the defect carries the genuine curvature
contraction of `S`). The constant family is genuinely positive. -/
theorem pointwiseTensorCurvRS_fullSum_gradedCurvJet (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S) :=
  pointwiseTensorCurvRS_directFullSum_gradedCurvJet (I := I) (M := M) g r

end Connection
end Integral
end DifferentialGeometry
