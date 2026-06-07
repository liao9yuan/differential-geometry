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
  sorry

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

**Why this is TRUE.** As with the covariant case, `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` is intrinsic, and by
the iterated Ricci identity `Curv S` together with all its iterated covariant gradients is a curvature
contraction of the `≤ k + 2`-jet of `S`: the genuine pure-Riemann `R(∇S)` and differentiated-curvature
`(∇R) S` contractions (orders `1` and `0`) plus the moving-frame bracket discrepancy (genuinely
`∇²S`-order), whose top-order `∇^{k + 3}S` terms cancel by the iterated Ricci identity, leaving each
`∇^k (Curv S)` a contraction of `∇^{≤ k + 2}S` (the full-sum window `0 … k + 2`, shape `(0, 3)`), with
every curvature coefficient absorbed uniformly over the compact manifold. The full-sum window is the
sound one (the per-direction moving-frame bracket trace is non-tensorial, false term-by-term through
`smoothExtensionTangent`); the unsplit rank-`r` development has no sorry-free genuine-section
decomposition, so the whole defect is posited here directly in its genuine full-sum form (shape
`(0, 3)`), **not** the false order-separated single-top-order shape `(2, 1)`. It is the direct full-sum
graded-jet primitive the rank-`r` iterated-gradient commutator-defect pointwise fibre bound
(`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound`) consumes, bypassing the
order-separated base seed `pointwiseTensorCurvRS_gradedCurvJet_field_base` and its remainder.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(Curv S)(x) = 0` at `k = 0`, i.e. the order-`2`
commutator defect vanishes; *false* on a non-flat manifold (the defect carries the genuine curvature
contraction of `S`). The constant family is genuinely positive. Posited as the precise true full-sum
child (consumers transitively depend on `sorryAx`). -/
theorem pointwiseTensorCurvRS_fullSum_gradedCurvJet (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S) := by
  sorry

end Connection
end Integral
end DifferentialGeometry
