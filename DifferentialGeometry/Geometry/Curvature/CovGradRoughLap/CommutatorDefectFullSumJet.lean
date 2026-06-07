import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OrderSeparatedCurvatureJetRS

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
counterexample `∇²S = 0`, `∇S ≠ 0`, `R ≠ 0`), the full-sum bound is genuinely true and stays inside
the re-differentiable graded curvature-jet class: it is precisely the order-collapsed sum of the three
genuine jets of the `m = 0` field split.

## How it is proved

The explicit `m = 0` graded field split `pointwiseTensorCurv_gradedCurvJet_field_base` writes

```
Curv T = Gcurv + GcurvDeriv + Grem
```

with `Gcurv` a graded jet of lowest order `1` / width `1`, `GcurvDeriv` of lowest order `0` / width
`1`, and `Grem` of lowest order `2` / width `1`. Each of these `(p, w)` jets is, by the order-range
monotonicity `IsGradedCurvJet.le_shape` (a jet whose contracted-order window
`{p, …, p + w + k − 1}` is contained in the wider window `{p', …, p' + w' + k − 1}`, all summands
nonnegative), also a jet of the common shape `(p', w') = (0, 3)`:

* `Gcurv` : `(1, 1)`, `0 ≤ 1`, `1 + 1 = 2 ≤ 0 + 3`;
* `GcurvDeriv` : `(0, 1)`, `0 ≤ 0`, `0 + 1 = 1 ≤ 0 + 3`;
* `Grem` : `(2, 1)`, `0 ≤ 2`, `2 + 1 = 3 ≤ 0 + 3`.

Summing the three homogenized `(0, 3)` jets through the graded-jet subadditivity `IsGradedCurvJet.add`
(twice) gives `(Gcurv + GcurvDeriv) + Grem = Curv T` as a single `(0, 3)` graded jet, which is the
headline. The constant family is valence/order-dependent (the curvature-derivative term count grows
with the gradient order), as for every graded-jet primitive; consumers transitively depend on `sorryAx`
through the posited sub-children of the `m = 0` base seed.

## Non-vacuity

At gradient order `k = 0` the bound reads `rfns(Curv T)(x) ≤ (c s 0)² · (rfns(T) + rfns(∇T) +
rfns(∇²T))(x)`, the `m = 0` single-step defect fibre bound, which is *false* with `c s 0 = 0` on a
non-flat manifold (the defect carries the genuine curvature contraction of `T`). The constant family is
genuinely positive.

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
constant family is unchanged. This is the order-collapse step that brings the three order-separated
genuine jets of the `m = 0` split onto a single common full-sum shape. -/
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

/-- **The order-`2` commutator defect is a full-sum graded curvature jet of lowest order `0` and base
width `3`.** For a closed smooth Riemannian manifold `(M, g)` there is a valence/order-dependent
nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `T`, the order-`2` commutator defect
`Curv T := pointwiseTensorCurv g s T = Δ_∇(∇T) − ∇(Δ_∇ T)` is a **graded** curvature jet of `T` of
lowest contracted order `0` and base width `3`:

```
rfns(∇^k (Curv T))(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i T)(x).
```

**Proof.** This is the order-collapsed sum of the three genuine jets of the `m = 0` graded field split
`pointwiseTensorCurv_gradedCurvJet_field_base`: `Curv T = Gcurv + GcurvDeriv + Grem` with `Gcurv` of
shape `(1, 1)`, `GcurvDeriv` of shape `(0, 1)`, `Grem` of shape `(2, 1)`. Each is, by
`IsGradedCurvJet.le_shape`, also a jet of the common full-sum shape `(0, 3)` (each contracted-order
window `{p, …, p + 1 + k − 1}` sits inside `{0, …, 2 + k}`), and `IsGradedCurvJet.add` (applied twice)
sums the three homogenized jets to `(Gcurv + GcurvDeriv) + Grem = Curv T` as a single `(0, 3)` graded
jet. The constant family is genuinely positive (non-vacuity inherited from the base split: at `k = 0`
the bound is the `m = 0` defect fibre bound, false with constant `0` on a non-flat manifold).

This is the direct full-sum graded-jet primitive the iterated-gradient commutator-defect pointwise
fibre bound `exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound` consumes: its
`k = m` specialisation is exactly that bound's `∑_{i < m + 3}` conclusion. It does **not** route through
the order-separated pure-order remainder bound (whose moving-frame remainder, asserted pure top-order,
is false on a normal manifold). -/
theorem pointwiseTensorCurv_fullSum_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3
          (pointwiseTensorCurv (I := I) (M := M) g s T) := by
  classical
  obtain ⟨c, hc_nn, hbase⟩ := pointwiseTensorCurv_gradedCurvJet_field_base (I := I) (M := M) g
  -- The merged full-sum constant family: two `IsGradedCurvJet.add` applications square-combine the
  -- common per-order constant `c s k`. Surface the explicit closed form so the family is uniform in
  -- `s, k` and independent of the per-`T` field witnesses.
  refine ⟨fun s k =>
      Real.sqrt (2 * (Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2)) ^ 2 + (c s k) ^ 2)),
    fun s k => Real.sqrt_nonneg _, fun s T => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, hsum, hGcurv, hGcurvDeriv, hGrem⟩ := hbase s T
  -- Homogenize the three genuine jets to the common full-sum shape `(0, 3)`.
  have hGcurv' : IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3 Gcurv :=
    hGcurv.le_shape (I := I) (M := M) g T (by omega) (by omega)
  have hGcurvDeriv' : IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3 GcurvDeriv :=
    hGcurvDeriv.le_shape (I := I) (M := M) g T (by omega) (by omega)
  have hGrem' : IsGradedCurvJet (I := I) (M := M) g T (c s) 0 3 Grem :=
    hGrem.le_shape (I := I) (M := M) g T (by omega) (by omega)
  -- Sum the homogenized jets: `(Gcurv + GcurvDeriv) + Grem`, matching the base split's left-assoc sum.
  have hpair : IsGradedCurvJet (I := I) (M := M) g T
      (fun k => Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2))) 0 3 (Gcurv + GcurvDeriv) :=
    hGcurv'.add (I := I) (M := M) g T hGcurvDeriv'
  have htriple : IsGradedCurvJet (I := I) (M := M) g T
      (fun k => Real.sqrt (2 * (Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2)) ^ 2 + (c s k) ^ 2))) 0 3
      ((Gcurv + GcurvDeriv) + Grem) :=
    hpair.add (I := I) (M := M) g T hGrem'
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
and base width `3`.** The contravariant-rank analogue of `pointwiseTensorCurv_fullSum_gradedCurvJet`:
at fixed contravariant rank `r` there is a valence/order-dependent nonnegative constant family
`c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` is a
**graded** curvature jet of `S` of lowest contracted order `0` and base width `3`:

```
rfns(∇^k (Curv S))(x) ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^i S)(x).
```

**Proof.** The order-collapsed sum of the three genuine jets of the rank-`r` `m = 0` graded field
split `pointwiseTensorCurvRS_gradedCurvJet_field_base` (`Curv S = Gcurv + GcurvDeriv + Grem` with shapes
`(1, 1)`, `(0, 1)`, `(2, 1)`), each brought to the common full-sum shape `(0, 3)` by
`IsGradedCurvJetRS.le_shape` and summed via `IsGradedCurvJetRS.add` (twice). It is the direct full-sum
graded-jet primitive the rank-`r` iterated-gradient commutator-defect pointwise fibre bound
(`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound`) consumes, bypassing the
false order-separated pure-order remainder. Non-vacuity inherited from the base split (the `k = 0`
bound is the `m = 0` defect fibre bound, false with constant `0` on a non-flat manifold). -/
theorem pointwiseTensorCurvRS_fullSum_gradedCurvJet (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S) := by
  classical
  obtain ⟨c, hc_nn, hbase⟩ := pointwiseTensorCurvRS_gradedCurvJet_field_base (I := I) (M := M) g r
  refine ⟨fun s k =>
      Real.sqrt (2 * (Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2)) ^ 2 + (c s k) ^ 2)),
    fun s k => Real.sqrt_nonneg _, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, hsum, hGcurv, hGcurvDeriv, hGrem⟩ := hbase s S
  have hGcurv' : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Gcurv :=
    hGcurv.le_shape (I := I) (M := M) g S (by omega) (by omega)
  have hGcurvDeriv' : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 GcurvDeriv :=
    hGcurvDeriv.le_shape (I := I) (M := M) g S (by omega) (by omega)
  have hGrem' : IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem :=
    hGrem.le_shape (I := I) (M := M) g S (by omega) (by omega)
  have hpair : IsGradedCurvJetRS (I := I) (M := M) g S
      (fun k => Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2))) 0 3 (Gcurv + GcurvDeriv) :=
    hGcurv'.add (I := I) (M := M) g S hGcurvDeriv'
  have htriple : IsGradedCurvJetRS (I := I) (M := M) g S
      (fun k => Real.sqrt (2 * (Real.sqrt (2 * ((c s k) ^ 2 + (c s k) ^ 2)) ^ 2 + (c s k) ^ 2))) 0 3
      ((Gcurv + GcurvDeriv) + Grem) :=
    hpair.add (I := I) (M := M) g S hGrem'
  rw [hsum]
  exact htriple

end Connection
end Integral
end DifferentialGeometry
