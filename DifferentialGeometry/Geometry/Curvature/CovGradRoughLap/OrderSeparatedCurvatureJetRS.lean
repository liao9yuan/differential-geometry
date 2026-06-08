import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairingRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffCurvatureTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLocality

/-!
# The order-`m` order-separated moving-frame curvature-jet field decomposition at rank `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-rank-`r` lift of the order-`m` order-separated moving-frame curvature-jet field
decomposition `OrderSeparatedCurvatureJet` of the rank-generic order-`2` commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurvRS g r s S`, a `(r, s + 1)`-tensor field). It isolates the deepest order-`m`
order-separated section-field split of the `m`-fold iterated covariant gradient of `Curv S`, the direct
order-`m` lift of the `m = 0` field split
`exists_pointwiseTensorCurvRS_movingFrameField_orderSeparated_bracketFreePairing`
(`Geometry/Curvature/CovGradRoughLap/MovingFrameGenuineFieldPairingRS.lean`): applying `∇^m` to the
order-separated field split of `Curv S` and re-Leibniz-ing the curvature contractions, the iterated
Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order `∇^{m + 3}S`
terms, leaving — at every covariant rank `s`, gradient order `m`, smooth compactly-supported
`(r, s)`-tensor `S` and point `x` — three fields `Gcurv, GcurvDeriv, Grem` summing to `∇^m(Curv S)(x)`
with the three order-separated proportional fibre bounds: the differentiated-Riemann jet `Gcurv`
bounded by `∑_{i < m + 1} rfns(∇^{i + 1}S)` (orders `1 … m + 1`), the iterated differentiated-curvature
jet `GcurvDeriv` by `∑_{i < m + 1} rfns(∇^i S)` (orders `0 … m`), and the moving-frame remainder `Grem`
by `rfns(∇^{m + 2}S)` (the single top order).

This is the strictly-upstream curvature primitive that the rank-`r` aggregate fibre bound
`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound`
(`Geometry/Flow/RicciFlow/ShortTime/LocalWeylReproducingKernel.lean`) is proved on top of, exactly as
the rank-`0` aggregate bound `exists_iteratedCovGrad_pointwiseTensorCurv_pointwise_fiberNormSq_bound`
is proved from the rank-`0` order-separated split. The file lives upstream of
`LocalWeylReproducingKernel` (which does not import it back) so that file can cite this order-`m` child
without an import cycle.

## The re-differentiable graded curvature-jet invariant at rank `r`

As at rank `0` (`OrderSeparatedCurvatureJet`), the order-`m` split cannot be carried through the
induction on `m` as abstract `∃`-fields with only a single-order fibre bound: differentiating such a
field is uncontrolled. The induction therefore carries the re-differentiable graded invariant
`IsGradedCurvJetRS g S c p w G` — the verbatim rank-`r` mirror of `IsGradedCurvJet`: each genuine field
is required to satisfy, for *every* further gradient order `k` and every `x`, the bound

```
rfns(∇^k G)(x) ≤ (c k)² · ∑_{i < w + k} rfns(∇^{i + p} S)(x).
```

This predicate is closed under one covariant gradient (`IsGradedCurvJetRS_covGrad`): the `k`-th
gradient of `∇G` is the `(k + 1)`-th gradient of `G`, so the bound shifts `k → k + 1` and stays in the
family — exactly what the order-`m` induction's per-step consumes.

## What is proved vs. posited

The order-`m` field-level split is built by **induction on `m`** (the genuine glue written here),
carrying the re-differentiable graded invariant `IsGradedCurvJetRS`:

* the **base case `m = 0`** is the posited explicit graded curvature-jet seed at rank `r`
  `pointwiseTensorCurvRS_gradedCurvJet_field_base`: the `m = 0` split of `Curv S` into the three
  genuine graded jets (the pure-Riemann section `Gcurv` of lowest order `1`, the differentiated-
  curvature `GcurvDeriv` of lowest order `0`, and the moving-frame remainder `Grem` of lowest order
  `2`), each carrying the full graded gradient family of bounds. At rank `0` this is *glue* over the
  pure-Riemann section grid `GcurvSection_gradedCurvJet` and the combined diff-curvature/remainder
  `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`; at rank `r` the pure-Riemann grid
  tower (`FrozenFramePureRCurvatureTower`'s frame-free envelope) is itself stated only at rank `0`, so
  the entire graded seed is collected here as **one** posited primitive (folding the absent rank-`r`
  pure-Riemann grid into the seed), exactly as `MovingFrameGenuineFieldPairingRS` collects the
  rank-`r` deepest tri-split into one node;
* the **inductive step `m → m + 1`** is the posited genuine per-step primitive
  `iteratedCovGrad_pointwiseTensorCurvRS_gradedCurvJet_field_step`: applying one further covariant
  gradient `∇` to the order-`m` graded split and re-Leibniz-ing the curvature contractions, the
  iterated Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order
  `∇^{m + 3}S` term, producing the order-`(m + 1)` graded split with the genuine curvature-jet bounds
  advanced by one order. Its hypothesis is the *graded* order-`m` split and its conclusion the graded
  order-`(m + 1)` split — strictly weaker than the headline, hence not the conclusion itself.

This is exactly the rank-`0` posit count: the rank-`0` tower bottoms on two posited primitives
(`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`,
`exists_iteratedCovGrad_remainder_gradedCurvJet_refine`) with the pure-Riemann grid *proved* off the
frame-free envelope; the rank-`r` mirror bottoms on the two posited primitives
`pointwiseTensorCurvRS_gradedCurvJet_field_base`,
`iteratedCovGrad_pointwiseTensorCurvRS_gradedCurvJet_field_step` (the absent rank-`r` pure-Riemann grid
folded into the first, so the count does not increase). Consumers transitively depend on `sorryAx`
through these posited primitives.

The degenerate witness is rejected: at `m = 0`, gradient order `k = 0`, the split reads
`Curv S (x) = Gcurv + GcurvDeriv + Grem` with `rfns(Gcurv)(x) ≤ (c 0)²·rfns(∇S)(x)`,
`rfns(GcurvDeriv)(x) ≤ (c 0)²·rfns(S)(x)`, `rfns(Grem)(x) ≤ (c 0)²·rfns(∇²S)(x)`, which — merged — is
the `m = 0` two-term split, *false* with `c 0 = 0` on a non-flat manifold (the defect carries the
genuine curvature contraction of `S`).

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian. The covariant
gradient `covGrad g r s` raises the tensor rank from `(r, s)` to `(r, s + 1)`; `iteratedCovGrad g r s
j` is its `j`-fold iterate. All fibre norms are the intrinsic `riemannianFiberNormSq`.
-/

noncomputable section

set_option linter.style.setOption false
set_option linter.unusedSectionVars false
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

/-- **Heterogeneous rank-congruence for `covGrad` at rank `r`.** If two covariant ranks agree
(`h : a = b`) and the smooth compactly-supported `(r, ·)`-tensors `Y`, `Z` are heterogeneously equal,
then so are `covGrad g r a Y` and `covGrad g r b Z`. Proved by `subst` on the rank variable.
(File-local copy; the rank-generic version is the rank-`0`-locked `covGrad_heq_congr_local` of
`OrderSeparatedCurvatureJet`, which this file does not import.) -/
private theorem covGradRS_heq_congr_local (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g r a Y) (covGrad (I := I) (M := M) g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient at rank `r`.**
Applying `m` covariant gradients to `covGrad g r s X` is heterogeneously equal to the `(m + 1)`-fold
iterated gradient of `X`, the two living in the ranks `(s + 1) + m` and `s + (m + 1)`, which agree as
naturals. Proved by induction on `m` through `covGradRS_heq_congr_local`. The closure engine the
graded-jet `covGrad`-closure runs on; the rank index `r` is fully generic. -/
private theorem iteratedCovGradRS_covGrad_comm_heq_local (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad (I := I) (M := M) g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k)
        (covGrad (I := I) (M := M) g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGradRS_heq_congr_local g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The intrinsic fibre norm is invariant under a rank-`r` `SmoothCcTensor` rank-cast.**
Heterogeneously equal smooth compactly-supported `(r, ·)`-tensors over agreeing ranks have equal
section-value `riemannianFiberNormSq` at every point. Proved by `subst` on the rank variable. -/
private theorem riemannianFiberNormSqRS_toSection_heq_congr (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **The re-differentiable graded curvature-jet predicate at rank `r`.** The verbatim
contravariant-rank-`r` mirror of `IsGradedCurvJet` (`OrderSeparatedCurvatureJet`). For a closed smooth
Riemannian manifold `(M, g)`, a fixed source `(r, s)`-tensor `S`, an order-indexed nonnegative constant
family `c : ℕ → ℝ`, a lowest contracted order `p`, a base width `w`, and a field
`G : SmoothCcTensor g r t` (covariant rank generic), `IsGradedCurvJetRS g S c p w G` asserts that for
*every* further gradient order `k` and *every* point `x` the `k`-fold iterated covariant gradient
`∇^k G` is fibre-bounded by `(c k)²` times the truncated sum of the iterated-gradient fibre norms of
`S` from contracted order `p` up to width `w + k`:

```
rfns(∇^k G)(x) ≤ (c k)² · ∑_{i < w + k} rfns(∇^{i + p} S)(x).
```

The constant must be a *family* indexed by the gradient order `k` (not a single scalar): on a generic
closed manifold `sup_k ‖∇^k R‖_∞ = ∞`, so no single `c` dominates all gradient orders. The predicate
is closed under one covariant gradient (`IsGradedCurvJetRS_covGrad`), which is exactly what the
per-step of the order-`m` induction requires. -/
def IsGradedCurvJetRS (g : SmoothRiemannianMetric I M) {r s : ℕ} (S : SmoothCcTensor g r s)
    (c : ℕ → ℝ) (p w : ℕ) {t : ℕ} (G : SmoothCcTensor g r t) : Prop :=
  ∀ (k : ℕ) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
        ((iteratedCovGrad g r t k G).toSection x) ≤
      (c k) ^ 2 * ∑ i ∈ Finset.range (w + k),
        riemannianFiberNormSq (I := I) (M := M) g r (s + (i + p)) x
          ((iteratedCovGrad g r s (i + p) S).toSection x)

/-- **The rank-`r` graded curvature-jet predicate is closed under one covariant gradient.** If `G` is
a graded curvature jet of `S` of lowest order `p` and base width `w`, then its covariant gradient `∇G`
is a graded curvature jet of the same lowest order `p` with base width `w + 1`: the `k`-th gradient of
`∇G` is the `(k + 1)`-th gradient of `G`, so the bound shifts `k → k + 1`, i.e. width `w + k → w +
(k + 1) = (w + 1) + k`. The structural step that makes the order-`m` induction's per-step
re-differentiable. The verbatim mirror of `IsGradedCurvJet_covGrad`. -/
theorem IsGradedCurvJetRS_covGrad (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c : ℕ → ℝ} {p w t : ℕ} {G : SmoothCcTensor g r t}
    (hG : IsGradedCurvJetRS (I := I) (M := M) g S c p w G) :
    IsGradedCurvJetRS (I := I) (M := M) g S (fun k => c (k + 1)) p (w + 1)
      (covGrad (I := I) (M := M) g r t G) := by
  intro k x
  have hheq := riemannianFiberNormSqRS_toSection_heq_congr (I := I) (M := M) g r
    (by omega : (t + 1) + k = t + (k + 1))
    (iteratedCovGradRS_covGrad_comm_heq_local (I := I) (M := M) g r t k G) x
  rw [hheq]
  have hkey := hG (k + 1) x
  have hwidth : w + (k + 1) = (w + 1) + k := by omega
  rw [hwidth] at hkey
  exact hkey

/-- **The rank-`r` truncated graded-jet target sum is nonnegative.** Every summand is an intrinsic
squared fibre norm `riemannianFiberNormSq`, hence `≥ 0`; the finite sum is therefore `≥ 0`. -/
private lemma gradedCurvJetRS_targetSum_nonneg (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) (p w k : ℕ) (x : M) :
    0 ≤ ∑ i ∈ Finset.range (w + k),
        riemannianFiberNormSq (I := I) (M := M) g r (s + (i + p)) x
          ((iteratedCovGrad g r s (i + p) S).toSection x) :=
  Finset.sum_nonneg fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + (i + p)) x _

/-- **Monotonicity of the rank-`r` graded curvature-jet predicate in its constant family.** If `G` is
a graded curvature jet of `S` with nonnegative constant family `c` and `c k ≤ c' k` at every order
`k`, then `G` is also a graded curvature jet with the larger constant family `c'`. The verbatim mirror
of `IsGradedCurvJet.mono_const`. -/
theorem IsGradedCurvJetRS.mono_const (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c c' : ℕ → ℝ} {p w t : ℕ} {G : SmoothCcTensor g r t}
    (hc : ∀ k, 0 ≤ c k) (hcc' : ∀ k, c k ≤ c' k)
    (hG : IsGradedCurvJetRS (I := I) (M := M) g S c p w G) :
    IsGradedCurvJetRS (I := I) (M := M) g S c' p w G := by
  intro k x
  refine (hG k x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (gradedCurvJetRS_targetSum_nonneg (I := I) (M := M) g S p w k x)
  exact pow_le_pow_left₀ (hc k) (hcc' k) 2

/-- **The rank-`r` graded curvature-jet predicate is closed under addition of two jets of the same
shape.** If `G₁`, `G₂` are graded curvature jets of `S` of the *same* lowest order `p` and base width
`w`, with nonnegative constant families `c₁`, `c₂`, then their sum `G₁ + G₂` is a graded curvature jet
of the same lowest order `p` and base width `w`, with constant family
`k ↦ √(2·((c₁ k)² + (c₂ k)²))`. The field-level subadditivity that merges two genuine jets while
keeping the curvature-jet shape. The verbatim mirror of `IsGradedCurvJet.add`. -/
theorem IsGradedCurvJetRS.add (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c₁ c₂ : ℕ → ℝ} {p w t : ℕ}
    {G₁ G₂ : SmoothCcTensor g r t}
    (hG₁ : IsGradedCurvJetRS (I := I) (M := M) g S c₁ p w G₁)
    (hG₂ : IsGradedCurvJetRS (I := I) (M := M) g S c₂ p w G₂) :
    IsGradedCurvJetRS (I := I) (M := M) g S
      (fun k => Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2))) p w (G₁ + G₂) := by
  intro k x
  have hsum_nonneg := gradedCurvJetRS_targetSum_nonneg (I := I) (M := M) g S p w k x
  have hsplit : (iteratedCovGrad g r t k (G₁ + G₂)).toSection x =
      (iteratedCovGrad g r t k G₁).toSection x + (iteratedCovGrad g r t k G₂).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsplit]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (t + k) x
    ((iteratedCovGrad g r t k G₁).toSection x) ((iteratedCovGrad g r t k G₂).toSection x)
  have hcsq : Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2)) ^ 2 = 2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  rw [hcsq]
  calc riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
          ((iteratedCovGrad g r t k G₁).toSection x + (iteratedCovGrad g r t k G₂).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
            ((iteratedCovGrad g r t k G₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
            ((iteratedCovGrad g r t k G₂).toSection x) := hadd
    _ ≤ 2 * ((c₁ k) ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g r (s + (i + p)) x
                ((iteratedCovGrad g r s (i + p) S).toSection x)) +
          2 * ((c₂ k) ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g r (s + (i + p)) x
                ((iteratedCovGrad g r s (i + p) S).toSection x)) := by
        gcongr <;> [exact hG₁ k x; exact hG₂ k x]
    _ = 2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2) * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g r (s + (i + p)) x
                ((iteratedCovGrad g r s (i + p) S).toSection x) := by ring

/-- **The moving-centre pure-Riemann genuine section is a graded curvature jet of `S` at rank `r`
(shape `(1, 1)`), proved.** The contravariant-rank-`r` mirror of the rank-`0` `GcurvSection_gradedCurvJet`
(`OrderSeparatedCurvatureJet`). For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every
covariant rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the concrete
moving-centre pure-Riemann genuine curvature section `GcurvSectionRS g r s S` (the `R(∇S)` contraction)
is a graded curvature jet of `S` of lowest order `1` and width `1`:
`IsGradedCurvJetRS g S (c s) 1 1 (GcurvSectionRS g r s S)`.

This is **proved** by repackaging the rank-`r` frame-free pure-Riemann curvature-jet grid
`exists_GcurvSectionRS_iteratedCovGrad_grid_bound` (`MovingFrameGenuineFieldPairingRS`, now *sorry-free*,
discharged over the rank-`r` frame-free differentiated curvature tower `genuinePureRDiffOpRS_bilinOp`)
into the graded-jet predicate: the grid bound
`rfns(∇^k (GcurvSectionRS g r s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x)` is, slot for
slot, the `(p, w) = (1, 1)` instance of `IsGradedCurvJetRS` (the contracted-order window `1 … 1 + k` is
`∑_{i < 1 + k} rfns(∇^{i + 1} S)`). At rank `0` this repackaging is the proof of
`GcurvSection_gradedCurvJet`; at rank `r` it is the same repackaging of the now-discharged rank-`r`
grid. (File-local; the public general-rank version is `GcurvSectionRS_gradedCurvJet` of
`CurvatureJetGridRS`, which is downstream of this file and so cannot be cited here.) -/
private theorem gcurvSectionRS_gradedCurvJet_ofGrid (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 1
          (GcurvSectionRS (I := I) (M := M) g r s S) := by
  classical
  obtain ⟨c, hc_nn, hgrid⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨c, hc_nn, fun s S => ?_⟩
  intro k x
  -- `IsGradedCurvJetRS g S (c s) 1 1 (GcurvSectionRS …)` at gradient order `k`, point `x`, is exactly
  -- the grid bound (window `w + k = 1 + k`, lowest order `p = 1` so the target jets are `∇^{i + 1} S`).
  have hg := hgrid s S k x
  simpa only [Nat.add_comm 1 k] using hg

/-- **Rank-`r` differentiated-curvature `(∇R) S` graded jet for the concrete carrier `diffCurvSectionRS`
(proved over the rank-`r` carrier-tower grid).** The contravariant-rank-`r` mirror of the rank-`0`
differentiated-curvature graded jet `genuineDiffCurvSection_gradedCurvJet` (`DiffCurvatureGenuineTower`),
the `(∇R) S` operator-field carrier. For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a *valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ`
such that, at every covariant rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the
concrete gauge-glued tensorial differentiated-curvature carrier `diffCurvSectionRS g r s S`
(`RankRDiffCurvatureTower`, the order-`0` base of the `(∇R)·` tower) is a *graded* curvature jet of `S`
of lowest order `0` and width `1`:
```
IsGradedCurvJetRS g S (c s) 0 1 (diffCurvSectionRS g r s S).
```
The concrete field `diffCurvSectionRS g r s S` is pinned (no `∃ Gcd`), mirroring the rank-`0`
`genuineDiffCurvSection_gradedCurvJet` which pins `genuineDiffCurvSection g s S`.

**Proof (over the carrier-tower grid).** `IsGradedCurvJetRS g S (c s) 0 1 (diffCurvSectionRS g r s S)`
at gradient order `k`, point `x`, is exactly the raw iterated-gradient grid bound
`exists_diffCurvSectionRS_iteratedCovGrad_grid_bound` (`RankRDiffCurvatureTower`, window `w + k = 1 + k`,
lowest order `p = 0`, target jets `∇^{i + 0} S`), which is *proved* off the rank-`r` `(∇R)·` carrier
tower's binomial covariant-Leibniz grid and per-order envelope. Consumers transitively depend on `sorryAx`
through the carrier tower's single posited node `exists_diffCurvGenuineTowerRS`.
This carries NO remainder and NO section split (those are
`exists_pointwiseTensorCurvRS_remainder_afterDiffCurv_gradedCurvJet` below).

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` forces `rfns(diffCurvSectionRS g r s S)(x) = 0`,
i.e. the differentiated-curvature contraction vanishes; *false* on a manifold with `∇R ≠ 0` and `S ≠ 0`.
The constant family is genuinely positive. -/
theorem exists_diffCurvSectionRS_gradedCurvJet (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1
          (diffCurvSectionRS (I := I) (M := M) g r s S) := by
  classical
  obtain ⟨c, hc_nn, hgrid⟩ :=
    exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨c, hc_nn, fun s S => ?_⟩
  intro k x
  -- `IsGradedCurvJetRS g S (c s) 0 1 (diffCurvSectionRS …)` at gradient order `k`, point `x`, is exactly
  -- the carrier-tower grid bound (window `w + k = 1 + k`, lowest order `p = 0`, target jets `∇^{i+0} S`).
  exact hgrid s S k x

/-- **Posited rank-`r` moving-frame remainder graded jet after the differentiated-curvature peel (the
genuine remainder core).** The contravariant-rank-`r` analogue of the rank-`0` remainder content of
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)`, fixed contravariant rank `r`, there is a
*valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s` and for every smooth compactly-supported `(r, s)`-tensor `S`, peeling off the *concrete* gauge-glued
differentiated-curvature carrier `diffCurvSectionRS g r s S` (the `(∇R) S` field, the canonical carrier
pinned by `exists_diffCurvSectionRS_gradedCurvJet`), there is a moving-frame remainder field
`Grem : SmoothCcTensor g r (s + 1)` such that the order-`2` commutator defect splits over the
pure-Riemann section `GcurvSectionRS g r s S` and that carrier:
`pointwiseTensorCurvRS g r s S = GcurvSectionRS g r s S + diffCurvSectionRS g r s S + Grem`, with `Grem`
a graded curvature jet of lowest order `2` and width `1`: `IsGradedCurvJetRS g S (c s) 2 1 Grem`.

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0` remainder content. By the
rank-`r` genuine+bracket field split of the defect (the iterated-Ricci third-order Weitzenböck split,
sorry-free at the section level) the defect is `GcurvSectionRS + (∇R)S\text{-trace} + \text{remainder}`;
defining `Grem := pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S` (a
literal subtraction, so the section split is `abel`), `Grem` is the moving-frame / frame-bracket
remainder genuinely `∇²S`-order after the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` cancels the top-order `∇³S` terms, each `∇^k Grem` a
sum of contractions of `∇^p R` (`p ≤ k`) against `∇^{q + 2}S` (`q ≤ k`), contracted-order window
`2 … 2 + k` (the `(p, w) = (2, 1)` graded shape), all curvature coefficients absorbed uniformly over the
compact `M`. The rank-`r` moving-frame remainder graded refinement is absent sorry-free below this file
(the rank-`0` carriers and the field split use the rank-`0`-locked curvature contractions), so it is
posited here as one precise true core — the rank-`r` analogue of the genuine rank-`0` remainder content
(itself a posited `sorry` at rank `0`, the remainder half of
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`). The carrier `diffCurvSectionRS` carries
the genuine `(∇R) S` (order-`0`) content, so subtracting it off is exactly what makes the surviving
`Grem` order-`2`. Consumers transitively depend on `sorryAx`.

**Signature soundness — why the carrier `Gcd` is pinned, not a free input.** The carrier is the concrete
`diffCurvSectionRS g r s S`, *not* a universally-quantified `Gcd` input. A version taking an arbitrary
graded-jet field `Gcd` (of lowest order `0`, width `1`) as input, with the constant family `c` chosen
*before* `Gcd`, is FALSE: the section equation forces `Grem = Curv − Gcurv − Gcd`, and feeding the
admissible witness `Gcd = 0` (a graded jet of any order with the zero family) forces
`Grem = Curv − Gcurv`, whose graded-`2` bound at `k = 0` reads `rfns(Curv − Gcurv)(x) ≤ (c s 0)² ·
rfns(∇²S)(x)`. At a point where the covariant `2`-jet of `S` vanishes but `S(x) ≠ 0` and `∇R(x) ≠ 0`
the pure-Riemann `Gcurv` (reading `∇S(x) = 0`) and the `∇²S`-order remainder both vanish while the
differentiated-curvature `(∇R) S` content is genuinely non-zero, so `rfns(Curv − Gcurv)(x) > 0 =
(c s 0)² · 0` — contradiction for any finite `c`. Equivalently, two admissible carriers (e.g.
`diffCurvSectionRS` and `0`) would force `diffCurvSectionRS = Grem₀ − Grem₁` to be a graded jet of
lowest order `2`, contradicting that `diffCurvSectionRS` is genuinely order-`0` (its non-vacuity at
`exists_diffCurvSectionRS_gradedCurvJet`). Pinning the carrier to the canonical
`diffCurvSectionRS g r s S` (the same field `exists_diffCurvSectionRS_gradedCurvJet` pins) removes this
defect and matches both the rank-`0` analogue (which carries `Gcd` *existentially*, not as an input) and
the sole consumer `exists_pointwiseTensorCurvRS_diffCurvAndRemainder_gradedCurvJet` (which always feeds
`Gcd = diffCurvSectionRS g r s S`).

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` forces `rfns(Grem)(x) = 0`, i.e.
`Curv S = GcurvSectionRS + diffCurvSectionRS`; *false* on a non-flat manifold (the moving-frame bracket
remainder is genuinely non-zero). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 2 1
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
            GcurvSectionRS (I := I) (M := M) g r s S -
            diffCurvSectionRS (I := I) (M := M) g r s S) := by
  sorry

/-- **Posited rank-`r` moving-frame remainder graded jet after the differentiated-curvature peel (the
genuine remainder core), in existential-`Grem` form (proved over the pinned-remainder graded jet).** The
contravariant-rank-`r` analogue of the rank-`0` remainder content of
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)`, fixed contravariant rank `r`, there is a
*valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s` and for every smooth compactly-supported `(r, s)`-tensor `S`, peeling off the *concrete* gauge-glued
differentiated-curvature carrier `diffCurvSectionRS g r s S` (the `(∇R) S` field, the canonical carrier
pinned by `exists_diffCurvSectionRS_gradedCurvJet`), there is a moving-frame remainder field
`Grem : SmoothCcTensor g r (s + 1)` such that the order-`2` commutator defect splits over the
pure-Riemann section `GcurvSectionRS g r s S` and that carrier:
`pointwiseTensorCurvRS g r s S = GcurvSectionRS g r s S + diffCurvSectionRS g r s S + Grem`, with `Grem`
a graded curvature jet of lowest order `2` and width `1`: `IsGradedCurvJetRS g S (c s) 2 1 Grem`.

**Proof (glue over the pinned-remainder graded jet).** The moving-frame remainder is the literal
subtraction `Grem := pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S`,
so the section split `Curv S = GcurvSectionRS + diffCurvSectionRS + Grem` is `abel`, and its order-`2`
graded jet is exactly the pinned-remainder graded jet
`exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_gradedCurvJet` (the genuine remainder core, transiting
`sorryAx`). The carrier `diffCurvSectionRS` carries the genuine `(∇R) S` (order-`0`) content, so
subtracting it off is exactly what makes the surviving `Grem` order-`2`. Consumers transitively depend on
`sorryAx`.

**Signature soundness — why the carrier `Gcd` is pinned, not a free input.** The carrier is the concrete
`diffCurvSectionRS g r s S`, *not* a universally-quantified `Gcd` input. A version taking an arbitrary
graded-jet field `Gcd` (of lowest order `0`, width `1`) as input, with the constant family `c` chosen
*before* `Gcd`, is FALSE: the section equation forces `Grem = Curv − Gcurv − Gcd`, and feeding the
admissible witness `Gcd = 0` (a graded jet of any order with the zero family) forces
`Grem = Curv − Gcurv`, whose graded-`2` bound at `k = 0` reads `rfns(Curv − Gcurv)(x) ≤ (c s 0)² ·
rfns(∇²S)(x)`. At a point where the covariant `2`-jet of `S` vanishes but `S(x) ≠ 0` and `∇R(x) ≠ 0`
the pure-Riemann `Gcurv` (reading `∇S(x) = 0`) and the `∇²S`-order remainder both vanish while the
differentiated-curvature `(∇R) S` content is genuinely non-zero, so `rfns(Curv − Gcurv)(x) > 0 =
(c s 0)² · 0` — contradiction for any finite `c`. Equivalently, two admissible carriers (e.g.
`diffCurvSectionRS` and `0`) would force `diffCurvSectionRS = Grem₀ − Grem₁` to be a graded jet of
lowest order `2`, contradicting that `diffCurvSectionRS` is genuinely order-`0` (its non-vacuity at
`exists_diffCurvSectionRS_gradedCurvJet`). Pinning the carrier to the canonical
`diffCurvSectionRS g r s S` (the same field `exists_diffCurvSectionRS_gradedCurvJet` pins) removes this
defect and matches both the rank-`0` analogue (which carries `Gcd` *existentially*, not as an input) and
the sole consumer `exists_pointwiseTensorCurvRS_diffCurvAndRemainder_gradedCurvJet` (which always feeds
`Gcd = diffCurvSectionRS g r s S`).

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` forces `rfns(Grem)(x) = 0`, i.e.
`Curv S = GcurvSectionRS + diffCurvSectionRS`; *false* on a non-flat manifold (the moving-frame bracket
remainder is genuinely non-zero). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_remainder_afterDiffCurv_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S +
                diffCurvSectionRS (I := I) (M := M) g r s S + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 2 1 Grem := by
  classical
  obtain ⟨c, hc_nn, hjet⟩ :=
    exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_gradedCurvJet (I := I) (M := M) g r
  refine ⟨c, hc_nn, fun s S => ?_⟩
  refine ⟨pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S -
      diffCurvSectionRS (I := I) (M := M) g r s S, ?_, hjet s S⟩
  abel

/-- **Rank-`r` combined differentiated-curvature / moving-frame remainder graded split (proved over the
two genuine cores).** The contravariant-rank-`r` mirror of the rank-`0`
`exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
*valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` splits, *over the concrete pure-Riemann genuine section*
`GcurvSectionRS g r s S`, into a differentiated-curvature graded jet `Gcd` and a moving-frame remainder
graded jet `Grem`:

```
Curv S = GcurvSectionRS g r s S + Gcd + Grem,
```

with `Gcd` a graded curvature jet of `S` of lowest order `0` and width `1`
(`IsGradedCurvJetRS g S (c s) 0 1 Gcd`, the `(∇R) S` contraction) and `Grem` a graded curvature jet of
lowest order `2` and width `1` (`IsGradedCurvJetRS g S (c s) 2 1 Grem`, the moving-frame / frame-bracket
remainder whose top-order `∇³S` terms cancel by the iterated Ricci identity).

**Proof (composition over the two genuine cores).** This is the contravariant-rank-`r` mirror of the
rank-`0` `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`, *glued* (as at rank `0`) over
the differentiated-curvature `(∇R) S` graded jet `exists_diffCurvSectionRS_gradedCurvJet` (the rank-`r`
analogue of `genuineDiffCurvSection_gradedCurvJet`) and the remainder split after the
differentiated-curvature peel `exists_pointwiseTensorCurvRS_remainder_afterDiffCurv_gradedCurvJet` (the
rank-`r` analogue of the moving-frame remainder content): the first produces the `(∇R) S` field `Gcd`
with its graded jet `IsGradedCurvJetRS g S · 0 1 Gcd`, and the second — fed that `Gcd` — produces the
moving-frame remainder `Grem` with the section split `Curv S = GcurvSectionRS + Gcd + Grem` and
`IsGradedCurvJetRS g S · 2 1 Grem`. The two constant families merge into one per-order family by `max`
through `IsGradedCurvJetRS.mono_const`. Consumers transitively depend on `sorryAx` through the two cores.

**Non-vacuity.** With `c s 0 = 0` the two bounds force, at `k = 0`, `rfns(Gcd)(x) = rfns(Grem)(x) = 0`,
so the split reads `Curv S = GcurvSectionRS g r s S`, forcing the entire differentiated-curvature plus
bracket content to vanish; *false* on a non-flat manifold (the `(∇R) S` content is genuinely `rfns(S)`-
order non-zero when `∇R ≠ 0` and `S ≠ 0`). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_diffCurvAndRemainder_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S + Gcd + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 Gcd ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 2 1 Grem := by
  classical
  obtain ⟨c₁, hc₁_nn, hdiff⟩ := exists_diffCurvSectionRS_gradedCurvJet (I := I) (M := M) g r
  obtain ⟨c₂, hc₂_nn, hrem⟩ :=
    exists_pointwiseTensorCurvRS_remainder_afterDiffCurv_gradedCurvJet (I := I) (M := M) g r
  refine ⟨fun s k => max (c₁ s k) (c₂ s k),
    fun s k => le_trans (hc₁_nn s k) (le_max_left _ _), fun s S => ?_⟩
  -- The concrete `(∇R) S` carrier `diffCurvSectionRS g r s S` is the differentiated-curvature field
  -- `Gcd`; its `(0, 1)` graded jet `hdiff s S` (the proved concrete leaf) and the remainder split
  -- (the pinned-carrier core `hrem s S`, producing `Grem` with `Curv S = GcurvSectionRS +
  -- diffCurvSectionRS + Grem` and `Grem`'s `(2, 1)` graded jet) together fill the combined split.
  obtain ⟨Grem, hsplit, hGrem_jet⟩ := hrem s S
  refine ⟨diffCurvSectionRS (I := I) (M := M) g r s S, Grem, hsplit, ?_, ?_⟩
  · exact (hdiff s S).mono_const (I := I) (M := M) g S (hc₁_nn s) (fun k => le_max_left _ _)
  · exact hGrem_jet.mono_const (I := I) (M := M) g S (hc₂_nn s) (fun k => le_max_right _ _)

/-- **Explicit graded curvature-jet seed at rank `r`: the `m = 0` order-separated graded field split of
the order-`2` commutator defect (proved by composition).** The contravariant-rank-`r` mirror of the
rank-`0` graded seed `pointwiseTensorCurv_gradedCurvJet_field_base` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
family `c : ℕ → ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits an
explicit graded curvature-jet split

```
Curv S = Gcurv + GcurvDeriv + Grem
```

into three smooth compactly-supported `(r, s + 1)`-tensor fields, where each is a *graded* curvature jet
of `S` (`IsGradedCurvJetRS`) at the appropriate lowest order: the differentiated-Riemann jet `Gcurv`
(the pure-Riemann contraction `R(∇S)`, concretely `GcurvSectionRS g r s S`) of lowest order `1` and
width `1`, the iterated differentiated-curvature jet `GcurvDeriv` (the `(∇R) S` contraction) of lowest
order `0` and width `1`, and the moving-frame remainder `Grem` of lowest order `2` and width `1`.

This is **proved by composition** (the rank-`r` mirror of the rank-`0` glue): the pure-Riemann channel
`Gcurv := GcurvSectionRS g r s S` is a graded jet of shape `(1, 1)` *sorry-free* by
`gcurvSectionRS_gradedCurvJet_ofGrid` (off the now-discharged rank-`r` frame-free pure-Riemann grid); the
differentiated-curvature jet `GcurvDeriv := Gcd` (shape `(0, 1)`) and the moving-frame remainder
`Grem` (shape `(2, 1)`), together with the section split `Curv S = GcurvSectionRS + Gcd + Grem`, come
from the single posited combined child `exists_pointwiseTensorCurvRS_diffCurvAndRemainder_gradedCurvJet`;
the three constant families are merged into one per-order family by `max` through `IsGradedCurvJetRS.mono_const`.
The rank-`r` mirror's posit count therefore does not exceed the rank-`0` count (which has the same single
genuine posit, the pure-Riemann channel being sorry-free at both ranks). Consumers transitively depend on
`sorryAx` through the single combined diff-curvature/remainder child.

**Non-vacuity.** With `c s 0 = 0` the three bounds force `rfns(Gcurv)(x) = rfns(GcurvDeriv)(x) =
rfns(Grem)(x) = 0` at `k = 0`, making the split `Curv S = 0`; *false* on a non-flat manifold where the
defect carries the genuine curvature contraction of `S` (`R ≠ 0`, `∇S ≠ 0`). The constant family is
genuinely positive. -/
theorem pointwiseTensorCurvRS_gradedCurvJet_field_base
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S = Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 1 Gcurv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 GcurvDeriv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 2 1 Grem := by
  classical
  -- The three genuine fields are `GcurvSectionRS` (pure-Riemann, shape `(1, 1)`, sorry-free off the
  -- now-discharged rank-`r` grid) and the existential differentiated-curvature `Gcd` (shape `(0, 1)`)
  -- and moving-frame remainder `Grem` (shape `(2, 1)`) of the combined posited graded tri-split;
  -- promote all three to a single common per-order family by `mono_const`.
  obtain ⟨c₁, hc₁_nn, hcurv⟩ := gcurvSectionRS_gradedCurvJet_ofGrid (I := I) (M := M) g r
  obtain ⟨c₂, hc₂_nn, hdiffrem⟩ :=
    exists_pointwiseTensorCurvRS_diffCurvAndRemainder_gradedCurvJet (I := I) (M := M) g r
  refine ⟨fun s k => max (c₁ s k) (c₂ s k), fun s k => le_trans (hc₁_nn s k) (le_max_left _ _),
    fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hGcd_jet, hGrem_jet⟩ := hdiffrem s S
  refine ⟨GcurvSectionRS (I := I) (M := M) g r s S, Gcd, Grem, hsplit, ?_, ?_, ?_⟩
  · exact (hcurv s S).mono_const (I := I) (M := M) g S (hc₁_nn s) (fun k => le_max_left _ _)
  · exact hGcd_jet.mono_const (I := I) (M := M) g S (hc₂_nn s) (fun k => le_max_right _ _)
  · exact hGrem_jet.mono_const (I := I) (M := M) g S (hc₂_nn s) (fun k => le_max_right _ _)

/-- **Posited genuine per-step moving-frame remainder-refinement at rank `r` (the iterated Ricci
cancellation).** The contravariant-rank-`r` mirror of the rank-`0` remainder-refinement
`exists_iteratedCovGrad_remainder_gradedCurvJet_refine` (`OrderSeparatedCurvatureJet`, *which transits
`sorryAx`* at rank `0`). For a closed smooth Riemannian manifold `(M, g)`, fixed contravariant rank `r`,
covariant rank `s`, gradient order `m`, and nonnegative input-bound family `C : ℕ → ℝ`, there is a
nonnegative family `C' : ℕ → ℝ` — depending only on `g, r, s, m, C`, *uniform* in the source `S` and the
remainder field `Grem` — such that for every smooth compactly-supported `(r, s)`-tensor `S` and every
smooth compactly-supported `(r, s + 1 + m)`-tensor field `Grem` that is a graded curvature jet of `S` of
lowest order `m + 2` and width `1`, the single covariant gradient `∇Grem := covGrad g r (s + 1 + m) Grem`
splits as `∇Grem = Greclass + Grem'`, with `Greclass` a graded curvature jet of `S` of lowest order `1`
and width `m + 2`, and `Grem'` a graded curvature jet of lowest order `m + 3` and width `1`.

**Why this is TRUE — the cancellation.** This is the verbatim contravariant-rank-`r` lift of the rank-`0`
`exists_iteratedCovGrad_remainder_gradedCurvJet_refine`. Differentiating the order-`(m + 2)` moving-frame
remainder once produces a field of naive graded order `m + 2`, width `2`; the extra top contracted-order
term is where two covariant gradients commute by the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (the rank-`(r, s + 1 + m)` instance, sorry-free), the
antisymmetrised second covariant derivative equalling a `riemannOp` contraction of *one-lower* order; the
commuted curvature term is a graded jet of lowest order `1` (`Greclass`), and what remains (`Grem'`) is
genuinely order `m + 3`, width `1`. All curvature coefficients are uniformly bounded over the compact `M`.
At rank `0` this is itself a posited `sorry`; the rank-`r` iterated moving-frame curvature-derivation
content (the rank-`0` remainder refinement uses the rank-`0`-locked curvature contractions) is absent
sorry-free below this file, so it is posited here as one precise true child — the rank-`r` analogue of the
genuine rank-`0` `sorry` leaf. Consumers transitively depend on `sorryAx`.

**Strictly weaker than the per-step (no hypothesis-packaging).** This refines *one field's* single
covariant gradient; it neither mentions `Curv S` nor produces the order-`(m + 1)` triple split — the
per-step is assembled on top of it together with `IsGradedCurvJetRS_covGrad` and `IsGradedCurvJetRS.add`.
**Non-vacuity.** With `C' = 0` the conclusion forces `rfns(Greclass) = rfns(Grem') = 0` at every order,
hence `∇Grem = 0` for every graded remainder `Grem`; false on a non-flat manifold where the
once-differentiated moving-frame remainder is genuinely non-zero. -/
theorem exists_iteratedCovGrad_remainderRS_gradedCurvJet_refine
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) (C : ℕ → ℝ) (_hC : ∀ k, 0 ≤ C k) :
    ∃ C' : ℕ → ℝ, (∀ k, 0 ≤ C' k) ∧
      ∀ (S : SmoothCcTensor g r s) (Grem : SmoothCcTensor g r (s + 1 + m)),
        IsGradedCurvJetRS (I := I) (M := M) g S C (m + 2) 1 Grem →
        ∃ Greclass Grem' : SmoothCcTensor g r (s + 1 + (m + 1)),
          covGrad (I := I) (M := M) g r (s + 1 + m) Grem = Greclass + Grem' ∧
          IsGradedCurvJetRS (I := I) (M := M) g S C' 1 (m + 2) Greclass ∧
          IsGradedCurvJetRS (I := I) (M := M) g S C' (m + 3) 1 Grem' := by
  sorry

/-- **Posited genuine per-step moving-frame curvature-jet primitive at rank `r`: one covariant-gradient
step of the order-separated *graded* section-field split of the iterated commutator defect (proved over
the remainder refinement and the graded-jet closure lemmas).** The contravariant-rank-`r` mirror of the
rank-`0` per-step primitive `iteratedCovGrad_pointwiseTensorCurv_gradedCurvJet_field_step`
(`OrderSeparatedCurvatureJet`). For a closed smooth Riemannian manifold `(M, g)`, a fixed covariant rank
`s`, gradient order `m`, and nonnegative constant family `C : ℕ → ℝ`, suppose the `m`-fold iterated
covariant gradient of the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits,
for *every* smooth
compactly-supported `(r, s)`-tensor `S`, an order-separated *graded* section-level split

```
∇^m(Curv S) = Gcurv + GcurvDeriv + Grem
```

where each field is a **graded** curvature jet (`IsGradedCurvJetRS`) of the appropriate lowest order:
`Gcurv` of lowest order `1` and width `m + 1`, `GcurvDeriv` of lowest order `0` and width `m + 1`, and
`Grem` of lowest order `m + 2` and width `1`. Then there is a nonnegative constant family `C' : ℕ → ℝ`
such that the *one-higher* iterated covariant gradient `∇^{m + 1}(Curv S)` admits, for every `S`, the
order-`(m + 1)` order-separated graded split

```
∇^{m + 1}(Curv S) = Gcurv' + GcurvDeriv' + Grem',
```

with `Gcurv'` a graded jet of lowest order `1` and width `m + 2`, `GcurvDeriv'` of lowest order `0`
and width `m + 2`, and `Grem'` of lowest order `m + 3` and width `1`.

**Why this is TRUE — the cancellation.** This is the genuinely-irreducible per-step third-order
moving-frame Bochner–Weitzenböck content at rank `r`. Its construction applies one further covariant
gradient `∇ = covGrad g r (s + 1 + m)` to the order-`m` section identity and re-Leibniz-es the
curvature contractions: the top-order `∇^{m + 3}S` term produced by differentiating the genuine Riemann
jet `Gcurv` *cancels* against its swapped partner via the iterated Ricci identity
(`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, the rank-`(r, s + 1 + m)` instance), commuting two
of the gradients into a `riemannOp` of one-lower order; the surviving genuine curvature-jet
contractions advance by exactly one order, all coefficients — covariant derivatives of curvature —
sup-bounded on the compact manifold by the uniform sups; and the moving-frame remainder lands at order
`m + 3` precisely because of the cancellation. This is **proved by composition** (the rank-`r` mirror of
the rank-`0` per-step glue): the remainder-refinement child
`exists_iteratedCovGrad_remainderRS_gradedCurvJet_refine` supplies the order-advancing reclassification
of the differentiated remainder, and the sorry-free graded-jet closure lemmas `IsGradedCurvJetRS_covGrad`
(advancing the two genuine jets by one order, re-windowing `C → fun k => C (k + 1)`),
`IsGradedCurvJetRS.add` (merging the reclassified piece into the differentiated-Riemann jet) and
`IsGradedCurvJetRS.mono_const` (promoting to a common per-order family) assemble the order-`(m + 1)` triple
split. The section identity is `iteratedCovGrad_succ` + `covGrad_add` + the refinement split. Consumers
transitively depend on `sorryAx` through the remainder-refinement child.

**Strictly weaker than the headline (no hypothesis-packaging).** It consumes the order-`m` graded
split as a hypothesis and produces only the order-`(m + 1)` graded split, so it is not the conclusion
itself. **Non-vacuity.** At `m = 0`, gradient order `k = 0`, taking `Gcurv = GcurvDeriv = 0` makes the
order-`0` hypothesis the false statement `rfns(Curv S) ≤ 0`, which already fails on a non-flat
manifold; the genuine fields must carry the actual curvature contractions, and one further gradient
genuinely advances their order. -/
theorem iteratedCovGrad_pointwiseTensorCurvRS_gradedCurvJet_field_step
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) (C : ℕ → ℝ) (_hC : ∀ k, 0 ≤ C k)
    (hm : ∀ S : SmoothCcTensor g r s,
      ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g r (s + 1 + m),
        iteratedCovGrad g r (s + 1) m (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
            Gcurv + GcurvDeriv + Grem ∧
        IsGradedCurvJetRS (I := I) (M := M) g S C 1 (m + 1) Gcurv ∧
        IsGradedCurvJetRS (I := I) (M := M) g S C 0 (m + 1) GcurvDeriv ∧
        IsGradedCurvJetRS (I := I) (M := M) g S C (m + 2) 1 Grem) :
    ∃ C' : ℕ → ℝ, (∀ k, 0 ≤ C' k) ∧
      ∀ S : SmoothCcTensor g r s,
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g r (s + 1 + (m + 1)),
          iteratedCovGrad g r (s + 1) (m + 1) (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
              Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S C' 1 (m + 1 + 1) Gcurv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S C' 0 (m + 1 + 1) GcurvDeriv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S C' (m + 1 + 2) 1 Grem := by
  classical
  obtain ⟨Cref, hCref_nn, href⟩ :=
    exists_iteratedCovGrad_remainderRS_gradedCurvJet_refine (I := I) (M := M) g r s m C _hC
  refine ⟨fun k => max (max (C (k + 1)) (Cref k))
      (Real.sqrt (2 * ((C (k + 1)) ^ 2 + (Cref k) ^ 2))), fun k => ?_, fun S => ?_⟩
  · exact le_trans (_hC (k + 1)) (le_trans (le_max_left _ _) (le_max_left _ _))
  · obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem⟩ := hm S
    obtain ⟨Greclass, Grem', hrefeq, hreclass, hrem'⟩ := href S Grem hrem
    have hstep_eq :
        iteratedCovGrad g r (s + 1) (m + 1) (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
          (covGrad (I := I) (M := M) g r (s + 1 + m) Gcurv + Greclass) +
            covGrad (I := I) (M := M) g r (s + 1 + m) GcurvDeriv + Grem' := by
      rw [iteratedCovGrad_succ, hsplit, covGrad_add, covGrad_add, hrefeq]
      abel
    refine ⟨covGrad (I := I) (M := M) g r (s + 1 + m) Gcurv + Greclass,
      covGrad (I := I) (M := M) g r (s + 1 + m) GcurvDeriv, Grem', hstep_eq, ?_, ?_, ?_⟩
    · have hadvCurv : IsGradedCurvJetRS (I := I) (M := M) g S (fun k => C (k + 1)) 1 ((m + 1) + 1)
          (covGrad (I := I) (M := M) g r (s + 1 + m) Gcurv) :=
        IsGradedCurvJetRS_covGrad (I := I) (M := M) g S hcurv
      have hmerge := hadvCurv.add (I := I) (M := M) g S hreclass
      exact hmerge.mono_const (I := I) (M := M) g S (fun k => Real.sqrt_nonneg _)
        (fun k => le_max_right _ _)
    · have hadvDeriv : IsGradedCurvJetRS (I := I) (M := M) g S (fun k => C (k + 1)) 0 ((m + 1) + 1)
          (covGrad (I := I) (M := M) g r (s + 1 + m) GcurvDeriv) :=
        IsGradedCurvJetRS_covGrad (I := I) (M := M) g S hcurvDeriv
      exact hadvDeriv.mono_const (I := I) (M := M) g S (fun k => _hC (k + 1))
        (fun k => le_trans (le_max_left _ _) (le_max_left _ _))
    · exact hrem'.mono_const (I := I) (M := M) g S hCref_nn
        (fun k => le_trans (le_max_right _ _) (le_max_left _ _))

/-- **The deepest order-`m` curvature primitive at rank `r`: the order-`m` order-separated section-field
decomposition of the iterated commutator defect.** The contravariant-rank-`r` lift of
`exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field` (`OrderSeparatedCurvatureJet`). For a
closed smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
`Cper : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, gradient order `m`, smooth
compactly-supported `(r, s)`-tensor `S`, and *every point* `x`, the fibre value of the `m`-fold
iterated covariant gradient of the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s
S` splits as `∇^m(Curv S)(x) = Gcurv + GcurvDeriv + Grem`, with the differentiated-Riemann jet `Gcurv`
fibre-bounded by `∑_{i < m + 1} rfns(∇^{i + 1}S)` (orders `1 … m + 1`), the iterated differentiated-
curvature jet `GcurvDeriv` by `∑_{i < m + 1} rfns(∇^i S)` (orders `0 … m`), and the moving-frame
remainder `Grem` by `rfns(∇^{m + 2}S)` (the single top order), each by `(Cper s m)²`.

This is **proved** by induction on `m`, carrying the re-differentiable **graded** curvature-jet
invariant `IsGradedCurvJetRS` (each genuine field controlled together with the full family of its own
iterated gradients): the base case `m = 0` is the posited explicit graded seed
`pointwiseTensorCurvRS_gradedCurvJet_field_base`; the inductive step `m → m + 1` is the posited per-step
primitive `iteratedCovGrad_pointwiseTensorCurvRS_gradedCurvJet_field_step`. The global constant `Cper`
is assembled from the per-`m` constants by choice. The final per-point fibre split is read off the
graded field split at gradient order `k = 0` and point `x`. The verbatim mirror of the rank-`0`
headline glue. -/
theorem exists_iteratedCovGrad_pointwiseTensorCurvRS_orderSeparated_field
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cper : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cper s m) ∧
      ∀ (s m : ℕ) (S : SmoothCcTensor g r s) (x : M),
        ∃ Gcurv GcurvDeriv Grem : TensorRSSpace r (s + 1 + m) I x,
          (iteratedCovGrad g r (s + 1) m
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S)).toSection x =
              Gcurv + GcurvDeriv + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Gcurv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 1)) x
                ((iteratedCovGrad g r s (i + 1) S).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x GcurvDeriv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad g r s i S).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Grem ≤
            Cper s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 2)) x
                ((iteratedCovGrad g r s (m + 2) S).toSection x) := by
  classical
  have hkey : ∀ m : ℕ, ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g r (s + 1 + m),
          iteratedCovGrad g r (s + 1) m (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
              Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 (m + 1) Gcurv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 (m + 1) GcurvDeriv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) (m + 2) 1 Grem := by
    intro m
    induction m with
    | zero =>
        obtain ⟨c, hc_nn, hbase⟩ :=
          pointwiseTensorCurvRS_gradedCurvJet_field_base (I := I) (M := M) g r
        refine ⟨c, hc_nn, fun s S => ?_⟩
        obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem⟩ := hbase s S
        refine ⟨Gcurv, GcurvDeriv, Grem, ?_, hcurv, hcurvDeriv, hrem⟩
        rw [iteratedCovGrad_zero]; exact hsplit
    | succ m ih =>
        obtain ⟨c, hc_nn, hsplit⟩ := ih
        have hstep : ∀ s : ℕ, ∃ C' : ℕ → ℝ, (∀ k, 0 ≤ C' k) ∧
            ∀ S : SmoothCcTensor g r s,
              ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g r (s + 1 + (m + 1)),
                iteratedCovGrad g r (s + 1) (m + 1)
                    (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
                    Gcurv + GcurvDeriv + Grem ∧
                IsGradedCurvJetRS (I := I) (M := M) g S C' 1 (m + 1 + 1) Gcurv ∧
                IsGradedCurvJetRS (I := I) (M := M) g S C' 0 (m + 1 + 1) GcurvDeriv ∧
                IsGradedCurvJetRS (I := I) (M := M) g S C' (m + 1 + 2) 1 Grem := by
          intro s
          exact iteratedCovGrad_pointwiseTensorCurvRS_gradedCurvJet_field_step (I := I) (M := M)
            g r s m (c s) (hc_nn s) (hsplit s)
        refine ⟨fun s => (hstep s).choose, fun s => (hstep s).choose_spec.1, fun s S => ?_⟩
        exact (hstep s).choose_spec.2 S
  refine ⟨fun s m => (hkey m).choose s 0, fun s m => (hkey m).choose_spec.1 s 0, fun s m S x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, heq, hcurv, hcurvDeriv, hrem⟩ :=
    (hkey m).choose_spec.2 s S
  have hcurv0 := hcurv 0 x
  have hcurvDeriv0 := hcurvDeriv 0 x
  have hrem0 := hrem 0 x
  rw [iteratedCovGrad_zero] at hcurv0 hcurvDeriv0 hrem0
  simp only [Nat.add_zero] at hcurv0 hcurvDeriv0 hrem0
  refine ⟨Gcurv.toSection x, GcurvDeriv.toSection x, Grem.toSection x, ?_, ?_, ?_, ?_⟩
  · rw [heq, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  · exact hcurv0
  · simpa only [Nat.add_zero] using hcurvDeriv0
  · rw [Finset.sum_range_one, zero_add] at hrem0
    exact hrem0

/-- **The order-`m` genuine + remainder fibre decomposition of the iterated commutator defect at rank
`r`.** The contravariant-rank-`r` lift of
`exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`PointwiseTensorCurvL2Bound`). For a closed smooth Riemannian manifold `(M, g)` there is a
*valence/order-dependent* nonnegative constant `Cgr : ℕ → ℕ → ℝ` such that, at every covariant rank
`s`, every gradient order `m`, for every smooth compactly-supported `(r, s)`-tensor `S`, and at *every
point* `x`, the fibre value of the `m`-fold iterated covariant gradient of the order-`2` commutator
defect `Curv S := pointwiseTensorCurvRS g r s S` splits as `(∇^m(Curv S))(x) = Ggen + Grem`, with the
genuine curvature-jet part `Ggen` fibre-bounded by `(Cgr s m)²` times `∑_{i ≤ m + 1} rfns(∇^i S)(x)`
and the moving-frame remainder `Grem` by `(Cgr s m)²` times `rfns(∇^{m + 2} S)(x)`.

This is **proved** from the order-`m` order-separated three-field split
`exists_iteratedCovGrad_pointwiseTensorCurvRS_orderSeparated_field` by merging the two genuine jets
`Ggen := Gcurv + GcurvDeriv` through the two-term fibre subadditivity `riemannianFiberNormSq_add_le`,
dominating both order-separated sub-sums (`∑_{i < m + 1} rfns(∇^{i + 1}S)` and `∑_{i < m + 1}
rfns(∇^i S)`) by the full low sum `∑_{i < m + 2} rfns(∇^i S)` via
`Finset.sum_le_sum_of_subset_of_nonneg` and the index shift `Finset.sum_range_succ'`, exactly as the
rank-`0` two-term split is proved from the rank-`0` three-field split. -/
theorem exists_iteratedCovGrad_pointwiseTensorCurvRS_genuineRemainder_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cgr : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cgr s m) ∧
      ∀ (s m : ℕ) (S : SmoothCcTensor g r s) (x : M),
        ∃ Ggen Grem : TensorRSSpace r (s + 1 + m) I x,
          (iteratedCovGrad g r (s + 1) m
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S)).toSection x = Ggen + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Ggen ≤
            Cgr s m ^ 2 * ∑ i ∈ Finset.range (m + 2),
              riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad g r s i S).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Grem ≤
            Cgr s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 2)) x
                ((iteratedCovGrad g r s (m + 2) S).toSection x) := by
  classical
  obtain ⟨Cper, hCper_nn, hsplit⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurvRS_orderSeparated_field (I := I) (M := M) g r
  refine ⟨fun s m => 2 * Cper s m, fun s m => ?_, fun s m S x => ?_⟩
  · exact mul_nonneg (by norm_num) (hCper_nn s m)
  · obtain ⟨Gcurv, GcurvDeriv, Grem, heq, hcurv, hcurvDeriv, hrem⟩ := hsplit s m S x
    set F : ℕ → ℝ := fun i =>
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad g r s i S).toSection x) with hF
    have hF_nn : ∀ i, 0 ≤ F i := fun i =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + i) x _
    set LowSum : ℝ := ∑ i ∈ Finset.range (m + 2), F i with hLowSum
    have hLowSum_nn : 0 ≤ LowSum := Finset.sum_nonneg (fun i _ => hF_nn i)
    have hsub : Finset.range (m + 1) ⊆ Finset.range (m + 2) :=
      Finset.range_subset_range.mpr (by omega)
    have hDeriv_dom : (∑ i ∈ Finset.range (m + 1), F i) ≤ LowSum := by
      rw [hLowSum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF_nn i)
    have hCurv_dom : (∑ i ∈ Finset.range (m + 1), F (i + 1)) ≤ LowSum := by
      have hsplit_low : LowSum = (∑ i ∈ Finset.range (m + 1), F (i + 1)) + F 0 := by
        rw [hLowSum, Finset.sum_range_succ' F (m + 1)]
      rw [hsplit_low]
      linarith [hF_nn 0]
    have hcurv' : riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Gcurv ≤
        Cper s m ^ 2 * (∑ i ∈ Finset.range (m + 1), F (i + 1)) := hcurv
    have hcurvDeriv' : riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x GcurvDeriv ≤
        Cper s m ^ 2 * (∑ i ∈ Finset.range (m + 1), F i) := hcurvDeriv
    have hCper_sq_nn : 0 ≤ Cper s m ^ 2 := sq_nonneg _
    have hcurv_low : riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Gcurv ≤
        Cper s m ^ 2 * LowSum :=
      le_trans hcurv' (mul_le_mul_of_nonneg_left hCurv_dom hCper_sq_nn)
    have hcurvDeriv_low : riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x GcurvDeriv ≤
        Cper s m ^ 2 * LowSum :=
      le_trans hcurvDeriv' (mul_le_mul_of_nonneg_left hDeriv_dom hCper_sq_nn)
    refine ⟨Gcurv + GcurvDeriv, Grem, by rw [heq], ?_, ?_⟩
    · have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1 + m) x Gcurv GcurvDeriv
      have hsq : (2 * Cper s m) ^ 2 = 4 * Cper s m ^ 2 := by ring
      rw [hsq]
      calc riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x (Gcurv + GcurvDeriv)
          ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x Gcurv +
              2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + m) x GcurvDeriv := hadd
        _ ≤ 2 * (Cper s m ^ 2 * LowSum) + 2 * (Cper s m ^ 2 * LowSum) := by
              have e1 := mul_le_mul_of_nonneg_left hcurv_low (by norm_num : (0 : ℝ) ≤ 2)
              have e2 := mul_le_mul_of_nonneg_left hcurvDeriv_low (by norm_num : (0 : ℝ) ≤ 2)
              linarith
        _ = 4 * Cper s m ^ 2 * LowSum := by ring
    · have hTop_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 2)) x
          ((iteratedCovGrad g r s (m + 2) S).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + (m + 2)) x _
      have hsq : (2 * Cper s m) ^ 2 = 4 * Cper s m ^ 2 := by ring
      rw [hsq]
      nlinarith [hrem, hTop_nn, hCper_sq_nn]

end Connection
end Integral
end DifferentialGeometry

end
