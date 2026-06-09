import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairingRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffCurvatureTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLocality

/-!
# The rank-`r` graded curvature-jet predicate and the genuine differentiated-curvature / moving-frame
remainder jets of the order-`2` commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-rank-`r` home of the re-differentiable **graded curvature-jet** invariant and the two
genuine curvature jets of the rank-generic order-`2` commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurvRS g r s S`, a `(r, s + 1)`-tensor field; `∇S = covGrad g r s S`). These are the
contravariant-rank-`r` analogues of the rank-`0` graded-jet predicate `IsGradedCurvJet` and the rank-`0`
genuine curvature jets of `OrderSeparatedCurvatureJet` / `DiffCurvatureGenuineTower`.

## The re-differentiable graded curvature-jet invariant at rank `r`

A genuine curvature jet of `S` cannot be controlled by a single-order fibre bound: differentiating it is
uncontrolled. The graded invariant `IsGradedCurvJetRS g S c p w G` — the verbatim rank-`r` mirror of
`IsGradedCurvJet` — controls a field `G` together with the full family of its own iterated gradients:
for *every* further gradient order `k` and every `x`,

```
rfns(∇^k G)(x) ≤ (c k)² · ∑_{i < w + k} rfns(∇^{i + p} S)(x).
```

The predicate is closed under one covariant gradient (`IsGradedCurvJetRS_covGrad`, shifting `k → k + 1`,
`w → w + 1`), under addition of two jets of the same shape (`IsGradedCurvJetRS.add`), and is monotone in
its constant family (`IsGradedCurvJetRS.mono_const`). These closure lemmas are the structural API the
downstream full-sum grid (`CurvatureJetGridRS`) and the order-`2` commutator full-sum jet
(`CommutatorDefectFullSumJet`) consume.

## The two genuine curvature jets

* `exists_diffCurvSectionRS_gradedCurvJet` — the **differentiated-curvature `(∇R) S` jet** of the
  concrete gauge-glued carrier `diffCurvSectionRS g r s S` (`RankRDiffCurvatureTower`): a graded jet of
  lowest order `0` and width `1`, *proved* off the rank-`r` `(∇R)·` carrier-tower grid
  `exists_diffCurvSectionRS_iteratedCovGrad_grid_bound` (consumers transitively depend on the carrier
  tower's single posited node `exists_diffCurvGenuineTowerRS`).

* `exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_fullSum_gradedCurvJet` — the **genuine
  iterated-Ricci moving-frame remainder jet** in the **sound full-sum shape `(0, 3)`**: after peeling
  off both the concrete pure-Riemann section `GcurvSectionRS g r s S` (the `R(∇S)` contraction) and the
  concrete differentiated-curvature carrier `diffCurvSectionRS g r s S`, the surviving moving-frame
  remainder `Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S` is a graded curvature jet of
  lowest order `0` and width `3` (bounded by the whole window `∇^{≤ k + 2}S`, **not** the false
  single-top-order shape `(2, 1)`: the per-direction moving-frame bracket trace is non-tensorial in the
  direction, so only the intrinsic full-sum window is order-controlled). This is the genuinely
  irreducible iterated-Ricci content at rank `r` — the contravariant-rank-`r` analogue of the rank-`0`
  `pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet` — *derived* here over the genuine
  three-field full-sum base split `exists_pointwiseTensorCurvRS_genuineThreeField_fullSum_m0_baseSplit`
  (the rank-`r` iterated-Ricci deep well, posited once here as one precise true core) by relaxing the two
  sorry-free concrete sections to the common shape and subtracting. Consumers transitively depend on
  `sorryAx` through the base split.

The genuine `(0, 3)` remainder jet, together with the pure-Riemann grid `GcurvSectionRS_gradedCurvJet`
and the `(0, 1)` differentiated-curvature jet above, is exactly what the rank-`r` full-sum seed
`exists_pointwiseTensorCurvRS_diffCurvAndRemainder_fullSum_gradedCurvJet_seed` (`CurvatureJetGridRS`)
assembles into the witnessed three-field full-sum split, the value the rank-`r` order-`2` commutator
full-sum jet `pointwiseTensorCurvRS_fullSum_gradedCurvJet` (`CommutatorDefectFullSumJet`) and the
downstream rank-`r` aggregate fibre bound
`exists_iteratedCovGrad_pointwiseTensorCurvRS_pointwise_fiberNormSq_bound`
(`Geometry/Flow/RicciFlow/ShortTime/LocalWeylReproducingKernel.lean`) consume.

## Non-vacuity

With `c s 0 = 0` the genuine `(0, 3)` remainder jet at gradient order `k = 0` forces
`rfns(Curv S − GcurvSectionRS − diffCurvSectionRS)(x) = 0`, i.e.
`Curv S = GcurvSectionRS + diffCurvSectionRS`; *false* on a non-flat manifold (the moving-frame bracket
discrepancy is genuinely non-zero). The constant family is genuinely positive.

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

/-- **Order-window domination for an order-shifted truncated sum (file-local).** For a nonnegative
order-indexed family `f`, the `(p, w)`-windowed sum `∑_{i < w + k} f (i + p)` is dominated by the
wider `(p', w')`-windowed sum `∑_{i < w' + k} f (i + p')` whenever `p' ≤ p` and `p + w ≤ p' + w'`:
both reindex (`Finset.sum_Ico_eq_sum_range`) onto `Ico`-sums over the order set, and the former
order-window is a subset of the latter with all summands `≥ 0`. (A file-local copy of the
`orderWindow_sum_le` bookkeeping homed in the downstream `CommutatorDefectFullSumJet`, which this file
may not import; the opaque `f` keeps the reindex free of the dependent rank-index motive.) -/
private theorem orderWindow_sum_le_local (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) {p w p' w' k : ℕ}
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

/-- **Order-range monotonicity of the rank-`r` graded curvature-jet predicate (file-local).** A
graded curvature jet of `S` of lowest order `p` / base width `w` is also a jet of any wider shape
`(p', w')` with `p' ≤ p` and `p + w ≤ p' + w'`, since the `(p, w)` order-window is a subset of the
`(p', w')` window with nonnegative summands; the constant family is unchanged. (A file-local copy of
the public `IsGradedCurvJetRS.le_shape` homed in the downstream `CommutatorDefectFullSumJet`, which
this file may not import; kept under a distinct private name so it does not collide.) -/
private theorem IsGradedCurvJetRS_le_shape_local (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c : ℕ → ℝ} {p w p' w' t : ℕ} {G : SmoothCcTensor g r t}
    (hp : p' ≤ p) (hpw : p + w ≤ p' + w')
    (hG : IsGradedCurvJetRS (I := I) (M := M) g S c p w G) :
    IsGradedCurvJetRS (I := I) (M := M) g S c p' w' G := by
  intro k x
  refine (hG k x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (c k))
  exact orderWindow_sum_le_local
    (fun q => riemannianFiberNormSq (I := I) (M := M) g r (s + q) x
      ((iteratedCovGrad g r s q S).toSection x))
    (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + q) x _) hp hpw

/-- **The rank-`r` graded curvature-jet predicate is closed under subtraction of two jets of the same
shape (file-local).** The difference analogue of `IsGradedCurvJetRS.add`: if `G₁`, `G₂` are graded
curvature jets of `S` of the *same* lowest order `p` and base width `w`, then their difference
`G₁ − G₂` is a graded curvature jet of the same shape with constant family
`k ↦ √(2·((c₁ k)² + (c₂ k)²))`, since `∇^k(G₁ − G₂) = ∇^k G₁ − ∇^k G₂` (`iteratedCovGrad_sub`,
`SmoothCcTensor.toSection_sub`) and the fibre norm is `≤ 2·rfns(∇^k G₁) + 2·rfns(∇^k G₂)`
(`riemannianFiberNormSq_sub_le`). (A file-local copy of the public `IsGradedCurvJet.sub` /
`IsGradedCurvJetRS_neg` machinery homed downstream, kept under a distinct private name.) -/
private theorem IsGradedCurvJetRS_sub_local (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {c₁ c₂ : ℕ → ℝ} {p w t : ℕ}
    {G₁ G₂ : SmoothCcTensor g r t}
    (hG₁ : IsGradedCurvJetRS (I := I) (M := M) g S c₁ p w G₁)
    (hG₂ : IsGradedCurvJetRS (I := I) (M := M) g S c₂ p w G₂) :
    IsGradedCurvJetRS (I := I) (M := M) g S
      (fun k => Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2))) p w (G₁ - G₂) := by
  intro k x
  have hsplit : (iteratedCovGrad g r t k (G₁ - G₂)).toSection x =
      (iteratedCovGrad g r t k G₁).toSection x - (iteratedCovGrad g r t k G₂).toSection x := by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsplit]
  have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (t + k) x
    ((iteratedCovGrad g r t k G₁).toSection x) ((iteratedCovGrad g r t k G₂).toSection x)
  have hcsq : Real.sqrt (2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2)) ^ 2 = 2 * ((c₁ k) ^ 2 + (c₂ k) ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  rw [hcsq]
  calc riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
          ((iteratedCovGrad g r t k G₁).toSection x - (iteratedCovGrad g r t k G₂).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
            ((iteratedCovGrad g r t k G₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g r (t + k) x
            ((iteratedCovGrad g r t k G₂).toSection x) := hsub
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

/-- **Posited rank-`r` `m = 0` genuine three-field full-sum graded base split of the order-`2`
commutator defect (the iterated-Ricci deep well at general rank, sound full-sum remainder).** For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
*valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` splits into three smooth compactly-supported `(r, s + 1)`-tensor
fields carried **existentially**
```
Curv S = Gcurv + Gdiff + Grem
```
each a **graded** curvature jet (`IsGradedCurvJetRS`) of `S` at its genuine shape: the pure-Riemann
contraction `R(∇S)` jet `Gcurv` of lowest order `1` and width `1`, the differentiated-curvature `(∇R) S`
jet `Gdiff` of lowest order `0` and width `1`, and the moving-frame remainder `Grem` of the **sound
full-sum shape** lowest order `0` and width `3` (bounded by the whole window `∇^{≤ k + 2} S`, NOT the
false single-top-order shape `(2, 1)`).

This is the contravariant-rank-`r` analogue of the audited rank-`0` `m = 0` graded base seed
`pointwiseTensorCurv_gradedCurvJet_field_base` (`OrderSeparatedCurvatureJet`), upgraded to the sound
full-sum remainder shape `(0, 3)` (the rank-`0` seed carries the false single-top-order `(2, 1)`
remainder, which the full-sum route abandoned). It is the genuinely-irreducible iterated-Ricci content of
the order-`2` commutator defect at general rank, distinct from — and strictly more primitive than — the
target subtracted remainder jet below: this carries the **whole defect's** existential three-field split
at the genuine shapes, while the target subtracts the two *concrete* canonical sections
`GcurvSectionRS g r s S`, `diffCurvSectionRS g r s S` off the defect and asserts only the surviving
`(0, 3)` remainder.

**Why this is TRUE — and why the full-sum, not order-separated, shape.** Pointwise `Curv S` is the
genuine third-order Bochner–Weitzenböck field: by the metric-trace reading of the rough Laplacian
`Δ_∇ = tr_g ∘ ∇²` (`rawTensorConnLap_eq_metricTrace2`, frame-free, rank-generic) the defect
`Δ_∇(∇S) − ∇(Δ_∇ S)` is the metric trace of the antisymmetrised second covariant derivative of `∇S`,
which the third-order tensor Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` exhibits
as a `riemannOp`-contraction of `(∇S, S)`, lifted to the `(r, s)`-bundle through the slot-wise curvature
formula `riemannSec_tensorCov_apply_eval` (`TensorSlotwiseCurvatureRS`). Splitting that contraction into
its pure-Riemann `R(∇S)` part (`Gcurv`, lowest order `1`), its differentiated-curvature `(∇R) S` part
(`Gdiff`, lowest order `0`), and the surviving moving-frame / frame-bracket discrepancy (`Grem`,
genuinely `∇²S`-order, the full-sum window `0 … k + 2` after the iterated-Ricci cancellation of the top
`∇^{k + 3} S` terms), with every curvature coefficient absorbed uniformly over the compact manifold
(`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The contracted-order window is the
**full-sum** `0 … k + 2` (shape `(0, 3)`): the per-direction moving-frame bracket trace is non-tensorial
in the direction (false term-by-term through `smoothExtensionTangent`, chart-selection-unbounded on
`S²`), so only the intrinsic full-sum window is order-controlled, and the three fields are carried
*existentially* (never per-direction `smoothExtensionTangent`-curried). The rank-`r` iterated-Ricci grid
is absent sorry-free below this file, so this is posited here as the single precise true child.
Consumers transitively depend on `sorryAx`.

**Strictly more primitive than the target (genuine decomposition, no hypothesis-packaging).** This posits
the *witnessed* three-field split of the whole defect together with each field's genuine (tighter) graded
shape; the target subtracted-remainder jet is *derived* from it by relaxing each genuine jet to the
common shape `(0, 3)` (`IsGradedCurvJetRS_le_shape_local`) and subtracting the two sorry-free concrete
sections `GcurvSectionRS g r s S` (graded by `GcurvSectionRS_gradedCurvJet`) and `diffCurvSectionRS g r s
S` (graded by `exists_diffCurvSectionRS_gradedCurvJet`) through `IsGradedCurvJetRS_sub_local`. The
existential three-field split carries strictly more information than the bare subtracted-remainder jet, so
the target cannot reconstruct it and this node is not its own conclusion.

**Non-vacuity.** With `c s 0 = 0` the three bounds force `rfns(Gcurv)(x) = rfns(Gdiff)(x) =
rfns(Grem)(x) = 0` at `k = 0`, hence the section equation gives `Curv S = 0`; *false* on a non-flat
manifold, where the order-`2` commutator defect carries the genuine curvature contraction of `S`
(`R ≠ 0`, `∇S ≠ 0`). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_genuineThreeField_fullSum_m0_baseSplit
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcurv Gdiff Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S = Gcurv + Gdiff + Grem ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 1 1 Gcurv ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 1 Gdiff ∧
          IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3 Grem :=
  sorry

/-- **Rank-`r` moving-frame remainder full-sum graded jet after the differentiated-curvature peel (the
genuine iterated-Ricci remainder core, sound full-sum shape `(0, 3)`), derived from the genuine
three-field base split.** The contravariant-rank-`r` analogue of the rank-`0` moving-frame remainder
full-sum content `pointwiseTensorCurv_movingFrameRemainder_fullSum_gradedCurvJet`
(`CommutatorDefectFullSumJet`). For a closed smooth Riemannian manifold `(M, g)`, fixed contravariant
rank `r`, there is a *valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at
every covariant rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, peeling off both
the concrete pure-Riemann section `GcurvSectionRS g r s S` (the `R(∇S)` contraction) and the *concrete*
gauge-glued differentiated-curvature carrier `diffCurvSectionRS g r s S` (the `(∇R) S` field, the
canonical carrier pinned by `exists_diffCurvSectionRS_gradedCurvJet`), the surviving moving-frame
remainder `pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S` is a
**graded** curvature jet of the **sound full-sum shape** lowest contracted order `0` and base width `3`:
```
rfns(∇^k (Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S))(x)
  ≤ (c s k)² · ∑_{i < 3 + k} rfns(∇^{i} S)(x).
```

**Proof (over the genuine three-field base split).** This is *derived* from the witnessed genuine
three-field full-sum base split `exists_pointwiseTensorCurvRS_genuineThreeField_fullSum_m0_baseSplit`
(the iterated-Ricci deep well): `Curv S = Gcurv + Gdiff + Grem` with `Gcurv` a `(1, 1)` graded jet,
`Gdiff` a `(0, 1)` graded jet, and `Grem` the sound full-sum `(0, 3)` graded jet. Substituting the split,
the target remainder regroups as
`Curv S − GcurvSectionRS − diffCurvSectionRS = (Gcurv − GcurvSectionRS) + ((Gdiff − diffCurvSectionRS) +
Grem)` (`abel`), and each leg is a `(0, 3)` graded jet: `Gcurv` and the *sorry-free* concrete
`GcurvSectionRS g r s S` (`GcurvSectionRS_gradedCurvJet`) are both `(1, 1)` jets relaxed to `(0, 3)`
(`IsGradedCurvJetRS_le_shape_local`), so their difference is `(0, 3)`
(`IsGradedCurvJetRS_sub_local`); likewise `Gdiff` and the concrete `diffCurvSectionRS g r s S`
(`exists_diffCurvSectionRS_gradedCurvJet`) are `(0, 1)` jets relaxed to `(0, 3)`; and `Grem` is already
`(0, 3)`. Summing the three legs (`IsGradedCurvJetRS.add`, twice) gives the remainder as a single
`(0, 3)` graded jet. The genuinely-irreducible iterated-Ricci content lives entirely in the base split;
this node is mere graded-jet bookkeeping on top of it. Consumers transitively depend on `sorryAx` through
the base split.

**Why the base split is TRUE — and why it is the FULL-SUM, not the order-separated `(2, 1)`, shape.**
Pointwise, after removing the two genuine curvature contractions — the pure-Riemann `R(∇S)` and the
differentiated-curvature `(∇R) S` — the surviving remainder is the frame-bracket discrepancy, genuinely
`∇²S`-order; each of its own iterated gradients is, after the iterated-Ricci cancellation of the top
`∇^{k + 3}S` terms (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), a curvature contraction of
`∇^{≤ k + 2}S` (contracted-order window `0 … k + 2`, shape `(0, 3)`), with every curvature coefficient
absorbed uniformly over the compact manifold. The contracted-order window is the **full-sum** `0 … k + 2`,
*not* the single top order `k + 2` (the order-separated `(2, 1)` shape): the per-direction moving-frame
bracket trace is non-tensorial in the direction (false term-by-term through `smoothExtensionTangent`,
chart-selection-unbounded on `S²`), so only the intrinsic full-sum window is order-controlled.

**Signature soundness — why both carriers are pinned, not free inputs.** The carriers are the concrete
`GcurvSectionRS g r s S` and `diffCurvSectionRS g r s S`, *not* universally-quantified inputs. The
remainder is the literal subtraction `Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S`, so the
section split `Curv S = GcurvSectionRS + diffCurvSectionRS + remainder` is `abel`. A version taking
arbitrary carriers as input (with the constant family `c` chosen *before* them) is FALSE: feeding the
admissible witness `diffCurvSectionRS = 0` would force the remainder to absorb the genuine `(∇R) S`
content, and the full-sum `(0, 3)` bound would then read `rfns(Curv − GcurvSectionRS)(x) ≤ (c s 0)² ·
(rfns(S) + rfns(∇S) + rfns(∇²S))(x)` — but at a point where `S(x) ≠ 0`, `∇S(x) = 0`, `∇²S(x) = 0`, the
pure-Riemann `GcurvSectionRS` (reading `∇S(x) = 0`) vanishes while the genuine differentiated-curvature
`(∇R) S` content does not, so the bound is not vacuous and constrains the carriers. Pinning both carriers
to the canonical `GcurvSectionRS g r s S` and `diffCurvSectionRS g r s S` matches the rank-`0` analogue
and the sole consumer (the rank-`r` full-sum seed of `CurvatureJetGridRS`, which always feeds these two
concrete carriers).

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` forces
`rfns(Curv S − GcurvSectionRS − diffCurvSectionRS)(x) = 0`, i.e.
`Curv S = GcurvSectionRS + diffCurvSectionRS`; *false* on a non-flat manifold (the moving-frame bracket
discrepancy is genuinely non-zero). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_fullSum_gradedCurvJet
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        IsGradedCurvJetRS (I := I) (M := M) g S (c s) 0 3
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
            GcurvSectionRS (I := I) (M := M) g r s S -
            diffCurvSectionRS (I := I) (M := M) g r s S) := by
  classical
  -- The genuine three-field full-sum base split of the whole defect (the iterated-Ricci deep well),
  -- and the two sorry-free graded jets of the concrete sections subtracted in the target field.
  obtain ⟨cBase, hcBase_nn, hbase⟩ :=
    exists_pointwiseTensorCurvRS_genuineThreeField_fullSum_m0_baseSplit (I := I) (M := M) g r
  -- The pure-Riemann section's `(1, 1)` graded jet is sorry-free: it IS the rank-`r` pure-Riemann grid
  -- (`exists_GcurvSectionRS_iteratedCovGrad_grid_bound`) unfolded as `IsGradedCurvJetRS g S c 1 1`.
  obtain ⟨cA, hcA_nn, hAgrid⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  have hAjet : ∀ (s : ℕ) (S : SmoothCcTensor g r s),
      IsGradedCurvJetRS (I := I) (M := M) g S (cA s) 1 1
        (GcurvSectionRS (I := I) (M := M) g r s S) := fun s S k x => hAgrid s S k x
  obtain ⟨cB, hcB_nn, hBjet⟩ := exists_diffCurvSectionRS_gradedCurvJet (I := I) (M := M) g r
  -- A single per-order constant family dominating all three input families; the subtraction/addition
  -- closures then square-combine the common constant left-associatively.
  set C : ℕ → ℕ → ℝ := fun s k => max (max (cBase s k) (cA s k)) (cB s k) with hC_def
  refine ⟨fun s k =>
      Real.sqrt (2 * ((Real.sqrt (2 * ((C s k) ^ 2 + (C s k) ^ 2))) ^ 2
        + Real.sqrt (2 * ((Real.sqrt (2 * ((C s k) ^ 2 + (C s k) ^ 2))) ^ 2 + (C s k) ^ 2)) ^ 2)),
    fun s k => Real.sqrt_nonneg _, fun s S => ?_⟩
  obtain ⟨Gcurv, Gdiff, Grem, hsplit, hGcurv, hGdiff, hGrem⟩ := hbase s S
  -- Promote each genuine jet to the common per-order family `C s`, then relax to the full-sum shape.
  have hGcurv_C : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 1 1 Gcurv :=
    hGcurv.mono_const (I := I) (M := M) g S (hcBase_nn s)
      (fun k => le_trans (le_max_left _ _) (le_max_left _ _))
  have hGdiff_C : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 1 Gdiff :=
    hGdiff.mono_const (I := I) (M := M) g S (hcBase_nn s)
      (fun k => le_trans (le_max_left _ _) (le_max_left _ _))
  have hGrem_C : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 3 Grem :=
    hGrem.mono_const (I := I) (M := M) g S (hcBase_nn s)
      (fun k => le_trans (le_max_left _ _) (le_max_left _ _))
  have hA_C : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 1 1
      (GcurvSectionRS (I := I) (M := M) g r s S) :=
    (hAjet s S).mono_const (I := I) (M := M) g S (hcA_nn s)
      (fun k => le_trans (le_max_right _ _) (le_max_left _ _))
  have hB_C : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 1
      (diffCurvSectionRS (I := I) (M := M) g r s S) :=
    (hBjet s S).mono_const (I := I) (M := M) g S (hcB_nn s) (fun k => le_max_right _ _)
  -- Relax all five jets to the common full-sum shape `(0, 3)`.
  have hGcurv_03 : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 3 Gcurv :=
    IsGradedCurvJetRS_le_shape_local (I := I) (M := M) g S (by omega) (by omega) hGcurv_C
  have hGdiff_03 : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 3 Gdiff :=
    IsGradedCurvJetRS_le_shape_local (I := I) (M := M) g S (by omega) (by omega) hGdiff_C
  have hA_03 : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 3
      (GcurvSectionRS (I := I) (M := M) g r s S) :=
    IsGradedCurvJetRS_le_shape_local (I := I) (M := M) g S (by omega) (by omega) hA_C
  have hB_03 : IsGradedCurvJetRS (I := I) (M := M) g S (C s) 0 3
      (diffCurvSectionRS (I := I) (M := M) g r s S) :=
    IsGradedCurvJetRS_le_shape_local (I := I) (M := M) g S (by omega) (by omega) hB_C
  -- `Gcurv − GcurvSectionRS` and `Gdiff − diffCurvSectionRS` are `(0, 3)` graded jets.
  have hsub1 := IsGradedCurvJetRS_sub_local (I := I) (M := M) g S hGcurv_03 hA_03
  have hsub2 := IsGradedCurvJetRS_sub_local (I := I) (M := M) g S hGdiff_03 hB_03
  -- Sum the three `(0, 3)` legs: `(Gcurv − GcurvSectionRS) + ((Gdiff − diffCurvSectionRS) + Grem)`.
  have hpair := hsub2.add (I := I) (M := M) g S hGrem_C
  have htriple := hsub1.add (I := I) (M := M) g S hpair
  -- The target field equals that three-leg regrouping (substitute the split, then `abel`).
  have hfield : pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S -
        diffCurvSectionRS (I := I) (M := M) g r s S =
      (Gcurv - GcurvSectionRS (I := I) (M := M) g r s S) +
        ((Gdiff - diffCurvSectionRS (I := I) (M := M) g r s S) + Grem) := by
    rw [hsplit]; abel
  rw [hfield]
  exact htriple

end Connection
end Integral
end DifferentialGeometry

end
