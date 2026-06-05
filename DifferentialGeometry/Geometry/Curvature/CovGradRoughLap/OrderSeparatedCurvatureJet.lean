import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineBracketSectionSplit
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth

/-!
# The order-`m` order-separated moving-frame curvature-jet field decomposition

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
deepest **order-`m` order-separated section-field split** of the `m`-fold iterated covariant
gradient of the rank-generic order-`2` commutator defect

```
Curv T := Δ_∇(∇T) − ∇(Δ_∇ T)
```

(`pointwiseTensorCurv g s T`, a `(0, s + 1)`-tensor field). It is the genuine order-`m` lift of the
`m = 0` section-field split `exists_pointwiseTensorCurv_orderSeparated_field`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`): applying `∇^m` to the
order-separated field split of `Curv T` and re-Leibniz-ing the curvature contractions, the iterated
Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order
`∇^{m + 3}T` terms, leaving — at every rank `s`, gradient order `m`, smooth compactly-supported
`(0, s)`-tensor `T` and point `x` — three fields `Gcurv, GcurvDeriv, Grem` summing to
`∇^m(Curv T)(x)` with the three order-separated proportional fibre bounds: the differentiated-Riemann
jet `Gcurv` bounded by `∑_{i < m + 1} rfns(∇^{i + 1}T)` (orders `1 … m + 1`), the iterated
differentiated-curvature jet `GcurvDeriv` by `∑_{i < m + 1} rfns(∇^i T)` (orders `0 … m`), and the
moving-frame remainder `Grem` by `rfns(∇^{m + 2}T)` (the single top order).

This is the strictly-upstream curvature primitive that the assembly-ready order-`m` two-term split
`exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`) is *proved* on top of, by
merging the two genuine jets `Ggen := Gcurv + GcurvDeriv` through the two-term fibre subadditivity
`riemannianFiberNormSq_add_le`, dominating both order-separated sub-sums by the full low sum
`∑_{i < m + 2} rfns(∇^i T)` via `Finset.sum_le_sum_of_subset_of_nonneg` and the index shift
`Finset.sum_range_succ'` — exactly as the `m = 0` model
`exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` merges its two genuine pieces. The
file lives upstream of `PointwiseTensorCurvL2Bound` (it does not import it) so that file can cite this
order-`m` child without an import cycle.

## The re-differentiable graded curvature-jet invariant

The order-`m` split cannot be carried through the induction on `m` as *abstract* `∃`-fields with
*only* a fibre bound at the single order `m`: differentiating such a field is uncontrolled (a fibre
bound on `F` gives no bound on `rfns(∇F)`; the library controls iterated gradients only in `L²`). The
induction therefore carries a **re-differentiable graded invariant**: each genuine field is required
to satisfy, not only its order-`m` fibre bound, but the entire graded family of its own iterated
covariant gradients, in the same order-separated curvature-jet form. Concretely the carrier is the
predicate `IsGradedCurvJet g T c p w G`, asserting that for *every* further gradient order `k` and
every `x` the `k`-fold iterated gradient `∇^k G` is fibre-bounded by
`c² · ∑_{i < w + k} rfns(∇^{i + p}T)(x)` (lowest contracted order `p`, base width `w`). This predicate
is **closed under one covariant gradient** (`IsGradedCurvJet_covGrad`): the `k`-th gradient of `∇G`
is the `(k + 1)`-th gradient of `G`, so the bound shifts `k → k + 1` and stays in the family. This is
the exact structure the per-step consumes: applying one further `∇` to the order-`m` split and
re-Leibniz-ing keeps every genuine jet inside the graded family, advancing its order by one.

## What is proved vs. posited

The order-`m` order-separated *field*-level split is built by **induction on `m`** (the genuine glue
written in this file), carrying the re-differentiable graded invariant:

* the **base case `m = 0`** is the posited explicit graded curvature-jet seed
  `pointwiseTensorCurv_gradedCurvJet_field_base`: the `m = 0` split of `Curv T` into the genuine
  graded jets and the bracket remainder, each carrying the full graded gradient family of bounds (the
  explicit re-differentiable form of the `m = 0` field split, built from the explicit field identity
  `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` and the uniform curvature /
  differentiated-curvature sups);
* the **inductive step `m → m + 1`** is the posited genuine moving-frame curvature primitive
  `iteratedCovGrad_pointwiseTensorCurv_gradedCurvJet_field_step`: applying one further covariant
  gradient `∇` to the order-`m` graded split and re-Leibniz-ing the curvature contractions, the
  iterated Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order
  `∇^{m + 3}T` term against its swapped partner, producing the order-`(m + 1)` graded split with the
  genuine curvature-jet bounds advanced by one order (the new curvature-derivative contractions
  sup-bounded on the compact manifold by the uniform curvature / differentiated-curvature sups
  `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
  `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). Its hypothesis is the *graded*
  (re-differentiable) order-`m` split, not the abstract single-order one; its conclusion is the graded
  order-`(m + 1)` split — a strictly weaker implication than the headline (it consumes the order-`m`
  split and produces the order-`(m + 1)` split), so it is the genuinely-irreducible per-step
  Weitzenböck content and not the conclusion itself.

Both posited children carry the graded-jet predicate, so the per-step's hypothesis is genuinely
re-differentiable; the headline glue then reads the abstract three-field order-`m` split off the
graded invariant by specialising `IsGradedCurvJet` to gradient order `k = 0`. Consumers transitively
depend on `sorryAx` through these two posited primitives.

The degenerate witness is rejected: at `m = 0`, gradient order `k = 0`, the split reads
`Curv T (x) = Gcurv + GcurvDeriv + Grem` with `rfns(Gcurv)(x) ≤ c²·rfns(∇T)(x)`,
`rfns(GcurvDeriv)(x) ≤ c²·rfns(T)(x)`, `rfns(Grem)(x) ≤ c²·rfns(∇²T)(x)`, which — merged — is the
`m = 0` two-term split `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`, *false* with
`c = 0` on a non-flat manifold (the defect carries the genuine curvature contraction of `T`).

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian. The covariant
gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`; `iteratedCovGrad
g 0 s j` is its `j`-fold iterate. All fibre norms are the intrinsic `riemannianFiberNormSq`.
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

/-- **Heterogeneous rank-congruence for `covGrad`.** If two ranks agree (`h : a = b`) and the smooth
compactly-supported tensors `Y`, `Z` are heterogeneously equal, then so are `covGrad g r a Y` and
`covGrad g r b Z`. Proved by `subst` on the rank variable. (A file-local copy of the generic
`covGrad` rank-naturality, kept private; the public form lives in the downstream
`PointwiseTensorCurvL2Bound`, which this file may not import.) -/
private theorem covGrad_heq_congr_local (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g r a Y) (covGrad (I := I) (M := M) g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying
`m` covariant gradients to `covGrad g r s X` (the once-differentiated `(r, s + 1)`-tensor) is
heterogeneously equal to the `(m + 1)`-fold iterated gradient of `X`, the two living in the ranks
`(s + 1) + m` and `s + (m + 1)`, which agree as naturals. Proved by induction on `m` through
`covGrad_heq_congr_local`. (File-local copy; the public form is downstream.) -/
private theorem iteratedCovGrad_covGrad_comm_heq_local (g : SmoothRiemannianMetric I M)
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
      exact covGrad_heq_congr_local g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The intrinsic fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value
`riemannianFiberNormSq` at every point. Proved by `subst` on the rank variable. -/
private theorem riemannianFiberNormSq_toSection_heq_congr (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **The re-differentiable graded curvature-jet predicate.** For a closed smooth Riemannian
manifold `(M, g)`, a fixed source `(0, s)`-tensor `T`, a nonnegative constant `c`, a lowest
contracted order `p`, a base width `w`, and a field `G : SmoothCcTensor g 0 r` (rank generic),
`IsGradedCurvJet g T c p w G` asserts that for *every* further gradient order `k` and *every* point
`x` the `k`-fold iterated covariant gradient `∇^k G` is fibre-bounded by `c²` times the truncated sum
of the iterated-gradient fibre norms of `T` from contracted order `p` up to width `w + k`:

```
rfns(∇^k G)(x) ≤ c² · ∑_{i < w + k} rfns(∇^{i + p} T)(x).
```

This is the operational meaning of "`G` is a curvature jet of `T` of lowest order `p`": not merely a
single-order fibre bound (which is uncontrolled under differentiation), but the entire graded family,
so the field can be differentiated arbitrarily often while staying in the curvature-jet class. The
predicate is closed under one covariant gradient (`IsGradedCurvJet_covGrad`), which is exactly what
the per-step of the order-`m` induction requires: one further `∇` keeps every genuine jet inside the
family, with its order advanced by one. The genuine fields of the order-`m` split satisfy it; the
abstract single-order fibre bound the headline exposes is the `k = 0` specialisation. -/
def IsGradedCurvJet (g : SmoothRiemannianMetric I M) {s : ℕ} (T : SmoothCcTensor g 0 s)
    (c : ℝ) (p w : ℕ) {r : ℕ} (G : SmoothCcTensor g 0 r) : Prop :=
  ∀ (k : ℕ) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
        ((iteratedCovGrad g 0 r k G).toSection x) ≤
      c ^ 2 * ∑ i ∈ Finset.range (w + k),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
          ((iteratedCovGrad g 0 s (i + p) T).toSection x)

/-- **The graded curvature-jet predicate is closed under one covariant gradient.** If `G` is a graded
curvature jet of `T` of lowest order `p` and base width `w`, then its covariant gradient `∇G` is a
graded curvature jet of the same lowest order `p` with base width `w + 1`: the `k`-th gradient of
`∇G` is the `(k + 1)`-th gradient of `G`, so the bound shifts `k → k + 1`, i.e. width `w + k → w +
(k + 1) = (w + 1) + k`. This is the structural step that makes the order-`m` induction's per-step
re-differentiable — differentiating a genuine jet keeps it in the curvature-jet family. -/
theorem IsGradedCurvJet_covGrad (g : SmoothRiemannianMetric I M) {s : ℕ} (T : SmoothCcTensor g 0 s)
    {c : ℝ} {p w r : ℕ} {G : SmoothCcTensor g 0 r}
    (hG : IsGradedCurvJet (I := I) (M := M) g T c p w G) :
    IsGradedCurvJet (I := I) (M := M) g T c p (w + 1)
      (covGrad (I := I) (M := M) g 0 r G) := by
  intro k x
  -- The `k`-fold gradient of `∇G` is the `(k + 1)`-fold gradient of `G`, the two living in the ranks
  -- `(r + 1) + k` and `r + (k + 1)`, which agree as naturals; the intrinsic fibre norm is invariant
  -- under that rank reassociation.
  have hheq := riemannianFiberNormSq_toSection_heq_congr (I := I) (M := M) g 0
    (by omega : (r + 1) + k = r + (k + 1))
    (iteratedCovGrad_covGrad_comm_heq_local (I := I) (M := M) g 0 r k G) x
  rw [hheq]
  -- The graded bound for `G` at order `k + 1` is over `range (w + (k + 1)) = range ((w + 1) + k)`.
  have hkey := hG (k + 1) x
  have hwidth : w + (k + 1) = (w + 1) + k := by omega
  rw [hwidth] at hkey
  exact hkey

/-- **The truncated graded-jet target sum is nonnegative.** Every summand is an intrinsic squared
fibre norm `riemannianFiberNormSq`, hence `≥ 0`; the finite sum is therefore `≥ 0`. This is the
positivity used to monotone the graded bound in its constant. -/
private lemma gradedCurvJet_targetSum_nonneg (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor g 0 s) (p w k : ℕ) (x : M) :
    0 ≤ ∑ i ∈ Finset.range (w + k),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
          ((iteratedCovGrad g 0 s (i + p) T).toSection x) :=
  Finset.sum_nonneg fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + (i + p)) x _

/-- **Monotonicity of the graded curvature-jet predicate in its constant.** If `G` is a graded
curvature jet of `T` with nonnegative constant `c` and `c ≤ c'`, then `G` is also a graded curvature
jet with the larger constant `c'`: at every gradient order `k` the bound multiplier grows
(`c² ≤ c'²`, since `0 ≤ c ≤ c'`) while the truncated target sum stays nonnegative, so the bound only
weakens. This lets several jets of the same `(p, w)` shape but distinct constants be promoted to a
single common constant. -/
theorem IsGradedCurvJet.mono_const (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor g 0 s) {c c' : ℝ} {p w r : ℕ} {G : SmoothCcTensor g 0 r}
    (hc : 0 ≤ c) (hcc' : c ≤ c') (hG : IsGradedCurvJet (I := I) (M := M) g T c p w G) :
    IsGradedCurvJet (I := I) (M := M) g T c' p w G := by
  intro k x
  refine (hG k x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (gradedCurvJet_targetSum_nonneg (I := I) (M := M) g T p w k x)
  exact pow_le_pow_left₀ hc hcc' 2

/-- **The graded curvature-jet predicate is closed under addition of two jets of the same shape.**
If `G₁`, `G₂` are graded curvature jets of `T` of the *same* lowest order `p` and base width `w`,
with nonnegative constants `c₁`, `c₂`, then their sum `G₁ + G₂` is a graded curvature jet of the same
lowest order `p` and base width `w`, with constant `√(2·(c₁² + c₂²))`: at every gradient order `k`,
`∇^k(G₁ + G₂) = ∇^k G₁ + ∇^k G₂` (`iteratedCovGrad_add`, `SmoothCcTensor.toSection_add`), so the
fibre norm is `≤ 2·rfns(∇^k G₁) + 2·rfns(∇^k G₂)` (`riemannianFiberNormSq_add_le`), each term bounded
by its jet, giving `2(c₁² + c₂²)` times the shared target sum. This is the field-level subadditivity
that merges two genuine jets while keeping the curvature-jet shape — exactly the per-step's
reclassification merge. -/
theorem IsGradedCurvJet.add (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : SmoothCcTensor g 0 s) {c₁ c₂ : ℝ} {p w r : ℕ}
    {G₁ G₂ : SmoothCcTensor g 0 r}
    (hG₁ : IsGradedCurvJet (I := I) (M := M) g T c₁ p w G₁)
    (hG₂ : IsGradedCurvJet (I := I) (M := M) g T c₂ p w G₂) :
    IsGradedCurvJet (I := I) (M := M) g T (Real.sqrt (2 * (c₁ ^ 2 + c₂ ^ 2))) p w (G₁ + G₂) := by
  intro k x
  have hsum_nonneg := gradedCurvJet_targetSum_nonneg (I := I) (M := M) g T p w k x
  have hsplit : (iteratedCovGrad g 0 r k (G₁ + G₂)).toSection x =
      (iteratedCovGrad g 0 r k G₁).toSection x + (iteratedCovGrad g 0 r k G₂).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsplit]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (r + k) x
    ((iteratedCovGrad g 0 r k G₁).toSection x) ((iteratedCovGrad g 0 r k G₂).toSection x)
  have hcsq : Real.sqrt (2 * (c₁ ^ 2 + c₂ ^ 2)) ^ 2 = 2 * (c₁ ^ 2 + c₂ ^ 2) := by
    rw [Real.sq_sqrt]
    positivity
  rw [hcsq]
  calc riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
          ((iteratedCovGrad g 0 r k G₁).toSection x + (iteratedCovGrad g 0 r k G₂).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
            ((iteratedCovGrad g 0 r k G₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 0 (r + k) x
            ((iteratedCovGrad g 0 r k G₂).toSection x) := hadd
    _ ≤ 2 * (c₁ ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x)) +
          2 * (c₂ ^ 2 * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x)) := by
        gcongr <;> [exact hG₁ k x; exact hG₂ k x]
    _ = 2 * (c₁ ^ 2 + c₂ ^ 2) * ∑ i ∈ Finset.range (w + k),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + p)) x
                ((iteratedCovGrad g 0 s (i + p) T).toSection x) := by ring

/-- **Posited graded curvature-jet bound for the pure-Riemann genuine section `GcurvSection`.** For a
closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`c : ℕ → ℝ` such that, at every covariant rank `s` and every smooth compactly-supported `(0, s)`-
tensor `T`, the moving-centre pure-Riemann genuine curvature section `GcurvSection g s T`
(`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ}T)`, i.e. the `R(∇T)` contraction) is a **graded** curvature jet of `T` of lowest
order `1` and base width `1`:

```
rfns(∇^k (GcurvSection g s T))(x) ≤ (c s)² · ∑_{i < 1 + k} rfns(∇^{i + 1} T)(x).
```

**Why this is TRUE.** `GcurvSection g s T` is the slot-`0` assembly of the moving-frame pure-Riemann
trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ}T)`, a fixed-curvature contraction applied to the *single* differentiated
section `∇T = covGrad g 0 s T`. Each `∇^k` of it is, by the iterated covariant Leibniz expansion
(`covGrad_prod`-style), a sum of contractions of iterated covariant derivatives of curvature `∇^p R`
(`p ≤ k`) against iterated gradients `∇^{q}(∇T) = ∇^{q + 1}T` (`q ≤ k`); every curvature coefficient
`‖∇^p R‖` is absorbed, uniformly over the compact manifold, into `(c s)²` via the curvature /
differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The contracted-order range is
`1 … 1 + k` (lowest order `1`, since the contraction acts on `∇T`), exactly the `(p, w) = (1, 1)`
graded shape. This is the moving-frame graded refinement of the per-contraction grid bound
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le` summed over the frame; it
is posited as a precise true child (consumers transitively depend on `sorryAx`).

**Non-vacuity.** With `c s = 0` the bound forces `rfns(GcurvSection g s T)(x) = 0` at `k = 0`, i.e.
the pure-Riemann contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ}T)` vanishes; false on a non-flat manifold (`R ≠ 0`)
for a non-parallel `T` (`∇T ≠ 0`). The constant is genuinely positive. -/
theorem GcurvSection_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g T (c s) 1 1
          (GcurvSection (I := I) (M := M) g s T) := by
  sorry

/-- **Posited graded curvature-jet bound for the differentiated-curvature genuine section
`GcurvDerivSection`.** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `c : ℕ → ℝ` such that, at every covariant rank `s` and every smooth
compactly-supported `(0, s)`-tensor `T`, the moving-centre differentiated-curvature genuine section
`GcurvDerivSection g s T` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the moving-frame
trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) T)`, i.e. the `(∇R) T` contraction) is a **graded** curvature jet of `T` of
lowest order `0` and base width `1`:

```
rfns(∇^k (GcurvDerivSection g s T))(x) ≤ (c s)² · ∑_{i < 1 + k} rfns(∇^{i + 0} T)(x).
```

**Why this is TRUE.** `GcurvDerivSection g s T` is the slot-`0` assembly of the moving-frame
differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) T)`, a fixed (once-differentiated) curvature
operator applied to the *undifferentiated* section `T`. Each `∇^k` of it is, by the iterated covariant
Leibniz expansion, a sum of contractions of iterated covariant derivatives of curvature `∇^p R`
(`p ≤ k + 1`) against iterated gradients `∇^{q}T` (`q ≤ k`); every curvature coefficient `‖∇^p R‖` is
absorbed uniformly over the compact manifold into `(c s)²` via the curvature / differentiated-curvature
sups. The contracted-order range is `0 … k` (lowest order `0`, the contraction acting on `T`), exactly
the `(p, w) = (0, 1)` graded shape. Posited as a precise true child (consumers transitively depend on
`sorryAx`).

**Non-vacuity.** With `c s = 0` the bound forces `rfns(GcurvDerivSection g s T)(x) = 0` at `k = 0`,
i.e. the differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) T)` vanishes; false on a manifold
with `∇R ≠ 0` for a non-zero `T`. The constant is genuinely positive. -/
theorem GcurvDerivSection_gradedCurvJet (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        IsGradedCurvJet (I := I) (M := M) g T (c s) 0 1
          (GcurvDerivSection (I := I) (M := M) g s T) := by
  sorry

/-- **Posited graded curvature-jet bracket-remainder field for the `m = 0` split.** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `c : ℕ → ℝ`
such that, at every covariant rank `s` and every smooth compactly-supported `(0, s)`-tensor `T`, the
order-`2` commutator defect `Curv T := pointwiseTensorCurv g s T` splits as

```
Curv T = GcurvSection g s T + GcurvDerivSection g s T + Grem
```

for a smooth compactly-supported `(0, s + 1)`-tensor remainder field `Grem` that is a **graded**
curvature jet of `T` of lowest order `2` and base width `1`:

```
rfns(∇^k Grem)(x) ≤ (c s)² · ∑_{i < 1 + k} rfns(∇^{i + 2} T)(x).
```

**Why this is TRUE.** By the committed sorry-free fibre field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`, the defect `Curv T` is, in the slot-`0`
witness frame, the sum of the genuine third-order curvature field and the bracket field; and
`GcurvSection + GcurvDerivSection` fibre-matches the genuine field exactly
(`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField`). Hence
`Grem := Curv T − GcurvSection g s T − GcurvDerivSection g s T` is the global bracket-remainder field,
which equals the moving-frame/frame-bracket discrepancy `tensor3rdCurvBracket` plus the moving-frame
residual — genuinely `rfns(∇²T)`-order (the bracket carries two covariant derivatives of `T`). Each
`∇^k Grem` is, by the iterated covariant Leibniz expansion of the bracket contraction, a sum of
contractions of `∇^p R` (`p ≤ k`) against `∇^{q + 2}T` (`q ≤ k`), with all curvature coefficients
absorbed uniformly into `(c s)²` via the curvature / differentiated-curvature sups; the contracted-
order range is `2 … 2 + k`, exactly the `(p, w) = (2, 1)` graded shape. Posited as a precise true
child (consumers transitively depend on `sorryAx`).

**Non-vacuity.** With `c s = 0` the bound forces `rfns(Grem)(x) = 0` at `k = 0`, making the split
`Curv T = GcurvSection + GcurvDerivSection`; merged with the two genuine jets this is the `m = 0`
two-term split `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` with vanishing
remainder, *false* on a non-flat manifold where the moving-frame bracket discrepancy is genuinely
non-zero. The constant is genuinely positive. -/
theorem exists_pointwiseTensorCurv_bracketRemainder_gradedCurvJet
    (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        ∃ Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s T =
              GcurvSection (I := I) (M := M) g s T + GcurvDerivSection (I := I) (M := M) g s T +
                Grem ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 2 1 Grem := by
  sorry

/-- **Posited explicit graded curvature-jet seed: the `m = 0` order-separated graded field split of
the order-`2` commutator defect.** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `c : ℕ → ℝ` such that, at every covariant rank `s` and for
every smooth compactly-supported `(0, s)`-tensor `T`, the order-`2` commutator defect
`Curv T := pointwiseTensorCurv g s T` admits an explicit graded curvature-jet split

```
Curv T = Gcurv + GcurvDeriv + Grem
```

into three smooth compactly-supported `(0, s + 1)`-tensor fields, where each is a *graded* curvature
jet of `T` (`IsGradedCurvJet`) at the appropriate lowest order: the differentiated-Riemann jet
`Gcurv` of lowest order `1` and width `1` (so its own gradients are bounded by the iterated gradients
of `∇T = ∇^{0 + 1}T` upward), the iterated differentiated-curvature jet `GcurvDeriv` of lowest order
`0` and width `1` (bounded by `T` upward), and the moving-frame remainder `Grem` of lowest order `2`
and width `1` (bounded by `∇²T` upward).

This is the explicit re-differentiable form of the `m = 0` section-field split
`exists_pointwiseTensorCurv_orderSeparated_field`: the three genuine fields are surfaced as
re-differentiable graded jets (the entire family of their own gradient bounds, not a single fibre
bound), built from the explicit field identity
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` (the genuine + bracket frame-field
split) and the uniform curvature / differentiated-curvature sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. It is the strictly-more-primitive
seed the order-`m` induction starts from; the abstract single-order `m = 0` split is its `k = 0`
specialisation.

The degenerate witness is rejected: at gradient order `k = 0`, the split reads
`Curv T (x) = Gcurv + GcurvDeriv + Grem` with the three `k = 0` order-separated bounds, which —
merged — is the `m = 0` two-term split `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`,
*false* with `c s = 0` on a non-flat manifold (the defect carries the genuine curvature contraction of
`T`). -/
theorem pointwiseTensorCurv_gradedCurvJet_field_base
    (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s T = Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 1 1 Gcurv ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 0 1 GcurvDeriv ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 2 1 Grem := by
  classical
  -- The three genuine fields are `GcurvSection` (pure-Riemann, order `1`), `GcurvDerivSection`
  -- (differentiated-curvature, order `0`), and the bracket remainder (order `2`); each carries its
  -- own graded constant family. Promote all three to a single common constant by `mono_const`.
  obtain ⟨c₁, hc₁_nn, hcurv⟩ := GcurvSection_gradedCurvJet (I := I) (M := M) g
  obtain ⟨c₂, hc₂_nn, hcurvDeriv⟩ := GcurvDerivSection_gradedCurvJet (I := I) (M := M) g
  obtain ⟨c₃, hc₃_nn, hrem⟩ := exists_pointwiseTensorCurv_bracketRemainder_gradedCurvJet
    (I := I) (M := M) g
  refine ⟨fun s => max (max (c₁ s) (c₂ s)) (c₃ s), fun s => ?_, fun s T => ?_⟩
  · exact le_trans (hc₁_nn s) (le_trans (le_max_left _ _) (le_max_left _ _))
  · obtain ⟨Grem, hsplit, hrem_jet⟩ := hrem s T
    refine ⟨GcurvSection (I := I) (M := M) g s T, GcurvDerivSection (I := I) (M := M) g s T, Grem,
      hsplit, ?_, ?_, ?_⟩
    · exact (hcurv s T).mono_const (I := I) (M := M) g T (hc₁_nn s)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact (hcurvDeriv s T).mono_const (I := I) (M := M) g T (hc₂_nn s)
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact hrem_jet.mono_const (I := I) (M := M) g T (hc₃_nn s) (le_max_right _ _)

/-- **Posited genuine per-step moving-frame remainder-refinement (the iterated Ricci cancellation).**
For a closed smooth Riemannian manifold `(M, g)`, a fixed covariant rank `s`, gradient order `m`, and
nonnegative input-bound constant `C`, there is a nonnegative constant `C'` — depending only on
`g, s, m, C`, *uniform* in the source `T` and the remainder field `Grem` — such that: for every smooth
compactly-supported `(0, s)`-tensor `T` and every smooth compactly-supported `(0, s + 1 + m)`-tensor
field `Grem` that is a **graded** curvature jet of `T` of lowest order `m + 2` and width `1`, the
*single covariant gradient* `∇Grem := covGrad g 0 (s + 1 + m) Grem` splits as

```
∇Grem = Greclass + Grem',
```

with `Greclass` a graded curvature jet of `T` of lowest order `1` and width `m + 2`, and `Grem'` a
graded curvature jet of lowest order `m + 3` and width `1`.

**Why this is TRUE — the cancellation.** Differentiating the order-`(m + 2)` moving-frame remainder
once produces a field whose naive graded bound is order `m + 2`, width `2`
(`IsGradedCurvJet_covGrad`: width `1 → 2`), i.e. it picks up the *single extra* contracted-order-`m+2`
term beyond the order-`(m + 3)`/width-`1` target. That extra top term is exactly the place where two
covariant gradients can be commuted by the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (the rank-`(0, s + 1 + m)` instance): the
antisymmetrized second covariant derivative equals a `riemannOp` contraction of *one-lower* order. The
commuted curvature term is a contraction of curvature (a uniformly bounded coefficient on the compact
manifold, `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`) against the field, hence a graded jet
of *lowest order `1`* (`Greclass`, absorbable into the genuine differentiated-Riemann jet); what
remains, `Grem'`, is genuinely order `m + 3` and width `1`. The constant `C'` multiplies `C` by the
manifold's curvature sup and the frame-count, uniform in `T, Grem`. Posited as a precise true child
(consumers transitively depend on `sorryAx`).

**Strictly weaker than the per-step (no hypothesis-packaging).** This refines *one field's* single
covariant gradient; it neither mentions `Curv T` nor produces the order-`(m + 1)` triple split — the
per-step is assembled on top of it together with `IsGradedCurvJet_covGrad` on the two genuine jets and
`IsGradedCurvJet.add`. **Non-vacuity.** With `C' = 0` the conclusion forces `rfns(Greclass) = 0` and
`rfns(Grem') = 0` at every order, hence `∇Grem = 0` for every graded remainder `Grem`; false on a
non-flat manifold where the once-differentiated moving-frame remainder is genuinely non-zero. -/
theorem exists_iteratedCovGrad_remainder_gradedCurvJet_refine
    (g : SmoothRiemannianMetric I M) (s m : ℕ) (C : ℝ) (_hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (T : SmoothCcTensor g 0 s) (Grem : SmoothCcTensor g 0 (s + 1 + m)),
        IsGradedCurvJet (I := I) (M := M) g T C (m + 2) 1 Grem →
        ∃ Greclass Grem' : SmoothCcTensor g 0 (s + 1 + (m + 1)),
          covGrad (I := I) (M := M) g 0 (s + 1 + m) Grem = Greclass + Grem' ∧
          IsGradedCurvJet (I := I) (M := M) g T C' 1 (m + 2) Greclass ∧
          IsGradedCurvJet (I := I) (M := M) g T C' (m + 3) 1 Grem' := by
  sorry

/-- **Posited genuine per-step moving-frame curvature-jet primitive: one covariant-gradient step of
the order-separated *graded* section-field split of the iterated commutator defect.** For a closed
smooth Riemannian manifold `(M, g)`, a fixed covariant rank `s`, gradient order `m`, and nonnegative
constant `C`, suppose the `m`-fold iterated covariant gradient of the order-`2` commutator defect
`Curv T := pointwiseTensorCurv g s T` admits, for *every* smooth compactly-supported `(0, s)`-tensor
`T`, an order-separated *graded* section-level split

```
∇^m(Curv T) = Gcurv + GcurvDeriv + Grem
```

where each field is a **graded** curvature jet (`IsGradedCurvJet` — re-differentiable: the entire
family of its own iterated-gradient bounds is controlled) of the appropriate lowest order: `Gcurv` of
lowest order `1` and width `m + 1`, `GcurvDeriv` of lowest order `0` and width `m + 1`, and `Grem` of
lowest order `m + 2` and width `1`. Then there is a nonnegative constant `C'` such that the
*one-higher* iterated covariant gradient `∇^{m + 1}(Curv T)` admits, for every `T`, the
order-`(m + 1)` order-separated graded split

```
∇^{m + 1}(Curv T) = Gcurv' + GcurvDeriv' + Grem',
```

with `Gcurv'` a graded jet of lowest order `1` and width `m + 2`, `GcurvDeriv'` of lowest order `0`
and width `m + 2`, and `Grem'` of lowest order `m + 3` and width `1`.

This is the genuinely-irreducible per-step third-order moving-frame Bochner–Weitzenböck content. Its
construction applies one further covariant gradient `∇ = covGrad g 0 (s + 1 + m)` to the order-`m`
section identity (`covGrad`-additivity `covGrad_add`) and re-Leibniz-es the curvature contractions:
the top-order `∇^{m + 3}T` term produced by differentiating the genuine Riemann jet `Gcurv` *cancels*
against its swapped partner via the iterated Ricci identity
(`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, the rank-`(0, s + 1 + m)` instance), commuting
two of the gradients into a `riemannOp` of one-lower order; the surviving genuine curvature-jet
contractions (`tensor3rdCurvGenuine`, `covGradCurvatureContraction`, fibre-bounded by
`riemannianFiberNormSq_tensor3rdCurvGenuine_le`) advance by exactly one order, all coefficients —
covariant derivatives of curvature — sup-bounded on the compact manifold by the uniform sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`; and the moving-frame remainder lands
at order `m + 3` (not `m + 4`) precisely because of the cancellation. The graded invariant
(`IsGradedCurvJet`, closed under `∇` by `IsGradedCurvJet_covGrad`) makes the order-`m` hypothesis
re-differentiable — the fix for the abstract single-order fibre bound that gives no control over the
gradients of the fields. The constant grows because the tensor-bundle curvature endomorphism is an
`O(s + m)`-slot derivation and the curvature-derivative term count grows with `m`.

It is a *strictly weaker* implication than the headline order-separated field split
`exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field`: it consumes the order-`m` graded
split as a hypothesis and produces only the order-`(m + 1)` graded split, so it is not the conclusion
itself (no hypothesis-packaging). The degenerate witness is rejected: at `m = 0`, gradient order
`k = 0`, taking `Gcurv = GcurvDeriv = 0` makes the order-`0` hypothesis the false statement
`rfns(Curv T) ≤ 0`, which already fails on a non-flat manifold; the genuine fields must carry the
actual curvature contractions, and one further gradient genuinely advances their order. -/
theorem iteratedCovGrad_pointwiseTensorCurv_gradedCurvJet_field_step
    (g : SmoothRiemannianMetric I M) (s m : ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (hm : ∀ T : SmoothCcTensor g 0 s,
      ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + m),
        iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T) =
            Gcurv + GcurvDeriv + Grem ∧
        IsGradedCurvJet (I := I) (M := M) g T C 1 (m + 1) Gcurv ∧
        IsGradedCurvJet (I := I) (M := M) g T C 0 (m + 1) GcurvDeriv ∧
        IsGradedCurvJet (I := I) (M := M) g T C (m + 2) 1 Grem) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ T : SmoothCcTensor g 0 s,
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + (m + 1)),
          iteratedCovGrad g 0 (s + 1) (m + 1) (pointwiseTensorCurv (I := I) (M := M) g s T) =
              Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJet (I := I) (M := M) g T C' 1 (m + 1 + 1) Gcurv ∧
          IsGradedCurvJet (I := I) (M := M) g T C' 0 (m + 1 + 1) GcurvDeriv ∧
          IsGradedCurvJet (I := I) (M := M) g T C' (m + 1 + 2) 1 Grem := by
  classical
  -- The remainder-refinement child supplies the order-advancing constant for the differentiated
  -- remainder (the iterated-Ricci-cancellation reclassification), uniform in `T`.
  obtain ⟨Cref, hCref_nn, href⟩ :=
    exists_iteratedCovGrad_remainder_gradedCurvJet_refine (I := I) (M := M) g s m C _hC
  -- The order-`(m + 1)` constant must dominate both `C` (for the two `covGrad`-advanced genuine jets)
  -- and the merged-genuine constant `√(2·(C² + Cref²))` produced by adding the reclassified piece
  -- into the differentiated-Riemann jet, as well as `Cref` (for the order-`(m + 3)` remainder).
  refine ⟨max (max C Cref) (Real.sqrt (2 * (C ^ 2 + Cref ^ 2))), ?_, fun T => ?_⟩
  · exact le_trans _hC (le_trans (le_max_left _ _) (le_max_left _ _))
  · obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem⟩ := hm T
    obtain ⟨Greclass, Grem', hrefeq, hreclass, hrem'⟩ := href T Grem hrem
    -- `∇^{m+1}(Curv T) = ∇(∇^m(Curv T)) = ∇(Gcurv + GcurvDeriv + Grem)`
    --   = ∇Gcurv + ∇GcurvDeriv + (Greclass + Grem').
    have hstep_eq :
        iteratedCovGrad g 0 (s + 1) (m + 1) (pointwiseTensorCurv (I := I) (M := M) g s T) =
          (covGrad (I := I) (M := M) g 0 (s + 1 + m) Gcurv + Greclass) +
            covGrad (I := I) (M := M) g 0 (s + 1 + m) GcurvDeriv + Grem' := by
      rw [iteratedCovGrad_succ, hsplit, covGrad_add, covGrad_add, hrefeq]
      abel
    refine ⟨covGrad (I := I) (M := M) g 0 (s + 1 + m) Gcurv + Greclass,
      covGrad (I := I) (M := M) g 0 (s + 1 + m) GcurvDeriv, Grem', hstep_eq, ?_, ?_, ?_⟩
    · -- `Gcurv'`: merge the `∇`-advanced pure-Riemann jet (order `1`, width `(m + 1) + 1`) with the
      -- reclassified remainder piece `Greclass` (order `1`, width `m + 2`), then promote to the
      -- common constant.
      have hadvCurv : IsGradedCurvJet (I := I) (M := M) g T C 1 ((m + 1) + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1 + m) Gcurv) :=
        IsGradedCurvJet_covGrad (I := I) (M := M) g T hcurv
      have hmerge := hadvCurv.add (I := I) (M := M) g T hreclass
      exact hmerge.mono_const (I := I) (M := M) g T (Real.sqrt_nonneg _) (le_max_right _ _)
    · -- `GcurvDeriv'`: the `∇`-advanced differentiated-curvature jet (order `0`, width `(m + 1) + 1`),
      -- promoted to the common constant.
      have hadvDeriv : IsGradedCurvJet (I := I) (M := M) g T C 0 ((m + 1) + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1 + m) GcurvDeriv) :=
        IsGradedCurvJet_covGrad (I := I) (M := M) g T hcurvDeriv
      exact hadvDeriv.mono_const (I := I) (M := M) g T _hC
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · -- `Grem'`: the order-`(m + 3)` width-`1` remainder, promoted to the common constant.
      exact hrem'.mono_const (I := I) (M := M) g T hCref_nn
        (le_trans (le_max_right _ _) (le_max_left _ _))

/-- **The deepest order-`m` curvature primitive: the order-`m` order-separated section-field
decomposition of the iterated commutator defect (rank/order-generic).** The direct order-`m` lift of
the `m = 0` section-field split `exists_pointwiseTensorCurv_orderSeparated_field`. For a closed smooth
Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
`Cper : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, gradient order `m`, smooth
compactly-supported `(0, s)`-tensor `T`, and *every point* `x`, the fibre value of the `m`-fold
iterated covariant gradient of the order-`2` commutator defect `Curv T := pointwiseTensorCurv g s T`
splits as `∇^m(Curv T)(x) = Gcurv + GcurvDeriv + Grem`, with:

* the **differentiated-Riemann jet** `Gcurv` (the `∇^m` Leibniz expansion of the pure-Riemann
  contraction `R(∇T)` — `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, each Leibniz term a
  covariant derivative of curvature against `∇^{i + 1}T`, `i ≤ m`) fibre-bounded by
  `∑_{i < m + 1} rfns(∇^{i + 1}T)` (orders `1 … m + 1`);
* the **iterated differentiated-curvature jet** `GcurvDeriv` (the `∇^m` Leibniz expansion of the
  differentiated-curvature contraction `(∇R) T` — `covGradCurvatureContraction`, each term a
  covariant derivative of curvature against `∇^i T`, `i ≤ m`) fibre-bounded by
  `∑_{i < m + 1} rfns(∇^i T)` (orders `0 … m`);
* the **moving-frame remainder** `Grem` fibre-bounded by `rfns(∇^{m + 2}T)` (the single top order),
  the moving-frame/frame-bracket discrepancy after the iterated Ricci cancellation of the top-order
  `∇^{m + 3}T` terms.

Each fibre bound is by `(Cper s m)²`, uniformly in `T`, all coefficients (covariant derivatives of
curvature) sup-bounded on the compact manifold by `exists_uniform_riemannianFiberNormSq_riemannOp_bound`
/ `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The constant is
valence/order-dependent because the tensor-bundle curvature endomorphism is an `O(s + m)`-slot
derivation and the curvature-derivative term count grows with `m` (a single scalar uniform over all
`s, m` is unsatisfiable on a non-flat closed manifold).

This is **proved** by induction on `m`, carrying the re-differentiable **graded** curvature-jet
invariant `IsGradedCurvJet` (each genuine field controlled together with the full family of its own
iterated gradients): the base case `m = 0` is the posited explicit graded seed
`pointwiseTensorCurv_gradedCurvJet_field_base`; the inductive step `m → m + 1` is the posited per-step
primitive `iteratedCovGrad_pointwiseTensorCurv_gradedCurvJet_field_step`, whose construction applies
one further covariant gradient and cancels the top-order `∇^{m + 3}T` term via the iterated Ricci
identity (the graded invariant, closed under `∇` by `IsGradedCurvJet_covGrad`, makes the order-`m`
hypothesis re-differentiable). The global constant `Cper` is assembled from the per-`m` constants by
choice. The final per-point fibre split — the abstract single-order three-field form the headline
exposes — is read off the graded field split at gradient order `k = 0` and point `x` through
`SmoothCcTensor.toSection_add`, after collapsing the empty index shift `i + 0 = i` and the base width
`1 + 0 = 1`.

The degenerate witness is rejected: at `m = 0` the split reads `Curv T (x) = Gcurv + GcurvDeriv +
Grem` with `Gcurv` bounded by `rfns(∇T)`, `GcurvDeriv` by `rfns(T)`, `Grem` by `rfns(∇²T)`, which —
merged — is the `m = 0` two-term split `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`,
*false* with `Cper s 0 = 0` on a non-flat manifold (the defect carries the genuine curvature
contraction of `T`). The assembly-ready two-term split
`exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`) is *proved* on top of this by
merging the two genuine jets through `riemannianFiberNormSq_add_le`. -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cper s m) ∧
      ∀ (s m : ℕ) (T : SmoothCcTensor g 0 s) (x : M),
        ∃ Gcurv GcurvDeriv Grem : TensorRSSpace 0 (s + 1 + m) I x,
          (iteratedCovGrad g 0 (s + 1) m
              (pointwiseTensorCurv (I := I) (M := M) g s T)).toSection x =
              Gcurv + GcurvDeriv + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Gcurv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
                ((iteratedCovGrad g 0 s (i + 1) T).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x GcurvDeriv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((iteratedCovGrad g 0 s i T).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Grem ≤
            Cper s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
                ((iteratedCovGrad g 0 s (m + 2) T).toSection x) := by
  classical
  -- A field-level (global `SmoothCcTensor`) version of the order-separated split at each order `m`,
  -- carrying the re-differentiable graded curvature-jet invariant `IsGradedCurvJet`, proved by
  -- induction on `m`. The per-`m` constant family `c : ℕ → ℝ` (indexed by rank `s`) is existentially
  -- produced; the global `Cper` is its choice.
  have hkey : ∀ m : ℕ, ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + m),
          iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T) =
              Gcurv + GcurvDeriv + Grem ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 1 (m + 1) Gcurv ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) 0 (m + 1) GcurvDeriv ∧
          IsGradedCurvJet (I := I) (M := M) g T (c s) (m + 2) 1 Grem := by
    intro m
    induction m with
    | zero =>
        -- Base case: the posited explicit graded curvature-jet seed (the `m = 0` split with the full
        -- graded gradient family of bounds). At `m = 0` the iterated gradient is the identity and the
        -- rank is `s + 1`; the seed's three widths are exactly the `m = 0` widths.
        obtain ⟨c, hc_nn, hbase⟩ :=
          pointwiseTensorCurv_gradedCurvJet_field_base (I := I) (M := M) g
        refine ⟨c, hc_nn, fun s T => ?_⟩
        obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem⟩ := hbase s T
        refine ⟨Gcurv, GcurvDeriv, Grem, ?_, hcurv, hcurvDeriv, hrem⟩
        rw [iteratedCovGrad_zero]; exact hsplit
    | succ m ih =>
        obtain ⟨c, hc_nn, hsplit⟩ := ih
        -- The per-step primitive turns the order-`m` graded field split (uniform in `T` at rank `s`)
        -- into the order-`(m + 1)` graded field split. Apply it at each rank `s` and choose the
        -- resulting constant.
        have hstep : ∀ s : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧
            ∀ T : SmoothCcTensor g 0 s,
              ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + (m + 1)),
                iteratedCovGrad g 0 (s + 1) (m + 1)
                    (pointwiseTensorCurv (I := I) (M := M) g s T) =
                    Gcurv + GcurvDeriv + Grem ∧
                IsGradedCurvJet (I := I) (M := M) g T C' 1 (m + 1 + 1) Gcurv ∧
                IsGradedCurvJet (I := I) (M := M) g T C' 0 (m + 1 + 1) GcurvDeriv ∧
                IsGradedCurvJet (I := I) (M := M) g T C' (m + 1 + 2) 1 Grem := by
          intro s
          exact iteratedCovGrad_pointwiseTensorCurv_gradedCurvJet_field_step (I := I) (M := M)
            g s m (c s) (hc_nn s) (hsplit s)
        refine ⟨fun s => (hstep s).choose, fun s => (hstep s).choose_spec.1, fun s T => ?_⟩
        exact (hstep s).choose_spec.2 T
  -- Assemble the global constant `Cper s m := (hkey m).choose s` and read the abstract single-order
  -- three-field split off the graded invariant at gradient order `k = 0` and point `x`.
  refine ⟨fun s m => (hkey m).choose s, fun s m => (hkey m).choose_spec.1 s, fun s m T x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, heq, hcurv, hcurvDeriv, hrem⟩ :=
    (hkey m).choose_spec.2 s T
  -- Specialise each graded jet to gradient order `k = 0`: `∇^0 G = G`, width `w + 0 = w`, and the
  -- contracted index shift `i + p` over `range (w + 0)` is the headline's order-separated sum.
  have hcurv0 := hcurv 0 x
  have hcurvDeriv0 := hcurvDeriv 0 x
  have hrem0 := hrem 0 x
  rw [iteratedCovGrad_zero] at hcurv0 hcurvDeriv0 hrem0
  simp only [Nat.add_zero] at hcurv0 hcurvDeriv0 hrem0
  refine ⟨Gcurv.toSection x, GcurvDeriv.toSection x, Grem.toSection x, ?_, ?_, ?_, ?_⟩
  · rw [heq, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  · -- `Gcurv`: width `m + 1`, lowest order `1`. The graded bound at `k = 0` is over `range (m + 1)`
    -- of `rfns(∇^{i + 1}T)`, exactly the headline's `Gcurv` sum.
    exact hcurv0
  · -- `GcurvDeriv`: width `m + 1`, lowest order `0`. The graded bound at `k = 0` is over
    -- `range (m + 1)` of `rfns(∇^{i + 0}T) = rfns(∇^i T)`, exactly the headline's `GcurvDeriv` sum.
    simpa only [Nat.add_zero] using hcurvDeriv0
  · -- `Grem`: width `1`, lowest order `m + 2`. The graded bound at `k = 0` is over `range 1` of
    -- `rfns(∇^{i + (m + 2)}T)`, i.e. the single term `rfns(∇^{m + 2}T)`.
    rw [Finset.sum_range_one, zero_add] at hrem0
    exact hrem0

end Connection
end Integral
end DifferentialGeometry

end
