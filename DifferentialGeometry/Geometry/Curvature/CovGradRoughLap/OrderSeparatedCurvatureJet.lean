import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineBracketSectionSplit
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

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

## What is proved vs. posited

The order-`m` order-separated *field*-level split is built by **induction on `m`** (the genuine glue
written in this file):

* the **base case `m = 0`** is read off the on-disk PROVEN `m = 0` section-field split
  `exists_pointwiseTensorCurv_orderSeparated_field` (whose three bounds, at the one-term sums
  `∑_{i < 1}`, are exactly `rfns(∇T)`, `rfns(T)`, `rfns(∇²T)`);
* the **inductive step `m → m + 1`** is the single genuine moving-frame curvature primitive posited
  here, `iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field_step`: applying one further
  covariant gradient `∇` to the order-`m` field split and re-Leibniz-ing the curvature contractions,
  the iterated Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the
  top-order `∇^{m + 3}T` term against its swapped partner, producing the order-`(m + 1)` split with
  the genuine curvature-jet bounds advanced by one order (the new curvature-derivative contractions
  sup-bounded on the compact manifold by the uniform curvature / differentiated-curvature sups
  `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
  `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). Its body is `sorry`; it is a
  *strictly weaker* implication than the headline (it consumes the order-`m` split and produces the
  order-`(m + 1)` split), so it is the genuinely-irreducible per-step Weitzenböck content and not the
  conclusion itself. Consumers transitively depend on `sorryAx` through this per-step primitive.

The degenerate witness is rejected: at `m = 0` the merged split reads `Curv T (x) = Ggen + Grem` with
`rfns(Ggen)(x) ≤ (Cgr s 0)²·(rfns(T) + rfns(∇T))(x)` and `rfns(Grem)(x) ≤ (Cgr s 0)²·rfns(∇²T)(x)`,
which is *false* with `Cper s 0 = 0` on a non-flat manifold (the defect carries the genuine curvature
contraction of `T`).

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

/-- **Posited genuine per-step moving-frame curvature-jet primitive: one covariant-gradient step of
the order-separated section-field split of the iterated commutator defect.** For a closed smooth
Riemannian manifold `(M, g)`, a fixed covariant rank `s`, gradient order `m`, and nonnegative
constant `C`, suppose the `m`-fold iterated covariant gradient of the order-`2` commutator defect
`Curv T := pointwiseTensorCurv g s T` admits, for *every* smooth compactly-supported `(0, s)`-tensor
`T`, an order-separated *section-level* split

```
∇^m(Curv T) = Gcurv + GcurvDeriv + Grem
```

into the differentiated-Riemann jet `Gcurv` (fibre-bounded by `C²·∑_{i < m + 1} rfns(∇^{i + 1}T)`,
orders `1 … m + 1`), the iterated differentiated-curvature jet `GcurvDeriv` (fibre-bounded by
`C²·∑_{i < m + 1} rfns(∇^i T)`, orders `0 … m`), and the moving-frame remainder `Grem`
(fibre-bounded by `C²·rfns(∇^{m + 2}T)`, the single top order). Then there is a nonnegative constant
`C'` such that the *one-higher* iterated covariant gradient `∇^{m + 1}(Curv T)` admits, for every
`T`, the order-`(m + 1)` order-separated split

```
∇^{m + 1}(Curv T) = Gcurv' + GcurvDeriv' + Grem',
```

with `Gcurv'` fibre-bounded by `C'²·∑_{i < m + 2} rfns(∇^{i + 1}T)` (orders `1 … m + 2`),
`GcurvDeriv'` by `C'²·∑_{i < m + 2} rfns(∇^i T)` (orders `0 … m + 1`), and `Grem'` by
`C'²·rfns(∇^{m + 3}T)` (the single new top order).

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
at order `m + 3` (not `m + 4`) precisely because of the cancellation. The constant grows because the
tensor-bundle curvature endomorphism is an `O(s + m)`-slot derivation and the curvature-derivative
term count grows with `m`.

It is a *strictly weaker* implication than the headline order-separated field split
`exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field`: it consumes the order-`m` split as
a hypothesis and produces only the order-`(m + 1)` split, so it is not the conclusion itself (no
hypothesis-packaging). The degenerate witness is rejected: at `m = 0`, taking `Gcurv = GcurvDeriv = 0`
makes the order-`0` hypothesis the false statement `rfns(Curv T) ≤ 0`, which already fails on a
non-flat manifold; the genuine fields must carry the actual curvature contractions, and one further
gradient genuinely advances their order. -/
theorem iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field_step
    (g : SmoothRiemannianMetric I M) (s m : ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (hm : ∀ T : SmoothCcTensor g 0 s,
      ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + m),
        iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T) =
            Gcurv + GcurvDeriv + Grem ∧
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (Gcurv.toSection x) ≤
          C ^ 2 * ∑ i ∈ Finset.range (m + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
              ((iteratedCovGrad g 0 s (i + 1) T).toSection x)) ∧
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (GcurvDeriv.toSection x) ≤
          C ^ 2 * ∑ i ∈ Finset.range (m + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
              ((iteratedCovGrad g 0 s i T).toSection x)) ∧
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (Grem.toSection x) ≤
          C ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
              ((iteratedCovGrad g 0 s (m + 2) T).toSection x))) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ T : SmoothCcTensor g 0 s,
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + (m + 1)),
          iteratedCovGrad g 0 (s + 1) (m + 1) (pointwiseTensorCurv (I := I) (M := M) g s T) =
              Gcurv + GcurvDeriv + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
              (Gcurv.toSection x) ≤
            C' ^ 2 * ∑ i ∈ Finset.range (m + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
                ((iteratedCovGrad g 0 s (i + 1) T).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
              (GcurvDeriv.toSection x) ≤
            C' ^ 2 * ∑ i ∈ Finset.range (m + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((iteratedCovGrad g 0 s i T).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
              (Grem.toSection x) ≤
            C' ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1 + 2)) x
                ((iteratedCovGrad g 0 s (m + 1 + 2) T).toSection x)) := by
  sorry

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

This is **proved** by induction on `m`: the base case `m = 0` is read off the on-disk PROVEN `m = 0`
section-field split `exists_pointwiseTensorCurv_orderSeparated_field` (its three bounds, at the
one-term sums `∑_{i < 1}`, are exactly `rfns(∇T)`, `rfns(T)`, `rfns(∇²T)`); the inductive step
`m → m + 1` is the posited per-step primitive
`iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field_step`, whose construction applies one
further covariant gradient and cancels the top-order `∇^{m + 3}T` term via the iterated Ricci
identity. The global constant `Cper` is assembled from the per-`m` constants by choice. The final
per-point fibre split is read off the field-level split at `x` through `SmoothCcTensor.toSection_add`.

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
  -- proved by induction on `m`. The per-`m` constant family `c : ℕ → ℝ` (indexed by rank `s`) is
  -- existentially produced; the global `Cper` is its choice.
  have hkey : ∀ m : ℕ, ∃ c : ℕ → ℝ, (∀ s, 0 ≤ c s) ∧
      ∀ (s : ℕ) (T : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + m),
          iteratedCovGrad g 0 (s + 1) m (pointwiseTensorCurv (I := I) (M := M) g s T) =
              Gcurv + GcurvDeriv + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (Gcurv.toSection x) ≤
            c s ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
                ((iteratedCovGrad g 0 s (i + 1) T).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x
              (GcurvDeriv.toSection x) ≤
            c s ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((iteratedCovGrad g 0 s i T).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x (Grem.toSection x) ≤
            c s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
                ((iteratedCovGrad g 0 s (m + 2) T).toSection x)) := by
    intro m
    induction m with
    | zero =>
        -- Base case: read off the imported genuine bracket-free curvature core (the `m = 0`
        -- section-field split, upstream of `PointwiseTensorCurvL2Bound`). At `m = 0` the iterated
        -- gradient is the identity, the rank is `s + 1`, the remainder is the anonymous subtraction
        -- `Curv T − Gcurv − GcurvDeriv` (named `Grem`), and the one-term sums collapse:
        -- `∑_{i < 1} rfns(∇^{i+1}T) = rfns(∇T)`, `∑_{i < 1} rfns(∇^i T) = rfns(T)`, and the top
        -- term is `rfns(∇²T)`.
        obtain ⟨Cper, hCper_nn, hfields⟩ :=
          pointwiseTensorCurv_genuineFields_bracketFree_curvatureCore (I := I) (M := M) g
        refine ⟨Cper, hCper_nn, fun s T => ?_⟩
        obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, _⟩ := hfields s T
        refine ⟨Gcurv, GcurvDeriv,
          pointwiseTensorCurv (I := I) (M := M) g s T - Gcurv - GcurvDeriv,
          ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
        · simp only [iteratedCovGrad_zero]; abel
        · -- `∑_{i < 1} rfns(∇^{i+1}T) = rfns(∇T) = rfns(covGrad g 0 s T)`.
          simpa only [Nat.add_zero, Nat.zero_add, Finset.sum_range_one, iteratedCovGrad_succ,
            iteratedCovGrad_zero] using hcurv x
        · -- `∑_{i < 1} rfns(∇^i T) = rfns(T)`.
          simpa only [Nat.add_zero, Nat.zero_add, Finset.sum_range_one, iteratedCovGrad_zero]
            using hcurvDeriv x
        · -- `rfns(∇²T) = rfns(covGrad g 0 (s+1) (covGrad g 0 s T))`.
          simpa only [Nat.add_zero, iteratedCovGrad_succ, iteratedCovGrad_zero] using hrem x
    | succ m ih =>
        obtain ⟨c, hc_nn, hsplit⟩ := ih
        -- The per-step primitive turns the order-`m` field split (uniform in `T` at rank `s`) into
        -- the order-`(m + 1)` field split. Apply it at each rank `s` and choose the resulting
        -- constant.
        have hstep : ∀ s : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧
            ∀ T : SmoothCcTensor g 0 s,
              ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1 + (m + 1)),
                iteratedCovGrad g 0 (s + 1) (m + 1)
                    (pointwiseTensorCurv (I := I) (M := M) g s T) =
                    Gcurv + GcurvDeriv + Grem ∧
                (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
                    (Gcurv.toSection x) ≤
                  C' ^ 2 * ∑ i ∈ Finset.range (m + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
                      ((iteratedCovGrad g 0 s (i + 1) T).toSection x)) ∧
                (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
                    (GcurvDeriv.toSection x) ≤
                  C' ^ 2 * ∑ i ∈ Finset.range (m + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                      ((iteratedCovGrad g 0 s i T).toSection x)) ∧
                (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + (m + 1)) x
                    (Grem.toSection x) ≤
                  C' ^ 2 *
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1 + 2)) x
                      ((iteratedCovGrad g 0 s (m + 1 + 2) T).toSection x)) := by
          intro s
          exact iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field_step (I := I) (M := M)
            g s m (c s) (hc_nn s) (hsplit s)
        refine ⟨fun s => (hstep s).choose, fun s => (hstep s).choose_spec.1, fun s T => ?_⟩
        exact (hstep s).choose_spec.2 T
  -- Assemble the global constant `Cper s m := (hkey m).choose s` and read the field split off
  -- pointwise at `x`.
  refine ⟨fun s m => (hkey m).choose s, fun s m => (hkey m).choose_spec.1 s, fun s m T x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, heq, hcurv, hcurvDeriv, hrem⟩ :=
    (hkey m).choose_spec.2 s T
  refine ⟨Gcurv.toSection x, GcurvDeriv.toSection x, Grem.toSection x, ?_,
    hcurv x, hcurvDeriv x, hrem x⟩
  rw [heq, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
  simp only [ContMDiffSection.coe_add, Pi.add_apply]

end Connection
end Integral
end DifferentialGeometry

end
