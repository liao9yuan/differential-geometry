import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Corollary II endpoint (`lemma45_corII`, F4)

The book-facing F4 endpoint: Corollary II *with the intrinsic Lemma I discharged*
from the approximate-isometry data, so consumers (F5/F6, Step B) need no `hF3`
hypothesis.  Same-domain formulation: `g`, `gRef` two metrics on a common domain,
`T` a `(0,q₂)` tensor; for an `(ε,p)`-approximate isometry `g ≈ gRef`,
`|∇_g^r T|_g ≤ √((1+ε)^{q₂+r})·(|∇_gRef^r T|_gRef + ε·Cc·Σ_{k<r}|∇_gRef^k T|_gRef)`.

## Proof status — ONE narrow, mechanical `sorry`

The real mathematics is already done and green:
* `lemma45_F3` (`Lemma45Engine.lean`) — Lemma I in component (`compL2`) form;
* `compL2_tower_eq_gen` + `hF3_term` (`Lemma45Intrinsic.lean`) — the intrinsic
  lift (the genuine former frontier): the `compL2` Lemma I becomes the
  `normSq0S` `hF3` at a `g`-orthonormal frame point;
* `lemma45_cor_II_of_intrinsic` (`Lemma45Covariant.lean`) — Cor II from `hF3`.

What remains (the `sorry` below) is the mechanical assembly:
1. produce a `g`-orthonormal frame at each `x ∈ u` (apply the parallel session's
   `exists_goodFrame_compBound` with `gRef := g`; it is metric-generic);
2. discharge `lemma45_F3`'s per-frame inputs (`Ginv`/`hGinv` from the gram
   inverse, `hgK` from the supplied intrinsic bounds via the frame, smoothness
   from the trivialization frame);
3. `∃`-collect `hF3_term` over the orders into `hF3` and feed
   `lemma45_cor_II_of_intrinsic`.

This is plumbing, not new mathematics, and is intentionally deferred while the
good-frame producer (`RicBoundGoodFrame.lean`) is being finalized in the parallel
ric_bound track.  F5/F6 are built against the statement below.
-/

universe u

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **MSM135 Corollary II (`lbl370`), book-facing endpoint.**  On an open set `u`
where `g` is uniformly `(1+ε)`-equivalent to `gRef` and the `gRef`-derivatives of
`g` are `ε`-small up to order `p` (the `(ε,p)`-approximate-isometry data), every
`(0,q₂)` tensor field `T` satisfies, for `0 < r ≤ p`,
`|∇_g^r T|_g ≤ √((1+ε)^{q₂+r})·(|∇_gRef^r T|_gRef + ε·Cc·Σ_{k<r}|∇_gRef^k T|_gRef)`
at every `x ∈ u`, with `Cc` uniform over `u`.

The intrinsic lift that powers this is proven (`Lemma45Intrinsic.lean`); the
`sorry` is the mechanical good-frame assembly (see the module docstring). -/
theorem lemma45_corII
    {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + eps) * gRef.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) :
    ∃ Cc : Real, 0 ≤ Cc ∧ ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
          (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt ((1 + eps) ^ (q₂ + r)) *
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
              (iterCov (I := I) gRef q₂ T r x)) +
            eps * Cc * ∑ k ∈ Finset.range r,
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  sorry

/-- **Uniform-constant variant of `lemma45_corII` (the D1b-facing form).**  The book's
Corollary II constant depends only on the dimension and the orders `(q₂, p)` — NOT on the
metrics, the tensor, the set, or `ε` (chapter4.tex, lbl370; the geometry-free algebra is
`Lemma45Constants.lemma45Const`).  The `∃ Cc` therefore commutes past the manifold and all
data quantifiers.  The lbl406 recursion (D1b `exists_directedApproxSystem`) NEEDS this
order of quantifiers: it budgets `C_r Σ C_i⁻¹ 2⁻ⁱ ≤ 2^{1-r}` with the constants chosen
BEFORE the maps (STEPD_PLAN coda 37).  Same sorry-status as `lemma45_corII`; whoever proves
that one proves this one with the explicit constant. -/
theorem lemma45_corII_unif (q₂ p : ℕ) :
    ∃ Cc : Real, 0 ≤ Cc ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
        [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
        [IsManifold I 1 M'] [IsManifold I 2 M']
        [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
        {u : Set M'} (_ : IsOpen u)
        (g gRef : SmoothRiemannianMetric I M')
        (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) q₂)
        (eps : Real), 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
            g.inner x v v ≤ (1 + eps) * gRef.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
            (iterCov (I := I) gRef 2
              (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) →
        ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
              (iterCov (I := I) g q₂ T r x)) ≤
            Real.sqrt ((1 + eps) ^ (q₂ + r)) *
              (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
                  (iterCov (I := I) gRef q₂ T r x)) +
                eps * Cc * ∑ k ∈ Finset.range r,
                  Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                    (iterCov (I := I) gRef q₂ T k x))) := by
  sorry

end HCGCompactness
end DifferentialGeometry
