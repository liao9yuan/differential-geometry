import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct

/-! # The Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant gradients

This file isolates the **Lᵖ-form** of the closed-manifold tensor Gagliardo–Nirenberg interpolation
(Hamilton, *Three-manifolds with positive Ricci curvature* §12.5; Aubin): for a smooth
compactly-supported `(0, s)`-tensor `u` with `C⁰`-sup fibre bound `Λ₀`, a top order `k ≥ 1`, and an
intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated covariant gradient
is controlled by the interpolated product of the `L^∞` sup and the top-order covariant `L²`-jet:
```
‖∇^j u‖_{L^{2k/j}}^2 ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```
Equivalently, in the squared-fibre-norm integral form used by the diagonal-product-grid consumer,
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} ,
```
the left member being `‖∇^j u‖²_{L^{2k/j}}` (the `L^{2k/j}` norm of the *pointwise fibre norm*
`|∇^j u|`, raised to the second power and written through the squared fibre norm
`rfns(∇^j u) = |∇^j u|²`).

The companion `L²`-form already on disk
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`, `Analysis/Sobolev/MoserTameProduct.lean`)
is the *degenerate* `p = 2` case `j = k - 1` collapsed to the `L²` left member, and does **not**
imply this `L^{2k/j}` form: the diagonal-product-grid two-arm estimate
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`) integrates each pointwise
product `rfns(∇^i S)·rfns(∇^l T)` via Hölder at the conjugate pair `(k/i, k/l)`, which requires the
*genuine `L^{2k/i}` interpolation* of each factor — exactly the left member here, with a free
`L^p` exponent that the `L²`-form's fixed `L²` left member cannot supply.  This file is therefore
the precise Lᵖ-interpolation kernel the product grid consumes.

The single declaration is a posited leaf (`sorry` body): the genuine closed-manifold tensor `Lᵖ`
Gagliardo–Nirenberg interpolation content (the `L^{2k/j}`-endpoint version of the covariant `L²`-jet
log-convexity, i.e. Hamilton 12.5 with the intermediate `L^p` Sobolev embedding).  Consumers
transitively depend on its `sorryAx`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **(POSIT — the Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant
gradients; Hamilton 12.5.)**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single constant `C ≥ 0`
such that for every smooth compactly-supported `(0, s)`-tensor `u` whose `C⁰`-sup fibre norm is
`≤ Λ₀` and every intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated
covariant gradient — written through its squared fibre norm `rfns(∇^j u) = |∇^j u|²` as
`(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} = ‖∇^j u‖²_{L^{2k/j}}` — is controlled by the **interpolated**
product of the `L^∞` sup `Λ₀` and the top-order covariant `L²`-jet:
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```

This is the genuine **`Lᵖ` Gagliardo–Nirenberg interpolation** with the *free exponent* `p = 2k/j`:
the intermediate covariant gradient is estimated by interpolation between the `L^∞` bound (order
`0`) and the top-order `L²` bound (order `k`), the interpolation weights being `1 − j/k` (on the
sup) and `j/k` (on the top jet), now in the **`L^{2k/j}`** norm rather than the degenerate `L²` of
the companion `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`.  It is the precise kernel that
the diagonal covariant-jet product grid
(`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`) consumes through Hölder at the
conjugate pair `(k/i, k/l)`: each Hölder factor is exactly an `L^{2k/i}` norm of one tensor's `i`-th
fibre jet, which this statement bounds.

**Non-vacuity.**  The constant `C` is uniform over `(u, Λ₀, j)` (quantified before all of them);
the bound `0 < j < k` confines the interpolation exponent `j/k ∈ (0, 1)` (so `p = 2k/j ∈ (2, ∞)`),
and the `k = 1` case is vacuous (no `j` with `0 < j < 1`), so no degenerate witness is asserted; a
`C = 0` witness is rejected by any `u` with a nonvanishing intermediate jet.  Its body is `sorry`:
the genuine closed-manifold tensor `Lᵖ` Gagliardo–Nirenberg interpolation content; consumers
transitively depend on its `sorryAx`. -/
theorem exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
            C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ (2 * (j : ℝ) / k) :=
  sorry

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
