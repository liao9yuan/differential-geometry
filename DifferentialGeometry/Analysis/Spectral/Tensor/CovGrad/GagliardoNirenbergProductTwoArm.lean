import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct

/-! # The integrated Gagliardo–Nirenberg two-arm bound for diagonal covariant-jet product grids

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file posits the **integrated two-arm product estimate** for the
diagonal covariant-jet product grid of two independent smooth compactly-supported tensors
(Hamilton's interpolation corollary, *Three-manifolds with positive Ricci curvature* §12.5 /
Chow–Knopf): for `S : (0, s₁)`, `T : (0, s₂)` with `C⁰` fibre sups `√rfns(S) ≤ Λ_S`,
`√rfns(T) ≤ Λ_T`, and a window `k`,

  `∫ ∑_{i + l ≤ k} rfns(∇^i S) · rfns(∇^l T) dμ
     ≤ C · ( Λ_T² · ∑_{i ≤ k} ‖∇^i S‖² + Λ_S² · ∑_{l ≤ k} ‖∇^l T‖² )`,

with a single constant `C` per `(g, s₁, s₂, k)`, together with the integrability of the grid
integrand.  The diagonal `i + l ≤ k` is essential: each pointwise product
`rfns(∇^i S)·rfns(∇^l T)` is integrated via the Gagliardo–Nirenberg interpolation
`‖∇^i S‖_{L^{2k/i}} ≤ C·Λ_S^{1-i/k}·‖∇^k S‖^{i/k}`
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`, `Analysis/Sobolev/MoserTameProduct.lean`),
Hölder at the conjugate pair `(2k/i, 2k/l)` (admissible exactly on the diagonal `i + l ≤ k`), and
Young's inequality splitting the interpolated product into the two arms.  The **independent-square
grid** `(i ≤ k) × (l ≤ k)` is *not* integrable to two arms (the joint top-order term
`‖∇^k S‖²·‖∇^k T‖²` is quartic in top jets); only the diagonal is.

This is the integrated replacement for the refuted *pointwise* two-arm splits of the segment-metric
covariant Faà-di-Bruno difference expansion: pointwise, a joint concentration bump makes the
middle-diagonal Leibniz terms `∇^i(diff) ⊛ ∇^{j+1-i}(fixed)` (with `i` above the embedding window
and `j + 1 - i` above the ball order) larger than *both* arms, so a pointwise two-arm sum is false
at high order; after integration the Gagliardo–Nirenberg interpolation redistributes the orders and
the two-arm form is recovered.  Consumers therefore bound their sections **pointwise by the product
grid** (the honest covariant-Leibniz shape) and convert to two `L²` arms only through this
integrated engine.

The single declaration is a posited leaf (`sorry` body): the genuine closed-manifold tensor
interpolation content (Gagliardo–Nirenberg + Hölder + Young on the covariant `L²`-jet scale).
Consumers transitively depend on its `sorryAx`. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **(POSIT — the integrated Gagliardo–Nirenberg two-arm bound of the diagonal covariant-jet
product grid; Hamilton 12.5.)**

Fix an anchor `g`, two valences `s₁, s₂`, and a window `k`.  There is a single constant `C ≥ 0`
such that for any two smooth compactly-supported tensors `S : (0, s₁)`, `T : (0, s₂)` and any
`C⁰`-sup bounds `Λ_S, Λ_T ≥ 0` with `rfns(S)(x) ≤ Λ_S²` and `rfns(T)(x) ≤ Λ_T²` everywhere, the
diagonal product grid `∑_{i ≤ k} rfns(∇^i S) · ∑_{l ≤ k - i} rfns(∇^l T)` (all pointwise products
of squared covariant-jet fibre norms with `i + l ≤ k`) is integrable against the Riemannian volume
measure, and its integral satisfies the **two-arm tame bound**

  `∫ grid dμ ≤ C · ( Λ_T² · ∑_{i ≤ k} ‖∇^i S‖² + Λ_S² · ∑_{l ≤ k} ‖∇^l T‖² )`.

The high covariant order is redistributed by Gagliardo–Nirenberg interpolation
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`) so that each arm carries one tensor's full
`L²`-jet scale against the *other* tensor's `C⁰` sup — never a pointwise jet of either tensor
beyond order `0`.

**Non-vacuity.**  The constant is uniform over `(S, T, Λ_S, Λ_T)` (quantified before them); both
arms genuinely carry their tensors (the `i = 0` column of the grid integrates to
`≥ vol`-weighted `rfns(S)·rfns(∇^l T)` masses requiring the `Λ_S²`-arm, the `l = 0` row the
`Λ_T²`-arm); a `C = 0` witness is rejected by any pair with a nonvanishing grid.  The integrability
conjunct is the genuine "the grid integral makes sense" half of the classical statement (finite
sums of products of continuous compactly-supported integrands on a closed manifold).  Its body is
`sorry`: the genuine Gagliardo–Nirenberg/Hölder/Young tensor interpolation content; consumers
transitively depend on its `sorryAx`. -/
theorem exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
    (g : SmoothRiemannianMetric I M) (s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g 0 s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, (∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) :=
  sorry

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
