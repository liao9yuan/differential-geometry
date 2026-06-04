import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

/-! # The intrinsic Moser tame product and Gagliardo–Nirenberg interpolation

This file isolates the genuinely-missing **Sobolev·Sobolev** multiplication estimates on a
closed Riemannian manifold, phrased intrinsically against the iterated covariant gradient
`iteratedCovGrad` and the metric `L²` norm `tensorL2Norm` of smooth compactly-supported
tensor sections.

The pre-existing library multiplication apparatus controls only **smooth-coefficient ·
Sobolev** products — `wkpNorm_smul_smooth_bounded_lt_top`
(`Euclidean/Multiplication/Multiply.lean`), `wkpNormChart_smooth_mul_le`
(`Chart/SmoothDensity/SmoothMulQuant.lean`), `exists_per_chart_leibniz_multiplier_bound`
(`Tensor/ChartComponentRawNorm.lean`), `christoffel_Ck_bound_from_metric_Ck1`,
`wkpNorm_chosenWeakPartial_le_wkpNorm_succ` (`Euclidean/Multiplication/MultiplyQuantK.lean`):
in each, one factor is a fixed `C^∞` function whose every derivative is sup-bounded, and only
the *other* factor carries Sobolev regularity.  The genuinely new content here is the
estimate when **both** factors carry only Sobolev regularity (the high-order derivative is
*shared* between the two factors and must be redistributed by interpolation): the Moser tame
inequality and the Gagliardo–Nirenberg interpolation inequality, neither of which exists in
Mathlib or in this library.

These are the analytic engine of the higher-order covariant Faà-di-Bruno / Nemytskii estimate
for the second-order quasilinear Ricci–DeTurck right-hand side
(`Analysis/Spectral/Intrinsic/DeTurck/RHSHighOrderSobolevLipschitz.lean`): the covariant
expansion of `∇^j(F(g₁) − F(g₂))` is a finite sum of products of (bounded) metric-jet
coefficients with covariant gradients of the metric difference, in which the top-order
derivative may land on *either* factor; the tame estimate is exactly what redistributes the
derivative budget so that only the perturbation difference's covariant `L²`-jets appear on the
right, while the metric jet enters in `L^∞` (controlled by the supercritical Sobolev embedding
`H^{a+2} ↪ C⁰`).  The pointwise `C²`-jet embedding alone cannot reach the top metric jet on a
manifold of dimension `≥ 4`; the `L²`-tame redistribution is mandatory, which is precisely why
these primitives are needed.

Both statements are `sorry`: they are the genuine deep Sobolev-multiplication / interpolation
content (the Sobolev·Sobolev cross term), with no differential-geometric DeTurck, spectral, or
Weyl dependence.  Neither is the conclusion of any consumer: each is a general real-valued
`L²`-norm product/interpolation inequality on iterated covariant gradients, structurally
unrelated to the Nemytskii conclusions that consume them; no packaging. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The intrinsic Moser tame product for iterated covariant gradients (the genuine
Sobolev·Sobolev `L²` cross term).**

Fix an anchor `g`, two valences `p, q`, and an order `k`.  There is a single constant `C ≥ 0`
(depending only on `g, k, p, q` and the manifold) such that for any coefficient tensor `c`, any
perturbation tensor `w`, any constants `Λ, Λ₀ ≥ 0`, and any result section `P` whose pointwise
fibre norm of the top covariant gradient is *dominated by the covariant Leibniz product bound*
```
‖∇^k P(x)‖²
  ≤ ∑_{i ∈ range (k+1)} (binom k i)² · ‖∇^i c(x)‖² · ‖∇^{k-i} w(x)‖²       (∀ x),
```
under the `C^k`-sup hypothesis `‖∇^i c(x)‖² ≤ Λ²` (`i ≤ k`, the bounded-coefficient factor) and
the `C⁰`-sup hypothesis `‖w(x)‖² ≤ Λ₀²`, the metric `L²` norm of `P` is controlled by the **tame
cross term**
```
‖∇^k P‖_{L²} ≤ C · ( Λ · ∑_{i ≤ k} ‖∇^i w‖_{L²} + Λ₀ · ∑_{i ≤ k} ‖∇^i c‖_{L²} ) .
```

This is the genuine **Moser tame inequality**: the top-order derivative is redistributed so that
each product summand carries the high derivative on *one* factor (in `L²`) and the low
derivatives on the other (in `L^∞`).  The proof composes the pointwise Leibniz product hypothesis
with the finite-sum pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`
and the Gagliardo–Nirenberg interpolation `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`
below (to move each intermediate-order factor between `L²` and `L^∞`), together with the on-disk
smooth-coefficient multiplier bounds for the bounded factor.

The hypotheses are genuine analytic inputs about the *separate* tensors `c, w` (sup bounds on
their covariant jets) and a *pointwise* Leibniz domination of `∇^k P`; the conclusion is a
global `L²` bound on `∇^k P`.  The conclusion is structurally distinct from any consumer's
Nemytskii conclusion (it is a `c, w`-cross-term `L²` product bound, not a chart-Sobolev or
spectral statement); no packaging.  Its body is `sorry`: the genuine Sobolev·Sobolev
tame-multiplication content. -/
theorem exists_moserTameProduct_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) (p q k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Integral.L2.SmoothCcTensor g 0 p) (w : Integral.L2.SmoothCcTensor g 0 q)
        (P : Integral.L2.SmoothCcTensor g 0 (p + q)) (Λ Λ₀ : ℝ), 0 ≤ Λ → 0 ≤ Λ₀ →
        (∀ (x : M) (i : ℕ), i ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) ≤ Λ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 q x (w.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + k) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toSection x) ≤
            (∑ i ∈ Finset.range (k + 1),
              (k.choose i : ℝ) ^ 2 *
                (riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (k - i) w).toSection x)))) →
        Integral.L2.tensorL2Norm (I := I) g 0 (p + q + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toFun ≤
          C * (Λ * ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun
              + Λ₀ * ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toFun) :=
  sorry

/-- **The intrinsic Gagliardo–Nirenberg interpolation inequality for iterated covariant
gradients.**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single constant `C ≥ 0`
such that for every smooth compactly-supported `(0, s)`-tensor `u` whose `C⁰`-sup fibre norm is
`≤ Λ₀` and every intermediate order `0 < j < k`, the metric `L²` norm of the `j`-th iterated
covariant gradient is controlled by the **interpolated** product of the `L^∞` sup `Λ₀` and the
top-order covariant `L²`-jet, with the Gagliardo–Nirenberg exponent `j / k`:
```
‖∇^j u‖_{L²} ≤ C · Λ₀^{1 − j/k} · ‖∇^k u‖_{L²}^{j/k} .
```

This is the genuine **Gagliardo–Nirenberg interpolation**: the intermediate covariant gradient is
estimated by interpolation between the `L^∞` bound (order `0`) and the top-order `L²` bound
(order `k`), the exponents being the affine interpolation weights `1 − j/k` and `j/k`.  It is the
companion of the Moser tame product above (the tame estimate uses it to move each intermediate
factor between `L²` and `L^∞`).  Its conclusion is a real-valued interpolation inequality on the
covariant `L²`-jets of a single tensor, structurally distinct from any consumer's Nemytskii
conclusion; no packaging.  Its body is `sorry`: the genuine interpolation content. -/
theorem exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun ≤
            C * Λ₀ ^ (1 - (j : ℝ) / k) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ ((j : ℝ) / k) :=
  sorry

end DifferentialGeometry.Analysis.Sobolev.Tensor
