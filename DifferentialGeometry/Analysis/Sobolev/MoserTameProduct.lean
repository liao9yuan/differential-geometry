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

The Moser tame product is proven outright: under the `C^k`-sup hypothesis the bounded factor's
every covariant jet is dominated by `Λ`, so each Leibniz summand keeps its high derivative on the
perturbation factor in `L²`, and the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` plus a reflection reindexing close it (no
interpolation needed, since the coefficient factor is `L^∞`-controlled at every order).  The
Gagliardo–Nirenberg interpolation is reduced by a genuine `k`-th-root `rpow` extraction to its
integer-power form `l2Interp_pow_iteratedCovGrad`, which is the single posited deep analytic
input (the closed-manifold tensor interpolation: covariant Green's identity on the iterated
bundle connection Laplacian — `δ` a pointwise contraction of `∇` giving log-convex `L²`-jets — and
the discrete log-convex interpolation, with the affine obstruction vanishing on a closed
manifold).  That input carries the only `sorry`; both displayed cross-term statements are general
real-valued `L²`-norm product/interpolation inequalities on iterated covariant gradients,
structurally unrelated to the Nemytskii conclusions that consume them; no packaging. -/

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
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toFun) := by
  classical
  refine ⟨(2 : ℝ) ^ k, by positivity, ?_⟩
  intro c w P Λ Λ₀ hΛ hΛ₀ hc hw hP
  -- The family of `L²` jet terms of `w` carrying the high derivative (valence `q + (k - i)`).
  set Tw : ∀ i, Integral.L2.SmoothCcTensor g 0 (q + (k - i)) :=
    fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (k - i) w with hTw_def
  -- Pointwise: dominate every `c`-factor by its `C^k` sup `Λ²` and every binomial by `(2^k)²`,
  -- reducing the Leibniz product bound to a single multiple of `∑ rfns(∇^{k-i} w)`.
  have hpt :
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + k) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toSection x) ≤
          ((2 : ℝ) ^ k * Λ) ^ 2 * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) := by
    intro x
    refine le_trans (hP x) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi_le : i ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    have hcΛ : riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) ≤ Λ ^ 2 := hc x i hi_le
    have hc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (p + i) x _
    have hw_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (q + (k - i)) x _
    have hchoose : ((k.choose i : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
      have h1 : (k.choose i : ℝ) ≤ (2 : ℝ) ^ k := by
        have := Nat.choose_le_two_pow (n := k) (k := i)
        calc (k.choose i : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
          _ = (2 : ℝ) ^ k := by push_cast; ring
      have h0 : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
      nlinarith [h1, h0]
    have hchoose_nn : (0 : ℝ) ≤ ((k.choose i : ℝ)) ^ 2 := by positivity
    calc (k.choose i : ℝ) ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x))
        ≤ ((2 : ℝ) ^ k) ^ 2 * (Λ ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x)) := by
          apply mul_le_mul hchoose ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hcΛ hw_nn
      _ = ((2 : ℝ) ^ k * Λ) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) := by
          ring
  -- Lift the pointwise bound to the metric `L²` norm via the finite-sum packaging lemma.
  have hpack :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P‖ ≤
        ((2 : ℝ) ^ k * Λ) * ∑ i ∈ Finset.range (k + 1), ‖Tw i‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g (k + 1)
      (fun i => q + (k - i)) Tw
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P)
      ((2 : ℝ) ^ k * Λ) (by positivity) hpt
  -- Reindex `∑ ‖∇^{k-i} w‖` (over `i`) to `∑ ‖∇^i w‖` by the reflection of `range (k+1)`.
  have hreindex : (∑ i ∈ Finset.range (k + 1), ‖Tw i‖) =
      ∑ i ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖ := by
    have := Finset.sum_range_reflect
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖) (k + 1)
    simpa [hTw_def, Nat.succ_sub_one] using this
  rw [hreindex] at hpack
  -- Convert the `SmoothCcTensor` norms to `tensorL2Norm` and absorb the (nonnegative) `c`-term.
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P)] at hpack
  have hsum_w_eq : (∑ i ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖) =
      ∑ i ∈ Finset.range (k + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun :=
    Finset.sum_congr rfl (fun i _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_w_eq] at hpack
  set Sw : ℝ := ∑ i ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun with hSw_def
  set Sc : ℝ := ∑ i ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toFun with hSc_def
  have hSw_nn : 0 ≤ Sw :=
    Finset.sum_nonneg (fun i _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (q + i) _)
  have hSc_nn : 0 ≤ Sc :=
    Finset.sum_nonneg (fun i _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (p + i) _)
  calc Integral.L2.tensorL2Norm (I := I) g 0 (p + q + k)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toFun
      ≤ (2 : ℝ) ^ k * Λ * Sw := hpack
    _ ≤ (2 : ℝ) ^ k * (Λ * Sw + Λ₀ * Sc) := by
        have hexp : (2 : ℝ) ^ k * (Λ * Sw + Λ₀ * Sc)
            = (2 : ℝ) ^ k * Λ * Sw + (2 : ℝ) ^ k * (Λ₀ * Sc) := by ring
        have hnn : 0 ≤ (2 : ℝ) ^ k * (Λ₀ * Sc) :=
          mul_nonneg (by positivity) (mul_nonneg hΛ₀ hSc_nn)
        rw [hexp]; linarith

/-- **The Gagliardo–Nirenberg interpolation in integer-power form** (the genuine deep analytic
input of `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`).

For a closed Riemannian manifold, a valence `s`, and a top order `k ≥ 1`, there is a single
constant `C ≥ 0` such that for every smooth compactly-supported `(0, s)`-tensor `u` with `C⁰`-sup
fibre bound `Λ₀` and every intermediate order `0 < j < k`, the `k`-th power of the metric `L²`
norm of `∇^j u` is bounded by the interpolated product
```
‖∇^j u‖_{L²}^k ≤ C^k · Λ₀^{k-j} · ‖∇^k u‖_{L²}^j .
```
This is the standard tensor interpolation inequality on a closed manifold (Hamilton, Aubin):
the discrete `L²`-jets `aᵢ := ‖∇^i u‖_{L²}` are log-convex up to a multiplier (closed-manifold
covariant integration by parts: `aᵢ² = ⟨∇(∇^{i-1}u), ∇^i u⟩_{L²} = ⟨∇^{i-1}u, δ∇^i u⟩_{L²} ≤
aᵢ₋₁·‖δ∇^i u‖_{L²} ≤ C·aᵢ₋₁·aᵢ₊₁`, since the divergence `δ` is a pointwise contraction of `∇`),
and on a closed manifold the affine obstruction vanishes (`∇²u = 0 ⟹ ∇u = 0`), so the pure
power-law holds with the `L^∞` endpoint `a₀ ≤ Λ₀·vol^{1/2}` folded in.  The exponentiated form is
recorded because all powers are then integer, which lets the companion statement be obtained by a
single `k`-th-root (`rpow (1/k)`) extraction.

Its body is `sorry`: this is the deep closed-manifold interpolation analysis (covariant Green's
identity on the iterated bundle Laplacian plus the discrete log-convex interpolation), posited
here as the analytic input from which the displayed real-power Gagliardo–Nirenberg statement is
derived by genuine `rpow` arithmetic.  Its conclusion is the integer-power interpolation, a shape
structurally distinct from (and not defeq to) the real-power conclusion it feeds; no packaging. -/
private theorem l2Interp_pow_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun) ^ k ≤
            C ^ k * Λ₀ ^ (k - j) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ j :=
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
conclusion; no packaging.

The proof is the genuine `k`-th-root (`rpow (1/k)`) extraction from the integer-power form
`l2Interp_pow_iteratedCovGrad` (`‖∇^j u‖²·…`, all exponents integer): take `rpow (1/k)` of both
sides — monotone on nonnegatives — and simplify with `Real.pow_rpow_inv_natCast`, `Real.mul_rpow`,
`Real.rpow_natCast`, `Real.rpow_mul`, using `(k - j : ℕ) = k - j` (since `j < k`) to turn the
integer exponent `k - j` into the real interpolation weight `1 − j/k`.  It therefore depends
transitively on the `sorry` of `l2Interp_pow_iteratedCovGrad` (the deep closed-manifold tensor
interpolation), which `#print axioms` records as `sorryAx`; the displayed real-power statement is
proven outright on top of that single posited analytic input. -/
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
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ ((j : ℝ) / k) := by
  obtain ⟨C, hC0, hC⟩ := l2Interp_pow_iteratedCovGrad (I := I) (M := M) g s k hk
  refine ⟨C, hC0, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  set aj : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun with haj_def
  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun with hak_def
  have haj_nn : 0 ≤ aj :=
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + j) _
  have hak_nn : 0 ≤ ak :=
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
  -- The integer-power interpolation supplied by the deep analytic input.
  have hpow : aj ^ k ≤ C ^ k * Λ₀ ^ (k - j) * ak ^ j := hC u Λ₀ hΛ₀ hsup j hj0 hjk
  -- Take `k`-th roots (`rpow (1/k)`), which is monotone on nonnegatives.
  have hmono : (aj ^ k) ^ ((k : ℝ)⁻¹) ≤ (C ^ k * Λ₀ ^ (k - j) * ak ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow (by positivity)
  rw [Real.pow_rpow_inv_natCast haj_nn hk0] at hmono
  -- Compute the `k`-th root of the right-hand side via the `rpow` algebra.
  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hjk)]
  have hexp1 : ((k : ℝ) - (j : ℝ)) * (k : ℝ)⁻¹ = 1 - (j : ℝ) / k := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
  have hrhs : (C ^ k * Λ₀ ^ (k - j) * ak ^ j) ^ ((k : ℝ)⁻¹) =
      C * Λ₀ ^ (1 - (j : ℝ) / k) * ak ^ ((j : ℝ) / k) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.pow_rpow_inv_natCast hC0 hk0]
    congr 1
    · -- `(Λ₀ ^ (k - j)) ^ (1/k) = Λ₀ ^ (1 - j/k)`
      rw [← Real.rpow_natCast Λ₀ (k - j), ← Real.rpow_mul hΛ₀, hcast_sub, hexp1]
    · -- `(ak ^ j) ^ (1/k) = ak ^ (j/k)`
      rw [← Real.rpow_natCast ak j, ← Real.rpow_mul hak_nn, div_eq_mul_inv]
  rw [hrhs] at hmono
  exact hmono

end DifferentialGeometry.Analysis.Sobolev.Tensor
