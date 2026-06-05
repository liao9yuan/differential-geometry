import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder

/-! # The covariant Faà-di-Bruno term tree of a metric-difference contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, the covariant Faà-di-Bruno expansion of the second-order Ricci–DeTurck
right-hand-side **difference** `F(g₁) − F(g₂)` along the metric-difference family
`gₖ = g₀ + bilin(realizeSymm Tₖ)` reduces — by the covariant fundamental theorem of calculus and
the covariant product/chain rule — to a finite sum of *single-difference-factor terms*: each a
contracted product of a metric-built coefficient (a jet of `g₁`/`g₂`, organised as a fibrewise
contraction operator) with **exactly one** difference factor `w := realizeSymm (T₁ − T₂)` or a low
covariant jet of it.

This file builds the **reusable term-tree subsystem** that turns each such term into a
Moser-tame `L²` bound, plus the section-level algebraic primitives that produce the terms.  It does
*not* expand the (sealed) curvature/Lie objects `ricciTensor`, `lieDerivMetric` algebraically — that
expansion is the deep analytic content carried by the per-field posits in
`SegmentMetricRHSCovJetExpansion`.  It supplies the floor those posits stand on:

## The three sub-pieces (each a genuine reusable lemma cluster)

* **(b) Section-level product-difference telescoping.**  `telescope_two` /
  `telescope_three`: the pure `SmoothCcTensor`-algebra identities
  `A₁ + B₁ − (A₂ + B₂) = (A₁ − A₂) + (B₁ − B₂)` and the three-summand version, lifted to the
  retag/section level, that split a sum-of-terms difference into per-term differences.  These are
  the algebra by which `Σ_α term(g₁) − Σ_α term(g₂) = Σ_α (term(g₁) − term(g₂))`.

* **(c) The per-term `DiffBilinOp` → Moser-tame `hP` → `L²` feeder.**  A *single-difference-factor
  term* is an undifferentiated metric-contraction `Φ.op 0 r w` of a `DiffBilinOp Φ` (the
  metric-built coefficient family, with its per-order/per-rank envelope `kappa` kept **symbolic** —
  the coefficient jets of order `> 2` are *not* pointwise bounded over the supercritical family, so
  the envelope is carried, never sup-evaluated) against a difference factor `w`.
  `fdBTerm_iteratedCovGrad_l2Norm_le` proves outright, from the binomial covariant-Leibniz `rfns`
  grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` and the finite-sum pointwise-to-`L²`
  packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`, the per-term `L²` bound
  `‖∇^j(Φ.op 0 r w)‖_{L²} ≤ C r j · ∑_{q ≤ j} ‖∇^q w‖_{L²}` — exactly the `Σ‖∇^q w‖` shape the
  Moser-tame product's `Λ`-arm consumes, with the high derivative on the difference factor and the
  coefficient kept in the (symbolic) constant.

* **(a)/(difference-factor) The realize-difference covariant `L²`-jet bound.**  The difference factor
  enters the metric through the realization map, which gains no derivatives:
  `realizeSymm_iteratedCovGrad_l2Norm_le_jetSum` lifts the proven pointwise `rfns` realize-jet bound
  to the metric `L²` norm, so each `∇^i w = ∇^i (realizeSymm (T₁ − T₂))` is `L²`-controlled by the
  `≤ i`-order covariant gradients of the perturbation difference `T₁ − T₂` — the single high
  derivative landing on the perturbation factor.

## How the per-field posits assemble over this floor

A follow-up proves `exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le` (and the Lie analogue) by:
(i) writing the curvature-summand difference as a finite sum of single-difference-factor terms via
the covariant-FdB expansion of `Ric` (the deep step; the term coefficients are `DiffBilinOp`s of the
metric jet), and splitting the sum-difference with `telescope_*`; (ii) bounding each term's `L²` jet
with `fdBTerm_iteratedCovGrad_l2Norm_le`, the high derivative on `w = realizeSymm (T₁ − T₂)`;
(iii) folding the (symbolic, order-`> 2`) coefficient mass into the `‖(T₁ − T₂).toHs a‖`
`C⁰`-redistribution term through the Moser-tame product and the supercritical embedding, and the
realize-difference jets into `∑_{i ≤ j+2} ‖∇^i (T₁ − T₂)‖` via
`realizeSymm_iteratedCovGrad_l2Norm_le_jetSum`.

All conclusions here are real-valued `L²`/`rfns` inequalities and section-level algebra, structurally
unrelated to the Nemytskii conclusions that consume them; no packaging, no `sorry`. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### (b) Section-level product-difference telescoping

The pure `SmoothCcTensor`-algebra identities by which a sum of metric-contraction terms, differenced
between `g₁` and `g₂`, becomes a sum of per-term differences.  These are exactly the (commutative,
associative) additive-group telescopes; they are stated at `SmoothCcTensor` level so the
covariant-FdB term sum can be split term-by-term without touching any geometry.  The same statements
hold verbatim for the `g₀`-retagged sections (an additive-group homomorphism on the underlying
`toSection`). -/

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [CompleteSpace E] in
/-- **Two-factor product-difference telescope.**  The difference of two two-summand sections is the
sum of the per-summand differences:
`(A₁ + B₁) − (A₂ + B₂) = (A₁ − A₂) + (B₁ − B₂)`.  Pure additive-group algebra (`abel`); the load it
carries is splitting `(Ric + Lie)(g₁) − (Ric + Lie)(g₂)` into `(Ric(g₁) − Ric(g₂)) + (Lie(g₁) −
Lie(g₂))` and, inside each half, a covariant-FdB term sum into per-term differences. -/
theorem telescope_two {g₀ : SmoothRiemannianMetric I M} {r : ℕ}
    (A₁ B₁ A₂ B₂ : SmoothCcTensor g₀ 0 r) :
    (A₁ + B₁) - (A₂ + B₂) = (A₁ - A₂) + (B₁ - B₂) := by
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [CompleteSpace E] in
/-- **Three-factor product-difference telescope.**  The three-summand version of `telescope_two`:
`(A₁ + B₁ + C₁) − (A₂ + B₂ + C₂) = (A₁ − A₂) + (B₁ − B₂) + (C₁ − C₂)`.  Pure additive-group algebra;
splits the `g⁻¹·∂²g + g⁻¹·g⁻¹·∂g·∂g + …` style three-term contraction difference into per-term
differences (each then carrying a single difference factor after the multi-factor telescope below). -/
theorem telescope_three {g₀ : SmoothRiemannianMetric I M} {r : ℕ}
    (A₁ B₁ C₁ A₂ B₂ C₂ : SmoothCcTensor g₀ 0 r) :
    (A₁ + B₁ + C₁) - (A₂ + B₂ + C₂) = (A₁ - A₂) + (B₁ - B₂) + (C₁ - C₂) := by
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
/-- **`Finset`-sum product-difference telescope.**  The difference of two `Finset`-indexed sums of
sections is the sum of the per-index differences:
`(∑ a ∈ s, F a) − (∑ a ∈ s, G a) = ∑ a ∈ s, (F a − G a)`.  This is the `n`-term covariant-FdB telescope
the curvature/Lie expansion uses: the deep step writes each summand difference `Ric(g₁) − Ric(g₂) =
∑_α term α g₁ − ∑_α term α g₂`, and this lemma turns it into `∑_α (term α g₁ − term α g₂)`, one
single-difference-factor term per `α`. -/
theorem telescope_finsetSum {g₀ : SmoothRiemannianMetric I M} {r : ℕ} {ι : Type*}
    (s : Finset ι) (F G : ι → SmoothCcTensor g₀ 0 r) :
    (∑ a ∈ s, F a) - (∑ a ∈ s, G a) = ∑ a ∈ s, (F a - G a) := by
  rw [Finset.sum_sub_distrib]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [CompleteSpace E] in
/-- **Single-step bilinear product-difference telescope (the `AB`-telescope).**  For any bilinear
section product `mul : SmoothCcTensor g₀ 0 r → SmoothCcTensor g₀ 0 r' → SmoothCcTensor g₀ 0 r''`
(additive in *each* argument — the hypotheses `hL`, `hR`), the two-factor product telescopes onto its
two single-difference-factor pieces:
`mul A₁ B₁ − mul A₂ B₂ = mul (A₁ − A₂) B₁ + mul A₂ (B₁ − B₂)`.
This is the structural identity that puts a single difference factor on each term; iterating it on a
multi-factor contraction (`g⁻¹·g⁻¹·∂g·∂g`) peels the factors one at a time, each peel landing one
difference factor.  Proved by additivity of `mul` in each slot and additive-group cancellation. -/
theorem telescope_bilin {g₀ : SmoothRiemannianMetric I M} {r r' r'' : ℕ}
    (mul : SmoothCcTensor g₀ 0 r → SmoothCcTensor g₀ 0 r' → SmoothCcTensor g₀ 0 r'')
    (hL : ∀ a a' b, mul (a - a') b = mul a b - mul a' b)
    (hR : ∀ a b b', mul a (b - b') = mul a b - mul a b')
    (A₁ A₂ : SmoothCcTensor g₀ 0 r) (B₁ B₂ : SmoothCcTensor g₀ 0 r') :
    mul A₁ B₁ - mul A₂ B₂ = mul (A₁ - A₂) B₁ + mul A₂ (B₁ - B₂) := by
  rw [hL A₁ A₂ B₁, hR A₂ B₁ B₂]
  abel

/-! ### (c) The per-term `DiffBilinOp` → Moser-tame `L²` feeder

A *single-difference-factor term* of the covariant Faà-di-Bruno expansion is the undifferentiated
metric-contraction `Φ.op 0 r w` of a `DiffBilinOp Φ` (the metric-built coefficient family, the
fibrewise-linear non-parallel contraction of the metric jet, with its per-order/per-rank fibre
envelope `kappa` carried symbolically) against a difference factor `w`.  The following lemma is the
genuine bridge from the binomial covariant-Leibniz `rfns` grid to the metric `L²` norm of one term —
the per-term primitive a follow-up applies to each FdB term. -/

/-- **The per-term covariant `L²` bound for a single-difference-factor metric-contraction term.**

For a `DiffBilinOp Φ` (the metric-built coefficient family) there is a single nonnegative per-rank,
per-order constant `C : ℕ → ℕ → ℝ` such that for every base rank `r`, difference factor `w`, and
covariant-gradient order `j`, the metric `L²` norm of the `j`-th covariant gradient of the
single-difference-factor term `Φ.op 0 r w` is dominated by the constant times the sum of the
`≤ j`-order covariant `L²`-jets of the difference factor:
```
‖∇^j (Φ.op 0 r w)‖_{L²} ≤ C r j · ∑_{q ≤ j} ‖∇^q w‖_{L²}.
```

This is the exact `Σ_{q ≤ j} ‖∇^q w‖` shape the Moser-tame product's `Λ`-arm
(`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`) consumes — the high derivative on the
difference factor `w`, the metric-built coefficient absorbed into the (symbolic, order-uniform)
constant `C r j = √(4^j · gridWindowSum kappa 0 r j)`.  Proved outright by composing the binomial
covariant-Leibniz `rfns` single-sum grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`
(`rfns(∇^j(op 0 r w))(x) ≤ (4^j · gridWindowSum kappa 0 r j) · ∑_{q ≤ j} rfns(∇^q w)(x)`) with the
finite-sum pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` (whose
input is the squared constant times the `rfns` sum, so the packaging constant is the square root of
the grid constant).  No posit: the deep covariant-Leibniz content lives in the grid, which is itself
`sorry`-free; this lemma is the `√`-extraction + `L²` packaging. -/
theorem fdBTerm_iteratedCovGrad_l2Norm_le {g₀ : SmoothRiemannianMetric I M}
    (Φ : DiffBilinOp g₀) :
    ∃ C : ℕ → ℕ → ℝ, (∀ r j, 0 ≤ C r j) ∧
      ∀ (r : ℕ) (w : SmoothCcTensor g₀ 0 r) (j : ℕ),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (r + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r j (Φ.op 0 r w)).toFun ≤
          C r j * ∑ q ∈ Finset.range (j + 1),
            Integral.L2.tensorL2Norm (I := I) g₀ 0 (r + q)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w).toFun := by
  classical
  -- The single-sum collapse of the binomial covariant-Leibniz `rfns` grid: `rfns(∇^j(op 0 r w))(x)
  -- ≤ G r j · ∑_{q ≤ j} rfns(∇^q w)(x)` with `G r j := 4^j · gridWindowSum kappa 0 r j ≥ 0`.
  obtain ⟨G, hG_nn, hG⟩ := Φ.exists_rfns_iteratedCovGrad_singleSum_le
  -- The `L²`-packaging constant is the square root of the (nonnegative) `rfns` grid constant.
  refine ⟨fun r j => Real.sqrt (G r j), fun r j => Real.sqrt_nonneg _, fun r w j => ?_⟩
  -- Reduce to `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`, whose pointwise hypothesis is
  -- `rfns(Curv)(x) ≤ C² · ∑ rfns(T_i)(x)`: take `C := √(G r j)`, `T q := ∇^q w`, `Curv := ∇^j(op 0 r w)`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r j (Φ.op 0 r w)).toSection x) ≤
        (Real.sqrt (G r j)) ^ 2 *
          ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + q) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w).toSection x) := by
    intro x
    rw [Real.sq_sqrt (hG_nn r j)]
    exact hG r w j x
  -- The packaging lemma: `‖Curv‖ ≤ C · ∑ ‖T_i‖`, with `T_i = ∇^q w` at valence `r + q`.
  have hpack :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r j (Φ.op 0 r w)‖ ≤
        Real.sqrt (G r j) *
          ∑ q ∈ Finset.range (j + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀ (j + 1)
      (fun q => r + q)
      (fun q => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r j (Φ.op 0 r w))
      (Real.sqrt (G r j)) (Real.sqrt_nonneg _) hpt
  -- Convert the `SmoothCcTensor` norms to `tensorL2Norm` on both sides.
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r j (Φ.op 0 r w))] at hpack
  have hsum_eq : (∑ q ∈ Finset.range (j + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w‖) =
      ∑ q ∈ Finset.range (j + 1),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (r + q)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 r q w).toFun :=
    Finset.sum_congr rfl (fun q _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_eq] at hpack
  exact hpack

/-! ### The realize-difference covariant `L²`-jet bound (the difference-factor control)

The covariant-FdB difference factor is `w = realizeSymm (T₁ − T₂)`: the perturbation difference
enters the metric through the realization map, which gains no derivatives.  The following lemma lifts
the pointwise `rfns` realize-jet bound to the metric `L²` norm, so each covariant `L²`-jet of the
difference factor is controlled by the `≤`-order covariant `L²`-jets of the perturbation difference
`S := T₁ − T₂` — the `∑_{i ≤ j+2} ‖∇^i (T₁ − T₂)‖` shape the per-field posit's right-hand side
records.

The pointwise `rfns` bound is derived **inside the realization layer** (the half-sum decomposition
`realizeSymm S = ½ S + ½ flip S` with the slot-swap fibre isometry
`flipCcTensor_iteratedCovGrad_norm_eq`, giving the uniform `‖·‖`-realize constant `1`), so the term-
tree subsystem depends only on `RealizedCovGradJetGeneralOrder`, never on the downstream consumer
file — keeping it importable *by* that consumer without a cycle. -/

omit [BoundarylessManifold I M] in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`l` installed-bundle fibre norm equals the square root of `rfns`.**  Under the
installed Riemannian-bundle instance, the section-value fibre norm of the order-`l` covariant gradient
of a `SmoothCcTensor` equals `√(rfns …)`. -/
private theorem norm_iteratedCovGrad_eq_sqrt_rfns (g₀ : SmoothRiemannianMetric I M) (l : ℕ)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x‖) =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) := by
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M)
    g₀ 0 (2 + l) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)]
  exact Integral.Connection.norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`i` realize-jet `rfns` domination, with the explicit uniform constant `i + 1`.**

For every order `i`, base point `x`, and smooth compactly-supported `(0,2)`-tensor `S`,
```
rfns(∇^i (realizeSymm S))(x) ≤ (i + 1) · ∑_{l ≤ i} rfns(∇^l S)(x).
```
The uniform `‖·‖` realize bound with constant `1` — `‖∇^i (realizeSymm S)(x)‖ ≤ ‖∇^i S(x)‖ ≤
∑_{l ≤ i} ‖∇^l S(x)‖`, from the half-sum decomposition `realizeSymm S = ½ S + ½ flip S` and the
slot-swap fibre isometry `flipCcTensor_iteratedCovGrad_norm_eq` — squared with Cauchy–Schwarz
(`(∑ aₗ)² ≤ (i + 1) · ∑ aₗ²`) and `rfns = ‖·‖²` under the installed instance gives the constant
`i + 1`.  Derived solely from the realization layer; no posit. -/
private theorem realizeSymm_iteratedCovGrad_rfns_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ S)).toSection x) ≤
      (i + 1 : ℝ) * ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x) := by
  classical
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
  -- Per-order installed fibre norms `aₗ := ‖∇^l S(x)‖`, realize-jet norm `B := ‖∇^i(realizeSymm S)(x)‖`.
  set a : ℕ → ℝ := fun l =>
      (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x‖) with ha_def
  have ha_nn : ∀ l, 0 ≤ a l := by
    intro l; rw [ha_def]
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    exact norm_nonneg _
  set B : ℝ := ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
      (realizeSymmCcTensor (I := I) g₀ S)).toSection x‖ with hB_def
  have hB_nn : 0 ≤ B := norm_nonneg _
  -- Uniform `‖·‖` realize bound with constant `1`: `B = ‖∇^i(½ S + ½ flip S)‖ ≤ ½‖∇^i S‖ + ½‖∇^i flip S‖
  -- = ‖∇^i S‖ = a i ≤ ∑_{l ≤ i} aₗ` (the slot swap is a fibre isometry of every `∇^i`).
  have hflip_norm := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ S i x
  have hdecomp :
      PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ S) =
        (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ S) := by
    rw [realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      MetricRealization.iteratedCovGrad_smul, MetricRealization.iteratedCovGrad_smul]
  have hB_le_ai : B ≤ a i := by
    rw [hB_def, ha_def]
    change ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ S)).toSection x‖ ≤
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S).toSection x‖
    rw [hdecomp]
    rw [show ((1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ S)).toSection x =
        (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S).toSection x +
          (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ S)).toSection x from by
      rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
        SmoothCcTensor.toSection_smul]; rfl]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [hflip_norm]
  have hai_le_sum : a i ≤ ∑ l ∈ Finset.range (i + 1), a l :=
    Finset.single_le_sum (fun l _ => ha_nn l) (Finset.mem_range.mpr (Nat.lt_succ_self i))
  have hB_le_sum : B ≤ ∑ l ∈ Finset.range (i + 1), a l := le_trans hB_le_ai hai_le_sum
  -- `rfns(·) = ‖·‖²` (installed instance), via the `sqrt`-bridge squared.
  have hrfns_eq_sq : ∀ (l : ℕ) (T : Integral.L2.SmoothCcTensor g₀ 0 2),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) =
        (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x‖) ^ 2 := by
    intro l T
    rw [norm_iteratedCovGrad_eq_sqrt_rfns (I := I) (M := M) g₀ l T x]
    rw [Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)]
  rw [hrfns_eq_sq i (realizeSymmCcTensor (I := I) g₀ S)]
  rw [show (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ S)).toSection x‖) = B from rfl]
  have hsum_rfns_eq : (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x)) =
      ∑ l ∈ Finset.range (i + 1), a l ^ 2 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hrfns_eq_sq l S, ha_def]
  rw [hsum_rfns_eq]
  -- `B² ≤ (∑ aₗ)² ≤ (i + 1) · ∑ aₗ²` via Cauchy–Schwarz.
  have hBsq : B ^ 2 ≤ (∑ l ∈ Finset.range (i + 1), a l) ^ 2 :=
    pow_le_pow_left₀ hB_nn hB_le_sum 2
  have hCS : (∑ l ∈ Finset.range (i + 1), a l) ^ 2 ≤
      (Finset.range (i + 1)).card * ∑ l ∈ Finset.range (i + 1), a l ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hCS
  calc B ^ 2 ≤ (∑ l ∈ Finset.range (i + 1), a l) ^ 2 := hBsq
    _ ≤ ((i + 1 : ℕ) : ℝ) * ∑ l ∈ Finset.range (i + 1), a l ^ 2 := hCS
    _ = (i + 1 : ℝ) * ∑ l ∈ Finset.range (i + 1), a l ^ 2 := by push_cast; ring

/-- **The order-`i` realize-jet metric-`L²` bound for the metric-realization map.**

For every order `i` there is a single nonnegative constant `C` (namely `√(i + 1)`) such that for every
smooth compactly-supported `(0,2)`-tensor `S`, the metric `L²` norm of the order-`i` covariant
gradient of the realized symmetric tensor `realizeSymmCcTensor g₀ S` is dominated by `C` times the sum
of the metric `L²` norms of the order-`≤ i` covariant gradients of `S`:
```
‖∇^i (realizeSymm S)‖_{L²} ≤ C · ∑_{l ≤ i} ‖∇^l S‖_{L²}.
```

This is the `L²` companion of the pointwise `rfns` realize-jet bound
`realizeSymm_iteratedCovGrad_rfns_le_jetSum` (constant `i + 1`).  It is the structural step by which
the covariant-FdB difference factor `w = realizeSymm (T₁ − T₂)` has its covariant `L²`-jets controlled
by the perturbation difference `T₁ − T₂`'s covariant `L²`-jets — the single high derivative landing on
the perturbation factor.  Proved outright by the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` over the squared realize-jet `rfns` bound; no
posit. -/
theorem realizeSymm_iteratedCovGrad_l2Norm_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 2),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ S)).toFun ≤
          C * ∑ l ∈ Finset.range (i + 1),
            Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + l)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toFun := by
  classical
  refine ⟨Real.sqrt (i + 1), Real.sqrt_nonneg _, fun S => ?_⟩
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ S)).toSection x) ≤
        (Real.sqrt (i + 1)) ^ 2 *
          ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x) := by
    intro x
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (i + 1 : ℝ))]
    exact realizeSymm_iteratedCovGrad_rfns_le_jetSum (I := I) (M := M) g₀ i S x
  have hpack :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ S)‖ ≤
        Real.sqrt (i + 1) *
          ∑ l ∈ Finset.range (i + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀ (i + 1)
      (fun l => 2 + l)
      (fun l => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ S))
      (Real.sqrt (i + 1)) (Real.sqrt_nonneg _) hpt
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ S))] at hpack
  have hsum_eq : (∑ l ∈ Finset.range (i + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S‖) =
      ∑ l ∈ Finset.range (i + 1),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + l)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toFun :=
    Finset.sum_congr rfl (fun l _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_eq] at hpack
  exact hpack

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
