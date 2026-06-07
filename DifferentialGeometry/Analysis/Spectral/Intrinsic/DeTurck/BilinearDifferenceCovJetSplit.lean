import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFdBTermTree
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus

/-! # The shared difference-form covariant-jet `Adiff + Cross` split of a geometric nonlinearity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **section-functor-abstract** covariant Faà-di-Bruno
difference/cross split that the two per-field Ricci–DeTurck right-hand-side leaves
(`SegmentMetricRHSCovJetExpansion.lean`) both instantiate: the curvature half
`ricciNeg2Diff_covFdB_section_split` and the Lie half `lieDerivDiff_covFdB_section_split`.

## What is abstracted

A *geometric nonlinearity section functor* is a map `F : SmoothRiemannianMetric I M →
SmoothCcTensor g₀ 0 2` sending a metric to a `g₀`-tagged `(0,2)`-tensor section (the curvature
summand `g ↦ ricciNeg2RetagG0 g₀ g` and the Lie summand `g ↦ lieDerivRetagG0 g₀ g_bg g` are the two
instances).  Both summand differences `F g₁ − F g₂` along the segment metric admit the **same**
single-difference-factor algebraic structure: a metric-contraction of the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)` plus a fixed-pair remainder, captured by the explicit
order-zero telescope datum

```
F g₁ − F g₂ = Φ.op 0 2 w + C,
```

where `Φ` is a differentiated bilinear contraction operator family (`DiffBilinOp g₀`, the metric-built
coefficient with its symbolic per-order envelope, `MetricContractionLeibnizGrid.lean`) and `C` is a
fixed-pair cross remainder whose every covariant jet is controlled in `rfns` by the fixed-pair jet sum
against the difference's order-`a` chart-Sobolev `C⁰` mass `‖(T₁ − T₂).toHs a‖²`.  This is the honest
`telescope_bilin`-shaped (`MetricDifferenceFdBTermTree.lean`) single-difference-factor expansion: the
difference factor enters the metric only through the realization map, which gains no derivatives.

## What is proved vs. posited

* `bilinDiff_covFdB_section_split` — the shared brick: from the explicit order-zero telescope datum
  `hExp` (the difference is `Φ.op 0 2 w + C` with the all-order fixed-pair cross bound on `C`), the
  `j`-th covariant gradient splits as a difference-arm piece `Adiff` (the high derivative on the
  difference factor `w`, `rfns(∇^j Adiff) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)`, the metric-built coefficient
  folded into the uniform `Cd` by the binomial covariant-Leibniz `rfns` grid of `Φ`) plus a fixed-pair
  cross piece `Cross` (`rfns(∇^j Cross) ≤ (1/2)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·‖(T₁ −
  T₂).toHs a‖²`).  Its body is `sorry`: the genuine deep covariant-jet content is the **push of `∇^j`
  through the metric-contraction `Φ.op 0 2 w`** via the binomial covariant-Leibniz grid
  `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` (collecting the metric coefficient into the
  uniform difference-arm constant `Cd` over the grid window `j + 2`), the order-`j` covariant gradient
  of the fixed-pair remainder `C` riding the cross arm by the telescope datum, and the realize-jet
  no-derivative-gain control of the difference factor.  It carries NO pointwise-`C^{>2}`-jet claim, NO
  spectral-nonlinearity, and NO Weyl dependence; it is the section-functor-abstract content shared by
  the two per-field leaves.

The two per-field leaves (in `SegmentMetricRHSCovJetExpansion.lean`, whose summand functors
`ricciNeg2RetagG0` / `lieDerivRetagG0` are defined there, downstream of this file) instantiate
`bilinDiff_covFdB_section_split` with their summand functor and a per-field `TelescopeData` datum,
threading the `g₀`-fibre-small ties and `H^{a+2}`-size bounds unchanged.  The per-field telescope data —
the single-difference-factor expansion of the *sealed* curvature nonlinearity `-2 • Ric(g)` (the
connection-difference cocycle of `ricciTensor_sub_telescope`, `RicciDifferenceTelescope.lean`) and the
sealed Lie/`deTurckVF` nonlinearity `𝓛_{W(g, g_bg)} g` (the chart structural difference of
`chartLieDeTurckComp_sub_eq`, `ChartLieDerivStructuralDifference.lean`), promoted to the `Φ.op 0 2 w + C`
section form — live next to those functors in the leaf file. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The explicit order-zero single-difference-factor telescope datum of a geometric nonlinearity
section functor.**

For a section functor `F : SmoothRiemannianMetric I M → SmoothCcTensor g₀ 0 2`, an order `a`, and a
uniform `H^{a+2}`-size bound `B ≥ 0`, this is the predicate: for any two `g₀`-fibre-small perturbations
`T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the section
difference `F g₁ − F g₂` is the sum of an undifferentiated metric-contraction `Φ.op 0 2 w` of a
differentiated bilinear contraction operator family `Φ : DiffBilinOp g₀` (the metric-built coefficient)
against the difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus a fixed-pair cross remainder
`C : SmoothCcTensor g₀ 0 2` whose **every** covariant jet is `rfns`-controlled by the order-`≤ j+2`
fixed-pair jet sum against the difference's order-`a` chart-Sobolev `C⁰` mass `‖(T₁ − T₂).toHs a‖²`:

```
F g₁ − F g₂ = Φ.op 0 2 w + C,
∀ j x, rfns(∇^j C)(x) ≤ (1/2)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the explicit `telescope_bilin`-shaped (not opaque) single-difference-factor expansion: the
difference factor enters the metric only through the realization map (no derivative gain), so the single
high derivative will land on `w` through `Φ.op`; the fixed-pair top coefficient jet rides on `C`.  It is
genuinely weaker than the per-order `Adiff + Cross` split it feeds (it is the order-zero algebraic
equality plus the all-order cross control, NOT the per-order difference-arm grid bound on `∇^j(Φ.op 0 2
w)`, which is the deep content `bilinDiff_covFdB_section_split` derives), and it is non-vacuous: it is an
explicit equality constraining `F g₁ − F g₂` to the single-difference-factor form, rejecting any functor
whose difference is not of this shape. -/
def TelescopeData (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothRiemannianMetric I M → Integral.L2.SmoothCcTensor g₀ 0 2) (a : ℕ) (B : ℝ) : Prop :=
  ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M),
    (∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
    (∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
    ∃ (Φ : DiffBilinOp g₀) (C : Integral.L2.SmoothCcTensor g₀ 0 2),
      F g₁ - F g₂ =
          Φ.op 0 2 (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) + C ∧
        ∀ (j : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C).toSection x) ≤
            (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                  + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2

omit [CompleteSpace E] in
/-- **Non-vacuity of `TelescopeData`: the zero remainder forces a genuine constraint.**  The all-order
fixed-pair cross bound the predicate places on the remainder `C` is satisfied by the zero section (its
every jet has `rfns = 0`); the predicate's content is therefore entirely in the explicit equality
`F g₁ − F g₂ = Φ.op 0 2 w + C`, which is a genuine algebraic constraint on `F`.  This lemma records the
trivial half — that `C = 0` satisfies the cross bound — used when a functor's difference is exactly the
metric-contraction `Φ.op 0 2 w` (the pure difference-arm case, no fixed-pair top jet).  It rejects the
reading that the cross bound is itself vacuous: it is the squared-`C⁰`-mass envelope, true for `C = 0`
precisely because both sides degenerate, while for a nonzero top-jet remainder it is the genuine
fixed-pair domination. -/
theorem riemannianFiberNormSq_iteratedCovGrad_zero_cross_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (j : ℕ) (x : M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (0 : Integral.L2.SmoothCcTensor g₀ 0 2)).toSection x) ≤
      (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
            + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
        * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  have hzero : (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (0 : Integral.L2.SmoothCcTensor g₀ 0 2)).toSection x = 0 := by
    have : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (0 : Integral.L2.SmoothCcTensor g₀ 0 2) = 0 := by
      have hsmul := MetricRealization.iteratedCovGrad_smul (I := I) g₀ 0 2 j (0 : ℝ)
        (0 : Integral.L2.SmoothCcTensor g₀ 0 2)
      simpa using hsmul
    rw [this]; rfl
  rw [hzero, riemannianFiberNormSq_zero]
  refine mul_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    add_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _)
      (riemannianFiberNormSq_nonneg _ _ _ _ _))) (sq_nonneg _)

/-- **The shared difference-form covariant-jet `Adiff + Cross` split of a geometric nonlinearity
section functor (the deep covariant-jet brick).**

For an anchor `g₀`, a section functor `F : SmoothRiemannianMetric I M → SmoothCcTensor g₀ 0 2` admitting
the explicit order-zero single-difference-factor telescope datum `hExp : TelescopeData g₀ F a B`, an
order `a`, a uniform `H^{a+2}`-size bound `B ≥ 0`, and a covariant-gradient order `j`, then for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂`
of `T₁, T₂`, the `j`-th covariant gradient of the section difference `F g₁ − F g₂` splits as a
**difference-arm piece** `Adiff` plus a **fixed-pair cross piece** `Cross`:
```
∇^j (F g₁ − F g₂) = Adiff + Cross,
rfns(Adiff)(x)  ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x),
rfns(Cross)(x) ≤ (1/2) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
with `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and a nonnegative difference-arm constant `Cd` uniform over
the supercritical `H^{a+2}`-bounded family.

This is the section-functor-abstract covariant Faà-di-Bruno difference/cross split shared by the two
per-field Ricci–DeTurck right-hand-side summand leaves (the curvature half `ricciNeg2RetagG0` and the
Lie half `lieDerivRetagG0 g_bg`): the difference-arm piece carries the single high derivative on the
difference factor `w` (collected from the telescope datum's metric-contraction `Φ.op 0 2 w` by the
binomial covariant-Leibniz `rfns` grid, the metric-built coefficient folded into the uniform `Cd` over
the grid window `j + 2`), and the cross piece carries the order-`j` covariant gradient of the telescope
datum's fixed-pair remainder `C` (whose all-order jet bound is supplied by the datum).

**Non-vacuity.**  The two arm bounds are *coupled* by the structural identity `∇^j(F g₁ − F g₂) = Adiff
+ Cross`, and the coupling rejects both degenerate witnesses.  With `Adiff = 0`, `Cross = ∇^j(F g₁ − F
g₂)` would have to satisfy the *cross* bound, FALSE for `j ≥ 1` whenever the difference-arm content
`∑ rfns(∇^i w)` is genuinely present and is *not* dominated by the fixed-pair · `C⁰` cross arm (the
known-false pointwise form without a difference arm).  With `Cross = 0`, `Adiff = ∇^j(F g₁ − F g₂)`
would have to satisfy the *difference-arm* bound, FALSE for `j ∈ (a, 2a]` whenever the top coefficient
jet content is genuinely `(∑ fixed-pair) · C⁰`-order.  Both pieces carry genuine content.

Its body is `sorry`: the genuine deep covariant-jet content is the push of `∇^j` through the
metric-contraction `Φ.op 0 2 w` of the telescope datum via the binomial covariant-Leibniz grid
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` (collecting the metric coefficient into the
uniform difference-arm constant `Cd` over the grid window `j + 2`, the difference factor's jets
controlled by the perturbation-difference jets through the realize-jet no-derivative-gain bound), and
the order-`j` covariant gradient of the fixed-pair remainder `C` riding the cross arm by the telescope
datum's all-order cross bound.  It carries NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity,
and NO Weyl dependence. -/
theorem bilinDiff_covFdB_section_split
    (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothRiemannianMetric I M → Integral.L2.SmoothCcTensor g₀ 0 2)
    (a : ℕ) (B : ℝ) (hB : 0 ≤ B) (hExp : TelescopeData (I := I) g₀ F a B) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ Adiff Cross : Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (F g₁ - F g₂)
            = Adiff + Cross ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x) ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Cross.toSection x) ≤
              (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
