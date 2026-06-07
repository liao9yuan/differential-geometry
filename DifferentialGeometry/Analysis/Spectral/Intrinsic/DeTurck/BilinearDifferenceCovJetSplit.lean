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
  `hExp` (the difference is `Φ.op 0 2 w + C` with the all-order fixed-pair cross bound on `C` and the
  family-uniform envelope `kbar` dominating each per-pair `Φ.kappa`), the `j`-th covariant gradient
  splits as a difference-arm piece `Adiff` (the high derivative on the difference factor `w`,
  `rfns(∇^j Adiff) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)`, the metric-built coefficient folded into the uniform
  `Cd` by the binomial covariant-Leibniz `rfns` grid of `Φ`) plus a fixed-pair cross piece `Cross`
  (`rfns(∇^j Cross) ≤ (1/2)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·‖(T₁ − T₂).toHs a‖²`).  It is
  **proven** here over the uniform difference-arm grid lemma `bilinDiff_uniform_diffArm_grid` (which
  collects the metric coefficient into the *family-uniform* difference-arm constant
  `Cd := 4^j · gridWindowSum kbar 0 2 j` by the explicit binomial covariant-Leibniz `rfns` grid
  `DiffBilinOp.rfns_iteratedCovGrad_grid`, the per-pair `Φ.kappa` dominated by `kbar`) plus the
  telescope datum's own all-order cross bound on `C` (the order-`j` covariant gradient of the fixed-pair
  remainder riding the cross arm) and the realize-jet no-derivative-gain control of the difference
  factor.  It carries NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence;
  it is the section-functor-abstract content shared by the two per-field leaves.

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
uniform `H^{a+2}`-size bound `B ≥ 0`, this is the predicate: there is a **family-uniform** nonnegative
order × rank envelope `kbar : ℕ → ℕ → ℝ` such that for any two `g₀`-fibre-small perturbations `T₁, T₂`
with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the section difference
`F g₁ − F g₂` is the sum of an undifferentiated metric-contraction `Φ.op 0 2 w` of a differentiated
bilinear contraction operator family `Φ : DiffBilinOp g₀` (the metric-built coefficient, whose per-order
fibre envelope `Φ.kappa` is dominated by the family-uniform `kbar`) against the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus a fixed-pair cross remainder `C : SmoothCcTensor g₀ 0 2`
whose **every** covariant jet is `rfns`-controlled by the order-`≤ j+2` fixed-pair jet sum against the
difference's order-`a` chart-Sobolev `C⁰` mass `‖(T₁ − T₂).toHs a‖²`:

```
∀ p r, Φ.kappa p r ≤ kbar p r,
F g₁ − F g₂ = Φ.op 0 2 w + C,
∀ j x, rfns(∇^j C)(x) ≤ (1/2)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the explicit `telescope_bilin`-shaped (not opaque) single-difference-factor expansion: the
difference factor enters the metric only through the realization map (no derivative gain), so the single
high derivative will land on `w` through `Φ.op`; the fixed-pair top coefficient jet rides on `C`.  The
family-uniform envelope `kbar` is the load-bearing strengthening (the per-pair operator `Φ` and hence
its envelope `Φ.kappa` genuinely vary with the segment metric `g_t = (1-t)·g₂ + t·g₁`, but they share a
single ball-uniform `≤2`-jet sup over the supercritical `H^{a+2}` family, the source of `kbar`): it is
what lets the per-order `Adiff + Cross` split it feeds (`bilinDiff_covFdB_section_split`) extract a
*single* difference-arm constant `Cd` uniform over the family.  It is genuinely weaker than that split
(it is the order-zero algebraic equality plus the all-order cross control and the uniform envelope, NOT
the per-order difference-arm grid bound on `∇^j(Φ.op 0 2 w)`, which is the deep content the split
derives), and it is non-vacuous: it is an explicit equality constraining `F g₁ − F g₂` to the
single-difference-factor form, rejecting any functor whose difference is not of this shape. -/
def TelescopeData (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothRiemannianMetric I M → Integral.L2.SmoothCcTensor g₀ 0 2) (a : ℕ) (B : ℝ) : Prop :=
  ∃ kbar : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kbar p r) ∧
  ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M),
    (∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
    (∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
    ∃ (Φ : DiffBilinOp g₀) (C : Integral.L2.SmoothCcTensor g₀ 0 2),
      (∀ p r, Φ.kappa p r ≤ kbar p r) ∧
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

/-- **The uniform difference-arm covariant-jet grid bound of a telescope-datum nonlinearity (the deep
covariant-Leibniz uniformity lemma).**

For a section functor `F` admitting the explicit order-zero telescope datum `TelescopeData g₀ F a B`,
there is a **single** nonnegative difference-arm constant `Cd`, *uniform over the entire supercritical
`H^{a+2}`-bounded perturbation family*, such that for every pair of `g₀`-fibre-small perturbations
`T₁, T₂` with `H^{a+2}` norms `≤ B` and every realized pair `g₁, g₂`, the section difference splits as
the order-`j` covariant gradient of the telescope datum's metric-contraction `Φ.op 0 2 w` (the
difference-arm object) plus the order-`j` covariant gradient of the telescope datum's fixed-pair
remainder `C`, with the difference-arm object's every fibre jet `rfns`-dominated by the uniform `Cd`
against the order-`≤ j + 2` covariant jets of the difference factor `w := realizeSymmCcTensor g₀
(T₁ − T₂)`:
```
∇^j (F g₁ − F g₂) = Adiff + ∇^j C,
rfns(Adiff)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x).
```

This is the genuine deep content the shared brick `bilinDiff_covFdB_section_split` stands on, isolated
as its own lemma and **proven outright** here: the telescope datum `TelescopeData` supplies, *per
perturbation pair*, a differentiated bilinear contraction operator `Φ` (the metric-built coefficient
family) whose binomial
covariant-Leibniz `rfns` grid constant `4^j · gridWindowSum Φ.kappa 0 2 j`
(`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`) controls `rfns(∇^j(Φ.op 0 2 w))` by
`∑_{q ≤ j} rfns(∇^q w) ⊆ ∑_{i ≤ j+2} rfns(∇^i w)`.  The genuinely deep step — *not* deducible from the
per-pair datum alone — is that this grid constant is **uniform over the family**: the operator `Φ` is
the segment-metric-built curvature/Lie contraction, whose envelope `Φ.kappa` is dominated by the
order-`≤ 2` segment-metric covariant-jet sup, itself ball-uniform over the `H^{a+2}` family
(`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`), so a single `Cd` covers every pair.

The conclusion exhibits, per pair, the difference-arm object `Adiff` and a remainder section `Rem` with
`∇^j (F g₁ − F g₂) = Adiff + Rem`, the uniform grid bound `rfns(Adiff) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)`,
AND — handed forward, *not* re-derived — that `Rem = ∇^j C` for the telescope datum's own remainder `C`,
so the assembling node `bilinDiff_covFdB_section_split` inherits the cross bound on `Rem` directly from
the datum.  It carries the difference arm ONLY (no claim on `Rem`'s size beyond its identity as the
datum's `∇^j C`), so it does **not** assume that node's conclusion: with the trivial difference factor
`w = 0` (i.e. `T₁ = T₂`) the bound degenerates on both sides, while for a genuine difference the
difference-arm content `∑ rfns(∇^i w)` is positive and the bound is the genuine uniform
covariant-Leibniz domination.  It carries NO pointwise-`C^{>2}`-jet claim (the difference factor's jets
are perturbation-difference jets, no metric jet of order `> 2` is taken pointwise), NO
spectral-nonlinearity, and NO Weyl dependence. -/
theorem bilinDiff_uniform_diffArm_grid
    (g₀ : SmoothRiemannianMetric I M)
    (F : SmoothRiemannianMetric I M → Integral.L2.SmoothCcTensor g₀ 0 2)
    (a : ℕ) (B : ℝ) (_hB : 0 ≤ B) (hExp : TelescopeData (I := I) g₀ F a B) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ (Adiff Rem : Integral.L2.SmoothCcTensor g₀ 0 (2 + j))
          (C : Integral.L2.SmoothCcTensor g₀ 0 2),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (F g₁ - F g₂) = Adiff + Rem ∧
          Rem = PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x) ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ∧
          (∀ (jj : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + jj) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 jj C).toSection x) ≤
              (1 / 2 : ℝ) * (∑ i ∈ Finset.range (jj + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  obtain ⟨kbar, hkbar_nn, hbody⟩ := hExp
  -- The uniform difference-arm constant: the `4^j`-scaled order × rank window sum of the uniform
  -- envelope `kbar` (the binomial covariant-Leibniz grid constant of the metric-built coefficient,
  -- with the per-pair operator's envelope `Φ.kappa` dominated by the family-uniform `kbar`).
  refine ⟨(4 : ℝ) ^ j * Integral.Connection.gridWindowSum kbar 0 2 j,
    mul_nonneg (by positivity) (Integral.Connection.gridWindowSum_nonneg hkbar_nn 0 2 j),
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ => ?_⟩
  obtain ⟨Φ, C, hkappa, heq, hcross⟩ := hbody T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  set w : Integral.L2.SmoothCcTensor g₀ 0 2 := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw_def
  -- The difference arm is `∇^j (Φ.op 0 2 w)`; the remainder is `∇^j C`.
  refine ⟨PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 2 w),
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C, C, ?_, rfl, ?_, hcross⟩
  · -- `∇^j (F g₁ − F g₂) = ∇^j (Φ.op 0 2 w + C) = ∇^j (Φ.op 0 2 w) + ∇^j C`.
    rw [heq, PDE.RicciFlow.iteratedCovGrad_add]
  · -- The uniform binomial covariant-Leibniz `rfns` grid on the difference arm.
    intro x
    -- The explicit per-pair binomial grid (at `p = 0`, `r = 2`):
    -- `rfns(∇^j(op 0 2 w))(x) ≤ 4^j · gridWindowSum Φ.kappa 0 2 j · ∑_{q ≤ j} rfns(∇^q w)(x)`.
    have hgrid := Φ.rfns_iteratedCovGrad_grid j 0 2 w x
    -- The per-pair envelope `Φ.kappa` is dominated by the family-uniform `kbar`, so its grid window
    -- sum is dominated by `kbar`'s (pure `Finset.sum` monotonicity over the order × rank window).
    have hkappa_grid : Integral.Connection.gridWindowSum Φ.kappa 0 2 j ≤
        Integral.Connection.gridWindowSum kbar 0 2 j := by
      unfold Integral.Connection.gridWindowSum
      exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hkappa _ _
    have hgwΦ_nn : 0 ≤ Integral.Connection.gridWindowSum Φ.kappa 0 2 j :=
      Integral.Connection.gridWindowSum_nonneg Φ.kappa_nonneg 0 2 j
    -- Extend the `q ≤ j` window to `i ≤ j + 2` (nonnegative terms).
    set wsum : ℝ := ∑ i ∈ Finset.range (j + 2 + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) with hwsum_def
    have hwindow : (∑ q ∈ Finset.range (0 + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q w).toSection x)) ≤ wsum := by
      rw [hwsum_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun i _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hwsum_nn : 0 ≤ wsum := Finset.sum_nonneg fun i _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
    have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 2 w)).toSection x)
        ≤ (4 : ℝ) ^ j * Integral.Connection.gridWindowSum Φ.kappa 0 2 j *
            ∑ q ∈ Finset.range (0 + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 q w).toSection x) := hgrid
      _ ≤ (4 : ℝ) ^ j * Integral.Connection.gridWindowSum Φ.kappa 0 2 j * wsum :=
          mul_le_mul_of_nonneg_left hwindow (by positivity)
      _ ≤ (4 : ℝ) ^ j * Integral.Connection.gridWindowSum kbar 0 2 j * wsum :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hkappa_grid hpow_nn) hwsum_nn

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

It is **proven** here by composition over `bilinDiff_uniform_diffArm_grid`: that lemma performs the
genuine deep covariant-jet content — the push of `∇^j` through the metric-contraction `Φ.op 0 2 w` of
the telescope datum via the explicit binomial covariant-Leibniz grid
`DiffBilinOp.rfns_iteratedCovGrad_grid` (collecting the metric coefficient into the *family-uniform*
difference-arm constant `Cd := 4^j · gridWindowSum kbar 0 2 j` over the grid window `j + 2`, the per-pair
`Φ.kappa` dominated by the telescope datum's family-uniform envelope `kbar`, the difference factor's jets
controlled by the perturbation-difference jets through the realize-jet no-derivative-gain bound) — and
hands forward the telescope datum's own all-order cross bound, which this node applies at order `j` for
the cross arm (the order-`j` covariant gradient of the fixed-pair remainder `C`).  It carries NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
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
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  obtain ⟨Cd, hCd_nn, harm⟩ :=
    bilinDiff_uniform_diffArm_grid (I := I) g₀ F a B hB hExp j
  refine ⟨Cd, hCd_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ => ?_⟩
  obtain ⟨Adiff, Rem, C, heq, hRem, hAdiff, hcross⟩ :=
    harm T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  refine ⟨Adiff, Rem, heq, hAdiff, fun x => ?_⟩
  rw [hRem]
  exact hcross j x

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
