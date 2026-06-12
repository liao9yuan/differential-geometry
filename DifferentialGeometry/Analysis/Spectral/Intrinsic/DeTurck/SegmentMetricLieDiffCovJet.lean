import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricLieSectionDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricLieDifferenceCovJet

/-! # The Lie-deformation-difference covariant-jet split of the sealed Ricci–DeTurck gauge summand

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **gauge analogue** of the curvature-trace covariant-jet
reduction (`SegmentMetricCurvatureDifferenceCovJet.lean`), beneath the Lie-half Core-II covariant-jet
nodes of the Ricci–DeTurck right-hand-side expansion (`SegmentMetricRHSCovJetExpansion.lean`).

The sealed gauge nonlinearity is the Lie-derivative (gauge) summand `𝓛_{W(g, g_bg)} g` of the
Ricci–DeTurck right-hand side, `g₀`-retagged as `lieDerivRetagG0 g₀ g_bg g₁`
(`DeTurckRHSSectionRetag.lean`).  Its deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a
`g⁻¹·∂g`-type field, and one further metric derivative produces the Lie deformation, so the gauge
summand has the **same intrinsic order-`≤2` structure** as the curvature summand (the trace of the
Levi-Civita curvature operator).  Differenced along the segment metric `g_t = g₂ + t·(g₁ − g₂)`, the
gauge difference admits the **identical linear/cross split** as the curvature half: a
linear-in-difference part `lieLinearSection` carrying the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)` through its covariant jets — the order-`0` value jet included,
since the Lie summand depends on the metric at order zero — plus a
quadratic-in-difference Cross part `lieCrossSection` (the `D∘D`-type quadratic) carrying the top
coefficient jet on the fixed pair `T₁, T₂`.

## Concrete sections, mirroring the curvature half

The curvature half builds the **concrete** quadratic Cross section `crossSection g₀ g₁ g₂`
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`, from the concrete operator-trace value
`ricciNeg2SectionDiffCrossEval`) and the linear part as its algebraic complement
`linearSection := diff − crossSection`; its difference-arm/Cross-arm covariant-jet bounds are then stated
on the two **concrete** sections (`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`), each proved by composition over the
connection-level reductions — never on an arbitrary quadratic section.

The intrinsic-vector linear/quadratic split of the *Lie deformation* (which arises from the
`W(g)`-dependence of `𝓛_{W(g)} g`, distinct from the curvature half's `connDiffField ∧ connDiffField`
quadratic) is **genuinely absent on disk** — there is no concrete intrinsic Lie cross *value* to build a
`crossField`-style section from (only the chart-component telescope `chartLieDeTurckComp_sub_eq`
(`ChartLieDerivStructuralDifference.lean`, the `j = 0` chart witness) exists, the sole intrinsic value hook
being the order-zero fibre value `lieDerivRetagG0_sub_toModel_eq`).  So the concrete Lie sections
`lieCrossSection g₀ g_bg g₁ g₂` / `lieLinearSection g₀ g_bg g₁ g₂` are named
(`SegmentMetricLieSectionDecomposition.lean`) via `Classical.choose` of the single genuine deep posited
existence `lieDerivDiff_connLevel_sectionData`; this file states the Lie-half linear-arm reduction on the
**concrete** `lieLinearSection`, and assembles the order-zero split on the concrete pair.

## What is posited vs. derived

* `lieDerivDiff_connLevel_sectionData` (`SegmentMetricLieSectionDecomposition.lean`) — the single named
  deep covariant-gauge section-data node, derived there from the posited top/rest split
  `lieDerivDiff_connLevel_topRestSplit` (the genuine `sorry` leaf): existence of the concrete
  cross-section family with both arms' 0-jet-inclusive `w`-jet covariant two-arm bounds (the gauge
  analogue of the *pair* of curvature connection-level reductions, bundled because the determining
  intrinsic Lie cross value is genuinely absent on disk).

* `lieLinearSection_iteratedCovGrad_connLevel_rfns_le` — **derived by composition (TRANSIT)** over the
  section-data leaf: its first arm bound is the 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete
  `lieLinearSection`.

* `lieCrossSection_iteratedCovGrad_connLevel_rfns_le` (`SegmentMetricLieDifferenceCovJet.lean`) —
  **derived by composition (TRANSIT)**: the second arm bound of the section-data leaf.

* `exists_lieDerivDiff_connLevel_split` — **derived by composition (TRANSIT)**: witnesses
  `L := lieLinearSection`, `C := lieCrossSection`, with the section sum identity
  `lieDerivRetagG0_sub_eq_lieLinear_add_lieCross` (pure `abel`) and the two concrete-section reductions.
  The common constant is `max` of the two reductions' constants, widened on each arm.

Downstream (`SegmentMetricRHSCovJetExpansion.lean`) this split discharges the Lie-half value-level node
`exists_lieDerivLinearCross_section_connLevel` and the order-zero split assembler
`lieDerivDiff_order0_linearCross_split` verbatim — its arms already carry the `w`-jet shape those
consumers read (the former rank-`3` connection-level arm, certified false for the Lie half, was
re-signatured away, and no rank-shift step remains) — supplying the concrete linear/Cross section pair
with both `w`-jet arm bounds the order-`a` chart-RHS tower consumes.

The split carries **no** value-bounded `Φ.op 0 2 w` shape (the refuted structural split — the
`∇^{j+2} w` content rides on the difference arm, the unbounded top coefficient jet on the
fixed-pair cross arm), NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.
Both arm bounds are **coupled and non-vacuous** (in the section-data leaf): the difference arm carries the high derivative `∇^{j+2} w` (a zero `Cd` falsifies it whenever the linear part is genuinely
present), and the cross arm carries the unbounded top coefficient jet (`L²` mass of order
`j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound) on the fixed pair `T₁, T₂` against the
difference's order-`a` chart-Sobolev `C⁰` mass `‖(T₁ − T₂).toHs a‖²`. -/

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

/-- **(The 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete Lie linear section —
derived by composition (TRANSIT).)**  The gauge analogue of the curvature half's
connection-level linear reduction `ricciLinearSection_covGrad_traceReductionConn_rfns_le`, stated on the
**concrete** Lie linear section `lieLinearSection g₀ g_bg g₁ g₂`
(`SegmentMetricLieSectionDecomposition.lean`, the algebraic complement
`diff − lieCrossSection`).

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a uniform
`H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative **per-order constant
family** `Cd : ℕ → ℝ` (each `Cd j` uniform over the perturbation family; per-order because the
Lie-derivative nonlinearity doubles frequencies, so a `j`-uniform constant is refuted on flat `T²`) such
that for any two `g₀`-fibre-small
perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the
intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete Lie linear section
`lieLinearSection g₀ g_bg g₁ g₂` is dominated by the Hamilton/Moser two-arm sum, whose
difference arm is the **0-jet-inclusive** order-`≤ j+2` covariant jet sum of the realized
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
rfns(∇^j (lieLinearSection))(x) ≤ Cd(j) · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D².
```

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half, so the linear part's derivative jets ride, via the `g₀`-lowered Koszul form, on the
`w`-jets — the order-`0` value jet additionally carried, since the Lie summand depends on the metric
value — exactly as for the curvature linear part (bounds via the proven realized-Koszul jet
domination `koszulCombSection_iteratedCovGrad_rfns_le`), and the value-local model-basis trace folds the
metric-built `≤2`-jet coefficient into the family-uniform `Cd` over the window `j + 2`.

**Non-vacuity.**  The difference arm carries the high derivative `∇^{j+2} w` (a zero `Cd`
falsifies it); coupled with the Cross arm `lieCrossSection_iteratedCovGrad_connLevel_rfns_le` in the
section-data leaf, the degenerate readings are rejected (with the Cross part `0` the linear complement is
the full `diff`, whose linear-arm bound is FALSE for `j ∈ (a, 2a]`).  At `g₁ = g₂` the Lie-summand
difference vanishes and the bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  Proved by composition over the single genuine deep section-data leaf
`lieDerivDiff_connLevel_sectionData` (`SegmentMetricLieSectionDecomposition.lean`): its first arm bound is
exactly this 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete `lieLinearSection`.
Consumers
transitively depend on `sorryAx` only through that named section-data leaf. -/
theorem lieLinearSection_iteratedCovGrad_connLevel_rfns_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℕ → ℝ, (∀ j, 0 ≤ Cd j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ (j : ℕ),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (lieLinearSection (I := I) g₀ g_bg g₁ g₂)‖ ^ 2 ≤
            Cd j * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hbound⟩ :=
    (lieDerivDiff_connLevel_sectionData (I := I) g₀ g_bg).choose_spec a ha B hB δ hδ0 hδ1
  refine ⟨Cd, hCd0, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j
  -- The first arm bound of the section-data leaf is the integrated bound on the algebraic complement
  -- `diff − Cf`, which is definitionally `lieLinearSection`.
  have h := (hbound T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2).1 j
  rwa [show (lieLinearSection (I := I) g₀ g_bg g₁ g₂) =
      (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
        - (lieDerivDiff_connLevel_sectionData (I := I) g₀ g_bg).choose g₁ g₂ from rfl]

/-- **(POSIT — bundled into the section-data leaf — the gauge value-level linear/cross
split with both arms' covariant-jet bounds: the genuine Core-II value-level node of the Lie half, with the
0-jet-inclusive `w`-jet difference arm, derived by composition (TRANSIT).)**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a uniform
`H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative difference-arm constant
family `Cd : ℕ → ℝ` (each `Cd j` uniform over the perturbation family; per-order because the
Lie-derivative nonlinearity doubles frequencies, so a `j`-uniform constant is refuted on flat `T²`,
while the `L`, `C` sections themselves stay `j`-independent) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of
`T₁, T₂`, the `g₀`-retagged Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg
g₂` splits as a **linear-in-difference** section `L` plus a **quadratic-in-difference Cross** section `C`
(genuine smooth `SmoothCcTensor g₀ 0 2`s), with **both** per-order covariant gradients satisfying the
Hamilton/Moser two-arm bound whose difference arm is the **0-jet-inclusive** order-`≤ j+2` covariant jet sum of the realized
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd(j) · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
rfns(∇^j C)(x) ≤ Cd(j) · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

This is the gauge analogue of the curvature half's *pair* of connection-level reductions
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`) assembled over the concrete order-zero section
split.  Here the concrete sections are `L := lieLinearSection g₀ g_bg g₁ g₂` and `C := lieCrossSection g₀
g_bg g₁ g₂` (`SegmentMetricLieSectionDecomposition.lean`), with the value split the pure `abel` identity
`lieDerivRetagG0_sub_eq_lieLinear_add_lieCross`; since the determining intrinsic Lie cross value is genuinely
absent on disk (only the `j = 0` chart witness `chartLieDeTurckComp_sub_eq` exists), the concrete sections
are named via `Classical.choose` of the single genuine deep posited existence
`lieDerivDiff_connLevel_sectionData`, on which both arm bounds are recorded.

**Non-vacuity (the value split and both arm bounds are coupled, rejecting the degenerate readings).**  In
the section-data leaf, with `C = 0`, `L = diff` would have to satisfy the linear-arm bound, FALSE for
`j ∈ (a, 2a]` — the top coefficient jet content of the full Lie difference is genuinely `(∑ fixed-pair) ·
C⁰`-order (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the
fixed-pair *cross* arm can carry it).  So the genuine quadratic top-jet content **must** ride on `C`, and
`L` is the genuine linear-in-difference part; symmetrically the cross-arm bound rejects `C = diff`.  A zero
`Cd` is rejected (each difference arm carries the high derivative `∇^{j+2} w`).  At
`g₁ = g₂` (so `T₁ = T₂` realized) the Lie-summand difference vanishes and the split is `0 = 0 + 0` with
both bounds `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  Proven by composition over the two concrete-section
reductions `lieLinearSection_iteratedCovGrad_connLevel_rfns_le` (this file, the linear arm on the concrete
`lieLinearSection`) and `lieCrossSection_iteratedCovGrad_connLevel_rfns_le`
(`SegmentMetricLieDifferenceCovJet.lean`, the Cross arm on the concrete `lieCrossSection`), with the value
split the pure `abel` identity `lieDerivRetagG0_sub_eq_lieLinear_add_lieCross`.  The common constant is
`max CdL CdC`; each arm is widened from its reduction's constant upward (the difference-arm jet sum being
nonnegative).  Both reductions descend into the single genuine deep section-data leaf
`lieDerivDiff_connLevel_sectionData`; consumers transitively depend on `sorryAx` only through it. -/
theorem exists_lieDerivDiff_connLevel_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℕ → ℝ, (∀ j, 0 ≤ Cd j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L‖ ^ 2 ≤
              Cd j * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C‖ ^ 2 ≤
              Cd j * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  -- **Linear reduction** (the genuinely-absent intrinsic content, on the concrete `lieLinearSection`):
  -- produces the integrated `w`-jet linear-arm two-arm bound on `∇^j (lieLinearSection)`.
  obtain ⟨CdL, hCdL0, hL⟩ :=
    lieLinearSection_iteratedCovGrad_connLevel_rfns_le (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  -- **Cross reduction** (on the concrete `lieCrossSection`): the integrated `w`-jet cross-arm two-arm
  -- bound on `∇^j (lieCrossSection)`.
  obtain ⟨CdC, hCdC0, hC⟩ :=
    lieCrossSection_iteratedCovGrad_connLevel_rfns_le (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨fun j => max (CdL j) (CdC j), fun j => le_trans (hCdL0 j) (le_max_left _ _), ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  refine ⟨lieLinearSection (I := I) g₀ g_bg g₁ g₂, lieCrossSection (I := I) g₀ g_bg g₁ g₂,
    lieDerivRetagG0_sub_eq_lieLinear_add_lieCross (I := I) g₀ g_bg g₁ g₂, fun j => ?_, fun j => ?_⟩
  · -- Linear arm: widen per order `CdL j → max (CdL j) (CdC j)` (the difference-arm jet sum is
    -- nonnegative).
    refine le_trans (hL T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (j + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    gcongr
    exact le_max_left _ _
  · -- Cross arm: widen per order `CdC j → max (CdL j) (CdC j)`.
    refine le_trans (hC T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (j + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    gcongr
    exact le_max_right _ _

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
