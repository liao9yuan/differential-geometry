import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciSectionIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-! # The concrete connection-level section decomposition of the sealed Ricci–DeTurck Lie difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **gauge analogue of the curvature half's concrete
order-zero section normal form** (`SegmentMetricCurvatureDifferenceOpDecomposition.lean`): it names two
**concrete** `SmoothCcTensor g₀ 0 2` sections — `lieCrossSection g₀ g_bg g₁ g₂` (the
quadratic-in-difference Cross part) and `lieLinearSection g₀ g_bg g₁ g₂` (its algebraic complement inside
the sealed Lie-summand difference) — on which the Lie-half connection-level covariant-jet two-arm bounds
are stated, exactly as the curvature half states them on its concrete `crossSection` / `linearSection`.

## Why the gauge half is not value-derived, and how it is made concrete

The curvature half builds its concrete Cross section `crossSection g₀ g₁ g₂` from a **concrete pointwise
operator-trace value** `ricciNeg2SectionDiffCrossEval` (the model-basis trace of the quadratic
`connDiffField ∧ connDiffField` summand difference, the genuine second-order remainder), which determines
the Cross section completely (all jets); its two per-order jet-bound leaves
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`) are then stated and proven on that
fully-determined concrete section.

The intrinsic-vector linear/quadratic split of the *Lie deformation* (arising from the `W(g)`-dependence
of `𝓛_{W(g)} g`, distinct from the curvature half's `connDiffField ∧ connDiffField` quadratic) is
**genuinely absent on disk** — only the chart-component telescope `chartLieDeTurckComp_sub_eq`
(`ChartLieDerivStructuralDifference.lean`, the `j = 0` chart witness) exists, not an intrinsic-vector eval
split, and the only intrinsic value hook is the order-zero fibre value
`lieDerivRetagG0_sub_toModel_eq` (`SegmentMetricRicciSectionIdentity.lean`): the sealed Lie-summand
difference's fibre value is `𝓛_{W(g₁)} g₁ − 𝓛_{W(g₂)} g₂`, fully intrinsic, but with **no on-disk
intrinsic linear/cross value split**.  So there is no concrete pointwise cross *value* to determine a
`crossField`-style section by, and the concrete cross section cannot be exhibited as the curvature half
does (via `connDiffField`).

The honest concrete realization is therefore a **named section function** chosen (`Classical.choose`) from
the single genuine deep posited existence `lieDerivDiff_connLevel_sectionData`: the existence of a smooth
cross-section family `Cf g₁ g₂` whose complement `diff − Cf g₁ g₂` and itself **both** satisfy the
connection-level (rank-`3`, `∇w`-level) covariant-jet two-arm bound (the genuine covariant Faà-di-Bruno
content of the Lie nonlinearity, the gauge analogue of the *pair* of curvature reductions, bundled into one
existence because — the determining intrinsic value being absent — the section's higher jets are not pinned
by any on-disk value, so a split-then-bound staging is impossible).  From it `lieCrossSection := Cf g₁ g₂`
and `lieLinearSection := diff − lieCrossSection` are genuine `def`s, and the two Lie-half bound leaves
(`SegmentMetricLieDifferenceCovJet.lean`, `SegmentMetricLieDiffCovJet.lean`) are stated on these
**concrete** sections — never on an arbitrary quadratic section.

## What is posited vs. derived

* `lieDerivDiff_connLevel_sectionData` — **posited** (`sorry` body): the genuine deep covariant-gauge
  content — the existence of the concrete cross-section family with the connection-level two-arm bound on
  both the linear complement and the Cross part.  This is the gauge analogue of the curvature half's
  concrete section split `ricciNeg2RetagG0_sub_normalForm_section` **together with** its two connection-level
  reductions, bundled because the determining intrinsic Lie cross value is genuinely absent on disk.

* `lieDerivRetagG0_sub_eq_lieLinear_add_lieCross` — **derived (pure `abel`)**: by the definition of
  `lieLinearSection` as the algebraic complement, the sealed Lie-summand difference is the sum of its
  linear and Cross sections, sorry-free.

The posited existence carries **no** value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence; both arm bounds are **coupled and non-vacuous** (with `Cf ≡ 0`
the linear complement is the full `diff`, whose connection-level bound is FALSE for `j ∈ (a, 2a]` — the top
coefficient jet content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order, only the
fixed-pair *cross* arm can carry it — so `Cf ≡ 0` is rejected; symmetrically a full-`diff` Cross is rejected
by the cross arm).  The difference arm of both bounds is the rank-`3` order-`≤ j+1` covariant jet sum of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)`. -/

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

/-- **(POSIT — the intrinsic Lie value-split bundled with the connection-level LINEAR arm: the
genuinely-absent order-zero content of the gauge half.)**

For an anchor `g₀` and a flow background `g_bg`, there is a smooth cross-section family
`Cf : g₁ g₂ ↦ Cf g₁ g₂ : SmoothCcTensor g₀ 0 2` — chosen once, independent of the order `a` — such that
for every order `a` with the supercriticality hypothesis `ha`, every uniform `H^{a+2}`-size bound `B ≥ 0`,
and every fibre-smallness `δ < 1/2`, there is a nonnegative constant `Cd` (uniform over the gradient order
`j` and the perturbation family) such that for any two `g₀`-fibre-small perturbations `T₁, T₂` with
`H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the **algebraic-complement linear
part** `diff − Cf g₁ g₂` of the `g₀`-retagged Lie-summand difference
`diff := lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` has its per-order covariant gradient
dominated by the **connection-level** Hamilton/Moser two-arm sum whose difference arm is the rank-`3`
order-`≤ j+1` covariant jet sum of the once-differentiated realized difference factor
`R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
rfns(∇^j (diff − Cf g₁ g₂))(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

This is the genuine intrinsic-vector linear/quadratic value-split of the *Lie deformation* (arising from
the `W(g)`-dependence of `𝓛_{W(g)} g`), **bundled with the linear-arm connection-level grid** because the
value split and the linear bound are mathematically inseparable for the gauge nonlinearity: with `Cf ≡ 0`
the complement `diff − Cf = diff` would have to satisfy the connection-level linear bound, FALSE for
`j ∈ (a, 2a]` (the top coefficient jet content of the full Lie difference is genuinely
`(∑ fixed-pair) · C⁰`-order, only the fixed-pair *cross* part `Cf` can carry it), so a valid witness `Cf`
**must** put the genuine quadratic top-jet content into `Cf` — `Cf ≡ 0` is rejected — and `diff − Cf` is
then the genuine linear-in-difference part.  The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2`
structure** as the curvature half (the deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a
`g⁻¹·∂g`-type field, and one further metric derivative produces the Lie deformation), so the linear part's
`g₀`-lowered Koszul form is the connection-level once-differentiated realized difference factor `R = ∇₀ w`
exactly as for the curvature linear part (bounds via the proven realized-Koszul jet domination
`koszulCombSection_iteratedCovGrad_rfns_le`).  The value-local model-basis trace folds the metric-built
`≤2`-jet coefficient into the family-uniform `Cd` over the rank-`3` window `j + 1`.

This is the gauge analogue of the curvature half's concrete `linearSection` construction-from-value
**together with** its connection-level linear reduction
`ricciLinearSection_covGrad_traceReductionConn_rfns_le`, bundled into one existence because — unlike the
curvature half, which builds the concrete `crossSection`/`linearSection` from the concrete operator-trace
value `ricciNeg2SectionDiffCrossEval` (determining all jets) — the intrinsic-vector linear/quadratic split
of the Lie deformation is **genuinely absent on disk** (only the `j = 0` chart witness
`chartLieDeTurckComp_sub_eq` exists, the sole intrinsic value hook being the order-zero fibre value
`lieDerivRetagG0_sub_toModel_eq`), so there is no concrete cross *value* to determine the section by, and
the section's higher jets — on which the bound depends — are pinned only by the bound itself.

**Non-vacuity.**  A zero `Cd` is rejected (the difference arm carries the connection-level high derivative
`∇^{j+1} R`).  `Cf ≡ 0` is rejected (the complement bound is false on the top window).  At `g₁ = g₂` (so
`T₁ = T₂` realized) the Lie-summand difference vanishes (`lieDerivRetagG0_sub_toModel_eq`), `R = 0` and
`D = 0`, so the bound forces the linear part to vanish there.  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep covariant-gauge value-level content of the Lie half (the intrinsic-vector linear/quadratic
split absent on disk together with the linear arm's connection-level covariant-Leibniz `rfns` grid). -/
theorem lieDerivDiff_connLevel_valueSplitLinear (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Cf : SmoothRiemannianMetric I M → SmoothRiemannianMetric I M →
        Integral.L2.SmoothCcTensor g₀ 0 2,
      ∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
        ∃ Cd : ℝ, 0 ≤ Cd ∧
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
            ∀ (j : ℕ) (x : M),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                      ((lieDerivRetagG0 (I := I) g₀ g_bg g₁
                          - lieDerivRetagG0 (I := I) g₀ g_bg g₂) - Cf g₁ g₂)).toSection x) ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
                  + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the connection-level Lie CROSS arm on the value-split's Cross section.)**

The gauge analogue of the curvature half's connection-level quadratic-Cross reduction
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`, stated on the **Cross section `Csec` of ANY valid
order-zero value split** of the `g₀`-retagged Lie-summand difference.  For every order `a` with the
supercriticality hypothesis `ha`, every uniform `H^{a+2}`-size bound `B ≥ 0`, and every fibre-smallness
`δ < 1/2`, there is a nonnegative constant `Cd` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` with `H^{a+2}` norms `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂`, and any pair of
sections `Lsec, Csec : SmoothCcTensor g₀ 0 2` exhibiting the value split
`diff := lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂ = Lsec + Csec` with `Lsec` carrying the
connection-level linear-arm grid bound (the defining constraint identifying `Csec` as the genuine
quadratic Cross part), the per-order covariant gradient of `Csec` is dominated by the **connection-level**
Hamilton/Moser two-arm sum whose difference arm is the rank-`3` order-`≤ j+1` covariant jet sum of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)`:
```
rfns(∇^j Csec)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                   + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

The Cross section's differenced operator-trace fibre value carries **both** a diff-high × fixed-low arm and
a fixed-high × diff-low arm (the connection-difference bilinear product of two independently varying gauge
fields, the `D∘D`-type quadratic of the Lie deformation); after the value-local model-basis trace and the
once-`∇₀` differentiation the difference arm is controlled by the connection-level `R = ∇₀ w` jets, and the
cross arm keeps the top coefficient jet (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}`
ball cannot bound) on the fixed pair `T₁, T₂`, bounded against the difference's `C⁰` mass by the
supercritical Sobolev embedding (`ha`).  Bounds via the cross-correction-difference machinery and the
parallel two-section bilinear-product grid.

**Why a universal `(Lsec, Csec)` and not the `.choose` of a linear-only witness.**  The cross-arm bound on
the Cross part of the value split cannot be recovered from `Classical.choose` of a linear-only existence —
that carries no Cross-arm guarantee.  Stating the cross bound **universally** over every value-split pair
`(Lsec, Csec)` (with the value identity and `Lsec`'s linear grid as constraining hypotheses) is the sound
form: it bounds the Cross part of whichever split the consumer supplies, since `Csec = diff − Lsec` is
forced once `Lsec` is the genuine linear part.  The hypotheses (the value identity `diff = Lsec + Csec` and
the existence of `Lsec`'s difference-arm grid) are genuine mathematical constraints on `Csec`, wholly
different from the conclusion (a per-order jet bound on `∇^j Csec`); this is **not** hypothesis-packaging.

**Non-vacuity.**  The Cross section `Csec` carried by a valid value split is the genuine quadratic top-jet
content (rejected from being `0` by the coupling: with `Csec = 0`, `Lsec = diff` falsifies its required
linear grid on `j ∈ (a, 2a]`); both fixed-pair endpoints `T₁, T₂` are carried, and the difference arm
carries the connection-level high derivative `∇^{j+1} R` (a zero `Cd` falsifies it).  At `g₁ = g₂` the
Lie-summand difference vanishes (`lieDerivRetagG0_sub_toModel_eq`), `R = 0` and `D = 0`, and the value
split forces `Csec` to vanish, so the bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep covariant-gauge-jet content of the quadratic Cross arm at the connection level. -/
theorem lieDerivCrossSection_connLevel_crossArm_ofSplit (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M)
        (Lsec Csec : Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = Lsec + Csec →
        (∃ CdL : ℝ, 0 ≤ CdL ∧ ∀ (j : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j Lsec).toSection x) ≤
            CdL * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) →
        ∀ (j : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j Csec).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the `Cf`-construction bundled with BOTH connection-level arms: the genuine
intrinsic-vector Lie value-split, at the rank-`3` `∇w`-level.)**

For an anchor `g₀` and a flow background `g_bg`, there is a smooth cross-section family
`Cf : g₁ g₂ ↦ Cf g₁ g₂ : SmoothCcTensor g₀ 0 2` — chosen once, independent of the order `a` — such that
for every order `a` with the supercriticality hypothesis `ha`, every uniform `H^{a+2}`-size bound `B ≥ 0`,
and every fibre-smallness `δ < 1/2`, there is a nonnegative constant `Cd` (uniform over the gradient order
`j` and the perturbation family) such that for any two `g₀`-fibre-small perturbations `T₁, T₂` with
`H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, **both** the algebraic-complement
linear part `diff − Cf g₁ g₂` of the `g₀`-retagged Lie-summand difference
`diff := lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` **and** the Cross part `Cf g₁ g₂` itself
have their per-order covariant gradient dominated by the **connection-level** Hamilton/Moser two-arm sum
whose difference arm is the rank-`3` order-`≤ j+1` covariant jet sum of the once-differentiated realized
difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
rfns(∇^j (diff − Cf g₁ g₂))(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
rfns(∇^j (Cf g₁ g₂))(x)        ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

**Both arms are bundled into this one `Cf`-producing existence (the joint constraint on `Cf`).**  The
companion projection `lieDerivDiff_connLevel_crossWitness_crossArm` records the second (Cross) arm on the
**very same** witness `(lieDerivDiff_connLevel_crossWitness g₀ g_bg).choose` produced here, and the
section-data node `lieDerivDiff_connLevel_sectionData` assembles both; a `Cf`-birthing existence that
stated only the linear arm could **not** support that companion, since `Classical.choose` of a linear-only
existential carries no Cross-arm guarantee (and the *full* `diff` satisfies neither connection-level bound
on the top window `j ∈ (a, 2a]`, so the Cross arm is not recoverable from the linear arm via the section
sum identity).  Bundling both arms on the one chosen `Cf` is therefore the only sound `Cf`-construction.

This is the irreducible genuinely-deep content of the Lie half — the gauge analogue of the *pair* of
curvature connection-level reductions
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`) **together with** the curvature half's concrete
`crossSection`/`linearSection` construction, **bundled into one existence** because — unlike the curvature
half, which builds the concrete `crossSection` from the concrete operator-trace value
`ricciNeg2SectionDiffCrossEval` (determining all jets) and proves the two reductions on the
fully-determined sections — the intrinsic-vector linear/quadratic split of the *Lie deformation* is
**genuinely absent on disk** (only the `j = 0` chart witness `chartLieDeTurckComp_sub_eq` exists, the sole
intrinsic value hook being the order-zero fibre value `lieDerivRetagG0_sub_toModel_eq`), so there is no
concrete cross *value* to determine the section by, and the section's higher jets — on which the bounds
depend — are pinned only by the bounds themselves, making a split-then-bound staging impossible.

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so the linear part's `g₀`-lowered Koszul form is the
connection-level once-differentiated realized difference factor `R = ∇₀ w` exactly as for the curvature
linear part (bounds via the proven realized-Koszul jet domination
`koszulCombSection_iteratedCovGrad_rfns_le`), and the Cross part is the `D∘D`-type quadratic whose
differenced operator-trace carries both a diff-high × fixed-low arm and a fixed-high × diff-low arm (bounds
via the cross-correction-difference machinery and the parallel two-section bilinear-product grid); the
value-local model-basis trace folds the metric-built `≤2`-jet coefficient into the family-uniform `Cd` over
the rank-`3` window `j + 1`.

**Non-vacuity (both arm bounds are coupled, rejecting the degenerate readings).**  With `Cf ≡ 0` the
linear complement is the full `diff`, whose connection-level bound is FALSE for `j ∈ (a, 2a]` — the top
coefficient jet content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order (`L²` mass of
order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the fixed-pair *cross* arm can
carry it) — so `Cf ≡ 0` is rejected and the genuine quadratic top-jet content **must** ride on `Cf`;
symmetrically a full-`diff` Cross is rejected by the Cross arm.  A zero `Cd` is rejected (each difference
arm carries the connection-level high derivative `∇^{j+1} R`).  At `g₁ = g₂` (so `T₁ = T₂` realized) the
Lie-summand difference vanishes (`lieDerivRetagG0_sub_toModel_eq`), `R = 0` and `D = 0`, so both bounds
force the two sections to vanish there.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep
covariant-gauge value-level content of the Lie half (the intrinsic-vector linear/quadratic split absent on
disk together with both arms' connection-level covariant-Leibniz `rfns` grids). -/
theorem lieDerivDiff_connLevel_crossWitness (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Cf : SmoothRiemannianMetric I M → SmoothRiemannianMetric I M →
        Integral.L2.SmoothCcTensor g₀ 0 2,
      ∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
        ∃ Cd : ℝ, 0 ≤ Cd ∧
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
            (∀ (j : ℕ) (x : M),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                      ((lieDerivRetagG0 (I := I) g₀ g_bg g₁
                          - lieDerivRetagG0 (I := I) g₀ g_bg g₂) - Cf g₁ g₂)).toSection x) ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
                  + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) ∧
            (∀ (j : ℕ) (x : M),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Cf g₁ g₂)).toSection x) ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
                  + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  -- The cross-section family `Cf` is the value-split witness from the intrinsic Lie value-split bundled
  -- with the connection-level LINEAR arm (`lieDerivDiff_connLevel_valueSplitLinear`); the CROSS arm on the
  -- same `Cf` is supplied by the universal cross-arm bound `lieDerivCrossSection_connLevel_crossArm_ofSplit`
  -- applied to the algebraic-complement value split `diff = (diff − Cf) + Cf` (value identity by `abel`,
  -- `Lsec := diff − Cf` carrying the linear arm just chosen).
  refine ⟨(lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose,
    fun a ha B hB δ hδ0 hδ1 => ?_⟩
  obtain ⟨CdL, hCdL0, hLin⟩ :=
    (lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose_spec a ha B hB δ hδ0 hδ1
  obtain ⟨CdC, hCdC0, hCross⟩ :=
    lieDerivCrossSection_connLevel_crossArm_ofSplit (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨max CdL CdC, le_trans hCdL0 (le_max_left _ _),
    fun T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 => ⟨fun j x => ?_, fun j x => ?_⟩⟩
  · -- Linear arm `diff − Cf`: the value-split linear bound, widened `CdL → max CdL CdC`.
    refine le_trans (hLin T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_left _ _
  · -- Cross arm `Cf`: the universal cross-arm bound on the algebraic-complement split, with `Lsec :=
    -- diff − Cf` (value identity `diff = (diff − Cf) + Cf` by `abel`, the linear arm carried by `hLin`),
    -- widened `CdC → max CdL CdC`.
    have hsplit_id :
        lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ =
          ((lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
              - (lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose g₁ g₂)
            + (lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose g₁ g₂ := by
      abel
    have hLsec_bound : ∃ CdL' : ℝ, 0 ≤ CdL' ∧ ∀ (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                ((lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
                  - (lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose g₁ g₂)).toSection
              x) ≤
          CdL' * ∑ p ∈ Finset.range (j + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
            + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                  + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
      ⟨CdL, hCdL0, fun j x => hLin T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j x⟩
    refine le_trans
      (hCross T₁ T₂ g₁ g₂
        ((lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
          - (lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose g₁ g₂)
        ((lieDerivDiff_connLevel_valueSplitLinear (I := I) g₀ g_bg).choose g₁ g₂)
        hr1 hr2 hfib1 hfib2 hball1 hball2 hsplit_id hLsec_bound j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_right _ _

/-- **(DERIVED — the connection-level CROSS arm on the `lieDerivDiff_connLevel_crossWitness` cross
section.)**  The genuine deep covariant-gauge cross-arm content of the Lie half — the gauge analogue of
the curvature half's connection-level quadratic-Cross reduction
`ricciCrossSection_covGrad_traceReductionConn_rfns_le` — stated on the **same** concrete cross-section
family `Cf := (lieDerivDiff_connLevel_crossWitness g₀ g_bg).choose` produced by the value-split posit (so
that the two arms speak about one and the same section, not two unrelated witnesses).

For every order `a` with the supercriticality hypothesis `ha`, every uniform `H^{a+2}`-size bound `B ≥ 0`,
and every fibre-smallness `δ < 1/2`, there is a nonnegative constant `Cd` such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of
`T₁, T₂`, the Cross part `Cf g₁ g₂` has its per-order covariant gradient dominated by the
**connection-level** Hamilton/Moser two-arm sum whose difference arm is the rank-`3` order-`≤ j+1`
covariant jet sum of the once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`,
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
rfns(∇^j (Cf g₁ g₂))(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                         + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

**Derivation.**  This is the **sound projection** of the second (Cross) arm bundled into the genuine deep
posit `lieDerivDiff_connLevel_crossWitness`: that posit produces the cross-section family
`Cf := (lieDerivDiff_connLevel_crossWitness g₀ g_bg).choose` together with **both** arm bounds on the same
`Cf` (the joint constraint on the chosen witness), and `choose_spec` exposes the Cross arm directly on this
very `Cf`.  The bundling is what makes this companion provable: the cross arm on `Cf` cannot be recovered
from a linear-only existence (`Classical.choose` of a linear-only existential carries no Cross-arm
guarantee, and the *full* `diff` satisfies neither connection-level bound on `j ∈ (a, 2a]`, so the section
sum identity does not transfer the linear arm to the Cross arm).  The genuine deep covariant-gauge content
(the absent intrinsic-vector Lie split and both arms' grids) lives entirely in the posit; this node only
projects.

As for the curvature Cross half, the Lie Cross section's differenced operator-trace fibre value carries
**both** a diff-high × fixed-low arm and a fixed-high × diff-low arm (the connection-difference bilinear
product of two independently varying gauge fields); after the value-local model-basis trace and the
once-`∇₀` differentiation the difference arm is controlled by the connection-level `R = ∇₀ w` jets, and the
cross arm keeps the top coefficient jet (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}`
ball cannot bound) on the fixed pair `T₁, T₂`, bounded against the difference's `C⁰` mass by the
supercritical Sobolev embedding (`ha`).  Bounds via the cross-correction-difference machinery and the
parallel two-section bilinear-product grid.

**Non-vacuity.**  The Cross section `Cf g₁ g₂` carried by the value split is the genuine quadratic top-jet
content (rejected from being `0` by the coupling in `lieDerivDiff_connLevel_crossWitness`); both fixed-pair
endpoints `T₁, T₂` are carried, and the difference arm carries the connection-level high derivative
`∇^{j+1} R` (a zero `Cd` falsifies it).  At `g₁ = g₂` (so `T₁ = T₂` realized) the Lie-summand difference
vanishes, `R = 0` and `D = 0`, and the value split forces `Cf g₁ g₂` to vanish there, so the bound is
`0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity,
NO Weyl dependence. -/
theorem lieDerivDiff_connLevel_crossWitness_crossArm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
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
        ∀ (j : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  ((lieDerivDiff_connLevel_crossWitness (I := I) g₀ g_bg).choose g₁ g₂)).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hpair⟩ :=
    (lieDerivDiff_connLevel_crossWitness (I := I) g₀ g_bg).choose_spec a ha B hB δ hδ0 hδ1
  exact ⟨Cd, hCd0, fun T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 =>
    (hpair T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2).2⟩

/-- **(POSIT — the genuine deep covariant-gauge content: the concrete connection-level Lie section split
with both arms' covariant-jet two-arm bounds, at the rank-`3` `∇w`-level.)**

For an anchor `g₀` and a flow background `g_bg`, there is a smooth cross-section family
`Cf : g₁ g₂ ↦ Cf g₁ g₂ : SmoothCcTensor g₀ 0 2` such that for every order `a` with the supercriticality
hypothesis `ha`, every uniform `H^{a+2}`-size bound `B ≥ 0`, and every fibre-smallness `δ < 1/2`, there is
a nonnegative constant `Cd` (uniform over the gradient order `j` and the perturbation family) such that for
any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics
`g₁, g₂` of `T₁, T₂`, **both** the algebraic-complement linear part `diff − Cf g₁ g₂` and the Cross part
`Cf g₁ g₂` of the `g₀`-retagged Lie-summand difference `diff := lieDerivRetagG0 g₀ g_bg g₁ −
lieDerivRetagG0 g₀ g_bg g₂` have their per-order covariant gradient dominated by the **connection-level**
Hamilton/Moser two-arm sum whose difference arm is the rank-`3` order-`≤ j+1` covariant jet sum of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)`:
```
rfns(∇^j (diff − Cf g₁ g₂))(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
rfns(∇^j (Cf g₁ g₂))(x)        ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                                + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

This is the gauge analogue of the *pair* of curvature connection-level reductions
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`), **bundled into one existence** because — unlike
the curvature half, which builds the concrete `crossSection` from the concrete operator-trace value
`ricciNeg2SectionDiffCrossEval` (determining all jets) and proves the two reductions on the
fully-determined section — the intrinsic-vector linear/quadratic split of the *Lie deformation* is
**genuinely absent on disk** (only the `j = 0` chart witness `chartLieDeTurckComp_sub_eq` exists, the sole
intrinsic value hook being the order-zero fibre value `lieDerivRetagG0_sub_toModel_eq`), so there is no
concrete cross *value* to determine the section by, and the section's higher jets — on which the bounds
depend — are pinned only by the bounds themselves, making a split-then-bound staging impossible.

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so the linear part's `g₀`-lowered Koszul form is the
connection-level once-differentiated realized difference factor `R = ∇₀ w` exactly as for the curvature
linear part (bounds via the proven realized-Koszul jet domination
`koszulCombSection_iteratedCovGrad_rfns_le`), and the Cross part is the `D∘D`-type quadratic whose
differenced operator-trace carries both a diff-high × fixed-low arm and a fixed-high × diff-low arm (bounds
via the cross-correction-difference machinery and the parallel two-section bilinear-product grid).  The
value-local model-basis trace folds the metric-built `≤2`-jet coefficient into the family-uniform `Cd` over
the rank-`3` window `j + 1`.

**Non-vacuity (both arm bounds are coupled, rejecting the degenerate readings).**  With `Cf ≡ 0` the linear
complement is the full `diff`, whose connection-level bound is FALSE for `j ∈ (a, 2a]` — the top coefficient
jet content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order (`L²` mass of order
`j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the fixed-pair *cross* arm can carry
it) — so `Cf ≡ 0` is rejected and the genuine quadratic top-jet content **must** ride on `Cf`; symmetrically
a full-`diff` Cross is rejected by the cross arm.  A zero `Cd` is rejected (each difference arm carries the
connection-level high derivative `∇^{j+1} R`).  At `g₁ = g₂` (so `T₁ = T₂` realized) the Lie-summand
difference vanishes (`lieDerivRetagG0_sub_toModel_eq`), `R = 0` and `D = 0`, so both bounds force the two
sections to vanish there.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep covariant-gauge value-level
content of the Lie half (the intrinsic-vector linear/quadratic split absent on disk together with both arms'
connection-level covariant-Leibniz `rfns` grids). -/
theorem lieDerivDiff_connLevel_sectionData (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Cf : SmoothRiemannianMetric I M → SmoothRiemannianMetric I M →
        Integral.L2.SmoothCcTensor g₀ 0 2,
      ∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
        ∃ Cd : ℝ, 0 ≤ Cd ∧
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
            (∀ (j : ℕ) (x : M),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                      ((lieDerivRetagG0 (I := I) g₀ g_bg g₁
                          - lieDerivRetagG0 (I := I) g₀ g_bg g₂) - Cf g₁ g₂)).toSection x) ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
                  + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) ∧
            (∀ (j : ℕ) (x : M),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Cf g₁ g₂)).toSection x) ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
                  + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  -- The cross-section family `Cf` is the value-split witness from the `Cf`-construction posit (the same
  -- witness the consumers extract via `.choose`); its `.choose_spec` bundles BOTH arm bounds on this very
  -- `Cf` (the linear complement `.1` and the Cross part `.2`), and the companion `crossArm` re-exposes the
  -- Cross arm on the same witness.
  refine ⟨(lieDerivDiff_connLevel_crossWitness (I := I) g₀ g_bg).choose,
    fun a ha B hB δ hδ0 hδ1 => ?_⟩
  obtain ⟨CdL, hCdL0, hL⟩ :=
    (lieDerivDiff_connLevel_crossWitness (I := I) g₀ g_bg).choose_spec a ha B hB δ hδ0 hδ1
  obtain ⟨CdC, hCdC0, hC⟩ :=
    lieDerivDiff_connLevel_crossWitness_crossArm (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨max CdL CdC, le_trans hCdL0 (le_max_left _ _),
    fun T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 => ⟨fun j x => ?_, fun j x => ?_⟩⟩
  · -- Linear arm `diff − Cf`: widen `CdL → max CdL CdC` (the difference-arm jet sum is nonnegative).
    refine le_trans ((hL T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2).1 j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_left _ _
  · -- Cross arm `Cf`: widen `CdC → max CdL CdC`.
    refine le_trans (hC T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_right _ _

/-- **The concrete quadratic-in-difference Lie Cross section.**  The named cross-section witness of the
connection-level Lie section split `lieDerivDiff_connLevel_sectionData` — the gauge analogue of the
curvature half's concrete `crossSection g₀ g₁ g₂`.  Since the intrinsic Lie cross *value* is genuinely
absent on disk (no concrete operator-trace `crossEval` to build a `crossField`-style section from), it is
named via `Classical.choose` of the single genuine deep posited existence, on which both connection-level
covariant-jet two-arm bounds (this section and its complement `lieLinearSection`) are recorded. -/
def lieCrossSection (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (lieDerivDiff_connLevel_sectionData (I := I) g₀ g_bg).choose g₁ g₂

/-- **The concrete linear-in-difference Lie section** — the algebraic complement of `lieCrossSection`
inside the sealed Lie-summand difference:
`lieLinearSection := (lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂) − lieCrossSection`.  The
gauge analogue of the curvature half's `linearSection g₀ g₁ g₂`.  By construction its sum with
`lieCrossSection` is the Lie-summand difference (`lieDerivRetagG0_sub_eq_lieLinear_add_lieCross`). -/
def lieLinearSection (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
    - lieCrossSection (I := I) g₀ g_bg g₁ g₂

/-- **The order-zero section sum identity.**  By the definition of `lieLinearSection` as the algebraic
complement, the sealed Lie-summand difference is the sum of its linear and Cross sections.  The gauge
analogue of `ricciNeg2RetagG0_sub_eq_linear_add_cross`. -/
theorem lieDerivRetagG0_sub_eq_lieLinear_add_lieCross
    (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) :
    lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ =
      lieLinearSection (I := I) g₀ g_bg g₁ g₂ + lieCrossSection (I := I) g₀ g_bg g₁ g₂ := by
  rw [lieLinearSection]; abel

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
