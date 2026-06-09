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
                    * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  sorry

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
