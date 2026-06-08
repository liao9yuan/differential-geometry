import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

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
gauge difference admits the **identical connection-level linear/cross split** as the curvature half: a
linear-in-difference part `L` whose `g₀`-lowered Koszul form is the connection-level once-differentiated
realized difference factor `R = ∇₀ w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus a
quadratic-in-difference cross part `C` (the `D∘D`-type quadratic, `D = connDiffField g g₀`) carrying the
top coefficient jet on the fixed pair `T₁, T₂`.

## What the curvature half does, and why the gauge half differs

The curvature half builds the **concrete** quadratic Cross section `crossSection g₀ g₁ g₂`
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`, through the connection-difference operator field
`connDiffField`) and the linear part as its algebraic complement `linearSection := diff − crossSection`;
the difference-arm/Cross-arm covariant-jet bounds are then stated on the two **concrete** sections
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`), each proved by composition over the
connection-level splits.  Crucially, the curvature Cross reduction is stated on the **concrete**
`crossSection`, never on an arbitrary quadratic section.

The intrinsic-vector linear/quadratic split of the *Lie deformation* (which arises from the
`W(g)`-dependence of `𝓛_{W(g)} g`, distinct from the curvature half's `connDiffField ∧ connDiffField`
quadratic) is **genuinely absent on disk** — only the chart-component telescope `chartLieDeTurckComp_sub_eq`
(`ChartLieDerivStructuralDifference.lean`, the `j = 0` chart witness, exhibiting the Lie-summand
difference as a finite sum of products of metric `≤2`-jets, each carrying a single
Gram/vector-field-component difference factor) exists, not an intrinsic-vector eval split.  So the gauge
linear/cross sections cannot be *exhibited concretely* (the curvature half's `connDiffField`-built
construction has no on-disk Lie counterpart); the value split is therefore stated **existentially**, with
its two arm bounds **bundled** into the single posit below (the value split and the arm bounds being
mathematically inseparable: a degenerate `C = 0` reading — under which `L = diff` and the linear-arm bound
is FALSE for `j ∈ (a, 2a]` — is rejected only by the linear-arm bound).

## What is posited vs. derived downstream

* `exists_lieDerivDiff_connLevel_split` — **posited** (`sorry` body): the genuine deep covariant-gauge
  value-level content of the Lie half — the existence of the intrinsic-vector linear/quadratic split
  `(L, C)` of the `g₀`-retagged Lie-summand difference, **bundled** with both arms' **connection-level**
  (rank-`3`, `∇w`-level) covariant-jet two-arm bounds, with a single difference-arm constant uniform over
  the gradient order `j` and over the supercritical `H^{a+2}`-bounded perturbation family.  This is the
  gauge analogue of the *pair* of curvature reductions
  (`ricciLinearSection_covGrad_traceReductionConn_rfns_le` and
  `ricciCrossSection_covGrad_traceReductionConn_rfns_le`), bundled because the split is existential.

Downstream (`SegmentMetricRHSCovJetExpansion.lean`) this single connection-level posit, composed with the
**sorry-free** front/back-commutation rank-shift `connLevel_diffArm_to_wJet_le`
(`rfns(∇^p R) = rfns(∇^{p+1} w)`), discharges the Lie-half value-level node
`exists_lieDerivLinearCross_section_connLevel` and the order-zero split assembler
`lieDerivDiff_order0_linearCross_split` directly — supplying the concrete linear/Cross section pair with
both `w`-jet arm bounds the order-`a` chart-RHS tower consumes.

The posit carries **no** value-bounded `Φ.op 0 2 w` shape (the refuted structural split — the
connection-level `∇^{j+1} R` content rides on the difference arm, the unbounded top coefficient jet on the
fixed-pair cross arm), NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.
Both arm bounds are **coupled and non-vacuous**: the difference arm carries the connection-level high
derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the linear part is genuinely present), and the
cross arm carries the unbounded top coefficient jet (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an
`H^{a+2}` ball cannot bound) on the fixed pair `T₁, T₂` against the difference's order-`a` chart-Sobolev
`C⁰` mass `‖(T₁ − T₂).toHs a‖²`. -/

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

/-- **(POSIT — the connection-level gauge value-level linear/cross split bundled with both arms'
covariant-jet bounds: the genuine Core-II value-level leaf of the Lie half, at the rank-`3` `∇w`-level.)**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a uniform
`H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative difference-arm constant
`Cd` (uniform over the gradient order `j` and the perturbation family) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of
`T₁, T₂`, the `g₀`-retagged Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg
g₂` splits as a **linear-in-difference** section `L` plus a **quadratic-in-difference Cross** section `C`
(genuine smooth `SmoothCcTensor g₀ 0 2`s), with **both** per-order covariant gradients satisfying the
**connection-level** Hamilton/Moser two-arm bound whose difference arm is the rank-`3` order-`≤ j+1`
covariant jet sum of the once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`,
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
rfns(∇^j C)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

This is the gauge analogue of the *pair* of curvature connection-level reductions
(`ricciLinearSection_covGrad_traceReductionConn_rfns_le`,
`ricciCrossSection_covGrad_traceReductionConn_rfns_le`), bundled into one existential posit because the
intrinsic-vector linear/quadratic split of the Lie deformation is genuinely absent on disk (only the
`j = 0` chart witness `chartLieDeTurckComp_sub_eq` exists), so the linear and Cross sections cannot be
exhibited concretely as the curvature half does (via `connDiffField`).  The Lie field `𝓛_{W(g)} g` has the
**same intrinsic order-`≤2` structure** as the curvature half, so the linear part's `g₀`-lowered Koszul
form is the connection-level once-differentiated realized difference factor `R = ∇₀ w` exactly as for the
curvature linear part (bounds via the proven realized-Koszul jet domination
`koszulCombSection_iteratedCovGrad_rfns_le`), and the Cross part is the `D∘D`-type quadratic whose
differenced operator-trace carries both a diff-high × fixed-low arm and a fixed-high × diff-low arm (bounds
via the cross-correction-difference machinery `crossCorrectionDiff_iteratedCovGrad_connLevel_split` and the
parallel two-section bilinear-product grid).  The value-local model-basis trace folds the metric-built
`≤2`-jet coefficient into the family-uniform `Cd` over the rank-`3` window `j + 1`.

**Non-vacuity (the value split and both arm bounds are coupled, rejecting the degenerate readings).**  With
`C = 0`, `L = diff` would have to satisfy the linear-arm bound, FALSE for `j ∈ (a, 2a]` — the top
coefficient jet content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order (`L²` mass of
order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the fixed-pair *cross* arm can
carry it).  So a valid witness `(L, C)` **must** put the genuine quadratic top-jet content into `C` — `C =
0` is rejected — and `L` is the genuine linear-in-difference part; symmetrically the cross-arm bound
rejects `L = 0` (then `C = diff` would fail it).  A zero `Cd` is rejected (each difference arm carries the
connection-level high derivative `∇^{j+1} R`).  At `g₁ = g₂` (so `T₁ = T₂` realized) the Lie-summand
difference vanishes and the split is `0 = 0 + 0` with both bounds `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w`
shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`:
the genuine deep covariant-gauge value-level content of the Lie half (the intrinsic-vector linear/quadratic
split absent on disk together with both arms' connection-level covariant-Leibniz `rfns` grid). -/
theorem exists_lieDerivDiff_connLevel_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
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
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L).toSection x) ≤
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
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C).toSection x) ≤
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

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
