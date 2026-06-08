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

* `exists_lieDeriv_valueSplit_linearConn` — **posited** (`sorry` body): the genuinely-absent intrinsic
  value content — the existence of the intrinsic-vector linear/quadratic split `(L, C)` of the
  `g₀`-retagged Lie-summand difference (`diff = L + C`), **bundled** with the linear part's
  **connection-level** (rank-`3`, `∇w`-level) covariant-jet two-arm bound.  This is the gauge analogue of
  the curvature half's value-split construction `ricciNeg2RetagG0_sub_eq_linear_add_cross` **together with**
  its linear reduction `ricciLinearSection_covGrad_traceReductionConn_rfns_le`, bundled into one existential
  because (unlike the curvature half, which builds the concrete `crossSection` via `connDiffField` and takes
  `linearSection` as its algebraic complement) the intrinsic-vector linear/quadratic split of the *Lie
  deformation* is genuinely absent on disk (only the chart witness `chartLieDeTurckComp_sub_eq` exists), so
  the linear and Cross sections cannot be exhibited concretely; the value split and the linear-arm bound are
  also mathematically inseparable (the degenerate `C = 0` reading is rejected only by the linear bound).

* `lieDeriv_crossArm_connLevel_of_valueSplit` — **posited** (`sorry` body): the gauge analogue of the
  curvature half's quadratic-Cross reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le`, stated
  on the value-split's Cross section `C` (since the gauge Cross section is not concrete, `C` enters as a
  hypothesis, constrained by the value identity `diff = L + C` and the linear bound — the *other* summand of
  the order-zero split, a genuine constraint wholly different from the conclusion, not hypothesis-packaging).

* `exists_lieDerivDiff_connLevel_split` — **derived by composition (TRANSIT)** over the two children: Child
  A produces the pair `(L, C)`, the value identity, and the connection-level linear-arm bound; Child B,
  fed that very pair with the value identity and the linear bound, produces the connection-level
  cross-arm bound.  The common constant is `max` of the two children's constants, widened on each arm.

Downstream (`SegmentMetricRHSCovJetExpansion.lean`) this bundled connection-level split, composed with the
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

/-- **(POSIT — the intrinsic Lie value split bundled with the connection-level linear-arm jet bound: the
genuinely-absent intrinsic-vector content of the Lie half, at the rank-`3` `∇w`-level.)**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a uniform
`H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative constant `Cd` (uniform
over the gradient order `j` and the perturbation family) such that for any two `g₀`-fibre-small
perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the
`g₀`-retagged Lie-summand difference splits as a **linear-in-difference** section `L` plus a
**quadratic-in-difference Cross** section `C` (genuine smooth `SmoothCcTensor g₀ 0 2`s), with the **linear**
part's per-order covariant gradient satisfying the **connection-level** Hamilton/Moser two-arm bound whose
difference arm is the rank-`3` order-`≤ j+1` covariant jet sum of the once-differentiated realized
difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

This is the gauge analogue of the curvature half's value-split construction
`ricciNeg2RetagG0_sub_eq_linear_add_cross` **together with** its connection-level linear reduction
`ricciLinearSection_covGrad_traceReductionConn_rfns_le`, **bundled into one existential** because, unlike
the curvature half — which builds the concrete `crossSection` through the connection-difference operator
field `connDiffField` and takes `linearSection := diff − crossSection` as its algebraic complement (so the
value split is a pure `abel` and the linear reduction a separate leaf) — the intrinsic-vector
linear/quadratic split of the *Lie deformation* (arising from the `W(g)`-dependence of `𝓛_{W(g)} g`,
distinct from the curvature half's `connDiffField ∧ connDiffField` quadratic) is **genuinely absent on
disk**: only the chart-component telescope `chartLieDeTurckComp_sub_eq`
(`ChartLieDerivStructuralDifference.lean`, the `j = 0` chart witness exhibiting the Lie-summand difference
as a finite sum of products of metric `≤2`-jets, each carrying a single Gram/vector-field-component
difference factor) exists, not an intrinsic-vector eval split.  So the linear/Cross sections cannot be
exhibited concretely as the curvature half does, and the value split and the linear-arm bound are
**mathematically inseparable** (the degenerate `C = 0` reading — under which `L = diff` and the linear-arm
bound is FALSE for `j ∈ (a, 2a]` — is rejected only by the linear-arm bound).

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so the linear part's `g₀`-lowered Koszul form is the
connection-level once-differentiated realized difference factor `R = ∇₀ w` exactly as for the curvature
linear part (bounds via the proven realized-Koszul jet domination `koszulCombSection_iteratedCovGrad_rfns_le`),
and the value-local model-basis trace folds the metric-built `≤2`-jet coefficient into the family-uniform
`Cd` over the rank-`3` window `j + 1`.

**Non-vacuity.**  With `C = 0`, `L = diff` would have to satisfy the linear-arm bound, FALSE for
`j ∈ (a, 2a]` (the top coefficient jet content of the full Lie difference is genuinely
`(∑ fixed-pair) · C⁰`-order, only the fixed-pair *cross* arm can carry it), so a valid witness `(L, C)`
**must** put the genuine quadratic top-jet content into `C` — `C = 0` is rejected.  A zero `Cd` is rejected
(the difference arm carries the connection-level high derivative `∇^{j+1} R`).  At `g₁ = g₂` (so `T₁ = T₂`
realized) the Lie-summand difference vanishes and the split is `0 = 0 + 0` with the bound `0 ≤ 0`.  NO
value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl
dependence.  Its body is `sorry`: the genuine deep covariant-gauge value-level content of the Lie half (the
intrinsic-vector linear/quadratic split absent on disk together with the linear arm's connection-level
covariant-Leibniz `rfns` grid). -/
theorem exists_lieDeriv_valueSplit_linearConn
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
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  sorry

/-- **(POSIT — the connection-level Lie cross-arm covariant-jet bound, stated on the value-split's Cross
section, at the rank-`3` `∇w`-level.)**  The gauge analogue of the curvature half's connection-level
quadratic-Cross reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le`, stated on the
value-split's Cross section `C` (since the gauge Cross section is genuinely not concrete on disk, `C`
enters as a hypothesis, constrained by the value identity `diff = L + C` and the connection-level linear
bound — the *other* summand of the order-zero split, a genuine constraint wholly different from the
conclusion, hence NOT hypothesis-packaging).

For every quadratic-in-difference Cross section `C` arising as the second component of the value split
`exists_lieDeriv_valueSplit_linearConn` (i.e. satisfying the value identity
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` with `L` connection-level difference-arm bounded), the
intrinsic squared fibre norm of the order-`j` covariant gradient of `C` is dominated by the
**connection-level** Hamilton/Moser two-arm sum, whose difference arm is the rank-`3` order-`≤ j+1`
covariant jet sum of the once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`,
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus the fixed-pair cross piece keeping the top coefficient jet on
the fixed pair `T₁, T₂` against the difference's order-`a` chart-Sobolev `C⁰` mass:
```
rfns(∇^j C)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D².
```

As for the curvature Cross half, the Lie Cross section's differenced operator-trace fibre value carries
**both** a diff-high × fixed-low arm and a fixed-high × diff-low arm (the connection-difference bilinear
product of two independently varying gauge fields, bounds via the cross-correction-difference machinery
`crossCorrectionDiff_iteratedCovGrad_connLevel_split` and the parallel two-section bilinear-product grid);
after the value-local model-basis trace and the once-`∇₀` differentiation the difference arm is controlled
by the connection-level `R = ∇₀ w` jets, and the cross arm keeps the top coefficient jet (`L²` mass of
order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound) on the fixed pair, bounded against
the difference's `C⁰` mass by the supercritical Sobolev embedding (`ha`).

**Non-vacuity.**  The Cross section `C` carried by the value split is the genuine quadratic top-jet content
(rejected from being `0` by the coupling in `exists_lieDeriv_valueSplit_linearConn`); both fixed-pair
endpoints `T₁, T₂` are carried, and the difference arm carries the connection-level high derivative
`∇^{j+1} R` (a zero `Cd` falsifies it).  The defining hypothesis
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` with `L` connection-level difference-arm bounded is a
genuine constraint on `C` (it is the *other* summand of the order-zero split), wholly different from the
conclusion (a per-order jet bound on `∇^j C`) — this is not hypothesis-packaging.  NO value-bounded
`Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its
body is `sorry`: the genuine deep covariant-gauge-jet content of the quadratic Cross arm at the connection
level. -/
theorem lieDeriv_crossArm_connLevel_of_valueSplit
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M)
        (L C : Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C →
        (∃ CdL : ℝ, 0 ≤ CdL ∧ ∀ (j : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L).toSection x) ≤
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
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

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
shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  Proven by composition over the two genuine Core-II deep children
`exists_lieDeriv_valueSplit_linearConn` (the value split `(L, C)` bundled with the connection-level
linear-arm bound, the genuinely-absent intrinsic content) and `lieDeriv_crossArm_connLevel_of_valueSplit`
(the connection-level cross-arm bound on that very `(L, C)` pair, with the value identity and the linear
bound as its constraining hypotheses).  The common constant is `max CdA CdB`; each arm is widened from its
child's constant upward (the difference-arm jet sum being nonnegative).  Consumers transitively depend on
`sorryAx` only through the two named children. -/
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
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  -- **Child A** (the genuinely-absent intrinsic value split): produces the pair `(L, C)`, the value
  -- identity `diff = L + C`, and the connection-level linear-arm two-arm bound on `∇^j L`.
  obtain ⟨CdA, hCdA0, hA⟩ :=
    exists_lieDeriv_valueSplit_linearConn (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  -- **Child B** (the cross-arm bound on the value-split's `C`): fed `(L, C)`, the value identity, and the
  -- connection-level linear bound, produces the connection-level cross-arm two-arm bound on `∇^j C`.
  obtain ⟨CdB, hCdB0, hBd⟩ :=
    lieDeriv_crossArm_connLevel_of_valueSplit (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨max CdA CdB, le_trans hCdA0 (le_max_left _ _), ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  obtain ⟨L, C, hLC, hLbd⟩ := hA T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  -- The connection-level cross-arm bound on this very `C` (Child B, fed the value split + linear bound).
  have hCbd :=
    hBd T₁ T₂ g₁ g₂ L C hr1 hr2 hfib1 hfib2 hball1 hball2 hLC ⟨CdA, hCdA0, hLbd⟩
  refine ⟨L, C, hLC, fun j x => ?_, fun j x => ?_⟩
  · -- Linear arm: widen `CdA → max CdA CdB` (the difference-arm jet sum is nonnegative).
    refine le_trans (hLbd j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_left _ _
  · -- Cross arm: widen `CdB → max CdA CdB`.
    refine le_trans (hCbd j x) ?_
    have hSRnn : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
      Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
    gcongr
    exact le_max_right _ _

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
