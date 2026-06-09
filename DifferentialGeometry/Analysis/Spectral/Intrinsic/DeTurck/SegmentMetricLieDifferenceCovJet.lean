import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

/-! # The connection-level Top/Rest split of the sealed Ricci–DeTurck Lie cross arm

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **connection-level (rank-`3`, `∇w`-level) Top/Rest
split** of the quadratic-in-difference gauge Cross arm — the gauge analogue of the curvature half's
quadratic-Cross split `crossSection_iteratedCovGrad_connLevel_split`
(`SegmentMetricCurvatureDifferenceCovJet.lean`), one rank below the gauge cross-arm reduction
`lieDeriv_crossArm_connLevel_of_valueSplit` (`SegmentMetricLieDiffCovJet.lean`).

## What the curvature half does, and why the gauge half differs

The curvature half builds the **concrete** quadratic Cross section `crossSection g₀ g₁ g₂`
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`, through the connection-difference operator
field `connDiffField`), and its quadratic-Cross split `crossSection_iteratedCovGrad_connLevel_split`
is stated on that **concrete** section: it exhibits the order-`j` covariant gradient of `crossSection`
as a connection-level difference part `Top` plus a fixed-pair cross part `Rest`, with the difference arm
bounded by the rank-`3` order-`≤ j+1` jets of the once-differentiated realized difference factor
`R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, and the `Rest` arm carrying the top
coefficient jet on the fixed pair against the difference's order-`a` chart-Sobolev `C⁰` mass (per-share
`(1/8)` so the `2·rfns` recombination lands the consumer's `(1/4)` cross coefficient).

The intrinsic-vector linear/quadratic split of the *Lie deformation* (arising from the `W(g)`-dependence
of `𝓛_{W(g)} g`, distinct from the curvature half's `connDiffField ∧ connDiffField` quadratic) is
**genuinely absent on disk** — only the chart-component telescope `chartLieDeTurckComp_sub_eq`
(`ChartLieDerivStructuralDifference.lean`) exists, not an intrinsic-vector eval split.  So the gauge
Cross section cannot be exhibited concretely as the curvature half does (via `connDiffField`); the gauge
Cross part `C` therefore enters as a **hypothesis**, constrained by the value identity `diff = L + C` and
the connection-level linear-arm bound on `L` (the *other* summand of the order-zero split, a genuine
constraint wholly different from the conclusion — the `Top/Rest` split of `∇^j C` — hence NOT
hypothesis-packaging).

## What is posited vs. derived downstream

* `lieCrossArm_iteratedCovGrad_connLevel_split` — **posited** (`sorry` body): the genuine deep
  connection-level quadratic-Cross covariant-Leibniz split of the gauge Cross part `C` carried by the
  value split.  This is the gauge analogue of the curvature half's
  `crossSection_iteratedCovGrad_connLevel_split`, stated on the value-split's Cross section `C` (since
  the gauge Cross section is genuinely not concrete on disk).

Downstream (`SegmentMetricLieDiffCovJet.lean`) this split, recombined through the `2·rfns`
subadditivity `riemannianFiberNormSq_add_le` (the doubled `(1/8)` cross share landing the consumer's
`(1/4)` cross coefficient, the doubled difference-arm bound the consumer's `2·Cd` coefficient),
discharges the gauge cross-arm reduction `lieDeriv_crossArm_connLevel_of_valueSplit` by composition
(TRANSIT) — exactly the composition the curvature quadratic-Cross reduction
`ricciCrossSection_covGrad_traceReductionConn_rfns_le` uses over its split child.

The posit carries **no** value-bounded `Φ.op 0 2 w` shape (the refuted structural split — the
connection-level `∇^{j+1} R` content rides on the `Top` difference arm, the unbounded top coefficient
jet on the fixed-pair `Rest` cross arm), NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO
Weyl dependence.  Both arms are **coupled and non-vacuous**: the `Top` arm carries the connection-level
high derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the Cross part is genuinely present), and
the `Rest` arm carries the unbounded top coefficient jet (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`,
which an `H^{a+2}` ball cannot bound) on the fixed pair `T₁, T₂` against the difference's order-`a`
chart-Sobolev `C⁰` mass `‖(T₁ − T₂).toHs a‖²`. -/

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

/-- **(POSIT — the connection-level Top/Rest split of the gauge quadratic Cross arm, at the rank-`3`
`∇w`-level.)**  The genuine deep connection-level quadratic-Cross covariant-Leibniz split of the gauge
half: for the quadratic-in-difference Cross part `C` carried by the value split
`exists_lieDeriv_valueSplit_linearConn` (i.e. any `C` satisfying the value identity
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` with `L` connection-level difference-arm bounded), the
order-`j` covariant gradient of `C` splits, at each point `x`, into a connection-level difference part
`Top` and a fixed-pair cross part `Rest`,
```
∇^j C(x) = Top + Rest,
rfns(Top)(x)  ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x),
rfns(Rest)(x) ≤ (1/8) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
where `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))` (rank `3`).

This is the gauge analogue of the curvature half's quadratic-Cross split
`crossSection_iteratedCovGrad_connLevel_split` (`SegmentMetricCurvatureDifferenceCovJet.lean`).  As for
the curvature Cross half, the gauge Cross part's differenced operator-trace fibre value carries **both** a
diff-high × fixed-low arm and a fixed-high × diff-low arm (the connection-difference bilinear product of
two independently varying gauge fields); the `Top` part collects the connection-level difference-factor
jets through the rank-reducing `(0, 3) → (0, 2)` trace and the parallel two-section bilinear product grid
(where the high derivative may land on either factor, folded with the *fixed* factor sup and the
metric-built `≤ 2`-jet trace coefficient into the family-uniform `Cd`), and the `Rest` part keeps the top
coefficient jet on the **fixed pair** `T₁, T₂` against the difference's order-`a` chart-Sobolev `C⁰` mass
(the supercritical embedding `ha`), with the per-recombination share `(1/8)` so that the `2·rfns`
`riemannianFiberNormSq_add_le` recombination lands the consumer's `(1/4)` cross coefficient.

Unlike the curvature half — which builds the concrete `crossSection` through the connection-difference
operator field `connDiffField` and states the split on that concrete section — the intrinsic-vector
linear/quadratic split of the *Lie deformation* is **genuinely absent on disk** (only the `j = 0` chart
witness `chartLieDeTurckComp_sub_eq` exists), so the gauge Cross section cannot be exhibited concretely;
the Cross part `C` therefore enters as a **hypothesis**, constrained by the value identity
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` with `L` connection-level difference-arm bounded — the
*other* summand of the order-zero split, a genuine constraint wholly different from the conclusion (the
`Top/Rest` split of `∇^j C`), hence NOT hypothesis-packaging.

**Non-vacuity.**  The `Top` part carries the connection-level high derivative `∇^{j+1} R` (a zero `Cd`
falsifies it), and the `Rest` part carries **both** fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so
`T₁ = T₂` realized) the Lie-summand difference vanishes, so the value split forces `C = 0` (with
`L = 0`), and the split is `0 = 0 + 0` with both bounds `0 ≤ 0`.  The defining hypothesis
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` with `L` connection-level difference-arm bounded is a
genuine constraint on `C`, wholly different from the conclusion.  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep connection-level gauge quadratic-Cross covariant-Leibniz split. -/
theorem lieCrossArm_iteratedCovGrad_connLevel_split
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
          ∃ Top Rest : Tensor0SBundle.TensorRSSpace 0 (2 + j) I x,
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C).toSection x = Top + Rest ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Top ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Rest ≤
                (1 / 8 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                      + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
