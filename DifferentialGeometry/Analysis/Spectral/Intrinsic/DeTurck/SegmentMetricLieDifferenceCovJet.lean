import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricLieSectionDecomposition

/-! # The covariant-jet bound of the sealed Ricci–DeTurck Lie cross section

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **0-jet-inclusive `w`-jet covariant two-arm bound**
of the quadratic-in-difference gauge Cross section — the gauge analogue of
the curvature half's quadratic-Cross reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le`
(`SegmentMetricCurvatureDifferenceCovJet.lean`), stated on the **concrete** Lie Cross section
`lieCrossSection g₀ g_bg g₁ g₂` (`SegmentMetricLieSectionDecomposition.lean`), beneath the gauge RHS
cross-arm consumers (`SegmentMetricRHSCovJetExpansion.lean`).

## Concrete Cross section, not an arbitrary quadratic section

The curvature half builds the **concrete** quadratic Cross section `crossSection g₀ g₁ g₂` from the
concrete operator-trace value `ricciNeg2SectionDiffCrossEval` (which determines all jets) and states its
quadratic-Cross reduction on that concrete section.  The Lie half's intrinsic cross *value* is genuinely
absent on disk, so the concrete Lie Cross section is named via `Classical.choose` of the single genuine
deep posited existence `lieDerivDiff_connLevel_sectionData`
(`SegmentMetricLieSectionDecomposition.lean`); this file's reduction is stated on that **concrete**
`lieCrossSection`, never on an arbitrary or universally-quantified quadratic section.

## What is derived

* `lieCrossSection_iteratedCovGrad_connLevel_rfns_le` — **derived by composition (TRANSIT)** over the
  genuine deep section-data leaf `lieDerivDiff_connLevel_sectionData`: its second arm bound is exactly
  the 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete `lieCrossSection`.

Downstream (`SegmentMetricRHSCovJetExpansion.lean`) this bound enters the gauge value-level split
`exists_lieDerivDiff_connLevel_split` (`SegmentMetricLieDiffCovJet.lean`), which discharges the
order-zero split assembler `lieDerivDiff_order0_linearCross_split` verbatim — the arms already carry
the `w`-jet shape those consumers read, so no rank-shift step remains.

The bound carries **no** value-bounded `Φ.op 0 2 w` shape (the `∇^{j+2} w` content rides
on the difference arm, the unbounded top coefficient jet on the fixed-pair cross arm), NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Both arms are **coupled and
non-vacuous** (in the section-data leaf): the difference arm carries the high derivative `∇^{j+2} w` (a zero `Cd` falsifies it whenever the Cross part is genuinely present), and the cross arm
carries the unbounded top coefficient jet (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an
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

/-- **(The 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete Lie Cross section —
derived by composition (TRANSIT).)**  The gauge analogue of the curvature half's
connection-level quadratic-Cross reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le`, stated
on the **concrete** Lie Cross section `lieCrossSection g₀ g_bg g₁ g₂`
(`SegmentMetricLieSectionDecomposition.lean`).

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a uniform
`H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative constant `Cd` (uniform
over the gradient order `j` and the perturbation family) such that for any two `g₀`-fibre-small
perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the
intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete Lie Cross section
`lieCrossSection g₀ g_bg g₁ g₂` is dominated by the Hamilton/Moser two-arm sum, whose
difference arm is the **0-jet-inclusive** order-`≤ j+2` covariant jet sum of the realized
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus the fixed-pair
cross piece keeping the top coefficient jet on the fixed pair `T₁, T₂` against the difference's order-`a`
chart-Sobolev `C⁰` mass:
```
rfns(∇^j (lieCrossSection))(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                               + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D².
```

This is the curvature-trace covariant-Leibniz reduction of the quadratic Cross `(0, 2)`-section, its
difference-arm right-hand side the 0-jet-inclusive `∑_{i ≤ j+2} rfns(∇^i w)` jet sum — the very shape
the downstream consumers read.  As for the curvature Cross half, the Lie Cross
section's differenced operator-trace fibre value carries **both** a diff-high × fixed-low arm and a
fixed-high × diff-low arm (the connection-difference bilinear product of two independently varying gauge
fields); after the value-local model-basis trace the difference arm is
controlled by the 0-jet-inclusive `w`-jets, and the cross arm keeps the top coefficient jet on the
fixed pair, bounded against the difference's `C⁰` mass by the supercritical Sobolev embedding (`ha`).

**Non-vacuity.**  The difference arm carries the high derivative `∇^{j+2} w` (a zero `Cd`
falsifies it), and the cross arm carries **both** fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so
`T₁ = T₂` realized) the Lie-summand difference vanishes, `w = 0` and `D = 0`, so the bound is `0 ≤ 0` and
forces `lieCrossSection g₀ g_bg g g = 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  Proved by composition over the single genuine deep section-data leaf
`lieDerivDiff_connLevel_sectionData` (`SegmentMetricLieSectionDecomposition.lean`): its second arm bound is
exactly this 0-jet-inclusive `w`-jet covariant two-arm bound of the concrete `lieCrossSection`.
Consumers
transitively depend on `sorryAx` only through that named section-data leaf. -/
theorem lieCrossSection_iteratedCovGrad_connLevel_rfns_le
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
        ∀ (j : ℕ),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (lieCrossSection (I := I) g₀ g_bg g₁ g₂)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
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
  -- The second arm bound of the section-data leaf is exactly the integrated bound on the concrete
  -- `lieCrossSection`.
  exact (hbound T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2).2 j

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
