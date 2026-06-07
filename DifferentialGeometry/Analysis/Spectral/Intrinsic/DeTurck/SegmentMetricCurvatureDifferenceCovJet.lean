import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-! # The curvature-trace covariant-jet reduction of the sealed Ricci–DeTurck curvature difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **curvature-trace covariant-jet reduction** beneath the
curvature difference-arm Core-II covariant-jet leaf of the Ricci–DeTurck right-hand-side expansion
(`SegmentMetricRHSCovJetExpansion.lean`).

The sealed curvature nonlinearity `-2 • Ric(g)` is the trace of the Levi-Civita curvature operator
(`RicciConnection.lean`).  Its segment difference normalises (at order zero,
`SegmentMetricCurvatureDifferenceOpDecomposition.lean`) into the concrete linear-in-difference section
`linearSection g₀ g₁ g₂`, whose fibre value is the model-basis trace of the linear (`∇₀ D`) order of
the per-metric Ricci difference (`D = connDiff gₖ g₀` the connection difference,
`ricciNeg2SectionDiffLinearEval`).  By the connection-difference cocycle
`connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` the linear part carries the single difference factor
`connDiff g₁ g₂`, whose metrically-lowered Koszul form is the realized covariant derivative
`covDerivRealizeEval g₀ (T₁ − T₂)` of the perturbation difference
(`connDiffDiff_g0_lowered_koszul_diffFactor`) — i.e. the connection-level first covariant gradient
`R := covGrad g₀ 0 2 w` of the realized difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

The genuine covariant-Faà-di-Bruno content beneath the difference-arm leaf is the **curvature-trace
covariant-Leibniz reduction**: the rank-`2` order-`j` covariant jet of `linearSection` is dominated by
the rank-`3` order-`≤ j + 1` covariant jets of the connection-level realized covariant gradient `R`
(the trace, the cocycle, and the metric-built `≤2`-jet coefficient folded into a family-uniform
constant `Cd`).  This is the connection-difference covariant-jet machinery of
`ConnectionDifferenceFieldJets.lean` (`koszulCombSection_iteratedCovGrad_rfns_le`,
`loweredConnDiffSection`) lifted through the curvature trace and the two-metric cocycle; that lift — the
curvature-trace covariant-Leibniz reduction of the difference-normal-form section to the connection
level — is genuinely absent on disk for the *difference* curvature (the connection-level file is
single-metric, rank-`3`).  Per the project's assume-and-recurse discipline, the reduction
`ricciLinearSection_covGrad_traceReduction_rfns_le` posits exactly this genuinely-missing covariant-FdB
content as the honest atomic boundary just below the leaf.

The reduction is **structurally distinct** from, and **strictly smaller** than, the consumer leaf: its
right-hand side is the **connection-level** `∇^{≤ j+1} R` jet sum (rank `3`, the `∇w`-level), not the
leaf's `∇^{≤ j+2} w` jet sum; the difference-arm leaf is then proved by composing this reduction with
the **sorry-free** rank-shift `rfns(∇^p R) = rfns(∇^{p+1} w)` (the front-commutation
`iteratedCovGrad_covGrad_comm_heq`, `R = covGrad g₀ 0 2 w`) and the window inclusion
`∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)`.  The reduction is **non-vacuous** (it carries
the connection-level high derivative `∇^{j+1} R`, so a zero constant falsifies it whenever the linear
part is genuinely present — `linearSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and
carries no value-bounded `Φ.op 0 2 w` shape (the refuted structural split), NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, and NO Weyl dependence. -/

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

/-- **(POSIT — the curvature-trace covariant-jet reduction of the linear difference section to the
connection level.)**  The intrinsic squared fibre norm of the order-`j` covariant gradient of the
concrete linear-in-difference curvature section `linearSection g₀ g₁ g₂` is dominated by the
order-`≤ j + 1` covariant jets of the **connection-level** first covariant gradient
`R := covGrad g₀ 0 2 w` of the realized difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, with
a nonnegative constant `Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)   (R = covGrad g₀ 0 2 w).
```

This is the genuine covariant-Faà-di-Bruno content of the curvature half's difference arm, stated at
the **connection level** (rank `3`, the `∇w`-level), strictly below the leaf's `w`-level: the sealed
curvature nonlinearity `-2 • Ric(g)` is the trace of the Levi-Civita curvature operator, and its
order-zero linear-in-difference part `linearSection` is the model-basis trace of the antisymmetrised
covariant-derivative-of-connection-difference `∇₀ D` (`ricciNeg2SectionDiffLinearEval`).  By the
cocycle `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` the trace carries the single difference
factor `connDiff g₁ g₂`, whose metrically-lowered Koszul form is the connection-level realized
covariant gradient `R = covGrad g₀ 0 2 w` of the perturbation difference
(`connDiffDiff_g0_lowered_koszul_diffFactor`, `koszulCombSection_iteratedCovGrad_rfns_le`); the
curvature trace (one further covariant derivative, the model-basis sum a fibre-bounded contraction) and
the binomial covariant-Leibniz `rfns` grid (`DiffBilinOp`) place the single high derivative on `R` up to
order `j + 1`, the metric-built `≤2`-jet coefficient folded into the family-uniform `Cd` (ball-uniform
by the order-`≤2` segment-metric jet sup `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`).

**Non-vacuity.**  It carries the connection-level high derivative `∇^{j+1} R`; a zero `Cd` falsifies it
whenever the linear part is genuinely present (`linearSection_self_toModel` shows it vanishes only when
`g₁ = g₂`).  It is **strictly smaller** than the difference-arm leaf — its right side is the
connection-level `∇^{≤ j+1} R` sum, not the leaf's `∇^{≤ j+2} w` sum — and is **not** the leaf restated
(the leaf is recovered by the sorry-free rank-shift `rfns(∇^p R) = rfns(∇^{p+1} w)` and window
inclusion).  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep curvature-trace
covariant-Leibniz reduction content. -/
theorem ricciLinearSection_covGrad_traceReduction_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
