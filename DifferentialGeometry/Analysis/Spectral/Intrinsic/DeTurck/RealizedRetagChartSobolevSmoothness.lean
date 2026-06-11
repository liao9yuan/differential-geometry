import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSHighOrderSobolevLipschitz
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.BanachAlgebraSmoothness

/-! # `C^∞`-on-the-validity-ball of the chart-Sobolev realized DeTurck *retag* (the deep
inverse-Gram Neumann posit)

This file isolates, as a single consumer-minimal posit, the genuinely **deep analytic** content of
the realized Ricci–DeTurck remainder's all-order chart-Sobolev smoothness: that the intrinsic
chart-Sobolev class of the realized DeTurck **retag** `deTurckRHSRetag g₀ g_bg g₁`
(`= −2 Ric(g₁) + 𝓛 g₁`, the rational `Ric + Lie` summand of the realized metric `g₁`) is a
`ContDiffOn ℝ ∞` function of the chart-Sobolev class of the underlying perturbation `T`, on a
validity ball small enough that the supercritical embedding `H^q ↪ C⁰` keeps every section
uniformly fibre-small (so the realized metric stays uniformly non-degenerate).

## Why this is the irreducible deep stratum (the existing engine is insufficient)

The on-disk Ricci–DeTurck-RHS Sobolev tower (`RHSHighOrderSobolevLipschitz.lean`) controls only the
**first difference** of the retag, `‖(retag g₁ − retag g₂).toHs a‖ ≤ C · ‖(T₁ − T₂).toHs (a+2)‖`
(`exists_deTurckRHSRetagDiff_pouHa_le_toHs_highOrder`, the order-`a` Nemytskii Lipschitz bound); a
**Lipschitz** bound yields `ContinuousOn` (it is exactly what the on-disk order-`0` node
`deTurckRealizeRemainderOf_pouToHs_continuous_of_chartJet2Control` uses), but **not** `ContDiffOn`:
Lipschitz continuity carries no derivative.  Moreover the retag *value*
`deTurckRicciRHS g_bg g₁ = (−2)·ricciTensor g₁ + 𝓛_{deTurckVF g₁ g_bg} g₁` is exposed only as an
**opaque geometric section**, not as a chart-explicit rational-polynomial in the realized metric's
`≤ 2`-jet.  So `ContDiffOn` genuinely requires constructing the analytic (power-series / iterated
Fréchet) structure that the Lipschitz engine does not provide.

## The intended fill route (the Banach-algebra spine this file imports)

On the uniform-nondegeneracy ball the realized metric's `≤ 2`-jet enters the retag **rationally**:
the inverse Gram is a uniformly-convergent Neumann series (`Ring.inverse (1 − ·)`, the small
perturbation `g₁ − g₀`), and the Christoffel/Ricci/Lie numerators are bounded multilinear
contractions of that jet.  Discharging the posit is therefore a composition of (i) the
chart-Sobolev multiplication / multilinear-contraction smoothness (a supercritical Sobolev Banach
algebra structure, presently unbuilt at the `toHs` level), and (ii) the Banach-algebra inverse /
Neumann smoothness, for which this file already imports the sorry-free reusable spine
`DifferentialGeometry.Analysis.BanachAlgebraSmoothness`
(`contDiffOn_ringInverse_comp`, `contDiffOn_oneSub_inverse_comp`, `contDiffOn_bilinDiag`).  The
remaining gap is the chart-Sobolev product-smoothness layer plus the chart-rational representation
of the abstract `Ric + Lie` section — its own future fill, possibly multi-dispatch.

## The truncation litmus (why the ball is essential)

The analogous *global* claim is **false**: the finite `dif`-truncation of the perturbation-indexed
remainder switches the value to `0` across the fibre-small boundary `δ ↗ 1`, where the genuine
retag does not vanish (the inverse Gram blows up) — a value jump, hence a non-removable first-order
kink.  The radius-`ρ` ball excises that boundary.  T6: purely spatial. -/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 3200000

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **`C^∞`-on-the-validity-ball of the chart-Sobolev-valued realized DeTurck retag (the deep
inverse-Gram Neumann posit; body `sorry`).**

For a supercritical spectral order `a` (`2 a > dim M + 4`) and an intrinsic chart-Sobolev input
order `q ≥ a + 2` (the honest two-derivative loss), there is a radius `ρ > 0` and a map
`Ξ : TensorPouSobolevHilbert g₀ 0 2 q → TensorPouSobolevHilbert g₀ 0 2 a` that is `ContDiffOn ℝ ∞`
on the closed `H^q`-ball of radius `ρ` and factors the chart-Sobolev class of the realized DeTurck
**retag** through `SmoothCcTensor.toHs q`: for every smooth section `T` whose `H^q` class
`(T).toHs q` lies in the ball, `T` is fibre-small (`hfib`, an explicit existential witness, since
the ball radius forces `H^q ↪ C⁰` uniform non-degeneracy) and
```
Ξ ((T).toHs q) = (deTurckRHSRetag g₀ g_bg g₁).toHs a ,
```
where `g₁ = tensorSectionRealizeMetric g₀ T hfib.choose_spec.1 hfib.choose_spec.2` is the realized
metric built from that very witness.  Bundling the witness with the factoring lets a downstream
consumer (the perturbation-indexed `deTurckRealizeRemainderOf` retag arm) match its own
`dif`-reduced realized metric without re-deriving fibre-smallness.

This is the genuinely **nonlinear** (rational-polynomial / inverse-Gram-Neumann) content: the
linear `Δ_∇` summand has been removed (this is the bare `Ric + Lie` retag), so it is strictly
distinct from the linear rough-Laplacian CLM and from the full realized-remainder smoothness; no
packaging.

The body is `sorry`: it is the irreducible deep analytic content described in the module docstring
(the chart-Sobolev product-smoothness layer composed with the imported Banach-algebra inverse /
Neumann spine, on top of a chart-rational representation of the abstract `Ric + Lie` section), its
own future fill.  T6: purely spatial. -/
theorem exists_deTurckRHSRetag_toHs_contDiffOn_ball
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (q : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) (hq : a + 2 ≤ q) :
    ∃ (ρ : ℝ) (Ξ : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q →
        IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 a),
      0 < ρ ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) Ξ
        (Metric.closedBall
          (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ) ∧
      ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q T ∈
            Metric.closedBall
              (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ →
          ∃ hfib : ∃ δ : ℝ, δ < 1 ∧
              gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ,
            Ξ (IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q T)
              = IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
                  (deTurckRHSRetag (I := I) g₀ g_bg
                    (tensorSectionRealizeMetric (I := I) g₀ T hfib.choose_spec.1
                      hfib.choose_spec.2)) := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

end
