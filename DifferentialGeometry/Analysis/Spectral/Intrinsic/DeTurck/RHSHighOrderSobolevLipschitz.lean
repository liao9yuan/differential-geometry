import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding

/-! # The higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound

The on-disk coordinate Ricci–DeTurck-RHS Lipschitz
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (`RHSPointwiseLipschitz.lean`) is the **`C⁰`
base case**: it controls the chart-frame scalar DeTurck right-hand-side *value* difference by
the chart `2`-jet seminorm `chartMetricJet2DiffSup` of the metric difference (`2` derivatives
of the metric, `0` derivatives of the right-hand side).  That base case yields only the `H⁰`
(`L²`) norm of the right-hand-side difference, **never** the `Hᵃ` norm for `a ≥ 1`.

This file isolates the genuine **higher-order** analogue, the order-`a` Nemytskii bound: the
weighted-`Hᵃ` seminorm (`∑ᵢ (1+λᵢ)^a · |coeffᵢ|²`) of the `L²`-coordinate difference of the
realized Ricci–DeTurck *remainder* sections
`deTurckRHSSection g_bg gⱼ − rawTensorConnLapSmooth g₀ 0 2 Tⱼ`, where `gⱼ` is the realized
metric of the `g₀`-fibre-small perturbation `Tⱼ` (`gⱼ.inner = g₀.inner + ccTensorBilinSymm g₀
Tⱼ`), is controlled by the **`H^{a+2}` Sobolev norm** `‖(T₁ − T₂).toHs (a+2)‖` of the
perturbation difference — uniformly over a `H^{a+2}`-bounded family of perturbations (the
Nemytskii constant being uniform on a bounded family).  The order count is the honest one: the
DeTurck right-hand side is a second-order quasilinear operator in the metric, so its `Hᵃ` norm
needs `a + 2` derivatives of the metric, i.e. of the perturbation; this mirrors the on-disk
unconditional bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, which
controls the chart `2`-jet (the `a = 0` order) by the intrinsic `H^{2k}` norm of the
perturbation difference.

It is the genuine deep analytic input of the order-`a` chart-RHS tower (the higher-order
Nemytskii bound for the second-order DeTurck operator), stated entirely in pre-existing
objects (`deTurckRHSSection`, `rawTensorConnLapSmooth`, `tensorL2Coeff`, `tensorSobolevWeight`,
`SmoothCcTensor.toHs`) plus a fibrewise `inner`-identity tying each metric to its perturbation:
it carries no dependence on the spectral nonlinearity `deTurckG0SpectralN` or the
perturbation-indexed remainder `deTurckRealizeRemainderOf`, so the genuine-nonlinearity file
consumes it without an import cycle.  Its body is `sorry`: it is the genuine order-`a`
chart-RHS-tower content (the higher-order quasilinear Nemytskii estimate), with no spectral or
Weyl dependence. -/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The realized Ricci–DeTurck remainder section of a perturbation and its realized metric.**

For an anchor `g₀`, a flow background `g_bg`, a `g₀`-fibre-small perturbation `T`, and *any*
smooth metric `g₁` that is the realized metric of `T` (`g₁.inner = g₀.inner + ccTensorBilinSymm
g₀ T`, fibrewise — supplied as a hypothesis rather than constructed, so this is independent of
the `δ`-witness machinery of `tensorSectionRealizeMetric`), this is the `g₀`-tagged DeTurck
remainder `deTurckRHSSection g_bg g₁ − rawTensorConnLapSmooth g₀ 0 2 T`.  It is the chart-frame
section whose `L²` coordinates the higher-order Nemytskii bound below controls; it coincides
(by metric extensionality through that `inner`-identity) with the perturbation-indexed
remainder `deTurckRealizeRemainderOf g₀ g_bg T` of the genuine-nonlinearity file. -/
noncomputable def realizedRHSRemainderSection (g₀ g_bg g₁ : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (deTurckRHSSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (deTurckRHSSection (I := I) g_bg g₁).hasCompactSupport }
    - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

/-- **The higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound (the genuine deep analytic
input of the order-`a` chart-RHS tower).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂ : SmoothCcTensor g₀ 0 2` whose `H^{a+2}` norms are `≤ B`, and any two realized metrics
`g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities `hg₁, hg₂`), the weighted-`Hᵃ`
seminorm of the `L²`-coordinate difference of the realized Ricci–DeTurck *remainder* sections
`realizedRHSRemainderSection g₀ g_bg gⱼ Tⱼ` is summable and bounded by `(C · ‖(T₁ − T₂).toHs
(a+2)‖)²`:
```
∑ᵢ (1 + λᵢ)^a ·
    ( tensorL2Coeff (toL2 (remainder of T₁,g₁)) i − tensorL2Coeff (toL2 (remainder of T₂,g₂)) i )²
  ≤ ( C · ‖(T₁ − T₂).toHs (a+2)‖ )² .
```

The order count is the honest one for the second-order quasilinear DeTurck operator: `a + 2`
derivatives of the metric perturbation control `a` derivatives of the right-hand side.  This is
exactly the higher-order analogue of the `C⁰`/`2`-jet base case
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-RHS *value* difference `≤
C · chartMetricJet2DiffSup`), upgraded from the chart `0`-jet of the right-hand side to its
order-`a` weighted-`Hᵃ` spectral seminorm and from the chart `2`-jet of the metric difference
to the intrinsic `H^{a+2}` norm of the perturbation difference (the order-`a` analogue of
`chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, the `a = 0` instance).

The conclusion is a *real-valued* weighted-`Hᵃ` square-sum inequality (in the exact binder
shape that `tensorHs.norm_sq_eq_tsum` consumes to produce an `Hᵃ`-`dist` Lipschitz witness),
structurally distinct from any topological/`LipschitzOnWith` statement; no packaging.  The body
is `sorry`: it is the genuine order-`a` chart-RHS-tower content — the higher-order quasilinear
Nemytskii estimate composing the chart-frame DeTurck-RHS-component derivatives up to order `a`
(each a polynomial in `(g, ∂g, …, ∂^{a+2} g)` controlled by the chart `(a+2)`-jet of the metric
difference) with the chart-`Hᵃ`-to-intrinsic-`Hᵃ` partition-of-unity packaging — with no
spectral-nonlinearity, no perturbation-indexed-remainder, and no Weyl dependence. -/
theorem exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2 =>
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                    - Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2)
          ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                      - Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2)
              ≤ (C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
                  (T₁ - T₂)‖) ^ 2 := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
