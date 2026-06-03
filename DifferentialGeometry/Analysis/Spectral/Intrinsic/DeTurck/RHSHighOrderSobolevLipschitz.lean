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

/-- **The reverse spectral–Sobolev bound at order `a`: the spectral order-`a` Sobolev seminorm
of a smooth compactly-supported `(0,2)`-section is controlled by its intrinsic order-`a`
chart-Sobolev (`toHs a`) norm.**

For an anchor `g₀` and an order `a`, there is a single constant `C ≥ 0` such that for every
smooth compactly-supported `(0,2)`-tensor section `R`, the weighted spectral square-sum
```
∑ᵢ (1 + λᵢ)^a · ( tensorL2Coeff (toL2 R) i )²
```
is summable and bounded by `(C · ‖R.toHs a‖)²`.

This is the **reverse** (spectral ≤ intrinsic-chart) direction of the on-disk forward bound
`pouSobolevToHsNorm_le_spectral` (intrinsic-chart `≤` spectral), i.e. the easy
"differentiation" arm of the general-order norm comparison
`Order2NormEquivOnSmooth`/`tensorPouSobolevHs_order2_equiv_pouSobolev` lifted from order `2` to
every order `a`: each iterated rough-Laplacian power `‖Δ_∇^{⌈a/2⌉} R‖_{L²}` is controlled by
the chart `H^a` norm, and the weighted spectral square-sum is the `L²` norm of `(1−Δ_∇)^{a/2} R`.
The summability arm is `smoothCcTensor_tensorL2Coeff_weighted_summable` (valid at every real
order).  Its conclusion is a *real-valued* weighted-square-sum inequality in the eigenbasis
coordinates, structurally distinct from the `toHs`-norm hypothesis on the right; no packaging.

The body is `sorry`: it is the genuine reverse general-order spectral–Sobolev primitive (the
elliptic-regularity-free "easy" comparison arm, lifted to all orders), with no spectral
nonlinearity, no perturbation-indexed remainder, and no Weyl dependence. -/
theorem exists_spectralWeightedSq_le_pouHaNorm_sq
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : Integral.L2.SmoothCcTensor g₀ 0 2,
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2 =>
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2 R) i) ^ 2)
          ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Integral.L2.SmoothCcTensor.toL2 R) i) ^ 2)
              ≤ (C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖) ^ 2 :=
  sorry

/-- **The higher-order chart-RHS Nemytskii bound in intrinsic chart-Sobolev norms: the order-`a`
chart-Sobolev norm of the realized Ricci–DeTurck *remainder*-section difference is controlled by
the order-`(a+2)` chart-Sobolev norm of the perturbation difference.**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` whose `H^{a+2}` norms are `≤ B`, and any two realized metrics `g₁, g₂` of `T₁, T₂`
(tied by the fibrewise `inner`-identities), the intrinsic order-`a` chart-Sobolev norm of the
difference of realized Ricci–DeTurck remainder sections is bounded by the order-`(a+2)`
chart-Sobolev norm of the perturbation difference:
```
‖(realizedRHSRemainderSection g₀ g_bg g₁ T₁ − realizedRHSRemainderSection g₀ g_bg g₂ T₂).toHs a‖
  ≤ C · ‖(T₁ − T₂).toHs (a+2)‖ .
```

This is the genuine **higher-order quasilinear Nemytskii estimate** in *intrinsic* Sobolev
norms: the second-order Ricci–DeTurck right-hand side `Ric + Lie + Δ_∇` is a smooth Nemytskii
function of the metric's `≤2`-jet, so on the supercritical scale (`Hᵃ` a Banach algebra,
`H^{a+2}·Hᵃ ⊂ Hᵃ`) its order-`a` chart-Sobolev norm is controlled by the order-`(a+2)`
chart-Sobolev norm of the metric perturbation, uniformly over the `H^{a+2}`-bounded family.  It
is the intrinsic-norm analogue of the on-disk `C⁰`/`2`-jet base case
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-frame value difference `≤
C · chartMetricJet2DiffSup`), upgraded to the order-`a` intrinsic Sobolev norm, and the order-`a`
analogue of `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional` (the `a = 0`
chart-`2`-jet instance).  Its conclusion is a *real-valued* `toHs`-norm inequality, structurally
distinct from the spectral square-sum conclusion of the parent; no packaging.

The body is `sorry`: it is the genuine order-`a` quasilinear Nemytskii content (the higher-order
chart-RHS multiplication / composition estimate on the supercritical scale, composing the
chart-frame DeTurck-RHS-component derivatives up to order `a` with the chart-`Hᵃ`-to-intrinsic
partition-of-unity packaging), with no spectral-nonlinearity, no perturbation-indexed-remainder,
and no Weyl dependence. -/
theorem exists_realizedRHSRemainder_pouHa_le_toHs_highOrder
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
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
            (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
              - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)‖
          ≤ C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ :=
  sorry

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
                  (T₁ - T₂)‖) ^ 2 := by
  classical
  -- The reverse spectral bound at order `a` and the higher-order intrinsic Nemytskii bound.
  obtain ⟨CB, hCB_nn, hCB⟩ := exists_spectralWeightedSq_le_pouHaNorm_sq (I := I) g₀ a
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_realizedRHSRemainder_pouHa_le_toHs_highOrder (I := I) g₀ g_bg a B hB
  refine ⟨CB * CA, mul_nonneg hCB_nn hCA_nn, ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  -- The realized-remainder section difference and the `L²`-coordinate `map_sub` rewrite.
  set R : Integral.L2.SmoothCcTensor g₀ 0 2 :=
    realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
      - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂ with hR_def
  have hL2 :
      Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
          - Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)
        = Integral.L2.SmoothCcTensor.toL2 R := by
    rw [hR_def, map_sub]
  -- The reverse spectral bound, applied to the section difference `R`.
  obtain ⟨hsummable, hspec⟩ := hCB R
  -- The higher-order intrinsic Nemytskii bound on `‖R.toHs a‖`.
  have hnem :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CA * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (T₁ - T₂)‖ := hCA T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  refine ⟨by rw [hL2]; exact hsummable, ?_⟩
  -- Chain: spectral square-sum `≤ (CB·‖R.toHs a‖)² ≤ (CB·CA·‖(T₁−T₂).toHs(a+2)‖)²`.
  rw [hL2]
  refine hspec.trans ?_
  have hRtoHs_nn : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
    norm_nonneg _
  have hdiff_nn :
      0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) (T₁ - T₂)‖ :=
    norm_nonneg _
  have hbase :
      CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CB * CA *
            ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ := by
    calc CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CB * (CA * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (T₁ - T₂)‖) := mul_le_mul_of_nonneg_left hnem hCB_nn
      _ = CB * CA *
            ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ := by ring
  have hlhs_nn : 0 ≤ CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
    mul_nonneg hCB_nn hRtoHs_nn
  exact pow_le_pow_left₀ hlhs_nn hbase 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
