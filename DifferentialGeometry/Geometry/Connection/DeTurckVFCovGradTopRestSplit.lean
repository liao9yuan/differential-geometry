import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.LieDerivSectionCartan
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction

/-! # The covariant top/rest split of the symmetrised-lowered DeTurck-field difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **deep gauge covariant-Leibniz content** of the Lie
half of the Ricci–DeTurck linearization: the order-`j` covariant top/rest split of the difference of
two metrics' symmetrised covariant lowerings of the DeTurck vector field,
`symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg`.

This is the **gauge analogue (parity-depth)** of the curvature half's connection-level
quadratic-Cross top/rest split `crossCorrectionSection_iteratedCovGrad_topRest_split`
(`ConnectionDifferenceFieldJets.lean`, itself a posited primitive), and rides the **same sorry-free
covariant-calculus engine**:

* the metric-contraction binomial covariant-Leibniz `rfns` grid of a `DiffBilinOp`
  (`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`,
  `Analysis/Spectral/Tensor/CovGrad/MetricContractionLeibnizGrid.lean`);
* the parallel two-section bilinear-product `rfns` grid of an `RfnsBilinearProduct`
  (`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le`,
  `Analysis/Spectral/Tensor/CovGrad/QuadraticProductRfnsGrid.lean`);
* the realized-Koszul jet domination `koszulCombSection_iteratedCovGrad_rfns_le` and the
  fibre-small-gated lowered connection-difference jet bound
  `exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`
  (`ConnectionDifferenceFieldJets.lean`).

## Why the difference splits this way

The DeTurck field `W = deTurckVF g g_bg` is the metric `g`-trace of the connection difference
`connDiff (g, g_bg)` (`deTurckVF_apply_eq`), a `g⁻¹·∂g`-type field.  `symLoweredDeTurckVF g g_bg` is
the symmetrised `g`-lowering of its covariant gradient `∇W` (`cartanRHSBilin`), so it is a
covariant-Faà-di-Bruno contraction of the metric jet, **order-`≤2` in the metric**: the value jet,
the first-derivative jets riding (through the `g₀`-lowered Koszul form) on the `w`-jets, and a genuine
quadratic-in-difference `D∘D` part from the bilinear connection-difference product of two independently
varying gauge fields.

The difference of two such contractions telescopes (one difference factor per term).  The **`Top`**
part collects the difference-factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` jets through the
rank-reducing contraction and the two-section bilinear-product grid (the high derivative landing on
either factor, folded with the fixed factor sup and the metric-built `≤2`-jet coefficient into the
family-uniform `Cd`); the **`Rest`** part keeps the top coefficient jet on the *fixed pair* `T₁, T₂`
against the difference's order-`a` chart-Sobolev `C⁰` mass (the supercritical embedding `ha`), with the
per-recombination share `(1/8)` landing the consumer's `(1/4)`.

Unlike the curvature half — order-zero-immune (Palatini: `Γ(g₁) = Γ(g₂)` near `x` forces
`Ric(g₁) = Ric(g₂)` near `x`) — the Lie summand depends on the metric at **order zero** (the trace
weight `g⁻¹` and the value of the perturbation), so the difference arm is the **0-jet-inclusive**
order-`≤ j+2` covariant jet sum of `w`: the order-`0` jet `rfns(w)` is included.  A 0-jet-free arm is
Lean-refuted FALSE (the flat-`T²` counterexample documented at the leaf
`lieDerivDiff_connLevel_topRestSplit`). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **(P1b — POSIT — the INTEGRATED two-arm `L²` bound of the symmetrised-lowered DeTurck-field
difference, with the 0-jet-inclusive `w`-jet difference arm.)**

The genuine deep covariant-gauge content of the Lie half, the **gauge analogue (parity-depth)** of the
curvature half's connection-level quadratic-Cross top/rest split
`crossCorrectionSection_iteratedCovGrad_topRest_split` (`ConnectionDifferenceFieldJets.lean`, itself a
posited primitive), applied to the difference of the two metrics' symmetrised covariant lowerings of
the DeTurck vector field
`diff := symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg` — the
**intrinsic, `∇W`-manifest representative** of the sealed `g₀`-retagged Lie-summand difference (via the
section-level Cartan identity `lieDerivRetagG0_eq_symLoweredRetagG0`).

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a
uniform `H^{a+2}`-size bound `B ≥ 0`, and fibre-smallness `δ < 1/2`, there is a nonnegative constant
`Cd` (uniform over the gradient order `j` and the perturbation family) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics
`g₁, g₂` of `T₁, T₂`, the squared metric `L²` norm of the order-`j` covariant gradient of `diff` is
dominated by the **integrated Hamilton/Moser two-arm sum**
```
‖∇^j diff‖² ≤ Cd · ∑_{i ≤ j+2} ‖∇^i w‖²
            + (1/4) · (∑_{i ≤ j+2} (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖²,
```
where `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and `‖·‖` is the metric `L²` (semi)norm
(`‖S‖² = ∫ rfns(S) dμ`); the order-`0` jet `‖w‖²` is included.

**Why INTEGRATED, not pointwise.**  An earlier *pointwise* `rfns` per-`x` top/rest form (a `∇^j diff(x)
= Top + Rest` split with `rfns(Top)(x) ≤ Cd · ∑ rfns(∇^i w)(x)`) is **false** for the middle terms of
the covariant-Leibniz product at high frequency: when the differentiation order splits as `∇^p w ·
∇^{j+2−p} (fixed)` with both factors of order `≈ j/2`, neither factor is low-jet, so the on-disk
full-square `rfns` product grid cannot select the difference factor pointwise, and for `j > 2a` the
left side has frequency content `|ξ|^j` against a right side capped at `|ξ|^{2a}`.  This is
**Gagliardo–Nirenberg interpolation content** — true only after integration (the GN product inequality
trades a high jet of one factor for a low jet times an `L^∞`/`H^a` mass of the other, an `∫`-level
statement).  The bound is therefore stated at the integrated `L²`-norm-squared level, the form its
single consumer `exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le` actually reads (no pointwise
splitting is consumed downstream — the former `riemannianFiberNormSq_add_le` recombiner only ever
recombined fibre norms into this integrated bound).

**Decomposition (the engine the proof rides).**  `symLoweredDeTurckVF g g_bg` is the symmetrised
`g`-lowering of `∇W`, `W = g`-trace of `connDiff (g, g_bg)` (`cartanRHSBilin`, `deTurckVF_apply_eq`),
so it is a covariant-Faà-di-Bruno contraction of the metric jet.  The difference telescopes one
difference factor per term: the linear-in-difference part carries the `w`-jets through the realized
Koszul form and the `g⁻¹`-trace contraction; the quadratic `D∘D` part is a bilinear product of two
independently varying gauge fields, whose `∇^j` covariant-Leibniz expansion is integrated by the
**Gagliardo–Nirenberg product two-arm engine**
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`): the difference-arm `Cd ·
∑ ‖∇^i w‖²` collects the high derivative on the difference factor `w` (with the fixed factor's `≤2`-jet
sup folded into `Cd`), and the cross arm `(1/4) · (∑ (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖²`
keeps the top coefficient jet on the *fixed pair* `T₁, T₂` in `L²` against the difference's order-`a`
chart-Sobolev `C⁰`/`L^∞` mass (the supercritical embedding `ha`).

**Non-vacuity.**  The difference arm carries the order-`0` value jet `‖w‖²` and the high derivative
`‖∇^{j+2} w‖²` (a zero `Cd` falsifying it whenever the difference is genuinely present), and the cross
arm carries **both** fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the
difference vanishes (`lieDerivRetagG0_eq_symLoweredRetagG0` reduces it to the sealed Lie difference,
which vanishes by `lieDerivRetagG0_sub_toModel_eq`), `w = 0` and `‖(T₁ − T₂).toHs a‖ = 0`, so the bound
is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep integrated
covariant-Leibniz two-arm bound of the symmetrised-lowered DeTurck-field difference, riding the GN
product two-arm family, with the 0-jet-inclusive difference arm. -/
theorem symLoweredDeTurckVF_iteratedCovGrad_topRest_split (g₀ g_bg : SmoothRiemannianMetric I M)
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
        ∀ (j : ℕ),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
                    - symLoweredDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

end DeTurck
end PDE
end DifferentialGeometry

end
