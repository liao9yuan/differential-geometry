import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSHighOrderSobolevLipschitz

/-! # The δ-refined principal top-jet split of the realized DeTurck remainder difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file posits the **all-order δ-refined principal split** of the
realized Ricci–DeTurck *remainder* difference along two `g₀`-fibre-small perturbations: at
every covariant-gradient order `j`, the metric `L²` (semi)norm of `∇^j` of the remainder
difference is dominated by

* a **δ-proportional, order-uniform top arm** `c · δ · ‖∇^{j+2}(T₁ − T₂)‖_{L²}` carrying the
  single top jet order, with `c` depending only on `(g₀, g_bg, a)` — never on `j`, `B`, or
  `δ`; plus
* the generic Hamilton/Moser-tame lower arm `C j · (∑_{i ≤ k₀} ‖∇^i(T₁ − T₂)‖ + ∑_{i ≤ j+1}
  ‖∇^i(T₁ − T₂)‖_{L²})`, anchored at the **fixed low jet sum** of order `k₀` with
  `2 · k₀ ≤ a + 1`; plus
* the **order-uniform** fixed-pair cross arm `c₂ · (∑_{i ≤ j+2} (‖∇^i T₁‖ + ‖∇^i T₂‖)) ·
  ∑_{i ≤ k₀} ‖∇^i(T₁ − T₂)‖` carrying the unbounded top coefficient jet on the fixed pair
  against the same fixed low-jet anchor of the difference — Hamilton-tame top-order terms
  carry order-uniform constants, and an order-growing cross coefficient would make the
  Picard class-invariance recursion jointly unsatisfiable; ALL order growth is confined
  to the generic arm's family `C`,

together with its spectral-mass counterpart (the per-order `(1+λ)^d`-weighted square-sum
split), the currency the gated Picard pair consumes directly.

## Why the anchor must be LOW (the funded-window constraint)

The Moser/Hamilton-tame Lipschitz factor of the differentiated-coefficient terms needs only
**sup-norm** control of the (low jets of the) difference, supplied through the supercritical
Sobolev embedding from a FIXED low order — never the full order-`a` chart-Sobolev content.
Anchoring at `‖(T₁ − T₂).toHs a‖` (as the superseded shape did) is fatal for the consumer:
`toHs k ≍ 2k` covariant jets (`exists_iteratedCovGrad_l2Norm_le_toHs`), so the `toHs a`
anchor demands difference-proportional control of `≈ 2a` jets, while maximal regularity
funds difference-proportional control only to integrated mass-order `a + 2`
(`solFieldMass_le_forcingMass`) and `√T`-funded order `a + 1`
(`maxRegDuhamelSolFieldHa1_dist_le`) — at `2a` the difference is only ball-bounded, and the
Picard contraction cannot close.  The fixed anchor order `k₀` therefore carries the budget
`2 * k₀ ≤ a + 1`: low enough that the anchor sits strictly inside the maximal-regularity
funded window, and (internally to the posited proof) still supercritical for the sup-norm
embedding — such a `k₀` exists because `2 * a > dim M + 4` leaves
`(dim M)/4 + 1 < k₀ ≤ (a+1)/2` nonempty over `ℕ`.

## Why the split is true, and why it must be stated on the *remainder*

The remainder `N(g) = deTurckRHSRetag g₀ g_bg g − Δ_∇ T` subtracts exactly the anchor
principal part: by the principal-symbol cancellation
`deTurckNonlinearitySpectral_principalPart_cancels`
(`Analysis/Spectral/Intrinsic/DeTurck/NonlinearitySpectral.lean`), the second-order
coefficient of the DeTurck right-hand side is the metric inverse acting as a rough-Laplacian
symbol, so the remainder's second-order coefficient is `g⁻¹ − g₀⁻¹` — which under the fibre
gate `gFibreOpBound … δ` is Neumann-series bounded by `δ / (1 − δ) ≤ 2δ` for `δ ≤ 1/2`.
Refining per-order along the segment metric `g_t`: in the covariant Faà-di-Bruno expansion of
`∇^j(N(g₁) − N(g₂))`, the unique top term (the `k = 0` covariant-Leibniz term, binomial
coefficient `1`, hence **order-uniform**) is `[(g_t⁻¹ − g₀⁻¹)] · ∇^{j+2}(realize (T₁ − T₂))`
— a `δ`-proportional coefficient against the top difference jet, the standard quasilinear
principal structure.  Every other term either differentiates the coefficient at least once
(landing on `∇^{≤ j+1}(T₁ − T₂)` with a ball-bounded — but *not* δ-small — `∇g_t`-sized
coefficient: the generic lower arm) or differentiates the segment difference (the fixed-pair
cross arm of the landed tame sibling
`exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le`,
`SegmentMetricRHSCovJetExpansion.lean`, whose binders this statement mirrors).  Stated on the
**raw** right-hand-side difference the split is FALSE: there the top coefficient is
`g_t⁻¹`-sized, not `δ`-small — only the remainder subtracts the `g₀⁻¹∇²` core.

## Why the δ-arm is load-bearing

A generic-constant top arm (`C j` in place of `c · δ`) cannot drive the gated Picard scheme:
the top order sits exactly at the two-order maximal-regularity gain, where no positive power
of the horizon is available, so the absorption constant must be small — and the Lean probe of
the δ-defect (the `δ → 1` blow-up of the realized-metric Neumann series) shows the mechanism
genuinely fails without the `δ`-proportionality.  Order-uniformity of `c` is equally
load-bearing: a `j`-growing top coefficient would break the downward well-foundedness of the
per-order Picard invariance recursion.

## Non-vacuity

At `T₁ = T₂` the metric ties pin `g₁.inner = g₂.inner`, hence (by metric extensionality)
`g₁ = g₂`, and both sides vanish — the bound is an equality `0 ≤ 0`, not vacuously strong.
For `T₁ ≠ T₂` the left side is generically positive (distinct realized metrics produce
distinct remainders), so a degenerate `c = 0`, `C ≡ 0` witness is rejected; and the `δ`-arm
genuinely carries the top order: the lower arm stops at `i ≤ j + 1` (with a fixed low
anchor), so for high-frequency differences the right side without the `δ`-arm is strictly
smaller than the left at large `j`.

The headline `L²`-jet split is **proven by composition** (TRANSIT glue: seminorm triangle
inequality) over the single posited per-order decomposition
`exists_realizedRemainderDiff_covFdB_principalTopCell_split`, which materializes, at every
order `j`, the genuine `Top + Rest` section decomposition of `∇^j` of the remainder
difference together with the δ-Neumann bound on `Top` and the differentiated-coefficient
generic+cross bound on `Rest`.  The spectral-mass form
`exists_realizedRemainderDiff_principalTopSplit_allOrder_spectralMass_le` is a separate
posit in the `(1+λ)^d`-weighted square-sum currency (the ε-Young squared form, with the
`4^p`-type order growth confined to the order-indexed family `C d`).  Both posited bodies
remain `sorry`, so consumers transitively depend on `sorryAx` through them. -/

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The per-order `Top + Rest` covariant-Faà-di-Bruno decomposition of the realized DeTurck
remainder difference, with the δ-Neumann top-cell bound and the differentiated-coefficient
generic+cross rest bound anchored at a fixed low jet sum (the posited analytic input: the
per-order quasilinear principal refinement of the symbol-level cancellation).**

For an anchor `g₀`, a flow background `g_bg`, a supercritical order `a` (`2a > dim M + 4`),
there are a **fixed low anchor order `k₀` with `2 * k₀ ≤ a + 1`**, a top-arm constant
`c ≥ 0`, and a cross-arm constant `c₂ ≥ 0`, all depending only on `(g₀, g_bg, a)` — uniform
in the order `j`, the ball radius `B`, and the margin `δ` — such that for every
`H^{a+2}`-ball radius `B ≥ 0`, every fibre margin `0 ≤ δ < 1/2`, there is a nonnegative
order-indexed tame family `C : ℕ → ℝ` with: for
any two `g₀`-fibre-`δ`-small perturbations `T₁, T₂` of `H^{a+2}` norm `≤ B`, any two realized
metrics `g₁, g₂` (tied by the fibrewise `inner`-identities), and **every** gradient order
`j`, the `j`-th covariant gradient of the realized remainder difference splits as a sum of
two genuine smooth compactly-supported `(0, 2+j)`-tensor sections `Top + Rest` with

* **the δ-Neumann top-cell bound** `‖Top‖ ≤ c · δ · ‖∇^{j+2}(T₁ − T₂)‖`: `Top` is the unique
  un-differentiated (`k = 0` covariant-Leibniz, binomial coefficient `1`, hence
  order-uniform) FdB cell `[(g_t⁻¹ − g₀⁻¹)] · ∇^{j+2}(realize (T₁ − T₂))`, whose coefficient
  is the inverse-difference fibre operator — Neumann-series bounded by `δ/(1−δ) ≤ 2δ` under
  the fibre gate `gFibreOpBound … δ` for `δ < 1/2`, the per-order refinement of the proven
  symbol cancellation `deTurckNonlinearitySpectral_principalPart_cancels`
  (`NonlinearitySpectral.lean`: the remainder's second-order coefficient is `g⁻¹ − g₀⁻¹`,
  the `g₀⁻¹∇²` core being subtracted by the `Δ_∇` summand of
  `realizedRHSRemainderSection_eq_sub`); and
* **the differentiated-coefficient rest bound**: every other FdB term differentiates the
  coefficient at least once, dropping the difference jet to `≤ j+1` with a ball-bounded
  `≤2`-jet coefficient (the generic Hamilton/Moser-tame arm over `∑_{i ≤ j+1} ‖∇^i(T₁ −
  T₂)‖`, anchored at the fixed low jet sum `∑_{i ≤ k₀} ‖∇^i(T₁ − T₂)‖`), or lands the
  unbounded top coefficient jet on the fixed pair in `L²` against the difference's sup-norm
  mass (the cross arm `c₂ · (∑_{i ≤ j+2} (‖∇^i T₁‖ + ‖∇^i T₂‖)) · ∑_{i ≤ k₀} ‖∇^i(T₁ −
  T₂)‖`, whose Hamilton-tame top-order coefficient `c₂` is **order-uniform**: all order
  growth stays in the generic family `C`) —
  exactly the differenced-coefficient restriction of the landed tame sibling
  `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le`
  (`SegmentMetricRHSCovJetExpansion.lean`), whose binder discipline this posit mirrors.

**Why the anchor is the fixed low jet sum, not `‖(T₁−T₂).toHs a‖`.**  The Moser/Hamilton
Lipschitz factor needs only **sup-norm** control of the low jets of the difference, supplied
by the supercritical embedding from the fixed order `k₀` (which exists under
`2a > dim M + 4` with the budget `2 * k₀ ≤ a + 1`).  The superseded `toHs a` anchor pins
`≈ 2a` difference jets (`toHs k ≍ 2k` jets, `exists_iteratedCovGrad_l2Norm_le_toHs`), which
maximal regularity does NOT fund difference-proportionally (only `a+2` integrated / `a+1`
`√T`-funded orders are available: `solFieldMass_le_forcingMass`,
`maxRegDuhamelSolFieldHa1_dist_le`) — the gated Picard contraction cannot close over it.

The split must be **per-order**: a single section-level (`j = 0`) `Top` section with
all-order pure-δ bounds does NOT exist — for `j ≥ 1` the covariant derivatives hitting the
inverse-difference coefficient are ball-sized, not δ-small, so the `j`-dependent top cell is
re-collected at each order (which is why the two arm bounds are bundled with the
decomposition witnesses into one posit, exactly as in the on-disk Lie precedent
`lieDerivDiff_covFdB_section_split`: separate `Top`-bound and `Rest`-bound theorems could
not share the decomposition witnesses without a concrete named top-cell operator, which
awaits the contraction-coefficient machinery).

**Non-vacuity.**  The two arm bounds are coupled by the structural identity
`∇^j(remainder diff) = Top + Rest`: at `T₁ = T₂` the metric ties force `g₁ = g₂`, both sides
vanish, and the bounds are equalities `0 ≤ 0`; for `T₁ ≠ T₂` a degenerate witness
`Top = 0` is rejected for `j` large (the `Rest` arm stops at difference order `j+1` apart
from the fixed low anchor, while the left side carries genuine order-`(j+2)` difference
content), and `Rest = 0` is rejected already at `j = 0` whenever the remainders differ
beyond the principal cell.  The body is the posited analytic input; it remains `sorry`, so
consumers transitively depend on `sorryAx`. -/
theorem exists_realizedRemainderDiff_covFdB_principalTopCell_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ k₀ : ℕ, 2 * k₀ ≤ a + 1 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
          ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
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
              ∀ j : ℕ,
                ∃ Top Rest : Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
                  PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
                        - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)
                    = Top + Rest ∧
                  ‖Top‖ ≤
                    c * δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 2) (T₁ - T₂)‖ ∧
                  ‖Rest‖ ≤
                    C j * ((∑ i ∈ Finset.range (k₀ + 1),
                            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                        + ∑ i ∈ Finset.range (j + 1 + 1),
                            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                      + c₂ * (∑ i ∈ Finset.range (j + 2 + 1),
                            (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                              + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                          * ∑ i ∈ Finset.range (k₀ + 1),
                              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ :=
  sorry

/-- **The all-order δ-refined principal top-jet split of the realized DeTurck remainder
difference, anchored at a fixed low jet sum (the per-order quasilinear principal refinement
of the symbol-level cancellation).**

For an anchor `g₀`, a flow background `g_bg`, a supercritical order `a`
(`2a > dim M + 4`), there are a **fixed low anchor order `k₀` with `2 * k₀ ≤ a + 1`**, a
**top-arm constant `c ≥ 0`**, and a **cross-arm constant `c₂ ≥ 0`**, all depending only on
`(g₀, g_bg, a)` — uniform in the order `j`, the ball radius `B`, and the margin `δ` — such
that for every `H^{a+2}`-ball radius
`B ≥ 0` and every fibre margin `0 ≤ δ < 1/2` there is a nonnegative order-indexed tame
constant family `C : ℕ → ℝ` with: for any two `g₀`-fibre-`δ`-small perturbations `T₁, T₂` of
`H^{a+2}` norm `≤ B`, any two realized metrics `g₁, g₂` (tied by the fibrewise
`inner`-identities), and **every** gradient order `j`, the metric `L²` norm of `∇^j` of the
realized remainder difference
`realizedRHSRemainderSection g₀ g_bg g₁ T₁ − realizedRHSRemainderSection g₀ g_bg g₂ T₂`
is dominated by the δ-proportional top arm `c · δ · ‖∇^{j+2}(T₁ − T₂)‖`, the generic tame
lower arm over `∇^{≤ j+1}(T₁ − T₂)` anchored at the fixed low jet sum
`∑_{i ≤ k₀} ‖∇^i(T₁ − T₂)‖`, and the **order-uniform** fixed-pair cross arm `c₂ · (…) ·
(low anchor)` against the same low anchor (with `c₂` depending only on `(g₀, g_bg, a)`;
all order growth is confined to the generic family `C`).

The remainder's second-order coefficient is `g_t⁻¹ − g₀⁻¹` (the per-order refinement of
`deTurckNonlinearitySpectral_principalPart_cancels`), Neumann-bounded by `2δ` under the
fibre gate for `δ ≤ 1/2`, and the top covariant-Leibniz term has binomial coefficient `1`
— hence the top arm is both δ-proportional and order-uniform; all coefficient-derivative
terms drop at least one order and land in the generic arm, exactly as in the landed tame
sibling `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le`, whose
binder discipline (`δ < 1/2`, `H^{a+2}`-ball, fibrewise `inner`-ties) this statement
mirrors.  The Lipschitz factor of the differentiated-coefficient terms needs only sup-norm
control of the difference, supplied through the supercritical embedding from the fixed low
order `k₀` — and the budget `2 * k₀ ≤ a + 1` keeps the anchor strictly inside the
maximal-regularity difference-funded window (`toHs a` would pin `≈ 2a` difference jets,
which are only ball-bounded there; see the module docstring).  Non-vacuity: at `T₁ = T₂`
both sides vanish; the δ-arm genuinely carries the top order (the generic arm stops at
`i ≤ j + 1` apart from the fixed low anchor).

**Proven by composition** (TRANSIT glue): the posited per-order decomposition
`exists_realizedRemainderDiff_covFdB_principalTopCell_split` exhibits `∇^j` of the remainder
difference as `Top + Rest` with `‖Top‖` δ-Neumann-bounded by the top arm and `‖Rest‖`
bounded by the generic + cross arms; the seminorm triangle inequality `norm_add_le` and the
two arm bounds assemble the three-arm domination, with the same `k₀`, the same `c`, the
same `c₂`, and the same per-order family `C`.  Consumers transitively depend on `sorryAx` only through that
posited per-order decomposition. -/
theorem exists_realizedRemainderDiff_principalTopSplit_allOrder_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ k₀ : ℕ, 2 * k₀ ≤ a + 1 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
          ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
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
              ∀ j : ℕ,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                    (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
                      - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)‖ ≤
                  c * δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 2) (T₁ - T₂)‖
                    + C j * ((∑ i ∈ Finset.range (k₀ + 1),
                            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                        + ∑ i ∈ Finset.range (j + 1 + 1),
                            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                    + c₂ * (∑ i ∈ Finset.range (j + 2 + 1),
                          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                        * ∑ i ∈ Finset.range (k₀ + 1),
                            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ := by
  classical
  obtain ⟨k₀, hk₀, c, hc_nn, c₂, hc₂_nn, hbody⟩ :=
    exists_realizedRemainderDiff_covFdB_principalTopCell_split (I := I) g₀ g_bg a ha
  refine ⟨k₀, hk₀, c, hc_nn, c₂, hc₂_nn, fun B hB δ hδ0 hδ1 => ?_⟩
  obtain ⟨C, hC_nn, hsplit⟩ := hbody B hB δ hδ0 hδ1
  refine ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j => ?_⟩
  obtain ⟨Top, Rest, hdecomp, hTop, hRest⟩ :=
    hsplit T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
            - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)‖
      = ‖Top + Rest‖ := by rw [hdecomp]
    _ ≤ ‖Top‖ + ‖Rest‖ := norm_add_le _ _
    _ ≤ c * δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 2) (T₁ - T₂)‖
          + (C j * ((∑ i ∈ Finset.range (k₀ + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                + ∑ i ∈ Finset.range (j + 1 + 1),
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
              + c₂ * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                  * ∑ i ∈ Finset.range (k₀ + 1),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖) :=
        add_le_add hTop hRest
    _ = c * δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 2) (T₁ - T₂)‖
          + C j * ((∑ i ∈ Finset.range (k₀ + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
              + ∑ i ∈ Finset.range (j + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
          + c₂ * (∑ i ∈ Finset.range (j + 2 + 1),
                (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                  + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
              * ∑ i ∈ Finset.range (k₀ + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ :=
        (add_assoc _ _ _).symm

/-- **The per-eigenmode principal-cell microlocal split of the realized DeTurck remainder
difference, with the δ²-Neumann top-cell bound (child a) and the lower-order Nemytskii
cross-mass rest bound (child b) — the two genuine microlocal primitives of the per-mode
symbol estimate.**

This is the eigenmode transcription of the symbol-level cancellation
`deTurckNonlinearitySpectral_principalPart_cancels` (`NonlinearitySpectral.lean`).  Writing the
realized remainder as `realizedRHSRemainderSection g₀ g_bg g₁ T₁ = deTurckRHSRetag g₀ g_bg g₁ −
Δ_∇ T₁` (`realizedRHSRemainderSection_eq_sub`), the `L²`-eigencoordinate of the difference is
`coeffᵢ(R₁ − R₂) = coeffᵢ(retag₁ − retag₂) + λᵢ · coeffᵢ(T₁ − T₂)` (the Laplacian eigen-action
`rawConnLapSmooth_tensorL2Coeff`, `cᵢ(Δ_∇ T) = −λᵢ cᵢ(T)`).  This posit splits that single
coordinate as `principal + rest`, where:

* **child (a) — the per-mode quasilinear principal cell carries the sharp `δ²` top arm**:
  `principal² ≤ c · δ² · (1 + λᵢ)² · (coeffᵢ(T₁ − T₂))²`.  `principal` is the second-order
  quasilinear cell `[(g_t⁻¹ − g₀⁻¹)] · (second-order symbol)` of the retag difference: the
  `g₀⁻¹∇²` core of the retag's principal part is exactly the `+λᵢ · coeffᵢ(T₁ − T₂)` Laplacian
  term, so the order-2 content cancels and `principal`'s coefficient is the inverse-difference
  fibre operator `g⁻¹ − g₀⁻¹`, Neumann-bounded by `2δ` under the fibre gate
  `gFibreOpBound … δ` for `δ < 1/2`; the second-order symbol weight is `(1 + λᵢ)²`, and `c` is
  independent of `i` (the top covariant-Leibniz cell has binomial coefficient `1`); and

* **child (b) — the lower-order Nemytskii cross-mass carries the mid + cross arms**:
  `rest² ≤ C₀ · (1 + λᵢ)¹ · (coeffᵢ(T₁ − T₂))² + c₂ · mass_{k₀}(T₁ − T₂) · (1 + λᵢ)² ·
  ((coeffᵢ T₁)² + (coeffᵢ T₂)²)`, with the fixed low-anchor spectral mass
  `mass_{k₀}(T₁ − T₂) := ∑ⱼ (1 + λⱼ)^{k₀} (coeffⱼ(T₁ − T₂))²`.  `rest` collects every
  coefficient-differentiated FdB cell: the generic differentiated-coefficient term one full
  spectral order below the top (`(1 + λᵢ)¹`, per-mode constant `C₀` order-uniform), and the
  fixed-pair cross term carrying the unbounded fixed-pair top symbol `(1 + λᵢ)²` against the
  fixed low-anchor difference mass, with `c₂` independent of `i`.

The two arm bounds are coupled by the structural identity `coeffᵢ(R₁ − R₂) = principal + rest`,
so neither arm is vacuous: at `T₁ = T₂` the metric ties force `g₁ = g₂`, both `principal` and
`rest` vanish, and the bounds are equalities `0 ≤ 0`; for `T₁ ≠ T₂` a degenerate `principal = 0`
witness is rejected for high `i` (where the left side carries genuine order-2 difference content
that the `(1 + λᵢ)¹` rest arm cannot supply).  The body is the posited analytic input (the
per-mode DeTurck symbol cancellation + Nemytskii bound); it remains `sorry`, so consumers
transitively depend on `sorryAx`. -/
theorem realizedRemainderDiff_perMode_principalCell_symbol_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ k₀ : ℕ, 2 * k₀ ≤ a + 1 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
          ∃ C₀ : ℝ, 0 ≤ C₀ ∧
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
              ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                ∃ principal rest : ℝ,
                  tensorL2Coeff (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
                          - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i
                      = principal + rest ∧
                  -- child (a): the δ²-Neumann principal top cell
                  principal ^ 2 ≤
                    c * δ ^ 2 *
                      (tensorSobolevWeight (I := I) (M := M) i 2 *
                        (tensorL2Coeff (I := I) (M := M)
                            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                            (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2) ∧
                  -- child (b): the lower-order Nemytskii mid + cross mass
                  rest ^ 2 ≤
                    C₀ *
                        (tensorSobolevWeight (I := I) (M := M) i 1 *
                          (tensorL2Coeff (I := I) (M := M)
                              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                              (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
                    + c₂ *
                        (∑' j : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                            tensorSobolevWeight (I := I) (M := M) j (k₀ : ℝ) *
                              (tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) j) ^ 2) *
                          (tensorSobolevWeight (I := I) (M := M) i 2 *
                            ((tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2 +
                              (tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2)) :=
  sorry

/-- **The per-eigenmode symbol bound on the squared `L²`-eigencoefficient of the realized
DeTurck remainder difference (the genuine analytic content of the spectral-mass split,
posited as a single per-mode primitive).**

In eigenmode coordinates the realized remainder difference
`realizedRHSRemainderSection g₀ g_bg g₁ T₁ − realizedRHSRemainderSection g₀ g_bg g₂ T₂`
has, at each eigen-index `i`, a squared coefficient dominated by

* the **δ²-proportional top symbol** `c · δ² · (1 + λᵢ)² · (coeffᵢ(T₁ − T₂))²` — the square of
  the δ-proportional principal arm, with the second-order symbol weight `(1 + λᵢ)²` (the
  rough-Laplacian symbol whose `g₀⁻¹∇²` core is cancelled, leaving the `g⁻¹ − g₀⁻¹` fibre
  operator Neumann-bounded by `2δ` under the fibre gate), the constant `c` independent of `i`
  (the top covariant-Leibniz cell has binomial coefficient `1`); plus
* the generic lower symbol `C₀ · (1 + λᵢ)¹ · (coeffᵢ(T₁ − T₂))²` one full spectral order below
  the top (the differentiated-coefficient Moser/Hamilton-tame arm — in eigenmode coordinates
  the per-mode constant `C₀` is order-uniform, the `4^p` jet-order growth of the `L²`-jet
  sibling never appearing per mode); plus
* the **fixed-pair cross symbol** `c₂ · mass_{k₀}(T₁ − T₂) · (1 + λᵢ)² · ((coeffᵢ(T₁))² +
  (coeffᵢ(T₂))²)` carrying the unbounded fixed-pair top symbol against the fixed low-anchor
  spectral mass `mass_{k₀}(T₁ − T₂) := ∑ⱼ (1 + λⱼ)^{k₀} (coeffⱼ(T₁ − T₂))²` of the difference
  (a fixed scalar, treated per mode as a constant), with `c₂` independent of `i`.

Multiplying this per-mode bound by the order weight `(1 + λᵢ)^d` and summing over `i` lands
the three arms, at every real order `d ≥ 0`, sharply at spectral orders `d + 2`, `d + 1`, and
`d + 2` against the low anchor `mass_{k₀}` — exactly the
`exists_realizedRemainderDiff_principalTopSplit_allOrder_spectralMass_le` split, with the same
`k₀`, `c`, `c₂` and the constant order family `C d := C₀`.  The weights `(1 + λᵢ)^σ` are the
`tensorSobolevWeight i σ`, so the rpow algebra `(1 + λᵢ)^d · (1 + λᵢ)^σ = (1 + λᵢ)^{d+σ}`
(`tensorHs.tensorSobolevWeight_add`) is what makes the top arm land at order `d + 2` for every
real `d` — there is no integer-ceiling loss.  The body is the posited analytic input (the
per-mode DeTurck symbol estimate); it remains `sorry`, so consumers transitively depend on
`sorryAx`. -/
theorem realizedRemainderDiff_perMode_symbol_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ k₀ : ℕ, 2 * k₀ ≤ a + 1 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
          ∃ C₀ : ℝ, 0 ≤ C₀ ∧
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
              ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                (tensorL2Coeff (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
                          - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2 ≤
                  c * δ ^ 2 *
                      (tensorSobolevWeight (I := I) (M := M) i 2 *
                        (tensorL2Coeff (I := I) (M := M)
                            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                            (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
                    + C₀ *
                        (tensorSobolevWeight (I := I) (M := M) i 1 *
                          (tensorL2Coeff (I := I) (M := M)
                              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                              (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
                    + c₂ *
                        (∑' j : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                            tensorSobolevWeight (I := I) (M := M) j (k₀ : ℝ) *
                              (tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) j) ^ 2) *
                          (tensorSobolevWeight (I := I) (M := M) i 2 *
                            ((tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2 +
                              (tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2)) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hc_def
  obtain ⟨k₀, hk₀, c, hc_nn, c₂, hc₂_nn, hsplit⟩ :=
    realizedRemainderDiff_perMode_principalCell_symbol_split (I := I) g₀ g_bg a ha
  refine ⟨k₀, hk₀, 2 * c, by positivity, 2 * c₂, by positivity,
    fun B hB δ hδ0 hδ1 => ?_⟩
  obtain ⟨C₀, hC₀_nn, hcell⟩ := hsplit B hB δ hδ0 hδ1
  refine ⟨2 * C₀, by positivity, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ i => ?_⟩
  -- The genuine microlocal split of the per-mode remainder coefficient into a
  -- δ²-Neumann principal cell and a lower-order Nemytskii rest, supplied by the
  -- posited principal-cell split, together with its two arm bounds.
  obtain ⟨principal, rest, hdecomp, htop, hrest⟩ :=
    hcell T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ i
  -- The principal cell carries the sharp δ² top arm; the rest carries the lower +
  -- cross arms.  Squaring the split `coeffᵢ(R₁−R₂) = principal + rest` via the
  -- elementary `(p + q)² ≤ 2 p² + 2 q²` lands the three target arms (with the
  -- top and cross constants doubled, absorbed into the chosen `2 * c`, `2 * c₂`,
  -- `2 * C₀`).
  have hsq :
      (tensorL2Coeff (I := I) (M := M) hc
            (Integral.L2.SmoothCcTensor.toL2
              (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
                - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2
        ≤ 2 * principal ^ 2 + 2 * rest ^ 2 := by
    rw [hdecomp]; nlinarith [sq_nonneg (principal - rest)]
  calc
    (tensorL2Coeff (I := I) (M := M) hc
          (Integral.L2.SmoothCcTensor.toL2
            (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
              - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2
        ≤ 2 * principal ^ 2 + 2 * rest ^ 2 := hsq
    _ ≤ 2 * (c * δ ^ 2 *
            (tensorSobolevWeight (I := I) (M := M) i 2 *
              (tensorL2Coeff (I := I) (M := M) hc
                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2))
          + 2 * (C₀ *
              (tensorSobolevWeight (I := I) (M := M) i 1 *
                (tensorL2Coeff (I := I) (M := M) hc
                    (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
            + c₂ *
                (∑' j : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                    tensorSobolevWeight (I := I) (M := M) j (k₀ : ℝ) *
                      (tensorL2Coeff (I := I) (M := M) hc
                          (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) j) ^ 2) *
                  (tensorSobolevWeight (I := I) (M := M) i 2 *
                    ((tensorL2Coeff (I := I) (M := M) hc
                          (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2 +
                      (tensorL2Coeff (I := I) (M := M) hc
                          (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2))) := by
        gcongr
    _ = 2 * c * δ ^ 2 *
            (tensorSobolevWeight (I := I) (M := M) i 2 *
              (tensorL2Coeff (I := I) (M := M) hc
                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
          + 2 * C₀ *
              (tensorSobolevWeight (I := I) (M := M) i 1 *
                (tensorL2Coeff (I := I) (M := M) hc
                    (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
          + 2 * c₂ *
              (∑' j : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                  tensorSobolevWeight (I := I) (M := M) j (k₀ : ℝ) *
                    (tensorL2Coeff (I := I) (M := M) hc
                        (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) j) ^ 2) *
                (tensorSobolevWeight (I := I) (M := M) i 2 *
                  ((tensorL2Coeff (I := I) (M := M) hc
                        (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2 +
                    (tensorL2Coeff (I := I) (M := M) hc
                        (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2)) := by ring

/-- **The order-uniform per-order spectral-mass split of the realized DeTurck remainder
difference (the ε-Young squared form of the principal top-jet split, in the
`(1+λ)^d`-weighted square-sum currency the gated Picard pair consumes; posited analytic
input).**

For an anchor `g₀`, a flow background `g_bg`, a supercritical order `a` (`2a > dim M + 4`),
there are a **fixed low anchor order `k₀` with `2 * k₀ ≤ a + 1`**, a top-arm constant
`c ≥ 0`, and a cross-arm constant `c₂ ≥ 0`, all depending only on `(g₀, g_bg, a)` — uniform
in the spectral order `d`, the ball radius `B`, and the margin `δ` — such that for every `H^{a+2}`-ball radius `B ≥ 0` and every
fibre margin `0 ≤ δ < 1/2` there is a nonnegative order-indexed family `C : ℝ → ℝ` with: for
any two `g₀`-fibre-`δ`-small perturbations `T₁, T₂` of `H^{a+2}` norm `≤ B`, any two
realized metrics `g₁, g₂` (tied by the fibrewise `inner`-identities), and **every** spectral
order `d ≥ 0`, the order-`d` spectral mass (the `(1+λᵢ)^d`-weighted square-sum of the
`L²`-eigencoefficients) of the realized remainder difference is summable and dominated by

* the **order-uniform δ²-top arm** `c · δ² · mass_{d+2}(T₁ − T₂)` — the square of the
  δ-proportional principal arm, with `c` independent of `d` (the top covariant-Leibniz cell
  has binomial coefficient `1`, and ε-Young at a FIXED ε absorbs the cross term of the
  square into the two pure arms, so no order growth ever touches the δ²-coefficient); plus
* the order-indexed generic lower arm `C d · mass_{d+1}(T₁ − T₂)`: the Hamilton/Moser-tame
  arm one full spectral order below the top; plus
* the **order-uniform fixed-pair cross arm** `c₂ · (mass_{d+2}(T₁) + mass_{d+2}(T₂)) ·
  mass_{k₀}(T₁ − T₂)` carrying the unbounded fixed-pair top mass against the fixed
  low-anchor mass of the difference — its Hamilton-tame top-order coefficient `c₂` is
  independent of `d` (an order-growing cross coefficient would make the Picard
  class-invariance recursion jointly unsatisfiable against the middle arm's forced growth).
  ALL order growth — in particular the sharp binomial-Leibniz `4^p`-type emissions — is
  confined to the family `C d`, never to `c` or `c₂` (the `PROVE_REFUTED.md`-ratified
  ε-Young design: `δ < 1/2` uniform, `4^p` inside `C(p)`).

This is the spectral-mass transcription of the per-order `L²`-jet split
`exists_realizedRemainderDiff_principalTopSplit_allOrder_l2Norm_le`: the sharp Gårding
ladder matches the order-`d` spectral mass with the squared covariant jet sums at matching
order, the per-order split bounds each jet by `c·δ·(top jet) + (rest arms)`, and squaring
via ε-Young at fixed ε yields the δ²-top arm at spectral order `d + 2` (comfortably inside
the two-order maximal-regularity gain `solFieldMass_le_forcingMass`) with the rest collected
at order `d + 1` (the `√T`-funded window of `maxRegDuhamelSolFieldHa1_dist_le`) and the
fixed-pair masses against the low anchor `mass_{k₀}` (`2 * k₀ ≤ a + 1`).  Real orders `d`
interpolate between the integer rungs.  The conclusion's right-hand side uses the spectral
masses of the smooth compactly-supported sections `T₁, T₂, T₁ − T₂`, which are summable at
every order (smoothness gives super-polynomial eigencoefficient decay), so no junk-`tsum`
degeneracy can satisfy the bound vacuously.

**Non-vacuity.**  At `T₁ = T₂` the metric ties force `g₁ = g₂` and every mass on both sides
vanishes (`0 ≤ 0`); for `T₁ ≠ T₂` the left side is generically positive, rejecting the
degenerate `c = 0`, `C ≡ 0` witness, and the δ²-arm genuinely carries the top order: the
lower arm stops one full spectral order below (`d + 1`) apart from the fixed low anchor, so
for high-frequency differences the right side without the δ²-arm is strictly smaller than
the left at large `d`.  The body is the posited analytic input; it remains `sorry`, so
consumers transitively depend on `sorryAx`. -/
theorem exists_realizedRemainderDiff_principalTopSplit_allOrder_spectralMass_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ k₀ : ℕ, 2 * k₀ ≤ a + 1 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ (δ : ℝ), 0 ≤ δ → δ < 1 / 2 →
          ∃ C : ℝ → ℝ, (∀ d, 0 ≤ C d) ∧
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
              ∀ d : ℝ, 0 ≤ d →
                Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
                    tensorSobolevWeight (I := I) (M := M) i d *
                      (tensorL2Coeff (I := I) (M := M)
                          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                          (Integral.L2.SmoothCcTensor.toL2
                              (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                            - Integral.L2.SmoothCcTensor.toL2
                              (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2) ∧
                (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                    tensorSobolevWeight (I := I) (M := M) i d *
                      (tensorL2Coeff (I := I) (M := M)
                          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                          (Integral.L2.SmoothCcTensor.toL2
                              (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                            - Integral.L2.SmoothCcTensor.toL2
                              (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2)
                  ≤ c * δ ^ 2 *
                      (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                        tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                          (tensorL2Coeff (I := I) (M := M)
                              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                              (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
                    + C d *
                        (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                          tensorSobolevWeight (I := I) (M := M) i (d + 1) *
                            (tensorL2Coeff (I := I) (M := M)
                                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                                (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
                    + c₂ *
                        ((∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                                tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                                  (tensorL2Coeff (I := I) (M := M)
                                      (tensorResolventL2_isCompactOperator
                                        (I := I) (M := M) g₀ 0 2)
                                      (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2)
                              + (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                                  tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                                    (tensorL2Coeff (I := I) (M := M)
                                        (tensorResolventL2_isCompactOperator
                                          (I := I) (M := M) g₀ 0 2)
                                        (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2))
                        * (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
                            tensorSobolevWeight (I := I) (M := M) i (k₀ : ℝ) *
                              (tensorL2Coeff (I := I) (M := M)
                                  (tensorResolventL2_isCompactOperator
                                    (I := I) (M := M) g₀ 0 2)
                                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2) := by
  classical
  obtain ⟨k₀, hk₀, c, hc_nn, c₂, hc₂_nn, hbody⟩ :=
    realizedRemainderDiff_perMode_symbol_le (I := I) g₀ g_bg a ha
  refine ⟨k₀, hk₀, c, hc_nn, c₂, hc₂_nn, fun B hB δ hδ0 hδ1 => ?_⟩
  obtain ⟨C₀, hC₀_nn, hperMode⟩ := hbody B hB δ hδ0 hδ1
  refine ⟨fun _ => C₀, fun _ => hC₀_nn, ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ d hd
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hc_def
  -- The remainder difference as a single smooth compactly-supported section.
  set Rdiff : Integral.L2.SmoothCcTensor g₀ 0 2 :=
    realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
      - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂ with hRdiff_def
  set Tdiff : Integral.L2.SmoothCcTensor g₀ 0 2 := T₁ - T₂ with hTdiff_def
  -- Eigencoefficient families.
  set cRem : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 Rdiff) i
    with hcRem_def
  set cD : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 Tdiff) i
    with hcD_def
  set cT1 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 T₁) i
    with hcT1_def
  set cT2 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 T₂) i
    with hcT2_def
  -- The fixed low-anchor spectral mass of the difference (a constant scalar `Q`).
  set Q : ℝ := ∑' j : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) j (k₀ : ℝ) * (cD j) ^ 2 with hQ_def
  -- The toL2 of the section difference equals the difference of the toL2s (the LHS rewrite).
  have htoL2_sub :
      Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
          - Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)
        = Integral.L2.SmoothCcTensor.toL2 Rdiff := by
    rw [hRdiff_def]
    exact (ContinuousLinearMap.map_sub (Integral.L2.SmoothCcTensor.toL2)
      (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
      (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)).symm
  -- Summability of the weighted coefficient families at every real order.
  have hsumRem : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i d * (cRem i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ d Rdiff hc
  have hsumD2 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cD i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ (d + 2) Tdiff hc
  have hsumD1 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 1) * (cD i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ (d + 1) Tdiff hc
  have hsumT1 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT1 i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ (d + 2) T₁ hc
  have hsumT2 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT2 i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ (d + 2) T₂ hc
  -- The three weighted-RHS families and their summability.
  set topF : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => c * δ ^ 2 * (tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cD i) ^ 2)
    with htopF_def
  set lowF : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => C₀ * (tensorSobolevWeight (I := I) (M := M) i (d + 1) * (cD i) ^ 2) with hlowF_def
  set crossF : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => c₂ * Q *
      (tensorSobolevWeight (I := I) (M := M) i (d + 2) * ((cT1 i) ^ 2 + (cT2 i) ^ 2))
    with hcrossF_def
  have hsumTop : Summable topF := by
    rw [htopF_def]; exact (hsumD2.mul_left (c * δ ^ 2))
  have hsumLow : Summable lowF := by
    rw [hlowF_def]; exact (hsumD1.mul_left C₀)
  have hsumCross : Summable crossF := by
    rw [hcrossF_def]
    have : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
        ((cT1 i) ^ 2 + (cT2 i) ^ 2)) := by
      have heq : (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
            ((cT1 i) ^ 2 + (cT2 i) ^ 2))
          = (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT1 i) ^ 2
              + tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT2 i) ^ 2) := by
        funext i; ring
      rw [heq]; exact hsumT1.add hsumT2
    exact this.mul_left (c₂ * Q)
  have hsumRHS : Summable (fun i => topF i + lowF i + crossF i) :=
    (hsumTop.add hsumLow).add hsumCross
  -- Pointwise: the weighted per-mode bound (from the posited per-mode symbol estimate).
  have hpoint : ∀ i, tensorSobolevWeight (I := I) (M := M) i d * (cRem i) ^ 2
      ≤ topF i + lowF i + crossF i := by
    intro i
    have hmode := hperMode T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ i
    have hwnn := tensorSobolevWeight_nonneg (I := I) (M := M) i d
    have hstep := mul_le_mul_of_nonneg_left hmode hwnn
    refine le_trans hstep (le_of_eq ?_)
    simp only [htopF_def, hlowF_def, hcrossF_def, hQ_def, hcD_def, hcT1_def, hcT2_def, hTdiff_def]
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i d 2,
      tensorHs.tensorSobolevWeight_add (I := I) (M := M) i d 1]
    ring
  -- Compute the total of the weighted RHS as the three target masses.
  have htsumTop : ∑' i, topF i
      = c * δ ^ 2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cD i) ^ 2 := by
    simp only [htopF_def]; rw [tsum_mul_left]
  have htsumLow : ∑' i, lowF i
      = C₀ * ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 1) * (cD i) ^ 2 := by
    simp only [hlowF_def]; rw [tsum_mul_left]
  have htsumCross : ∑' i, crossF i
      = c₂ * Q *
          (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT1 i) ^ 2
            + ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT2 i) ^ 2) := by
    simp only [hcrossF_def]
    rw [tsum_mul_left]
    congr 1
    have heq : (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
          ((cT1 i) ^ 2 + (cT2 i) ^ 2))
        = (fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT1 i) ^ 2
            + tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT2 i) ^ 2) := by
      funext i; ring
    rw [heq, hsumT1.tsum_add hsumT2]
  -- The node conclusion is the summability of the LHS family together with the bound.
  refine ⟨?_, ?_⟩
  · refine hsumRem.congr (fun i => ?_)
    rw [hcRem_def, ← htoL2_sub]
  -- Assemble: sum the pointwise bound and identify the masses.
  calc ∑' i, tensorSobolevWeight (I := I) (M := M) i d *
          (tensorL2Coeff (I := I) (M := M) hc
              (Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                - Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2
      = ∑' i, tensorSobolevWeight (I := I) (M := M) i d * (cRem i) ^ 2 := by
        rw [htoL2_sub]
    _ ≤ ∑' i, (topF i + lowF i + crossF i) :=
        hsumRem.tsum_le_tsum hpoint hsumRHS
    _ = (∑' i, topF i + ∑' i, lowF i) + ∑' i, crossF i := by
        rw [(hsumTop.add hsumLow).tsum_add hsumCross, hsumTop.tsum_add hsumLow]
    _ = c * δ ^ 2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cD i) ^ 2
          + C₀ * ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 1) * (cD i) ^ 2
          + c₂ *
              (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT1 i) ^ 2
                + ∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) * (cT2 i) ^ 2) * Q := by
        rw [htsumTop, htsumLow, htsumCross]; ring
    _ = c * δ ^ 2 *
          (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) *
            (tensorL2Coeff (I := I) (M := M) hc
                (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
        + C₀ *
            (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 1) *
              (tensorL2Coeff (I := I) (M := M) hc
                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2)
        + c₂ *
            ((∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                  (tensorL2Coeff (I := I) (M := M) hc
                      (Integral.L2.SmoothCcTensor.toL2 T₁) i) ^ 2)
              + (∑' i, tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                  (tensorL2Coeff (I := I) (M := M) hc
                      (Integral.L2.SmoothCcTensor.toL2 T₂) i) ^ 2))
          * (∑' i, tensorSobolevWeight (I := I) (M := M) i (k₀ : ℝ) *
              (tensorL2Coeff (I := I) (M := M) hc
                  (Integral.L2.SmoothCcTensor.toL2 (T₁ - T₂)) i) ^ 2) := by
        simp only [hQ_def, hcD_def, hcT1_def, hcT2_def, hTdiff_def]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
