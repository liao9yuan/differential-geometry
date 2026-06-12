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
* the generic Hamilton/Moser-tame lower arm `C j · (‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j+1}
  ‖∇^i(T₁ − T₂)‖_{L²})`; plus
* the tame fixed-pair cross arm `C j · (∑_{i ≤ j+2} (‖∇^i T₁‖ + ‖∇^i T₂‖)) ·
  ‖(T₁ − T₂).toHs a‖` carrying the unbounded top coefficient jet on the fixed pair.

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
genuinely carries the top order: the lower arm stops at `i ≤ j + 1`, so for high-frequency
differences the right side without the `δ`-arm is strictly smaller than the left at large
`j`.

The body is the posited analytic input (the per-order quasilinear principal refinement of
the proven symbol-level cancellation); it remains `sorry`, so consumers transitively depend
on `sorryAx`. -/

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The all-order δ-refined principal top-jet split of the realized DeTurck remainder
difference (posited analytic input: the per-order quasilinear principal refinement of the
symbol-level cancellation).**

For an anchor `g₀`, a flow background `g_bg`, a supercritical order `a`
(`2a > dim M + 4`), there is a **top-arm constant `c ≥ 0` depending only on
`(g₀, g_bg, a)`** — uniform in the order `j`, the ball radius `B`, and the margin `δ` —
such that for every `H^{a+2}`-ball radius `B ≥ 0` and every fibre margin `0 ≤ δ < 1/2`
there is a nonnegative order-indexed tame constant family `C : ℕ → ℝ` with: for any two
`g₀`-fibre-`δ`-small perturbations `T₁, T₂` of `H^{a+2}` norm `≤ B`, any two realized
metrics `g₁, g₂` (tied by the fibrewise `inner`-identities), and **every** gradient order
`j`, the metric `L²` norm of `∇^j` of the realized remainder difference
`realizedRHSRemainderSection g₀ g_bg g₁ T₁ − realizedRHSRemainderSection g₀ g_bg g₂ T₂`
is dominated by the δ-proportional top arm `c · δ · ‖∇^{j+2}(T₁ − T₂)‖`, the generic tame
lower arm over `∇^{≤ j+1}(T₁ − T₂)` anchored at the order-`a` chart-Sobolev difference
norm, and the tame fixed-pair cross arm.

The remainder's second-order coefficient is `g_t⁻¹ − g₀⁻¹` (the per-order refinement of
`deTurckNonlinearitySpectral_principalPart_cancels`), Neumann-bounded by `2δ` under the
fibre gate for `δ ≤ 1/2`, and the top covariant-Leibniz term has binomial coefficient `1`
— hence the top arm is both δ-proportional and order-uniform; all coefficient-derivative
terms drop at least one order and land in the generic arm, exactly as in the landed tame
sibling `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le`, whose
binder discipline (`δ < 1/2`, `H^{a+2}`-ball, fibrewise `inner`-ties) this statement
mirrors.  Non-vacuity: at `T₁ = T₂` both sides vanish; the δ-arm genuinely carries the
top order (the generic arm stops at `i ≤ j + 1`).  The body is the posited analytic
input; it remains `sorry`, so consumers transitively depend on `sorryAx`. -/
theorem exists_realizedRemainderDiff_principalTopSplit_allOrder_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ c : ℝ, 0 ≤ c ∧
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
                  + C j * (‖IntrinsicSobolev.SmoothCcTensor.toHs
                        (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                      + ∑ i ∈ Finset.range (j + 1 + 1),
                          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
                  + C j * (∑ i ∈ Finset.range (j + 2 + 1),
                        (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                          + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                      * ‖IntrinsicSobolev.SmoothCcTensor.toHs
                          (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
