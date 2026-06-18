import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-! # The endpoint-dependent jet envelope for the Ricci–DeTurck section linearization

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` and a realize-tie endpoint
metric `g₁`, this file provides the *explicit definable jet-envelope functional* `coeffJetBound g₀ g₁`
that bounds the valence-dropping `dropKappa` engine constant of every coefficient operator field of the
intrinsic Lichnerowicz mean-value linearization of the nonlinear Ricci–DeTurck right-hand side, together
with its ball-uniform envelope over the realize-tie family.

The genuine DeTurck–Ricci linearization symbols are second-order operators `C₀·h + C₁·∇h + C₂·∇²h`
whose endpoint-dependent coefficient fields are read off the bedrock graded decomposition
`covDerivConnDiff_diff_endpoint_graded` (the order-`2` PRINCIPAL inverse-Gram symbol `(g₁⁻¹−g₀⁻¹)·∂²`,
the order-`1` Christoffel-variation symbol `δΓ = connDiff g₁ g₀`, the order-`0` inverse-Gram value
symbol).  Rather than committing to explicit closed forms for those coefficients (which carry the
`−2·Ric + 𝓛`-scaling of `deTurckRicciRHS` and so must be *existential*, not fixed `g₀`-built fields),
this file exposes only the **scalar jet bound** their `dropKappa` constants obey — a definable
functional of `g₁`'s covariant jets — which the consumer pairs with the existential coefficients.

## The jet-envelope functional

* `cometricTraceFieldG₀Tag g₀ g₁ p` — the `g₀`-tagged smooth `(p + 2, p)`-tensor whose fibre value at
  `x` is the genuine `g₁`-cometric double trace `cometricDoubleTraceFib g₁ p x` of the two leading
  covariant slots (smooth by `cometricDoubleTraceFib_contMDiff`).  The metric tag is phantom data, so the
  `g₁`-built fibre lives in the `g₀`-tagged operator-field type the section grids consume.  This is the
  canonical `g₁`-determined jet handle through which the envelope reads `g₁`'s covariant jets.
* `coeffJetBound g₀ g₁ p w := (p + 1) · ∑_{k ≤ p} dropFibreSup g₀ 4 2 (cometricTraceFieldG₀Tag g₀ g₁ 2)
  p w k` — the EXPLICIT definable nonnegative `(p, w)`-indexed jet bound (a function of `g₁`'s covariant
  jets, mirroring the shape of `dropKappa`); any linearization coefficient's `dropKappa` is dominated by
  it (this domination is bundled into the existential identity leaf in the consumer).

## The ball-uniform envelope (POSITED deep leaf)

`exists_uniform_coeffJetBound` posits the nonnegative per-order ball-uniform envelope `κ : ℕ → ℝ`
(outside the `∀ T T'` quantifier) dominating `4^q · gridWindowSum (coeffJetBound g₀ g₁) 0 0 q` of the
realize-tie endpoint `g₁ = realize(g₀ + T)` over the radius-`R` ball.  This is the genuine ball-compactness
of `g₁`'s covariant jets over the realize-tie metrics of the supercritical ball — the deep missing PDE
estimate.  Consumers transitively depend on its `sorryAx`.
-/

noncomputable section

set_option linter.style.setOption false

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The `g₀`-tagged endpoint cometric-trace field -/

/-- **The `g₀`-tagged `g₁`-cometric double-trace field, valence `(p + 2, p)`.**  The genuine endpoint
cometric double trace `cometricDoubleTraceField g₁ p` (raise the leading slot by the cometric `♯_{g₁}`,
then the frame-free natural trace), re-tagged to `g₀`.  The `SmoothCcTensor` metric tag is phantom data
(the underlying section is metric-free), so this `g₁`-built field is carried in the `g₀`-tagged
operator-field type that the section-level `appCc`/`dropKappa` grids consume. -/
def cometricTraceFieldG₀Tag (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ) :
    Integral.L2.SmoothCcTensor g₀ (p + 2) p where
  toSection := (cometricDoubleTraceField (I := I) g₁ p).toSection
  hasCompactSupport := (cometricDoubleTraceField (I := I) g₁ p).hasCompactSupport

/-! ## The explicit definable jet-envelope functional -/

/-- **The explicit definable jet-envelope functional `coeffJetBound g₀ g₁`.**  The nonnegative
`(p, w)`-indexed bound `(p + 1) · ∑_{k ≤ p} dropFibreSup g₀ 4 2 (cometricTraceFieldG₀Tag g₀ g₁ 2) p w k`:
a named finite sum of the fibre-norm sups of the `covGrad`/`slotExtend` jets of the canonical
`g₁`-determined cometric-trace handle, with no opaque outer `Classical.choose`.  It mirrors the shape of
`dropKappa` and is a definable function of `g₁`'s covariant jets; the existential Lichnerowicz
linearization coefficients (built from `g₁`'s cometric / connection difference / curvature) have their
`dropKappa` engine constant dominated by it (the domination is bundled into the consumer's existential
identity leaf). -/
def coeffJetBound (g₀ g₁ : SmoothRiemannianMetric I M) (p w : ℕ) : ℝ :=
  (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1),
    dropFibreSup (I := I) (M := M) g₀ 4 2 (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p w k

theorem coeffJetBound_nonneg (g₀ g₁ : SmoothRiemannianMetric I M) (p w : ℕ) :
    0 ≤ coeffJetBound (I := I) (M := M) g₀ g₁ p w :=
  mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k _ =>
      dropFibreSup_nonneg (I := I) (M := M) g₀ 4 2 (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p w k)

/-! ## Order × rank window-sum monotonicity -/

set_option linter.unusedSectionVars false in
/-- **Order × rank window-sum monotonicity under a pointwise bound.**  If a nonnegative two-index family
`κ` is dominated pointwise by `κ'`, then the order × rank window sum of the former is dominated by that of
the latter (all summands nonnegative).  The pure-arithmetic step promoting a pointwise `dropKappa` bound
to the per-order window envelope. -/
theorem gridWindowSum_mono (κ κ' : ℕ → ℕ → ℝ) (hκκ' : ∀ p w : ℕ, κ p w ≤ κ' p w) (p r j : ℕ) :
    gridWindowSum κ p r j ≤ gridWindowSum κ' p r j := by
  unfold gridWindowSum
  exact Finset.sum_le_sum fun p' _ => Finset.sum_le_sum fun r' _ => hκκ' (p + p') (r + r')

/-! ## The ball-uniform envelope (POSITED deep leaf) -/

set_option linter.unusedVariables false in
/-- **(POSITED deep bedrock — the ball-uniform per-order envelope of the explicit jet bound
`coeffJetBound` over the realize-tie family.)**

For `g₀`, `g_bg`, a supercritical order `a`, and a covariant-`L²` ball radius `R ≥ 0`, there is one
nonnegative per-order ball-uniform envelope `κ : ℕ → ℝ` (outside the `∀ T T'` quantifier) such that, for
every pair of `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, the order-`q` window-sum ball-sup of the explicit jet bound of the realize-tie
endpoint `g₁ = realize(g₀ + T)` obeys, per order `q ≤ a`,
```
4^q · gridWindowSum (coeffJetBound g₀ g₁) 0 0 q ≤ κ q.
```

**Why this is the genuine deep content (and why it is posited).**  `coeffJetBound g₀ g₁` is explicit, so
its order-`q` window sum is, on the *fixed* compact base for a *fixed* `g₁`, finite by compactness; the
content here is the ball-UNIFORMITY of that finite quantity across the family of realize-tie endpoints
`g₁ = realize(g₀ + T)` of the radius-`R` ball, which is the ball-compactness of `g₁`'s covariant jets,
made finite by the supercritical embedding `2 · finrank + 10 ≤ a` (via
`deTurckArmDiff_supercritical_pointwise_jet_le`: `g₁`'s pointwise jets ≤ the `R`-ball bound).  Consumers
transitively depend on its `sorryAx`.

**Non-vacuity.**  A `κ ≡ 0` envelope is rejected by the nonvanishing `dropFibreSup` jet handle of the
genuine (non-zero) `g₁`-cometric trace field on the supercritical ball; `κ` is uniform over the ball while
`coeffJetBound g₀ g₁` varies with the realize-tie endpoint. -/
theorem exists_uniform_coeffJetBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ κ : ℕ → ℝ, (∀ q, 0 ≤ κ q) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
          ∀ q : ℕ, q ≤ a →
            (4 : ℝ) ^ q * gridWindowSum
                (coeffJetBound (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) 0 0 q ≤ κ q :=
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
