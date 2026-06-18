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

/-! ## The supercritical ball-uniform fibre-norm bound on the cometric-trace field's jets (POSITED leaf) -/

set_option linter.unusedVariables false in
/-- **(POSITED deep bedrock — the supercritical ball-uniform fibre-norm-square bound on the
`covGrad`/`slotExtend` jets `dropTowerPsi` of the `g₁`-cometric double-trace field over the realize-tie
family.)**

For `g₀`, a supercritical order `a` (`2 · finrank E + 10 ≤ a`) and a covariant-`L²` ball radius
`R ≥ 0`, there is one nonnegative constant `K` such that, for every `g₀`-fibre-small smooth
perturbation `T` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, the
intrinsic fibre-norm-square of every drop-normal-form jet field
`dropTowerPsi g₀ 4 2 (cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2) p w k` (with indices
`p, w, k ≤ a`) is bounded by `K` at **every** base point `x`.

**Why this is the genuine deep content.**  The `dropTowerPsi` jets are the `covGrad`/`slotExtend`
covariant jets of the `g₁`-cometric double-trace field, i.e. the covariant jets of the inverse metric
`g₁⁻¹ = (g₀ + h_sym T)⁻¹` — a *nonlinear* (Moser-algebra) function of the metric perturbation `T`.
Bounding their fibre norms ball-uniformly over the realize family is the supercritical inverse-metric
jet estimate: the `δ < 1` fibre-operator bound keeps `g₁` uniformly positive-definite on the ball, so
`g₁⁻¹` and all its covariant derivatives are smooth functions of the order-`≤ a + 2` covariant jets of
`T`, which the supercritical embedding `2 · finrank E + 10 ≤ a`
(`deTurckArmDiff_supercritical_pointwise_jet_le`) controls pointwise by the `R`-ball `L²` data;
composing through the smooth inverse and the frame-free double trace yields the single ball-uniform
fibre bound `K`.  Consumers transitively depend on its `sorryAx`.

**Non-vacuity.**  A `K ≡ 0` bound is rejected by the nonvanishing genuine (non-zero) cometric jets on
the supercritical ball; `K` is uniform over the ball while the cometric jets vary with the realize-tie
endpoint. -/
theorem exists_ballUniform_cometricTraceField_dropTowerPsi_fibreNormSup
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
          ∀ p w k : ℕ, p ≤ a → w ≤ a → k ≤ a → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ ((4 + w) + k) ((2 + w) + p) x
                ((dropTowerPsi (I := I) (M := M) g₀ 4 2
                  (cometricTraceFieldG₀Tag (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) 2) p w k).toSection x) ≤ K :=
  sorry

/-! ## The ball-uniform envelope, reduced to the supercritical cometric-jet bound -/

set_option linter.unusedVariables false in
/-- **(The ball-uniform per-order envelope of the explicit jet bound `coeffJetBound` over the
realize-tie family.)**

For `g₀`, `g_bg`, a supercritical order `a`, and a covariant-`L²` ball radius `R ≥ 0`, there is one
nonnegative per-order ball-uniform envelope `κ : ℕ → ℝ` (outside the `∀ T T'` quantifier) such that, for
every pair of `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, the order-`q` window-sum ball-sup of the explicit jet bound of the realize-tie
endpoint `g₁ = realize(g₀ + T)` obeys, per order `q ≤ a`,
```
4^q · gridWindowSum (coeffJetBound g₀ g₁) 0 0 q ≤ κ q.
```

**Reduced to one clean classical estimate.**  `coeffJetBound g₀ g₁ p w = (p + 1) · ∑_{k ≤ p}
dropFibreSup g₀ 4 2 (cometricTraceFieldG₀Tag g₀ g₁ 2) p w k` is explicit, and the order-`q` window sum
ranges only over indices `p', w' ≤ q ≤ a` (so `k ≤ p' ≤ a`).  The new upper-bound handle
`dropFibreSup_le_of_fibreNormSup` turns the single supercritical ball-uniform fibre-norm bound `K`
supplied by `exists_ballUniform_cometricTraceField_dropTowerPsi_fibreNormSup` into a bound on every
`dropFibreSup` summand, whence `coeffJetBound g₀ g₁ p' w' ≤ (q + 1)² · K`, and the window double sum
(of `(q + 1)²` summands) times `4^q` is dominated by the explicit `R`-uniform envelope
`κ q := 4^q · (q + 1)² · (q + 1)² · K`.  All genuine deep content is concentrated in the child
estimate.

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
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) 0 0 q ≤ κ q := by
  classical
  obtain ⟨K, hK_nonneg, hK⟩ :=
    exists_ballUniform_cometricTraceField_dropTowerPsi_fibreNormSup (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun q => (4 : ℝ) ^ q * ((q + 1 : ℝ) ^ 2 * (q + 1 : ℝ) ^ 2) * K, fun q => by positivity, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hT hT' q hq
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
  -- Pointwise per-`(p', w')` bound on the cometric-trace jet `coeffJetBound`, valid for `p', w' ≤ q ≤ a`.
  have hcoeff : ∀ p' w' : ℕ, p' ≤ q → w' ≤ q →
      coeffJetBound (I := I) (M := M) g₀ g₁ p' w' ≤ (q + 1 : ℝ) ^ 2 * K := by
    intro p' w' hp' hw'
    unfold coeffJetBound
    -- Each `dropFibreSup` summand is bounded by `K` (child handle), then sum and the `(p' + 1)` factor.
    have hsummand : ∀ k ∈ Finset.range (p' + 1),
        dropFibreSup (I := I) (M := M) g₀ 4 2
          (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p' w' k ≤ K := by
      intro k hk
      have hk' : k ≤ q := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hp'
      refine dropFibreSup_le_of_fibreNormSup (I := I) (M := M) g₀ 4 2
        (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p' w' k hK_nonneg ?_
      intro x
      exact hK T hδ_lt hδ hT p' w' k (le_trans hp' hq) (le_trans hw' hq) (le_trans hk' hq) x
    have hsum_le : (∑ k ∈ Finset.range (p' + 1),
        dropFibreSup (I := I) (M := M) g₀ 4 2
          (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p' w' k) ≤ (p' + 1 : ℝ) * K := by
      calc (∑ k ∈ Finset.range (p' + 1),
              dropFibreSup (I := I) (M := M) g₀ 4 2
                (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p' w' k)
          ≤ ∑ _k ∈ Finset.range (p' + 1), K := Finset.sum_le_sum hsummand
        _ = (p' + 1 : ℝ) * K := by rw [Finset.sum_const, Finset.card_range]; ring
    calc (p' + 1 : ℝ) * ∑ k ∈ Finset.range (p' + 1),
            dropFibreSup (I := I) (M := M) g₀ 4 2
              (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) p' w' k
        ≤ (p' + 1 : ℝ) * ((p' + 1 : ℝ) * K) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (p' + 1 : ℝ) ^ 2 * K := by ring
      _ ≤ (q + 1 : ℝ) ^ 2 * K := by
          have hpq : (p' + 1 : ℝ) ≤ (q + 1 : ℝ) := by
            have : (p' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hp'
            linarith
          have hsq : (p' + 1 : ℝ) ^ 2 ≤ (q + 1 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hpq 2
          exact mul_le_mul_of_nonneg_right hsq hK_nonneg
  -- Sum the per-`(p', w')` bound over the order × rank window of width `q`.
  have hwindow : gridWindowSum (coeffJetBound (I := I) (M := M) g₀ g₁) 0 0 q ≤
      (q + 1 : ℝ) ^ 2 * ((q + 1 : ℝ) ^ 2 * K) := by
    unfold gridWindowSum
    calc (∑ p' ∈ Finset.range (q + 1), ∑ w' ∈ Finset.range (q + 1),
            coeffJetBound (I := I) (M := M) g₀ g₁ (0 + p') (0 + w'))
        ≤ ∑ p' ∈ Finset.range (q + 1), ∑ w' ∈ Finset.range (q + 1), (q + 1 : ℝ) ^ 2 * K := by
          refine Finset.sum_le_sum fun p' hp' => Finset.sum_le_sum fun w' hw' => ?_
          have hp'' : p' ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp')
          have hw'' : w' ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw')
          simpa using hcoeff p' w' hp'' hw''
      _ = (q + 1 : ℝ) ^ 2 * ((q + 1 : ℝ) ^ 2 * K) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
  -- Multiply by `4 ^ q` and rearrange into the explicit envelope.
  calc (4 : ℝ) ^ q * gridWindowSum (coeffJetBound (I := I) (M := M) g₀ g₁) 0 0 q
      ≤ (4 : ℝ) ^ q * ((q + 1 : ℝ) ^ 2 * ((q + 1 : ℝ) ^ 2 * K)) :=
        mul_le_mul_of_nonneg_left hwindow (by positivity)
    _ = (4 : ℝ) ^ q * ((q + 1 : ℝ) ^ 2 * (q + 1 : ℝ) ^ 2) * K := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
