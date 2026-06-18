import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-! # The endpoint-dependent Lichnerowicz coefficient fields for the Ricci–DeTurck section linearization

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)`, a realize-tie endpoint
metric `g₁`, and the bedrock graded decomposition `covDerivConnDiff_diff_endpoint_graded`, this file
packages the three explicit endpoint-dependent coefficient operator fields of the intrinsic
Lichnerowicz mean-value linearization of the nonlinear Ricci–DeTurck right-hand side, together with the
ball-uniform jet-envelope of their valence-dropping `dropKappa` grids.

## The coefficient fields

The mean-value Fréchet derivative of the Ricci–DeTurck RHS in the metric reads as a second-order
operator `C₀·h + C₁·∇h + C₂·∇²h` whose endpoint-dependent symbols are read off
`covDerivConnDiff_diff_endpoint_graded`: the order-`2` PRINCIPAL inverse-Gram symbol `(g₁⁻¹−g₀⁻¹)·∂²`
(the cometric double trace at the realize-tie endpoint `g₁`), the order-`1` Christoffel-variation symbol
`δΓ = connDiff g₁ g₀` precomposed with the cometric single trace, and the order-`0` inverse-Gram value
symbol `gInvDiffSlotEndo g₀ g₁` (the slot-insertion of the raised cometric-difference representative).

* `cometricTraceFieldG₀Tag g₀ g₁ p` — the `g₀`-tagged smooth `(p + 2, p)`-tensor whose fibre value at
  `x` is the genuine `g₁`-cometric double trace `cometricDoubleTraceFib g₁ p x` of the two leading
  covariant slots (smooth by `cometricDoubleTraceFib_contMDiff`).  The metric tag is phantom data, so the
  `g₁`-built fibre lives in the `g₀`-tagged operator-field type the section grids consume.
* `lichCoeff0 g₀ g₁` — the order-`0` `(2, 2)` symbol, the inverse-Gram value slot insertion
  `gInvDiffSlotCoeff g₀ g₁`.
* `lichCoeff1 g₀ g₁` — the order-`1` `(3, 2)` Christoffel-variation symbol, the composition of the
  connection-difference `(1, 2)`-pairing `connDiffSection g₁ g₀` with the cometric single trace
  `(3, 1)` against `g₁`.
* `lichCoeff2 g₀ g₁` — the order-`2` `(4, 2)` PRINCIPAL inverse-Gram symbol, the `g₁`-cometric double
  trace contracting the two leading covariant slots.

Each fibre operator genuinely uses the endpoint metric `g₁` (the cometric raise, the connection
difference) and is not the zero operator.

## The ball-uniform envelope (POSITED deep leaf B)

`exists_uniform_lichCoeff_dropKappa_envelope` posits the three nonnegative per-order ball-uniform
envelopes `κ₀, κ₁, κ₂ : ℕ → ℝ` (outside the `∀ T T'` quantifier) dominating the valence-dropping arm
jet-envelope ball-sups `4^q · gridWindowSum (dropKappa (lichCoeffₘ g₀ g₁)) 0 0 q` of the realize-tie
endpoint coefficient fields over the radius-`R` ball.  Its order-`0` sibling is the proved
`exists_gInvDiffFibreEndo_neumannFibreBound`; the higher-order ball-compactness over the realize-tie
metrics of the supercritical ball is the genuine missing PDE estimate.  Consumers transitively depend on
its `sorryAx`.
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

/-! ## The three endpoint-dependent Lichnerowicz coefficient fields -/

/-- **The order-`0` Lichnerowicz coefficient field `C₀`, valence `(2, 2)`.**  The endpoint inverse-Gram
value symbol: the leading-slot insertion `gInvDiffSlotEndo g₀ g₁` of the raised cometric-difference
representative, the `O(δ)`-small value-level arm of `covDerivConnDiff_diff_endpoint_graded`.  This is the
template metric-arm field `gInvDiffSlotCoeff`; its fibre genuinely uses `g₁` (rejects the zero
witness). -/
def lichCoeff0 (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  gInvDiffSlotCoeff (I := I) g₀ g₁

/-- **The order-`1` Lichnerowicz coefficient field `C₁`, valence `(3, 2)`.**  The endpoint
Christoffel-variation symbol `δΓ = connDiff g₁ g₀`: the connection-difference `(1, 2)`-pairing
`connDiffSection g₁ g₀` composed (through the operator-field action `appCcRS`) with the endpoint cometric
single trace `(3, 1)` against `g₁`.  Both factors genuinely use `g₁` (the connection difference and the
cometric raise), so the assembled `(3, 2)` symbol rejects the zero witness. -/
def lichCoeff1 (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 3 2 :=
  appCcRS (I := I) g₀ 3 1 2 (connDiffSection (I := I) g₁ g₀)
    (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 1)

/-- **The order-`2` Lichnerowicz coefficient field `C₂`, valence `(4, 2)`.**  The PRINCIPAL inverse-Gram
parabolic symbol `(g₁⁻¹ − g₀⁻¹)·∂²`: the endpoint cometric double trace contracting the two leading
covariant slots of `∇²(T − T')` against the cometric `♯_{g₁}`.  Its fibre genuinely uses `g₁` (rejects
the zero witness). -/
def lichCoeff2 (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 4 2 :=
  cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2

/-! ## POSITED deep bedrock — the ball-uniform `dropKappa` engine-constant bound

The genuine deep content of leaf B is the ball-compactness of the endpoint-dependent coefficient
fields over the realize-tie family.  Stated at the irreducible grain, it is a *per-`(p, w)*
ball-uniform bound on the valence-dropping engine constant `dropKappa (lichCoeffₘ g₀ g₁)`: the
`Classical.choose`-opaque constant of `exists_dropTower_jet_bound` is, for a fixed smooth field, the
partition-of-unity-compactness sup of the drop-normal-form operator fields' fibre norms — a sum of
non-explicit uniform bounds on the `covGrad`/`slotExtend` jets of the field.  Bounding it
*uniformly across the realize-tie metrics* `g₁ = realize(g₀ + T)` of the radius-`R` ball is the genuine
missing PDE estimate: it is the ball-uniform covariant-jet rfns control of the inverse-Gram value /
Christoffel-variation / inverse-Gram-principal coefficient fields, made finite by the supercritical
`2 · finrank + 10 ≤ a` embedding.  The order-`0` sibling is the proved
`exists_gInvDiffFibreEndo_neumannFibreBound`; the higher covariant orders are the deep arm.

This is the strictly-smaller bedrock the assembled envelope `exists_uniform_lichCoeff_dropKappa_envelope`
consumes: once the per-`(p, w)` `dropKappa` bound `Bₘ` is ball-uniform, the per-order envelope is the
pure-arithmetic `κₘ q := 4^q · gridWindowSum Bₘ 0 0 q`, dominating the realize-tie engine constant by the
pointwise monotonicity of the order × rank window sum (no further analysis).  Consumers transitively
depend on its `sorryAx`. -/

set_option linter.unusedVariables false in
/-- **(POSITED deep bedrock — the ball-uniform per-`(p, w)` `dropKappa` engine-constant bound of the
endpoint Lichnerowicz coefficient fields.)**

For `g₀`, `g_bg`, a supercritical order `a`, and a covariant-`L²` ball radius `R ≥ 0`, there are three
nonnegative two-index families `B₀, B₁, B₂ : ℕ → ℕ → ℝ` (outside the `∀ T T'` quantifier) such that for
every pair of `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, the valence-dropping engine constant `dropKappa (lichCoeffₘ g₀ g₁) p w` of the
realize-tie endpoint coefficient field `g₁ = realize(g₀ + T)` is dominated, per `(p, w)`, by `Bₘ p w`.

This is the irreducible ball-compactness of the coefficient fields' covariant jets over the realize-tie
metrics of the radius-`R` ball; the supercritical embedding `2 · finrank + 10 ≤ a` makes the per-`(p, w)`
field-jet rfns sups finite uniformly over the ball, and the `Classical.choose` engine constant `dropKappa`
is bounded by those sups (the drop-normal-form operator fields are `covGrad`/`slotExtend` jets of the
field).  Consumers transitively depend on its `sorryAx`. -/
theorem exists_ballUniform_lichCoeff_dropKappa_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ B₀ B₁ B₂ : ℕ → ℕ → ℝ,
      (∀ p w, 0 ≤ B₀ p w) ∧ (∀ p w, 0 ≤ B₁ p w) ∧ (∀ p w, 0 ≤ B₂ p w) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
          (∀ p w : ℕ,
            dropKappa (I := I) (M := M) g₀ 2 2
                (lichCoeff0 (I := I) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) p w ≤ B₀ p w) ∧
          (∀ p w : ℕ,
            dropKappa (I := I) (M := M) g₀ 3 2
                (lichCoeff1 (I := I) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) p w ≤ B₁ p w) ∧
          (∀ p w : ℕ,
            dropKappa (I := I) (M := M) g₀ 4 2
                (lichCoeff2 (I := I) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) p w ≤ B₂ p w) :=
  sorry

set_option linter.unusedSectionVars false in
/-- **Order × rank window-sum monotonicity of a `dropKappa` engine constant under a per-`(p, w)`
bound.**  If the valence-dropping engine constant `dropKappa C` of a fixed coefficient field `C` is
dominated per `(p, w)` by a nonnegative two-index family `B`, then the order × rank window sum of the
former is dominated by that of the latter (all summands nonnegative).  This is the pure-arithmetic step
promoting the ball-uniform per-`(p, w)` engine bound to the per-order envelope. -/
private theorem gridWindowSum_mono_dropKappa (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g₀ b₀ s₀) (B : ℕ → ℕ → ℝ)
    (hCB : ∀ p w : ℕ, dropKappa (I := I) (M := M) g₀ b₀ s₀ C p w ≤ B p w) (p r j : ℕ) :
    gridWindowSum (dropKappa (I := I) (M := M) g₀ b₀ s₀ C) p r j ≤ gridWindowSum B p r j := by
  unfold gridWindowSum
  exact Finset.sum_le_sum fun p' _ => Finset.sum_le_sum fun r' _ => hCB (p + p') (r + r')

/-! ## Assembled leaf B — the ball-uniform jet-envelope -/

set_option linter.unusedVariables false in
/-- **(The ball-uniform jet-envelope of the endpoint Lichnerowicz coefficient fields, assembled from the
per-`(p, w)` `dropKappa` bedrock by order × rank window-sum monotonicity.)**

Fix `g₀`, `g_bg`, a supercritical order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  Outside the
`∀ T T'` quantifier there are three nonnegative per-order ball-uniform envelopes `κ₀, κ₁, κ₂ : ℕ → ℝ`
such that, for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to
order `a + 2` lie in the radius-`R` ball, the valence-dropping arm jet-envelope ball-sups of the three
realize-tie endpoint coefficient fields `lichCoeffₘ g₀ (realize(g₀ + T))` are dominated, per order
`q ≤ a`, by `κₘ q`:
```
4^q · gridWindowSum (dropKappa (lichCoeff0 g₀ g₁)) 0 0 q ≤ κ₀ q,   (and idem for C₁, C₂).
```
The envelope `κ` lies OUTSIDE the `∀ T T'` quantifier (ball-uniform), while the coefficient
`lichCoeffₘ g₀ g₁` is per-`(T, T')` through the realize-tie endpoint `g₁ = realize(g₀ + T)`.

**Why this is the genuine deep content (and why it is posited).**  This is the ball-compactness of the
endpoint-dependent inverse-Gram value / Christoffel-variation / inverse-Gram-principal coefficient fields
over the realize-tie metrics `realize(g₀ + T)` of the radius-`R` ball, made finite by the supercritical
embedding; the per-order `dropKappa` jet-envelope of the *fixed* smooth coefficient on the compact base is
finite by compactness, and the ball-uniformity across the family of realize-tie endpoints is the genuine
missing PDE estimate.  The order-`0` sibling is the proved `exists_gInvDiffFibreEndo_neumannFibreBound`.
Consumers transitively depend on its `sorryAx`.

**Non-vacuity.**  A `κₘ ≡ 0` envelope is rejected by the nonvanishing `dropKappa` jet-envelope of the
genuine (non-zero) endpoint coefficient field on a section of positive fibre norm; `κ` is uniform over
the ball while the coefficient varies with the endpoint. -/
theorem exists_uniform_lichCoeff_dropKappa_envelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ κ₀ κ₁ κ₂ : ℕ → ℝ, (∀ q, 0 ≤ κ₀ q) ∧ (∀ q, 0 ≤ κ₁ q) ∧ (∀ q, 0 ≤ κ₂ q) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
          (∀ q : ℕ, q ≤ a →
            (4 : ℝ) ^ q * gridWindowSum
                (dropKappa (I := I) (M := M) g₀ 2 2
                  (lichCoeff0 (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))) 0 0 q ≤ κ₀ q) ∧
          (∀ q : ℕ, q ≤ a →
            (4 : ℝ) ^ q * gridWindowSum
                (dropKappa (I := I) (M := M) g₀ 3 2
                  (lichCoeff1 (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))) 0 0 q ≤ κ₁ q) ∧
          (∀ q : ℕ, q ≤ a →
            (4 : ℝ) ^ q * gridWindowSum
                (dropKappa (I := I) (M := M) g₀ 4 2
                  (lichCoeff2 (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))) 0 0 q ≤ κ₂ q) := by
  classical
  obtain ⟨B₀, B₁, B₂, hB₀_nn, hB₁_nn, hB₂_nn, hB⟩ :=
    exists_ballUniform_lichCoeff_dropKappa_bound (I := I) g₀ g_bg a ha_super hR
  refine ⟨fun q => (4 : ℝ) ^ q * gridWindowSum B₀ 0 0 q,
    fun q => (4 : ℝ) ^ q * gridWindowSum B₁ 0 0 q,
    fun q => (4 : ℝ) ^ q * gridWindowSum B₂ 0 0 q, ?_, ?_, ?_, ?_⟩
  · exact fun q => mul_nonneg (by positivity) (gridWindowSum_nonneg hB₀_nn 0 0 q)
  · exact fun q => mul_nonneg (by positivity) (gridWindowSum_nonneg hB₁_nn 0 0 q)
  · exact fun q => mul_nonneg (by positivity) (gridWindowSum_nonneg hB₂_nn 0 0 q)
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨hb₀, hb₁, hb₂⟩ := hB T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨fun q _ => ?_, fun q _ => ?_, fun q _ => ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (gridWindowSum_mono_dropKappa (I := I) (M := M) g₀ 2 2 _ B₀ hb₀ 0 0 q) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (gridWindowSum_mono_dropKappa (I := I) (M := M) g₀ 3 2 _ B₁ hb₁ 0 0 q) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (gridWindowSum_mono_dropKappa (I := I) (M := M) g₀ 4 2 _ B₂ hb₂ 0 0 q) (by positivity)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
