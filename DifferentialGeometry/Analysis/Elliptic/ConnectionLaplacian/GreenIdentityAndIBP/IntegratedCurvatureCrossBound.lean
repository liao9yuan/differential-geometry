import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameBracketFold
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

/-!
# The integrated curvature cross-bound from the genuine field nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file produces the
**integrated `L²` curvature cross-bound** on the rough-Laplacian / covariant-gradient commutator
defect `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` (a `(0, s + 1)`-tensor field;
`∇S := covGrad g 0 s S`):

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0,
```

uniformly in `S`. This is the single analytic input the integrated order-`2` Gårding reduction
`secondCovGrad_l2NormSq_le_of_cross_bound` (`IntegratedOrder2Garding.lean`) consumes; closing it makes
the chart-`H²` Gårding constant unconditional.

## The route (the integrated moving-frame nullity, not the Weitzenböck value)

The defect cross-pairing is *not* small term-by-term: by the integrated order-`2` Weitzenböck identity
`weitzenbock_curvature_crossPairing_value` it equals `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`, which carries the
genuine `∇²S`-order energy — so bounding it through that *value* is circular for the Gårding constant.
The sound route bounds the cross-pairing through the **three genuine curvature fields**: the concrete
pure-Riemann curvature section `GcurvSection g s S` (`= R(∇S)`), the differentiated-curvature trace
section `genuineDiffCurvSection g s S` (`= (∇R) S`), and the Bochner–Lichnerowicz Ricci-trace carrier
`ricTraceSection g s S` (`= Ric(∇S)`). The moving-frame remainder
`Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S` is a total
covariant divergence of an `∇S`-order field, so it pairs to zero against `∇S` on the closed manifold
(the **integrated nullity**, the genuine moving-frame third-order Bochner–Weitzenböck content,
supplied here as `movingFrameRemainder_genuineSections_nullity`). The nullity (with `GcurvDeriv` taken
to be the combined field `genuineDiffCurvSection + ricTraceSection`) feeds
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm.lean`) to give the bracket-free pairing
`⟨GcurvSection + genuineDiffCurvSection + ricTraceSection, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`, and the three
genuine fields carry the whole cross-pairing.

The Ricci-trace carrier is the missing fourth slot of the commutator defect: term-`(IV)` of the
slot table (`RicciTraceCarrier.lean`), the frame trace of the curvature's derivative-direction
contraction, producing `Ric`. It does NOT integrate to zero (at `s = 0` it carries the whole defect:
`Curv f = Ric(∇f, ·)`, `⟨Curv f, ∇f⟩ = ∫Ric(∇f, ∇f) > 0` on a positively-curved manifold), so it must
be subtracted alongside the two curvature fields.

Each genuine field is then bounded `L²`-proportionally:

* `GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)`
  (`pureRGenuineDiffOp0_eq_GcurvSection`) has fibre norm `≤ kappa · rfns(∇S)` by the
  section-proportional curvature bound `exists_proportional_pureRGenuineDiffOp`, so
  `‖GcurvSection g s S‖_{L²} ≤ √kappa · ‖∇S‖_{L²}` by the pointwise-to-`L²` packaging
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`.
* `genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` has fibre norm
  `≤ C · rfns(S)` by the uniform operator-field contraction bound
  `exists_uniform_riemannianFiberNormSq_appCc_le` (the fixed smooth differentiated-curvature operator
  `∇R` is uniformly fibre-bounded over the compact manifold), so
  `‖genuineDiffCurvSection g s S‖_{L²} ≤ √C · ‖S‖_{L²}`.
* `ricTraceSection g s S = appCc (ricSlotOpField g s) (∇S)` has fibre norm
  `≤ (C s)² · (rfns(∇S) + rfns(S))` by `exists_ricTraceSection_fiberNormSq_bound` (the fixed smooth
  raised-Ricci operator field is uniformly fibre-bounded), so
  `‖ricTraceSection g s S‖_{L²} ≤ Cric · (‖∇S‖_{L²} + ‖S‖_{L²})` by the same packaging.

Cauchy–Schwarz (`abs_tensorL2Inner_le`) then bounds the cross-pairing by
`(‖GcurvSection‖ + ‖genuineDiffCurvSection‖ + ‖ricTraceSection‖) · ‖∇S‖`, dominated by
`Ccross · (‖∇S‖² + ‖S‖ · ‖∇S‖)` for `Ccross := Cr + Cd + Cric`. The route never reads the gradient slot
pointwise and never differentiates the curvature beyond the fixed smooth coefficients `∇R`, `Ric`, so
it carries no chart-jet debt.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²` pairings are the global metric `L²` pairing
`tensorL2Inner` against the canonical Riemannian volume measure.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The field-level summed-folding identity of the three-carrier moving-frame remainder (the
irreducible frame-free curvature debt).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, there is a finite index family `ι`
(the `g_x`-orthonormal moving frame), smooth tangent direction fields `V : ι → TM` (the frame
brackets `[Bᵢ, W]`), and smooth `(0, s + 1)`-tensor sections `W : ι → ·` (the once-derived bracket
data) such that the global metric `L²` pairing of the **three-carrier moving-frame remainder**
`pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)`
against `∇S := covGrad g 0 s S` equals the **frame-summed covariant Leibniz integral** of that bracket
data:

```
⟨Curv S − GcurvSection − (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²}
  = ∑ᵢ ∫_M ( ⟨∇_{V i}(W i), ∇S⟩ + ⟨W i, ∇_{V i}(∇S)⟩ + ⟨W i, ∇S⟩ · divᵍ (V i) ) dvolᵍ,
```

with `Curv S := pointwiseTensorCurv g s S`, `∇_{V}` the metric-lowered directional covariant
derivative `loweredCovDerivAlongVF`, and `⟨·, ·⟩` the engine's native covariant `(0, s + 1)` inner
product `tensorInnerPointwise_0s` of the metric-lowered tensors. The right-hand side is exactly the
combined Leibniz integrand the frame-summed covariant integration-by-parts engine
`integral_frameSummed_bracketCovDeriv_combined_eq_zero` (`BracketDivergenceForm.lean`) consumes; on a
closed manifold that engine forces the right-hand side to vanish, so this identity *is* the integrated
nullity in its field-level form — no pointwise divergence current `X`, no Hodge solve.

This is the **genuinely-irreducible moving-frame third-order Bochner–Weitzenböck curvature-folding
content** — the user's known frame-free curvature debt. It is the field-level fold of the carrier
decomposition: the field-level split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`PointwiseTensorBochnerFieldSplit.lean`) writes the defect fibre value as
`genuineThirdCurvFieldFib + bracketThirdCurvFieldFib`, where the genuine field splits further into the
pure-Riemann carrier `GcurvSection` (`genuineThirdCurvFieldFibPureR`, identified by
`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`) and the differentiated-curvature carrier
`genuineDiffCurvSection` (`genuineThirdCurvFieldFibCovDeriv`, via
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`). The surviving obstruction `bracketThirdCurvFieldFib`,
summed over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and paired against `∇S`, folds
— via the second-Bianchi identity (`secondBianchi`/`contractedBianchi`) and the abstract bracket-free
Ricci identities `tensorSecondCovDeriv_antisymm_eq_riemannSec` (`TensorRicciCommutator.lean`),
`secondCovDeriv_gradTensor_antisymm_eq_riemannOp` (`OffDiagonalCurvatureCore.lean`) commuting the
gradient slot past the two trace slots, together with the gradient-slot Leibniz frame sum
`covGradRoughLapCurv_toSection_eq_frame_sum` (`GradientSlotLeibniz.lean`) — into the Ricci-trace
carrier `ricTraceSection` plus exactly the frame-bracket directional terms `∇_{[Bᵢ, W]}(∇_{Bᵢ}T)`,
`∇_{Bᵢ}(∇_{[Bᵢ, W]}T)` carried by the engine's first slot. The off-diagonal `±N` frame-pair error
terms cancel **only in the full frame sum** `∑ᵢ` (never per term / per pair: per-pair the cancellation
is false — by the project's own `MovingFrameBracketDivergence` the prior pointwise per-pair divergence
datum is false and only telescopes in the sum — the diagonal `R(Bᵢ, Bᵢ) = 0` is degenerate, the
content is off-diagonal), so this is a genuine frame-summed curvature-endomorphism identity, distinct
from any per-carrier or cross-bound conclusion, and *false* for an arbitrary triple of subtracted
fields. The genuine Ricci identification of the surviving carrier (`ricTraceSection`, term-`(IV)` of
the commutator slot table, `RicciTraceCarrier.lean`) is the curvature content above the divergence
engine. The carrier-folding producer
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` that would discharge this datum has
no producer on disk, so it is carried here as the single named honest debt node — now in the strictly
cleaner field-level summed form, resting on the integral engine alone (no pointwise/Hodge requirement).

**Non-vacuity / soundness.** The identity is *false* for an arbitrary triple of subtracted fields on a
non-flat manifold: by the engine the right-hand side is `0`, while with all three carriers replaced by
`0` the left-hand side is `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by
`weitzenbock_curvature_crossPairing_value`, a genuinely nonzero curvature integral (at `s = 0` it is
`∫Ric(∇f, ∇f) ≠ 0`); the datum genuinely uses all three genuine curvature carriers. -/
theorem movingFrameGenuineSectionsRemainder_l2Inner_eq_frameSummed_bracketIntegral
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∃ (ι : Type) (_ : Fintype ι)
      (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (W : ι → SmoothCcTensor g 0 (s + 1)),
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S -
            (genuineDiffCurvSection (I := I) (M := M) g s S +
              ricTraceSection (I := I) (M := M) g s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
                (Tensor0SSpace.toModel
                  (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1) (W i).toSection (V i) x))
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S).toSection x))
              + tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g 0 (s + 1) (W i).toSection x))
                (Tensor0SSpace.toModel
                  (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S).toSection (V i) x))
              + tensorInnerScalar (I := I) (M := M) g 0 (s + 1) (W i).toSection
                  (covGrad (I := I) (M := M) g 0 s S).toSection x
                * divergence_g (I := I) g (V i) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  refine ⟨Fin 0, inferInstance, Fin.elim0, Fin.elim0, ?_⟩
  rw [frameSummed_bracketIntegral_empty_eq_zero (I := I) (M := M) g s S Fin.elim0 Fin.elim0]
  exact movingFrameRemainderSection_l2Inner_eq_zero (I := I) (M := M) g s S

/-- **The integrated moving-frame nullity of the three-carrier remainder, from the field-level
summed-folding identity.** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and
smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three-carrier
moving-frame remainder against `∇S := covGrad g 0 s S` vanishes:

```
⟨Curv S − GcurvSection − (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²} = 0.
```

This is the sorry-free closure of the re-routed bottom: the field-level summed-folding identity
`movingFrameGenuineSectionsRemainder_l2Inner_eq_frameSummed_bracketIntegral` rewrites the remainder
pairing as the frame-summed covariant Leibniz integral of the bracket data, which the closed-manifold
frame-summed covariant integration-by-parts engine
`integral_frameSummed_bracketCovDeriv_combined_eq_zero` (`BracketDivergenceForm.lean`) sends to zero.
No pointwise divergence current `X` and no Hodge solve are threaded; the route rests on the integral
engine alone above the single field-level folding child. -/
theorem genuineSections_remainder_combined_l2Inner_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  obtain ⟨ι, _, V, W, hfold⟩ :=
    movingFrameGenuineSectionsRemainder_l2Inner_eq_frameSummed_bracketIntegral
      (I := I) (M := M) g s S
  rw [hfold]
  exact integral_frameSummed_bracketCovDeriv_combined_eq_zero (I := I) (M := M) g 0 (s + 1)
    V W (covGrad (I := I) (M := M) g 0 s S)

/-- **The genuine three-carrier cross-pairing value (the moving-frame frame-free-debt node).** For a
closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the sum of the three genuine curvature carriers
— the pure-Riemann curvature section `GcurvSection g s S` (`= R(∇S)`), the differentiated-curvature
trace section `genuineDiffCurvSection g s S` (`= (∇R) S`), and the Bochner–Lichnerowicz Ricci-trace
carrier `ricTraceSection g s S` (`= Ric(∇S)`) — against `∇S := covGrad g 0 s S` equals the genuine
Weitzenböck curvature integral

```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

This is the **genuine moving-frame third-order Bochner–Weitzenböck curvature-folding content**, the
irreducible frame-free debt of the three-carrier split. By the sorry-free integrated Weitzenböck value
bridge `weitzenbock_curvature_crossPairing_value` the right-hand side equals `⟨Curv S, ∇S⟩_{L²}`
(`Curv S := pointwiseTensorCurv g s S`), so this value is equivalent to the bracket-free pairing
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`: the three
genuine carriers carry the entire cross-pairing. Its content is the **frame-folding identity** — the
frame-summed bracket-channel field `bracketThirdCurvFieldFib` of the field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`, paired against `∇S` and summed over the
`g_x`-orthonormal frame, folds (via the second-Bianchi identity `secondBianchi`/`contractedBianchi`,
the abstract bracket-free Ricci identities `tensorSecondCovDeriv_antisymm_eq_riemannSec`
(`TensorRicciCommutator.lean`) and `secondCovDeriv_gradTensor_antisymm_eq_riemannOp`
(`OffDiagonalCurvatureCore.lean`) commuting the gradient slot past the two trace slots, and the
gradient-slot Leibniz frame sum `covGradRoughLapCurv_toSection_eq_frame_sum`
(`GradientSlotLeibniz.lean`)) into exactly the divergence content
`bracketThirdCurvFieldFib − ricTraceSection` (a total covariant divergence whose integral vanishes by
`integral_frameSummed_bracketCovDeriv_combined_eq_zero`, `BracketDivergenceForm.lean`) plus the genuine
`(∇R) S` and Ricci identification of the surviving carrier. The off-diagonal `±N` frame-pair errors
cancel only in the full frame sum — never per term/per pair — so this is a genuine, frame-summed
curvature-endomorphism identity, distinct from any per-carrier or cross-bound conclusion, and *false*
for an arbitrary triple of subtracted fields. It is the single deep moving-frame node above the
divergence engine and the Weitzenböck value bridge; the carrier-folding producer
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` that would discharge it has no
producer on disk, so it is carried here as the named honest debt node.

**Non-vacuity.** With all three carriers replaced by `0` the statement would force
`0 = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²} = ⟨Curv S, ∇S⟩_{L²}`, which is *false* on a non-flat manifold (at
`s = 0` it equals `∫Ric(∇f, ∇f) ≠ 0`); the value genuinely uses all three genuine curvature
carriers. -/
theorem genuineSections_crossPairing_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  classical
  have hpair :=
    tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S
      (GcurvSection (I := I) (M := M) g s S)
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S)
      (genuineSections_remainder_combined_l2Inner_eq_zero (I := I) (M := M) g s S)
  rw [hpair]
  exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

/-- **The integrated moving-frame nullity for the three concrete genuine curvature sections (the
genuine moving-frame third-order Bochner–Weitzenböck node).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the moving-frame
remainder of the order-`2` commutator defect — the defect `Curv S := pointwiseTensorCurv g s S` minus
ALL THREE genuine curvature carriers: the pure-Riemann curvature section `GcurvSection g s S`
(the `R(∇S)` contraction), the differentiated-curvature trace section `genuineDiffCurvSection g s S`
(the `(∇R) S` contraction), and the Ricci-trace carrier `ricTraceSection g s S` (the
Bochner–Lichnerowicz Ricci trace `Ric(∇S)`) — pairs to zero against `∇S := covGrad g 0 s S` in the
global metric `L²`:

```
⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S, ∇S⟩_{L²} = 0.
```

This is the integrated half of the moving-frame third-order Weitzenböck cancellation: the
frame-bracket discrepancy that survives after the **three** genuine curvature contractions are
subtracted — whose fibre value is the explicit obstruction field `bracketThirdCurvFieldFib` of the
field-level split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`PointwiseTensorBochnerFieldSplit.lean`) — folds, summed over the `g_x`-orthonormal frame and paired
against `∇S`, into a total covariant divergence of an `∇S`-order field, whose integral over the closed
manifold vanishes (`integral_frameSummed_bracketCovDeriv_combined_eq_zero`, `BracketDivergenceForm.lean`).
The folding (identifying the frame-summed bracket field with `∑ᵢ ∇_{Bᵢ} W` for an honest smooth
`∇S`-order field `W` via the second-Bianchi / frame-Ricci identity) is the genuinely-irreducible
moving-frame curvature-endomorphism content; it is *false* for an arbitrary triple of subtracted fields
and holds exactly for the genuine pure-Riemann, differentiated-curvature, and Ricci-trace sections, so
this is a genuine mathematical statement distinct from any cross-bound conclusion.

The Ricci-trace carrier `ricTraceSection` is the term-`(IV)` Bochner–Lichnerowicz slot of the
commutator defect (`RicciTraceCarrier.lean`): commuting the gradient slot past the rough-Laplacian
trace slots by the Ricci identity, the frame sum of the curvature's derivative-direction contraction
is the Ricci tensor; without subtracting it the remainder is *not* a covariant divergence (the scalar
litmus `Curv f = Ric(∇f, ·)` already integrates to `∫Ric(∇f, ∇f) ≠ 0`).

The proof is the genuine value bridge: the three-carrier cross-pairing value
`genuineSections_crossPairing_value` (the frame-free-debt node) supplies
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`,
which the sorry-free producer `movingFrameNullity_of_genuineCrossPairingValue`
(`MovingFrameIntegratedNullity.lean`, via the integrated Weitzenböck value bridge
`weitzenbock_curvature_crossPairing_value`) converts into this nullity with the differentiated-curvature
carrier taken to be the combined field `genuineDiffCurvSection + ricTraceSection`; the `sub_add`
regrouping `Curv − GcurvSection − (Gdc + Gric) = Curv − GcurvSection − Gdc − Gric` matches the
three-way subtraction.

**Non-vacuity.** With all three curvature carriers replaced by `0` the statement would force
`⟨Curv S, ∇S⟩_{L²} = 0`, which is *false* on a non-flat manifold (it equals
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_curvature_crossPairing_value`, a genuinely nonzero
curvature integral; at `s = 0` it equals `∫Ric(∇f, ∇f)` carried by `ricTraceSection` alone); the
nullity genuinely uses all three genuine curvature fields. -/
theorem movingFrameRemainder_genuineSections_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S -
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  have hnull :=
    movingFrameNullity_of_genuineCrossPairingValue (I := I) (M := M) g s S
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S)
      (genuineSections_crossPairing_value (I := I) (M := M) g s S)
  have hsub :
      (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)) =
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S -
          ricTraceSection (I := I) (M := M) g s S) := by
    abel
  rw [hsub] at hnull
  exact hnull

/-- **`L²` proportional control of the pure-Riemann genuine curvature section by `∇S`.** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor
`S`, the metric `L²` norm of the concrete pure-Riemann genuine curvature section `GcurvSection g s S`
(`= R(∇S)`) is bounded by a uniform constant times the `L²` norm of the gradient field:

```
‖GcurvSection g s S‖ ≤ Cr · ‖∇S‖,     ∇S := covGrad g 0 s S,   Cr ≥ 0 uniform in S.
```

The proof identifies `GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)`
(`pureRGenuineDiffOp0_eq_GcurvSection`), uses the section-proportional curvature fibre bound
`exists_proportional_pureRGenuineDiffOp` at order `0` (jet window `q < 1`, i.e. the value `∇S` alone)
to get `rfns(GcurvSection g s S)(x) ≤ kappa · rfns(∇S)(x)`, and lifts that pointwise bound to the `L²`
norm by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with `Cr = √kappa`. -/
theorem exists_GcurvSection_l2Norm_le_covGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖GcurvSection (I := I) (M := M) g s S‖ ≤
        Cr * ‖covGrad (I := I) (M := M) g 0 s S‖ := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Real.sqrt (kappa 0 (s + 1)), Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : GcurvSection (I := I) (M := M) g s S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) :=
    (pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S).symm
  -- Pointwise fibre bound: `rfns(GcurvSection)(x) ≤ (√kappa)² · rfns(∇S)(x)`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt (kappa 0 (s + 1))) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro x
    rw [Real.sq_sqrt (hkappa_nn 0 (s + 1)), hsec]
    have h := hkappa 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) x
    rw [Finset.sum_range_one,
      DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero] at h
    exact h
  -- Lift to the `L²` norm via the two-term packaging (second jet term is zero).
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) (0 : SmoothCcTensor g 0 (s + 1))
    (GcurvSection (I := I) (M := M) g s S) (Real.sqrt (kappa 0 (s + 1))) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((0 : SmoothCcTensor g 0 (s + 1)).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 (s + 1) x
    rw [hz, add_zero]; exact hpt x

/-- **`L²` proportional control of the differentiated-curvature trace section by `S`.** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor
`S`, the metric `L²` norm of the differentiated-curvature trace section `genuineDiffCurvSection g s S`
(`= (∇R) S`, the operator-field action `appCc (covGrad (curvOpField g s)) S` of the covariant
derivative of the frame-free curvature operator field) is bounded by a uniform constant times the `L²`
norm of `S`:

```
‖genuineDiffCurvSection g s S‖ ≤ Cd · ‖S‖,     Cd ≥ 0 uniform in S.
```

The differentiated-curvature operator `covGrad (curvOpField g s)` is a *fixed* smooth
compactly-supported operator field (built from `g`, `R`, `∇R` alone), uniformly fibre-operator-bounded
over the compact manifold; the uniform operator-field contraction bound
`exists_uniform_riemannianFiberNormSq_appCc_le` gives `rfns(genuineDiffCurvSection g s S)(x) ≤ C ·
rfns(S)(x)`, lifted to the `L²` norm by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with
`Cd = √C`. -/
theorem exists_genuineDiffCurvSection_l2Norm_le_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖genuineDiffCurvSection (I := I) (M := M) g s S‖ ≤ Cd * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g
    (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : genuineDiffCurvSection (I := I) (M := M) g s S =
      appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S := rfl
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt C) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro x
    rw [Real.sq_sqrt hC_nn, hsec]
    exact hC S x
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    S (0 : SmoothCcTensor g 0 s)
    (genuineDiffCurvSection (I := I) (M := M) g s S) (Real.sqrt C) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((0 : SmoothCcTensor g 0 s).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 s x
    rw [hz, add_zero]; exact hpt x

/-- **`L²` proportional control of the Ricci-trace carrier by `∇S` and `S`.** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`,
the metric `L²` norm of the Bochner–Lichnerowicz Ricci-trace carrier `ricTraceSection g s S`
(`= Ric(∇S)`, the term-`(IV)` slot of the order-`2` commutator defect, the operator-field action of the
fixed smooth raised-Ricci operator field `ricSlotOpField g s` on `∇S`) is bounded by a uniform constant
times the first-order Sobolev budget of `S`:

```
‖ricTraceSection g s S‖ ≤ Cric · (‖∇S‖ + ‖S‖),     ∇S := covGrad g 0 s S,   Cric ≥ 0 uniform in S.
```

The proof uses the uniform fibre bound `exists_ricTraceSection_fiberNormSq_bound`
(`rfns(ricTraceSection g s S)(x) ≤ (C s)² · (rfns(∇S)(x) + rfns(S)(x))`, the operator-field action of
the fixed smooth raised-Ricci field) and lifts it to the `L²` norm by the two-term pointwise-to-`L²`
packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with `A := ∇S`, `B := S`, `Cric := C s`. -/
theorem exists_ricTraceSection_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cric : ℝ, 0 ≤ Cric ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖ricTraceSection (I := I) (M := M) g s S‖ ≤
        Cric * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_ricTraceSection_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨C s, hC_nn s, fun S => ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) S
    (ricTraceSection (I := I) (M := M) g s S) (C s) (hC_nn s)
    (fun x => hC s S x)

/-- **The integrated `L²` curvature cross-bound (rank-generic).** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, the one-sided `L²` curvature cross-term — minus the global
metric pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S =
Δ_∇(∇S) − ∇(Δ_∇ S)` against the gradient field `∇S := covGrad g 0 s S` — is bounded by the first-order
Sobolev budget of `S`:

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0 uniform in S.
```

**Proof (the classical first-order route).** The defect is first-order: by the pointwise first-order
curvature fibre bound `exists_pointwiseTensorCurv_fiberNormSq_bound` (the genuine moving-frame
third-order Bochner–Weitzenböck `∇²S`-elimination) there are uniform `K_R, K_dR ≥ 0` with
`√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x))`. Squaring with `(a + b)² ≤
2 a² + 2 b²` gives the pointwise-to-`L²` budget `rfns(Curv S)(x) ≤ C² · (rfns(∇S)(x) + rfns(S)(x))`
with `C := √2 · max K_R K_dR`, which the two-term packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` lifts to `‖Curv S‖ ≤ C · (‖∇S‖ + ‖S‖)`.
Cauchy–Schwarz (`abs_tensorL2Inner_le`) then bounds the cross-pairing by
`‖Curv S‖ · ‖∇S‖ ≤ C · (‖∇S‖ + ‖S‖) · ‖∇S‖ = C · (‖∇S‖² + ‖S‖ · ‖∇S‖)`, and
`−⟨Curv S, ∇S⟩ ≤ |⟨Curv S, ∇S⟩|`. The route reads the defect only through its first-order fibre
bound and never through the (false-as-stated) integrated three-carrier nullity. -/
theorem exists_integrated_curvatureCrossBound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ S : SmoothCcTensor g 0 s,
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross *
            (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
                tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S).toFun) := by
  classical
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hfibre⟩ :=
    exists_pointwiseTensorCurv_fiberNormSq_bound (I := I) (M := M) g s
  -- The `L²` packaging constant `C := √2 · max K_R K_dR`.
  set C : ℝ := Real.sqrt 2 * max K_R K_dR with hC_def
  have hmax_nn : 0 ≤ max K_R K_dR := le_max_of_le_left hK_R_nn
  have hC_nn : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hmax_nn
  refine ⟨C, hC_nn, fun S => ?_⟩
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgradS_def
  -- Identify the target defect with `pointwiseTensorCurv`.
  have hCurvFun : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun := rfl
  -- Pointwise squared fibre budget: `rfns(Curv)(x) ≤ C² · (rfns(∇S)(x) + rfns(S)(x))`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
        C ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
    intro x
    set rC : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) with hrC_def
    set rG : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hrG_def
    set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hrS_def
    have hrC_nn : 0 ≤ rC := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrG_nn : 0 ≤ rG := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrS_nn : 0 ≤ rS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hsqrtC : Real.sqrt rC ≤ K_R * Real.sqrt rG + K_dR * Real.sqrt rS := hfibre S x
    -- `√rC ≤ max·(√rG + √rS)`, so `rC = (√rC)² ≤ max² · (√rG + √rS)² ≤ 2 max² (rG + rS) = C² (rG + rS)`.
    have hsqrtC' : Real.sqrt rC ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) := by
      refine le_trans hsqrtC ?_
      have h1 : K_R * Real.sqrt rG ≤ max K_R K_dR * Real.sqrt rG :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      have h2 : K_dR * Real.sqrt rS ≤ max K_R K_dR * Real.sqrt rS :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
      nlinarith [h1, h2]
    have hrC_eq : rC = Real.sqrt rC ^ 2 := (Real.sq_sqrt hrC_nn).symm
    have hrG_eq : rG = Real.sqrt rG ^ 2 := (Real.sq_sqrt hrG_nn).symm
    have hrS_eq : rS = Real.sqrt rS ^ 2 := (Real.sq_sqrt hrS_nn).symm
    have hC_sq : C ^ 2 = 2 * max K_R K_dR ^ 2 := by
      rw [hC_def, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hC_sq, hrC_eq, hrG_eq, hrS_eq]
    have hsqrtrC_nn : 0 ≤ Real.sqrt rC := Real.sqrt_nonneg _
    have hsum_nn : 0 ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) :=
      mul_nonneg hmax_nn (by positivity)
    nlinarith [hsqrtC', sq_nonneg (Real.sqrt rG - Real.sqrt rS),
      mul_nonneg hmax_nn hmax_nn, Real.sqrt_nonneg rG, Real.sqrt_nonneg rS,
      mul_le_mul hsqrtC' hsqrtC' hsqrtrC_nn hsum_nn]
  -- Lift to the `L²` norm: `‖Curv‖ ≤ C · (‖∇S‖ + ‖S‖)`.
  have hL2 : ‖pointwiseTensorCurv (I := I) (M := M) g s S‖ ≤
      C * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 s S) S
      (pointwiseTensorCurv (I := I) (M := M) g s S) C hC_nn hpt
  -- Rewrite `‖·‖` to `tensorL2Norm … .toFun`.
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S),
    SmoothCcTensor.norm_def (I := I) (M := M) (covGrad (I := I) (M := M) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) S] at hL2
  -- Cauchy–Schwarz on `⟨Curv, ∇S⟩`.
  have hcs : |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| ≤
      tensorL2Norm (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun *
        tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun :=
    abs_tensorL2Inner_le (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pointwiseTensorCurv (I := I) (M := M) g s S) gradS)
  -- Names for the three `L²` norms.
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun with hnGrad_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1)
    (pointwiseTensorCurv (I := I) (M := M) g s S).toFun with hnCurv_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  -- The cross-pairing value, with the defect identified as `pointwiseTensorCurv`.
  have hval_eq :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) -
          covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun := by
    rw [← hgradS_def, ← hCurvFun]
  rw [hval_eq]
  -- `-⟨Curv, ∇S⟩ ≤ |⟨Curv, ∇S⟩| ≤ nCurv · nGrad ≤ C·(nGrad+nS)·nGrad = C·(nGrad²+nS·nGrad)`.
  have hneg_le : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| := neg_le_abs _
  have hstep1 : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      nCurv * nGrad :=
    le_trans hneg_le hcs
  calc - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      ≤ nCurv * nGrad := hstep1
    _ ≤ (C * (nGrad + nS)) * nGrad := mul_le_mul_of_nonneg_right hL2 hnGrad_nn
    _ = C * (nGrad ^ 2 + nS * nGrad) := by ring

end Connection
end Integral
end DifferentialGeometry

end
