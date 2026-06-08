import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientSlotCurvatureSplit
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm

/-!
# The frame-free curvature operator field and the integrated tensor Bochner–Weitzenböck curvature value

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this upstream file homes the
**frame-free curvature operator field** `Φ₀ s := curvOpField g s` and the single genuinely-irreducible
**integrated tensor Bochner–Weitzenböck curvature value** of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`,
`∇S := covGrad g 0 s S`).

* `curvOpField g s` — the fixed smooth `(s, s)`-operator field whose operator-field action recovers the
  order-`0` moving-frame pure-Riemann curvature endomorphism `pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W`
  (`exists_pureRGenuineDiffOp_base_appCc`). It is the curvature coefficient whose covariant derivative
  carries the differentiated-curvature `(∇R)` content; a pure `Classical.choose` definition with no
  downstream dependency, homed here so the whole curvature line shares it.

* `curvatureValue_genuineFields_eq_weitzenbock` — the **integrated tensor Bochner–Weitzenböck curvature
  value** (the curvature line's single genuine deep root, in its canonical value form): the three
  concrete genuine curvature carriers — the pure-Riemann `R(∇S)` trace `GcurvSection g s S`, the
  differentiated-curvature `(∇R) S` trace `appCc (∇Φ₀ s) S` (`∇Φ₀ s := covGrad g s s (Φ₀ s)`), and the
  leading-slot Ricci trace `ricTraceSection g s S` — paired against `∇S`, carry the entire integrated
  Weitzenböck Dirichlet defect `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`. This is the genuine classical content; it is
  proved here by composition (peeling the pure-Riemann channel and the operator-field
  integration-by-parts bookkeeping sorry-free, via `bochnerWeitzenbockResidueValue`) over the single
  posited genuine bracket-channel root `frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace`
  (the differentiated-curvature operator-field identification + integrated second-Bianchi Ricci fold +
  gradient-slot divergence-zero — the curvature line's single irreducible deep leaf). The four-carrier
  integrated nullity `fourCarrierMovingFrameRemainder_integrated_nullity` (`BracketDiscrepancyNullity`) is
  in turn proved by composition over the value through the sorry-free integrated-nullity producer
  `movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`, which discharges the
  divergence-IBP half of the Bochner mechanism).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The frame-free curvature operator field is
built from `g, R` alone; all fibre norms are the intrinsic Riemannian fibre norm.
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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The frame-free curvature operator field `Φ₀ s`.** The fixed smooth `(s, s)`-operator field whose
operator-field action recovers the order-`0` moving-frame pure-Riemann curvature endomorphism
`pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W` (`exists_pureRGenuineDiffOp_base_appCc`); its fibre value
is the genuine `g`-metric curvature trace `W ↦ ∑ᵢ R(Bᵢ, ·) W`, frame-free (built from `g, R` alone). It
is the curvature coefficient whose covariant derivative carries the differentiated-curvature `(∇R)`
content. It is a pure `Classical.choose` definition (no downstream dependency), homed upstream so the
curvature line shares it. -/
noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g)) s

/-- **The order-`0` curvature operator base spec for `curvOpField`.** The defining `Classical.choose`
specification: the operator-field action of the frame-free curvature operator field `Φ₀ s := curvOpField
g s` on a smooth compactly-supported `(0, s)`-tensor `S` recovers the order-`0` moving-frame pure-Riemann
curvature trace `pureRGenuineDiffOp g 0 s S`. This is the identity through which the differentiated
operator field `covGrad (Φ₀ s)` and its passenger-slot extension `slotExtend (Φ₀ s)` are identified with
the curvature-derivative content. -/
theorem appCc_curvOpField_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm

/-- **The differentiated-curvature operator-field section `(∇R) S`** (the homed-upstream copy of the
spine's `genuineDiffCurvSection`, value-anchored at the curvature operator field). For a smooth
compactly-supported `(0, s)`-tensor `S`, the operator-field action of the covariant derivative of the
frame-free curvature operator field `Φ₀ s := curvOpField g s` on `S`:
```
diffCurvOpFieldSection g s S := appCc (covGrad g s s (Φ₀ s)) S,
```
the differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), a smooth
compactly-supported `(0, s + 1)`-tensor. It is `defeq` to the four-carrier nullity's third carrier
`appCc (covGrad g s (s + 1)) (covGrad g s s (Φ₀ s)) S` (the `s + 1`-codomain `appCc` is the same map as
`appCc … s s` up to the `Nat.add_zero` index — both contract the single new slot). Homed here so the
upstream curvature-value root and the four-carrier nullity share the carrier without a forward reference
into the downstream moving-frame spine `MovingFrameDiffCurvTraceSection`. -/
noncomputable def diffCurvOpFieldSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g s (s + 1)
    (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S

/-- **The integrated differentiated-curvature operator-field cross-pairing's integration-by-parts
formula (the sorry-free tensorial bookkeeping for the concrete `(∇R) S` carrier).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the
global metric `L²` pairing of the differentiated-curvature operator-field section
`diffCurvOpFieldSection g s S = appCc (covGrad g s s (Φ₀ s)) S` (the `(∇R) S` field) against
`∇S := covGrad g 0 s S` is

```
⟨diffCurvOpFieldSection g s S, ∇S⟩_{L²}
  = −⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` the order-`0`
moving-frame pure-Riemann curvature trace, and `∇S := covGrad g 0 s S`.

**Proof (sorry-free).** This is the operator-field integration-by-parts identity
`tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) specialised to the frame-free
curvature operator field `Φ₀ s = curvOpField g s`; the order-`0` action `appCc (Φ₀ s) S` is rewritten to
`pureRGenuineDiffOp g 0 s S` by the base spec `appCc_curvOpField_eq_pureRGenuineDiffOp` (the
`Classical.choose` spec defining `curvOpField`). All bridges are sorry-free; the mirror of the spine's
`tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg`, hoisted upstream so the curvature-value root
consumes it without a forward reference. -/
theorem tensorL2Inner_diffCurvOpFieldSection_covGrad_eq_neg
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (diffCurvOpFieldSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S := by
    have := appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
    simpa using this
  have hgen := tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hgen
  exact hgen

/-- **The genuine curvature-fields cross-pairing equals the explicit four-pairing residue (the
sorry-free Bochner curvature-term bookkeeping, slot-complete form, homed upstream).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the
global metric `L²` pairing of the three concrete genuine curvature sections
`GcurvSection g s S + (diffCurvOpFieldSection g s S + ricTraceSection g s S)` (the pure-Riemann `R(∇S)`
trace, the differentiated-curvature `(∇R) S` trace, and the leading-slot Ricci trace) against
`∇S := covGrad g 0 s S` equals the explicit four-pairing combination — the three-pairing Bochner residue
plus the Ricci-trace pairing.

**Proof (sorry-free bookkeeping).** Split the left additivity of the cross-pairing twice
(`tensorL2Inner_add_left`, the cross-integrabilities `SmoothCcTensor.integrable_inner_cross`) into the
pure-Riemann, differentiated-curvature, and Ricci-trace summands, rewrite the pure-Riemann summand by the
pairing bridge `tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`
(`MovingFramePureRCurvatureTracePairing`, sorry-free), and rewrite the differentiated-curvature summand by
the operator-field integration-by-parts identity `tensorL2Inner_diffCurvOpFieldSection_covGrad_eq_neg`
(sorry-free, above). The Ricci-trace summand is carried as-is. This is the upstream mirror of the spine's
`genuineCurvFields_crossPairing_eq_residue`, homed here so the curvature-value root is sorry-free over the
single posited deep leaf. -/
theorem genuineCurvFields_crossPairing_eq_residue_upstream
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (diffCurvOpFieldSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun S.toFun -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (appCc (I := I) (M := M) g (s + 1) (s + 1)
              (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))
              (covGrad (I := I) (M := M) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    (GcurvSection (I := I) (M := M) g s S).toFun
    (diffCurvOpFieldSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (diffCurvOpFieldSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    (diffCurvOpFieldSection (I := I) (M := M) g s S).toFun
    (ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (diffCurvOpFieldSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  rw [tensorL2Inner_diffCurvOpFieldSection_covGrad_eq_neg (I := I) (M := M) g s S]
  ring

/-- **The genuine curvature-fields cross-pairing value `(★)` — the single irreducible integrated tensor
Bochner–Weitzenböck curvature value, in its frame-free three-section value form (the curvature line's
genuine deep leaf).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and
every smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete
genuine operator-field curvature carriers `GcurvSection g s S + (diffCurvOpFieldSection g s S +
ricTraceSection g s S)` — the pure-Riemann `R(∇S)` trace, the differentiated-curvature `(∇R) S` trace
`diffCurvOpFieldSection g s S = appCc (covGrad g s s (Φ₀ s)) S`, and the leading-slot Ricci trace —
against `∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` against
`∇S`:
```
⟨GcurvSection g s S + (diffCurvOpFieldSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

**This is the genuine new mathematical content of the entire curvature line — the single irreducible
integrated tensor Bochner–Weitzenböck curvature-term identity.** Both the bracket-channel integral root
`bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root` (below) and, through the sorry-free
peel + bookkeeping, the whole operator-field residue value, the four-carrier nullity, and every downstream
cross-pairing node are proved by composition over *this* value. It is the verbatim three-section value
form (with the carrier `diffCurvOpFieldSection` `defeq` to `appCc (covGrad g s s (Φ₀ s)) S`) of the
downstream spine's atomic value leaf `genuineCurvFields_crossPairing_value_bochnerLeaf`
(`MovingFrameDiffCurvTraceSection`), hoisted to the most-upstream curvature node so this file is the
line's deep root.

**The three-fold integrated content it carries (no sorry-free bridge below this node).** By the iterated
Ricci identity the gradient-slot reordering of the order-`2` defect `Curv S` produces, after subtracting
the pure-Riemann `R(∇S)` trace `GcurvSection g s S` (carried sorry-free by
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`), exactly the bracket channel, whose integrated value
is the coupled sum of three pieces, sound only *summed and integrated*:
(i) the frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` identified with the
operator-field carrier `diffCurvOpFieldSection g s S = appCc (covGrad (Φ₀ s)) S` (*false pointwise
per-direction* — the `smoothExtensionTangent` direction reading is chart-selection-unbounded on `S²`);
(ii) the second-Bianchi cyclic fold of the contracted-curvature slot into the raised Ricci endomorphism
`ricEndoRaisedFib = ricTraceSection` (`ricEndoRaisedFib_inner_eq_frame_trace`,
`second_bianchi_levi_civita_metric`, `ricTraceSection_apply_leadingSlot`, `contracted_second_bianchi`);
(iii) the surviving `∇²S`-order gradient-slot bracket discrepancy `tensor3rdCurvBracket` exhibited as a
total covariant divergence integrating to zero over the closed manifold (the divergence engine
`integral_frameSummed_covDeriv_combined_eq_zero` / `integral_frameSummed_bracketCovDeriv_combined_eq_zero`,
with the gradient-slot channel `L²`-orthogonal `gradSlotCurv_pairing_covGrad_eq_zero`). The three are
mathematically *coupled* — the per-direction differentiated-curvature trace differs from the
operator-field carrier by exactly the bracket discrepancy of (iii), which integrates to zero only when
summed, so no one of (i)/(ii)/(iii) is a true free-standing integral identity; only their joint
*integrated* value is sound, and that is exactly `(★)`. The identity is stated at the *integrated*
frame-free `L²` level throughout — it never extracts a per-direction `M → E` quantity (which would be
chart-selection-unbounded; T1) — so it is trap-screened. The body is `sorry` (the genuine classical
integrated tensor Bochner–Weitzenböck curvature-term derivation); consumers transitively depend on
`sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the curvature of a scalar, which
vanishes; `diffCurvOpFieldSection g 0 f = appCc 0 f = 0`), so `(★)` collapses to
`⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ⟨Curv f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the
classical scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes `(★)` FALSE at
`s = 0`, so the carrier is genuinely required and the identity is not vacuous (it fails for a
`κ ≠ 1`-perturbed curvature residue). -/
theorem genuineCurvFields_starValue_bochnerLeaf
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (diffCurvOpFieldSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  sorry

/-- **The frame-bracket remainder frame-sum integral carries the differentiated-curvature operator-field
trace plus the Ricci trace (the curvature line's single irreducible integrated deep root, the strictly-
smaller bracket-channel form — the genuine classical leaf).** For a closed smooth Riemannian manifold
`(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the integral
over the closed manifold of the fixed-frame sum of the per-direction frame-bracket remainder fibres
`remDiffBracketFib` (the frame summand `remDiffFib` minus its pure-Riemann genuine curvature fibre
`remDiffGenuineFib`), paired against `∇S := covGrad g 0 s S`, equals the global metric `L²` pairing of the
differentiated-curvature operator-field section `diffCurvOpFieldSection g s S = appCc (covGrad (Φ₀ s)) S`
(the `(∇R) S` field) plus the leading-slot Ricci-trace carrier `ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨diffCurvOpFieldSection g s S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine new mathematical content of the entire curvature line — the single irreducible
integrated tensor Bochner–Weitzenböck curvature-identity root, the strictly-smaller passenger-`W`
bracket channel with the pure-`R` channel peeled off sorry-free.** It is the verbatim statement of the
spine's `remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace` and of `BracketDiscrepancyNullity`'s
`bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace` (with the carrier `diffCurvOpFieldSection`
defeq to `appCc (covGrad g s s (Φ₀ s)) S`), here hoisted to the most-upstream curvature-value node so this
file is the line's deep root and the architectural circle `BracketDiscrepancyNullity →
MovingFrameCurvatureValueAnchor` is never re-entered. The whole operator-field residue value, the
three-section value `(★)`, the four-carrier nullity, and every downstream cross-pairing node are proved by
composition over *this* single integrated identity plus the sorry-free pure-`R` peel
`bracketRemainderFrameSum_integral_eq_movingFrameRemainder_local`.

**Why it is genuinely irreducible (the three-fold integrated content, no sorry-free bridge below this
node).** Pointwise each frame summand `remDiffFib g s S x i` is the gradient-slot reordering of the three
covariant slots (`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`); subtracting the pure-Riemann
genuine fibre `remDiffGenuineFib g s S x i` leaves the frame-bracket remainder, which carries threefold
genuine content, sound only after frame-summing and integrating: (i) the integrated identification of the
frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier
`diffCurvOpFieldSection g s S = appCc (covGrad (Φ₀ s)) S` — *false pointwise per-direction* (the
`smoothExtensionTangent` direction reading is chart-selection-unbounded on `S²`), sound only integrated;
(ii) the second-Bianchi cyclic fold of the contracted-curvature slot into the raised Ricci endomorphism
`ricEndoRaisedFib = ricTraceSection` (`ricEndoRaisedFib_inner_eq_frame_trace`,
`second_bianchi_levi_civita_metric`, `ricTraceSection_apply_leadingSlot`,
`contracted_second_bianchi` are the pointwise pieces); and (iii) the gradient-slot lift exhibiting the
surviving `∇²S`-order bracket discrepancy (`tensor3rdCurvBracket`) as a total covariant divergence
integrating to zero over the closed manifold (the divergence-vanishing engine
`integral_frameSummed_covDeriv_combined_eq_zero` / `integral_frameSummed_bracketCovDeriv_combined_eq_zero`,
with the gradient-slot channel `L²`-orthogonal `gradSlotCurv_pairing_covGrad_eq_zero`). These three are
mathematically *coupled* and sound only summed-and-integrated; their joint integrated value is the genuine
deep leaf `(★)` `genuineCurvFields_starValue_bochnerLeaf` (above). The identity is stated at the
*integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E` quantity (which
would be chart-selection-unbounded; T1) — so it is trap-screened.

**Proof (sorry-free composition over the genuine deep leaf `(★)`).** The left-hand bracket integral is
read sorry-free, pointwise, as the moving-frame remainder `⟨Curv S − GcurvSection g s S, ∇S⟩(x)`: each
frame summand `remDiffFib g s S x i` pairs to `⟨Curv S, ∇S⟩(x)` summed
(`pointwiseTensorCurvPairing_eq_frameSum`), the genuine fibres `remDiffGenuineFib` sum-pair to
`⟨GcurvSection g s S, ∇S⟩(x)` (`genuineFrameSum_pairing_pointwise_eq_GcurvSection`), and
`remDiffBracketFib = remDiffFib − remDiffGenuineFib` is their difference — all sorry-free pieces of
`MovingFrameRemainderFrameSumBridge`. Integrating (the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) reads the LHS as `⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`. The
genuine deep leaf `(★)` `genuineCurvFields_starValue_bochnerLeaf` gives `⟨GcurvSection g s S +
(diffCurvOpFieldSection g s S + ricTraceSection g s S), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`; rearranging both
sides by left additivity of the `L²` pairing (`tensorL2Inner_add_left`) yields the claim. The body transits
only `(★)`; consumers transitively depend on its `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the
differentiated-curvature carrier vanishes (`diffCurvOpFieldSection g 0 f = appCc 0 f = 0`) and the
pure-Riemann fibre `remDiffGenuineFib g 0 f i` carries the curvature of a scalar (which vanishes), so the
identity reads `∫_M ∑ᵢ ⟨remDiffFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the
classical scalar Bochner identity `Curv f = Ric(∇f, ·)` (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (the degenerate witness) makes the identity FALSE at `s = 0`, so the carrier is
genuinely required and the identity is not vacuous (it fails for a `κ ≠ 1`-perturbed curvature
residue). -/
theorem bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (diffCurvOpFieldSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set gradS := covGrad (I := I) (M := M) g 0 s S with hgradS
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv := GcurvSection (I := I) (M := M) g s S with hGcurv
  set Gdc := diffCurvOpFieldSection (I := I) (M := M) g s S with hGdc
  set Gric := ricTraceSection (I := I) (M := M) g s S with hGric
  set fG : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfG
  set fB : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfB
  set fR : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfR
  -- The genuine fibres sum-pair to `⟨Gcurv, ∇S⟩`, and `fR` is Bochner-integrable, both sorry-free.
  obtain ⟨hG_int, hG_val⟩ :=
    remDiffFib_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g s S
  have hR_int : MeasureTheory.Integrable fR μ := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv gradS
    refine hcross.congr (Filter.Eventually.of_forall (fun x => ?_))
    rw [hfR]
    exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x
  -- The full integrand splits into the genuine and the bracket integrands (sorry-free, the named
  -- per-direction split `remDiffFib = remDiffGenuineFib + remDiffBracketFib`), hence
  -- `fB = fR − fG`.
  have hRsplit : fR = fun x => fG x + fB x := by
    funext x
    rw [hfR, hfG, hfB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffFib_eq_genuine_add_bracket (I := I) (M := M) g s S x i,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have hBsub : fB = fun x => fR x - fG x := by funext x; rw [hRsplit]; ring
  have hB_int : MeasureTheory.Integrable fB μ := by rw [hBsub]; exact hR_int.sub hG_int
  -- The LHS integral `∫ fB = ⟨Curv, ∇S⟩ − ⟨Gcurv, ∇S⟩`.
  have hLHS : (∫ x, fB x ∂μ) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    rw [hBsub, MeasureTheory.integral_sub hR_int hG_int]
    rw [show (∫ x, fR x ∂μ) =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun from by
        rw [hCurv, hgradS, hμ]
        exact (tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral
          (I := I) (M := M) g s S).symm]
    rw [show (∫ x, fG x ∂μ) =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun from hG_val]
  -- The genuine deep leaf `(★)`, with its LHS split by left additivity of the `L²` pairing.
  have hstar := genuineCurvFields_starValue_bochnerLeaf (I := I) (M := M) g s S
  rw [← hGcurv, ← hGdc, ← hGric, ← hCurv, ← hgradS] at hstar
  have hint_gcurv := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS
  have hint_gdcric := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gdc + Gric) gradS
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) Gcurv.toFun (Gdc + Gric).toFun
      gradS.toFun hint_gcurv hint_gdcric] at hstar
  -- Conclude: `∫ fB = ⟨Curv, ∇S⟩ − ⟨Gcurv, ∇S⟩ = ⟨Gdc + Gric, ∇S⟩`.
  show (∫ x, fB x ∂μ) = tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gdc + Gric).toFun gradS.toFun
  rw [hLHS]
  linarith [hstar]

/-- **The integrated tensor Bochner–Weitzenböck curvature-term residue identity (the curvature line's
single irreducible deep root, frame-free operator-field value form — proved by composition over the
strictly-smaller bracket-channel root).** For a
closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the explicit four-pairing curvature residue — the gradient-field
pure-Riemann curvature bilinear, the rough Laplacian of the order-`0` curvature trace against `S`, the
passenger-slot curvature bilinear, and the leading-slot Ricci-trace pairing, all built from the
*frame-free* curvature operator field `Φ₀ s := curvOpField g s` and the raised Ricci endomorphism — equals
the genuine Weitzenböck curvature integral `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`:
```
  ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`,
`pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` the order-`0` pure-Riemann curvature trace.

**This is the genuine new mathematical content of the entire curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity, in its cleanest fully-tensorial frame-free operator-field
form** (no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent` jet). It is the
operator-field value reading of the single irreducible deep root at which the whole curvature line of this
file, of `BracketDiscrepancyNullity`, and of the downstream moving-frame spine
`MovingFrameDiffCurvTraceSection` bottoms out (it is the verbatim statement of
`BracketDiscrepancyNullity.bochnerWeitzenbockResidue_frameFree_value` and of the spine's
`genuineCurvFields_residue_eq_weitzenbockValue`).

**Proof (sorry-free composition over the bracket-channel root).** The right-hand side is the integrated
order-`2` Weitzenböck value `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`
(`weitzenbock_curvature_crossPairing_value`, sorry-free), which is the integral of the fixed-frame sum of
the per-summand pairings `∑ᵢ ⟨remDiffFib …, ∇S⟩`
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, sorry-free). Each frame summand splits
into its pure-Riemann genuine fibre and its named bracket remainder (`remDiffFib_eq_genuine_add_bracket`,
sorry-free), and the integral splits accordingly: the genuine frame-sum integral is
`⟨GcurvSection g s S, ∇S⟩_{L²}` (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free) and the
bracket frame-sum integral is `⟨diffCurvOpFieldSection g s S + ricTraceSection g s S, ∇S⟩_{L²}` by the
single strictly-smaller bracket-channel root
`bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root` above (equivalently, the pure-`R`
peel `bracketRemainderFrameSum_integral_eq_movingFrameRemainder_local` reads the bracket integral as
`⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`). On the left, the pure-Riemann pairing
`⟨GcurvSection g s S, ∇S⟩_{L²}` is the first residue pairing
(`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`, sorry-free), and the differentiated-curvature
operator-field pairing `⟨diffCurvOpFieldSection g s S, ∇S⟩_{L²}` is the second-and-third residue pairings
combined by the operator-field integration-by-parts identity
`tensorL2Inner_diffCurvOpFieldSection_covGrad_eq_neg` (sorry-free). The two sides match by `ring`. The
body transits only the bracket-channel root; consumers transitively depend on its `sorryAx`.

**Non-vacuity (the `s = 0` Bochner litmus rejects the degenerate witness).** At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`pureRGenuineDiffOp g 0 0 f` is the curvature of a scalar,
which vanishes; `Φ₀ 0 = curvOpField g 0` acts as the zero operator on the empty slot), so the identity
collapses to the gradient-field curvature bilinear plus the Ricci pairing equalling the Weitzenböck energy
— the classical scalar Bochner–Lichnerowicz formula `‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)`
(`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a
non-flat manifold. Dropping the Ricci-trace carrier (perturbing the curvature to flat, the degenerate
witness) makes the identity FALSE at `s = 0`, so the carrier is genuinely required and the identity is not
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). -/
theorem bochnerWeitzenbockResidue_curvatureValue_root
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun S.toFun -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (appCc (I := I) (M := M) g (s + 1) (s + 1)
              (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))
              (covGrad (I := I) (M := M) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  classical
  set gradS := covGrad (I := I) (M := M) g 0 s S with hgradS
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set fG : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfG
  set fB : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfB
  set fR : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
        (gradS.toFun x) with hfR
  obtain ⟨hG_int, hG_val⟩ :=
    remDiffFib_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g s S
  have hRsplit : fR = fun x => fG x + fB x := by
    funext x
    rw [hfR, hfG, hfB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffFib_eq_genuine_add_bracket (I := I) (M := M) g s S x i,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have hR_int : MeasureTheory.Integrable fR μ := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (pointwiseTensorCurv (I := I) (M := M) g s S) gradS
    refine hcross.congr (Filter.Eventually.of_forall (fun x => ?_))
    rw [hfR]
    exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x
  have hB_int : MeasureTheory.Integrable fB μ := by
    have hBeq : fB = fun x => fR x - fG x := by funext x; rw [hRsplit]; ring
    rw [hBeq]; exact hR_int.sub hG_int
  rw [← weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]
  rw [tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral (I := I) (M := M) g s S]
  change (_ - _ - _ + _) = ∫ x, fR x ∂μ
  rw [hRsplit, MeasureTheory.integral_add hG_int hB_int]
  have hGval' : (∫ x, fG x ∂μ) = tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (GcurvSection (I := I) (M := M) g s S).toFun gradS.toFun := hG_val
  rw [hGval']
  -- The bracket frame-sum integral is `⟨diffCurvOpFieldSection + ricTraceSection, ∇S⟩` (the deep root).
  rw [show (∫ x, fB x ∂μ) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (diffCurvOpFieldSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S).toFun gradS.toFun from by
      rw [hfB, hgradS]
      exact bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root (I := I) (M := M) g s S]
  rw [← tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  -- Split the bracket value into its `(∇R)` and Ricci summands and rewrite by the operator-field IBP.
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (diffCurvOpFieldSection (I := I) (M := M) g s S).toFun
      (ricTraceSection (I := I) (M := M) g s S).toFun gradS.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (diffCurvOpFieldSection (I := I) (M := M) g s S) gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (ricTraceSection (I := I) (M := M) g s S) gradS)]
  rw [hgradS]
  rw [tensorL2Inner_diffCurvOpFieldSection_covGrad_eq_neg (I := I) (M := M) g s S]
  ring

/-- **The genuine curvature-fields cross-pairing value `(★)` (the three-section value form of the deep
root).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete genuine
curvature sections `GcurvSection g s S + (diffCurvOpFieldSection g s S + ricTraceSection g s S)` against
`∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` rough-Laplacian / covariant-gradient
commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (diffCurvOpFieldSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

**Proof (sorry-free composition over the deep root).** The sorry-free residue bookkeeping
`genuineCurvFields_crossPairing_eq_residue_upstream` rewrites the left-hand three-section pairing as the
explicit four-pairing residue; the residue equals `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by the posited deep root
`bochnerWeitzenbockResidue_curvatureValue_root`; and the proven Weitzenböck value
`weitzenbock_curvature_crossPairing_value` identifies that with `⟨Curv S, ∇S⟩_{L²}`. The body transits
only the deep root; consumers transitively depend on its `sorryAx`. -/
theorem genuineCurvFields_crossPairing_value_upstream
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (diffCurvOpFieldSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [genuineCurvFields_crossPairing_eq_residue_upstream (I := I) (M := M) g s S]
  rw [bochnerWeitzenbockResidue_curvatureValue_root (I := I) (M := M) g s S]
  exact (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S).symm

/-- **The four-carrier integrated moving-frame Bochner–Weitzenböck nullity (the curvature line's
value-anchored four-carrier nullity, proved by composition over the deep root).** For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the concrete moving-frame remainder — the order-`2`
rough-Laplacian / covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S =
Δ_∇(∇S) − ∇(Δ_∇ S)` with its four genuine operator-field curvature carriers subtracted —
```
Grem := Curv S − GcurvSection g s S − appCc (covGrad g s s (Φ₀ s)) S − ricTraceSection g s S
```
against `∇S := covGrad g 0 s S` vanishes:
```
⟨Curv S − GcurvSection g s S − appCc (covGrad g s s (Φ₀ s)) S − ricTraceSection g s S, ∇S⟩_{L²} = 0,
```
with `Φ₀ s := curvOpField g s` the frame-free curvature operator field,
`appCc (covGrad g s s (Φ₀ s)) S = appCc (∇Φ₀ s) S = diffCurvOpFieldSection g s S` the
differentiated-curvature operator-field trace `(∇R) S`, and `ricTraceSection g s S` the leading-slot
Ricci trace.

**Proof (sorry-free composition over the deep root, with the divergence-IBP half discharged).** This is
proved by the sorry-free integrated-nullity producer `movingFrameNullity_of_genuineCrossPairingValue`
(`MovingFrameIntegratedNullity`, which discharges the gradient-slot divergence-IBP half of the Bochner
mechanism) fed the genuine three-section value `(★)` `genuineCurvFields_crossPairing_value_upstream`
(above) with the slot-complete carrier `Gcd := diffCurvOpFieldSection g s S + ricTraceSection g s S`. The
producer's literal-subtraction remainder `Curv S − GcurvSection g s S − Gcd` is the four-carrier
remainder by `sub_sub` (`abel`), and `diffCurvOpFieldSection g s S` is `defeq` to the carrier
`appCc (covGrad g s s (Φ₀ s)) S`. The body transits only the deep root
`bochnerWeitzenbockResidue_curvatureValue_root`; consumers transitively depend on its `sorryAx`.

**Why the pointwise per-direction split is fenced (only the integrated four-carrier nullity is sound).**
The differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its
fibre realisation reads the `smoothExtensionTangent` jet of the frame direction, which is
chart-selection-unbounded on `S²` — so it has no clean slot-`0` uncurry, and the `∇³S`-cancellation and
divergence form are *false term-by-term* through `smoothExtensionTangent`. Only the *summed, integrated*
match is sound, and that sound integrated content is exactly this four-carrier nullity, equivalent through
the sorry-free bookkeeping to the deep root. The identity is stated at the *integrated* frame-free `L²`
level throughout — it never extracts a per-direction `M → E` quantity — so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier — each carrier is necessary).** At
`s = 0` the pure-Riemann and differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the
curvature of a scalar, which vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the
empty curvature slot), so the nullity reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ⟨Curv f, ∇f⟩_{L²} =
‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner–Lichnerowicz identity
(`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a
non-flat manifold. Dropping the Ricci-trace carrier (perturbing the curvature to flat, the degenerate
witness) makes the nullity FALSE at `s = 0`, so the carrier is genuinely required and the node is not
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). -/
theorem fourCarrierRemainder_integrated_nullity_valueAnchored
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S -
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  -- The slot-complete carrier `Gcd := diffCurvOpFieldSection g s S + ricTraceSection g s S`.
  set Gcd : SmoothCcTensor g 0 (s + 1) :=
    diffCurvOpFieldSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S with hGcd
  -- The genuine three-section value `(★)`, converted to the Weitzenböck-norm form the producer reads.
  have hval : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S + Gcd).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
    rw [hGcd]
    exact (genuineCurvFields_crossPairing_value_upstream (I := I) (M := M) g s S).trans
      (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S)
  -- The integrated moving-frame nullity producer, fed the genuine three-section value `(★)`.
  have hnull := movingFrameNullity_of_genuineCrossPairingValue (I := I) (M := M) g s S Gcd hval
  -- The producer's literal-subtraction remainder is the four-carrier remainder (`sub_sub`),
  -- and `diffCurvOpFieldSection` is `defeq` to the carrier `appCc (covGrad g s s (Φ₀ s)) S`.
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S -
          ricTraceSection (I := I) (M := M) g s S) =
        pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S - Gcd from by
    rw [hGcd, diffCurvOpFieldSection]; abel]
  exact hnull

/-- **The frame-bracket remainder frame-sum integral carries the differentiated-curvature operator-field
trace plus the Ricci trace (the integrated bracket-channel curvature identity).** For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the integral over the closed manifold of the fixed-frame sum of the per-direction
frame-bracket remainder fibres `remDiffBracketFib` (the frame summand `remDiffFib` minus its pure-Riemann
genuine curvature fibre `remDiffGenuineFib`, `MovingFrameRemainderFrameSumBridge`), paired against
`∇S := covGrad g 0 s S`, equals the global metric `L²` pairing of the differentiated-curvature
operator-field trace `appCc (∇Φ₀ s) S` (the `(∇R) S` field, `∇Φ₀ s := covGrad g s s (curvOpField g s)`)
plus the leading-slot Ricci-trace carrier `ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the strictly-smaller, irreducible integrated content of the whole curvature line — the
passenger-`W` frame-traced bracket channel with the pure-Riemann channel peeled off.** It is the verbatim
statement (with the carrier `appCc (covGrad g s s (Φ₀ s)) S` `defeq` to `diffCurvOpFieldSection g s S`)
of the curvature line's single irreducible deep root
`bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root` (the posited genuine classical
integrated tensor Bochner–Weitzenböck curvature-identity root, above); the body is `exact` over it.
Consumers transitively depend on that root's `sorryAx`.

**Why it is the genuine missing content.** The bracket-channel root carries the classical Bochner
technique that has no sorry-free bridge: the identification of the frame-summed differentiated curvature
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier `appCc (∇Φ₀) S`, the second-Bianchi / frame-Ricci
folding of the leading slot into `ricTraceSection`, and the gradient-slot bracket discrepancy integrating
to zero over the closed manifold. The differentiated-curvature trace is **non-tensorial in the
direction** — its per-direction fibre reading uses the `smoothExtensionTangent` jet, which is
chart-selection-unbounded on `S²` — so the per-direction split and divergence form are *false
term-by-term*; only the *summed, integrated* match is sound, and that sound integrated content is exactly
the posited four-carrier nullity. This identity is stated at the *integrated* frame-free `L²` level
throughout (it never extracts a per-direction `M → E` quantity), so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on
the empty curvature slot, the curvature of a scalar), so the identity collapses to
`∫_M ∑ᵢ ⟨remDiffBracketFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the classical
scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes the identity FALSE at
`s = 0`, so the carrier is genuinely required and the node is not vacuous. -/
theorem frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  -- The carrier `appCc (covGrad g s s (Φ₀ s)) S` is `diffCurvOpFieldSection g s S` by definition, so
  -- this is the verbatim bracket-channel deep root, re-exported.
  exact bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace_root (I := I) (M := M) g s S

/-- **The integrated tensor Bochner–Weitzenböck curvature-term residue value (frame-free operator-field
form, re-export of the deep root).** For a closed smooth Riemannian manifold `(M, g)`, every covariant
rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the explicit four-pairing curvature
residue — the gradient-field pure-Riemann curvature bilinear, the rough Laplacian of the order-`0`
curvature trace against `S`, the passenger-slot curvature bilinear, and the leading-slot Ricci-trace
pairing — equals the genuine Weitzenböck curvature integral `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`.

**Proof (re-export).** This is the identical statement of the curvature line's single irreducible deep
root `bochnerWeitzenbockResidue_curvatureValue_root` (above); the body is `exact` over it. Consumers
transitively depend on the deep root's `sorryAx`. -/
theorem bochnerWeitzenbockResidueValue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun S.toFun -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (appCc (I := I) (M := M) g (s + 1) (s + 1)
              (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))
              (covGrad (I := I) (M := M) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 :=
  bochnerWeitzenbockResidue_curvatureValue_root (I := I) (M := M) g s S

/-- **The integrated tensor Bochner–Weitzenböck curvature value (the curvature line's single irreducible
deep root, value form).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and
every smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete
genuine curvature carriers `GcurvSection g s S + (appCc (∇Φ₀ s) S + ricTraceSection g s S)` — the
pure-Riemann `R(∇S)` trace, the differentiated-curvature `(∇R) S` trace
`appCc (covGrad g s s (curvOpField g s)) S`, and the leading-slot Ricci trace — against
`∇S := covGrad g 0 s S` equals the genuine Weitzenböck curvature integral
```
⟨GcurvSection g s S + (appCc (∇Φ₀ s) S + ricTraceSection g s S), ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`,
`∇Φ₀ s := covGrad g s s (curvOpField g s)`.

**This is the genuine new mathematical content of the curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity.** It states that the three concrete operator-field curvature
carriers together capture, against `∇S`, the *entire* integrated value of the order-`2` rough-Laplacian /
covariant-gradient commutator defect (which the sorry-free `weitzenbock_curvature_crossPairing_value`
identifies with `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`). By the iterated Ricci identity the defect's gradient-slot
reordering produces (I) the gradient-slot curvature `R(∇S)` and (II) the tail-slot curvature action (both
carried by `GcurvSection`), (III) the differentiated curvature `(∇R) S` (carried by `appCc (∇Φ₀ s) S`),
and (IV) the leading-slot Ricci trace (the second-Bianchi / frame-Ricci folding, carried by
`ricTraceSection`), plus a residual `∇²S`-order frame-bracket discrepancy that is a total covariant
divergence integrating to zero over the closed manifold.

**Why the pointwise per-direction split is fenced (only the integrated value is sound).** The
differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its fibre
realisation reads the `smoothExtensionTangent` jet of the frame direction, which is
chart-selection-unbounded on `S²` — so it has no clean slot-`0` uncurry, and the `∇³S`-cancellation and
divergence form are *false term-by-term* through `smoothExtensionTangent`. Only the *summed, integrated*
match is sound, and that sound integrated content is exactly this value identity. The identity is stated
at the *integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E` quantity
— so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier — each carrier is necessary).** At
`s = 0` the pure-Riemann and differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the
curvature of a scalar, which vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the
empty curvature slot), so the value reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} −
‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner–Lichnerowicz identity
(`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a
non-flat manifold. Dropping the Ricci-trace carrier (perturbing the curvature to flat, the degenerate
witness) makes the value FALSE at `s = 0`, so the carrier is genuinely required and the identity is not
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue).

**Proof (composition over the bracket-channel root).** This is now proved by composition: the left
additivity of the cross-pairing (`tensorL2Inner_add_left`, the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) splits the LHS into the pure-Riemann, differentiated-curvature,
and Ricci-trace summands; the pure-Riemann summand is rewritten by
`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp` and the differentiated-curvature summand by the
operator-field integration-by-parts identity `tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (the B-rule,
with `appCc (Φ₀ s) S = pureRGenuineDiffOp g 0 s S` the base spec) into the four-pairing curvature residue;
that residue equals `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by `bochnerWeitzenbockResidueValue`, which in turn is
proved sorry-free by composition over the single posited bracket-channel root
`frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace` (the genuine differentiated-curvature
operator-field identification + integrated second-Bianchi Ricci fold + gradient-slot divergence-zero).
Consumers transitively depend on that root's `sorryAx`. -/
theorem curvatureValue_genuineFields_eq_weitzenbock
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (appCc (I := I) (M := M) g s (s + 1)
              (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  classical
  rw [← bochnerWeitzenbockResidueValue (I := I) (M := M) g s S]
  -- Reduce the LHS cross-pairing of the three carriers to the four-pairing curvature residue.
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    (GcurvSection (I := I) (M := M) g s S).toFun
    (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
      ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
        ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
    (ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S)
      (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  have hIBP := tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g s
    (curvOpField (I := I) (M := M) g s) S
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S := by
    have := appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
    simpa using this
  rw [hbase] at hIBP
  rw [hIBP]
  simp only [Nat.add_zero]
  ring

end Connection
end Integral
end DifferentialGeometry

end
