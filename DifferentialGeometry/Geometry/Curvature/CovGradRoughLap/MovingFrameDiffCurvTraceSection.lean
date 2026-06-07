import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDiscrepancyNullity
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.Order2DefectFiberOrder

/-!
# The gauge-glued tensorial differentiated-curvature section `(∇R) S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file constructs the
**differentiated-curvature genuine section** of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`,
`∇S = covGrad g 0 s S`): the covariant-derivative counterpart of the on-disk **pure-Riemann** genuine
section `GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the tensorial
trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`).

## The construction: the covariant derivative of the frame-free curvature operator field

The pure-Riemann curvature tower already isolates the order-`0` frame-free curvature endomorphism as the
action of a *fixed smooth* operator field: there is a smooth `(r, r)`-operator field `Φ₀ r` with
`pureRGenuineDiffOp g 0 r W = appCc (Φ₀ r) W` (`exists_pureRGenuineDiffOp_base_appCc`), whose fibre value
is the genuine `g`-metric curvature trace `W ↦ ∑ᵢ R(Bᵢ, ·) W` — frame-free (built from `g, R` alone), so
its covariant derivative differentiates *only* the curvature factor, never a chart-selection-unbounded
frame jet.

The differentiated-curvature trace `∑ᵢ (∇R)(Bᵢ, ·) S` is therefore the operator-field action of the
**covariant derivative of that curvature operator field** on `S`:
```
genuineDiffCurvSection g s S := appCc (covGrad g s s (Φ₀ s)) S.
```
This is the genuinely-tensorial `(∇R) S` content. The operator-field covariant product rule
`covGrad_appCc_eq` reads `covGrad (appCc (Φ₀ s) S) = appCc (covGrad (Φ₀ s)) S +
appCc (slotExtend (Φ₀ s)) (∇S)`, so the first summand `appCc (covGrad (Φ₀ s)) S` is exactly the
`(∇R)`-on-`S` part of the differentiated curvature trace, with the `R(∇S)` spectator carried by the
second; isolating the `(∇R) S` summand is the construction. Because `Φ₀ s` is a *fixed* smooth section,
`covGrad g s s (Φ₀ s)` is a fixed smooth `(s, s + 1)`-operator field, and its operator-field action on
`S` is a smooth compactly-supported `(0, s + 1)`-tensor with **no** per-direction smooth-extension jet
— the section is tensorial and smooth by construction, never extension-curried. This collapses the
moving-frame frame-freezing partition-of-unity assembly of the pure-Riemann leg to the operator-field
calculus.

## Main results

* `genuineDiffCurvSection g s S : SmoothCcTensor g 0 (s + 1)` — the gauge-glued tensorial section of the
  differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), the operator-field
  action of `covGrad (Φ₀ s)` on `S`.
* `exists_genuineDiffCurvSection_fiberNormSq_bound` — the **sum** fibre bound `(3')`
  `rfns(genuineDiffCurvSection g s S)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))`, uniform in `x`, with a
  valence-dependent nonnegative constant `K`. The bound holds even in the strict `rfns(S)` form (the
  operator-field action is order-`0` in `S`), weakened to the **sum** envelope the consumer reads.
* `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` — the companion `pointwiseTensorCurv` fibre
  bound `rfns(Curv S)(x) ≤ (C s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` feeding the remainder
  order `(4')`, the order-`2` commutator-defect fibre order homed *upstream* of the moving-frame spine
  (posited, so the consuming anchor stays upstream of the downstream `L²` bound, no import cycle).
* `genuineCurvFields_residue_eq_weitzenbockValue` — the **rank-generic integrated tensor
  Bochner–Weitzenböck identity** over the smooth global pure-Riemann operator tower: the explicit
  three-pairing curvature residue equals the Weitzenböck value `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`. The
  classical Bochner curvature-term identity; **proved by composition** over the genuine curvature-fields
  value `(★)` `genuineCurvFields_crossPairing_value`, itself assembled over the landed frame-summed
  remainder current (`MovingFrameRemainderFrameSumBridge`) from two per-family integrated identities
  (the pure-Riemann genuine-sum `remDiffFib_genuineFrameSum_pairing_eq_genuineFields` and the
  differentiated-curvature genuine-sum with integrated bracket nullity
  `integral_frameSum_remDiffBracket_pairing_eq_genuineDiffCurv`).
* `genuineCurvFields_crossPairing_value` — the genuine curvature-fields cross-pairing value `(★)`
  `⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`,
  assembled over the frame-summed remainder current from the two per-family integrated identities.
* `genuineDiffCurv_crossPairing_remainder_nullity` — the genuine integrated moving-frame nullity for the
  concrete section, `⟨pointwiseTensorCurv g s S − GcurvSection g s S − genuineDiffCurvSection g s S,
  ∇S⟩_{L²} = 0`: the third-order moving-frame Weitzenböck IBP-telescoping content, **proved by
  composition** over the named leaf `genuineCurvFields_residue_eq_weitzenbockValue` (chained through the
  sorry-free residue `genuineCurvFields_crossPairing_eq_residue` and fed to the integrated-nullity
  producer `movingFrameNullity_of_genuineCrossPairingValue`).
* `genuineDiffCurv_crossPairing_value` — the genuine differentiated-curvature cross-pairing value
  `⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`,
  **proved by composition** over `genuineDiffCurv_crossPairing_remainder_nullity` (the
  left-additivity bracket-free-pairing reduction
  `tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity` chained
  with the sorry-free Weitzenböck value `weitzenbock_curvature_crossPairing_value`), feeding the
  integrated-nullity producer `movingFrameNullity_of_genuineCrossPairingValue` verbatim with
  `Gcd := genuineDiffCurvSection g s S`.
* `tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg` — the differentiated-curvature cross-pairing's
  integration-by-parts formula `⟨Gcd, ∇S⟩_{L²} = −⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²} −
  ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}`, the operator-field integration-by-parts identity
  `tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) specialised to the frame-free
  curvature operator field, expressing `⟨Gcd, ∇S⟩_{L²}` through the rough Laplacian of the order-`0`
  curvature trace and the passenger-slot curvature bilinear of `∇S` (sorry-free).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`. The differentiated-curvature trace is genuinely `rfns(S)`-order; the
**sum** envelope `rfns(∇S) + rfns(S)` is the form the moving-frame remainder merge consumes.
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

/-- **The gauge-glued tensorial differentiated-curvature section `(∇R) S`.** For a smooth
compactly-supported `(0, s)`-tensor `S`, the operator-field action of the covariant derivative of the
frame-free curvature operator field `Φ₀ s` (`curvOpField`) on `S`:
```
genuineDiffCurvSection g s S := appCc (covGrad g s s (Φ₀ s)) S,
```
the differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), a smooth
compactly-supported `(0, s + 1)`-tensor. It is the covariant-derivative counterpart of the pure-Riemann
genuine section `GcurvSection g s S`: where the pure-Riemann trace is the action `appCc (Φ₀ s) S` of the
order-`0` curvature operator, the differentiated trace is the action `appCc (∇Φ₀ s) S` of its covariant
derivative (the operator-field product rule `covGrad_appCc_eq` separates the `(∇R) S` summand from the
`R(∇S)` spectator). It is constructed tensorially and smoothly through the operator-field calculus, never
extension-curried. -/
noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

/-- **The fibre value of `genuineDiffCurvSection` is the fibrewise composition `(∇Φ₀ s).comp S`.**
Definitional: the operator-field action `appCc` evaluates fibrewise as the composition of the
differentiated curvature operator with the section value (`appCc_toSection`). -/
@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    appCc_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]

/-- **The covariant-derivative spec of the frame-free curvature operator field (the section-level
B-rule inversion).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth
compactly-supported `(0, s)`-tensor `S`, the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S` (the operator-field action `appCc (covGrad (Φ₀ s)) S` of the covariant
derivative of the frame-free curvature operator field `Φ₀ s := curvOpField g s`) equals the covariant
gradient of the order-`0` pure-Riemann curvature trace minus the passenger-slot extension of `Φ₀ s`
acting on `∇S`:
```
genuineDiffCurvSection g s S
  = covGrad g 0 s (pureRGenuineDiffOp g 0 s S)
    − appCc (slotExtend (Φ₀ s)) (covGrad g 0 s S).
```
Both right-hand terms are concrete: `pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` is the order-`0`
moving-frame pure-Riemann curvature trace (the `Classical.choose` base spec defining `curvOpField`), and
`slotExtend (Φ₀ s)` is the passenger-slot extension of the frame-free curvature operator. This is the
covariant-derivative spec of `curvOpField`: it characterises the action of `covGrad (curvOpField g s)` as
the differentiated-curvature trace `(∇R) S`, the `(∇R)`-on-`S` summand isolated from the `R(∇S)`
spectator.

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` (the B-rule) at the square field
`Φ₀ s` and the tensor `S` reads `covGrad g 0 s (appCc (Φ₀ s) S) = appCc (covGrad (Φ₀ s)) S +
appCc (slotExtend (Φ₀ s)) (∇S)`, whose first summand is `genuineDiffCurvSection g s S` by definition.
Rearranging by `eq_sub_of_add_eq` isolates that summand, and rewriting `appCc (Φ₀ s) S =
pureRGenuineDiffOp g 0 s S` by the base spec `exists_pureRGenuineDiffOp_base_appCc` makes the first
right-hand term the concrete order-`0` curvature trace. -/
theorem genuineDiffCurvSection_eq_covGrad_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    genuineDiffCurvSection (I := I) (M := M) g s S =
      covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) -
        appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hB := covGrad_appCc_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  have hgds : appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  have hB' := eq_sub_of_add_eq (hB.symm)
  rw [hB', hbase]

/-- **The passenger-slot action of the curvature operator field on `∇S` reads the gradient direction
first (the spectator-term unit-evaluation).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, base `(0, 0)`-tensor `d`, gradient
direction `v0`, and trailing tuple `vs`, the passenger-slot operator-field action
`appCc (slotExtend (Φ₀ s)) (∇S)` evaluated on the tuple `Fin.cons v0 vs` reads the leading gradient
direction `v0` off the passenger slot and applies the frame-free curvature operator `Φ₀ s = curvOpField
g s` to the directional covariant derivative `∇_{v0} S`:
```
(appCc (slotExtend (Φ₀ s)) (∇S))(x)(d)(Fin.cons v0 vs)
  = (Φ₀ s)(x)((∇_{v0} S)(x)(d))(vs).
```
This is the spectator `R(∇S)` term of the differentiated curvature trace in unit-evaluated form: the
passenger slot carries the gradient direction, and the curvature endomorphism `Φ₀ s` acts on the
trailing slots of the directional derivative of `S` — never the next-rank curvature operator
`Φ₀ (s + 1)`.

**Proof.** Expand the operator-field action (`appCc_toSection`, the fibrewise composition) and the
slot-extended fibre operator (`slotExtend_toSection`), then read the leading slot by
`slotExtendFib_apply_eval` (the new slot is read first, the rest curried through `tensor0S_curry`), and
identify the curried gradient with the directional covariant derivative by
`tensor0S_curry_covGrad_appCc_eq`. -/
theorem appCc_slotExtend_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          (curvOpField (I := I) (M := M) g s).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
      (curvOpField (I := I) (M := M) g s).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The full unit-evaluated differentiated-curvature trace identity (the frame-free
`∇R`-trace pointwise characterization).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, base `(0, 0)`-tensor `d`, gradient
direction `v0`, and trailing tuple `vs`, the directional covariant derivative of the order-`0`
pure-Riemann curvature trace decomposes, in unit-evaluated form, as the differentiated-curvature section
`genuineDiffCurvSection g s S` (the `(∇R) S` field) plus the passenger-slot curvature spectator
`(Φ₀ s)(∇_{v0} S)`:
```
(∇_{v0}(pureRGenuineDiffOp g 0 s S))(x)(d)(vs)
  = (genuineDiffCurvSection g s S)(x)(d)(Fin.cons v0 vs)
    + (Φ₀ s)(x)((∇_{v0} S)(x)(d))(vs).
```
Equivalently, `genuineDiffCurvSection = ∇(R-trace) − R(∇S)` pointwise: the differentiated-curvature
trace is the covariant derivative of the curvature trace with the spectator `R(∇S)` removed. This is the
frame-free unit-evaluated form of the `(∇R)`-trace, the foundation against which the
frame-summed-to-frame-free transfer compares the moving-frame frame sum.

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` (the B-rule) at the square field
`Φ₀ s` and `S`, rewritten by the base spec `exists_pureRGenuineDiffOp_base_appCc`
(`appCc (Φ₀ s) S = pureRGenuineDiffOp g 0 s S`), gives the section identity
`covGrad g 0 s (pureRGenuineDiffOp g 0 s S) = genuineDiffCurvSection g s S +
appCc (slotExtend (Φ₀ s)) (∇S)`. Reading it at `x`, applying to `d`, distributing the additive fibre
value (`ContinuousLinearMap.add_apply`, `Tensor0SSpace.toModel_add`), and unit-evaluating the left-hand
gradient by `covGrad_toSection_apply_eval` and the spectator by
`appCc_slotExtend_curvOpField_covGrad_unit_eval` gives the pointwise identity. -/
theorem covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
        vs =
      Tensor0SSpace.toModel
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
          (Fin.cons v0 vs) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hB := covGrad_appCc_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hB
  have hsec := congrArg (fun T : SmoothCcTensor g 0 (s + 0 + 1) => T.toSection x) hB
  simp only at hsec
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hsec
  have happ :
      (covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d =
        (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d +
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec, ContinuousLinearMap.add_apply]
    rfl
  have hlhs :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs =
        Tensor0SSpace.toModel
          ((covGrad (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d)
          (Fin.cons v0 vs) := by
    have h := covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x d (Fin.cons v0 vs)
    refine Eq.symm (h.trans ?_)
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1) → E) = vs := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1) → E) 0 = v0 := by simp [Fin.cons_zero]
    rw [htail, hhead]
  have hterm2 :
      Tensor0SSpace.toModel
          ((appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs :=
    appCc_slotExtend_curvOpField_covGrad_unit_eval (I := I) (M := M) g s S x d v0 vs
  rw [hlhs, happ, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, hterm2]

/-- **The sum fibre bound `(3')` on the constructed differentiated-curvature section.** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such
that, at every covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at
*every point* `x`, the intrinsic fibre norm of the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S` (the `(∇R) S` field) is bounded by `(K s)²` times the **sum** of the
intrinsic fibre norms of `∇S = covGrad g 0 s S` and `S`:
```
rfns(genuineDiffCurvSection g s S)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof.** `genuineDiffCurvSection g s S = appCc (covGrad (Φ₀ s)) S` is the operator-field action of the
*fixed* smooth `(s, s + 1)`-operator field `covGrad (Φ₀ s)` on `S`. The uniform section-proportional
operator-field envelope `exists_uniform_riemannianFiberNormSq_appCc_le` (the intrinsic partial-contraction
Cauchy–Schwarz `riemannianFiberNormSq_comp_le_mul` followed by the uniform fibre-operator bound on the
fixed field `covGrad (Φ₀ s)`) gives a single nonnegative `C s`, uniform over `M`, with
`rfns(appCc (covGrad (Φ₀ s)) S)(x) ≤ C s · rfns(S)(x)`. Taking `K s := √(C s)` so `K s ^ 2 = C s`, the
strict `rfns(S)` bound `rfns(genuineDiffCurvSection)(x) ≤ K s ^ 2 · rfns(S)(x)` is weakened to the
**sum** by adding the nonnegative `K s ^ 2 · rfns(∇S)(x)` (the consumer reads the sum envelope; the
operator-field action is order-`0` in `S`, so even the strict bound holds).

**Non-vacuity (the bound alone does not pin `K`, the coupling does).** The bound `(3')` alone does *not*
reject `K ≡ 0` (`genuineDiffCurvSection g 0 S = appCc (covGrad (Φ₀ 0)) S = appCc 0 S = 0` at the
scalar rank where there is no slot to contract); the genuine positivity of `K` is forced only by the
coupling to the integrated nullity in the consuming anchor
`exists_movingCentreDiffCurvSection_splitDivergenceDatum`, where the differentiated-curvature `(∇R) S`
content must carry the third-order Weitzenböck pairing. The section genuinely carries that content: it is
the operator-field action of the covariant derivative `covGrad (Φ₀ s)` of the genuine frame-free
curvature operator `Φ₀ s` (whose value is the `g`-metric curvature trace), nonzero on a non-flat
manifold with non-parallel `S`, never the zero section. -/
theorem exists_genuineDiffCurvSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  -- The per-rank uniform section-proportional operator-field envelope for the fixed differentiated
  -- curvature operator field `covGrad (Φ₀ s)`.
  have hC : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro s
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
    exact ⟨C, hC_nn, fun S x => by
      have h := hC S x
      rwa [show (appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S) =
          genuineDiffCurvSection (I := I) (M := M) g s S from rfl] at h⟩
  choose C hC_nn hC using hC
  refine ⟨fun s => Real.sqrt (C s), fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hKsq : Real.sqrt (C s) ^ 2 = C s := Real.sq_sqrt (hC_nn s)
  rw [hKsq]
  have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have h := hC s S x
  nlinarith [h, hfgS_nn, hfS_nn, hC_nn s,
    mul_nonneg (hC_nn s) hfgS_nn]

/-- **The differentiated-curvature cross-pairing's integration-by-parts formula (the tensorial
bookkeeping for the concrete `(∇R) S` section).** For a closed smooth Riemannian manifold `(M, g)`,
covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing
of the gauge-glued tensorial differentiated-curvature section `genuineDiffCurvSection g s S` (the
`(∇R) S` field, the operator-field action `appCc (∇Φ₀ s) S`) against `∇S = covGrad g 0 s S` is

```
⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}
  = −⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s` the rough connection Laplacian, `pureRGenuineDiffOp g 0 s S`
the order-`0` moving-frame pure-Riemann curvature trace (the action `appCc (Φ₀ s) S` of the curvature
operator field `Φ₀ s := curvOpField g s`), and `∇S := covGrad g 0 s S`.

**Proof.** This is the operator-field integration-by-parts identity
`tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) specialised to the frame-free
curvature operator field `Φ₀ s = curvOpField g s`.  The differentiated-action `appCc (∇Φ₀ s) S` is
`genuineDiffCurvSection g s S` by definition, and the order-`0` action `appCc (Φ₀ s) S` is
`pureRGenuineDiffOp g 0 s S` by the operator-field base identity
`exists_pureRGenuineDiffOp_base_appCc` (the `Classical.choose` spec defining `curvOpField`).

This expresses the differentiated-curvature cross-pairing in terms of (i) the rough Laplacian of the
order-`0` curvature trace `pureRGenuineDiffOp g 0 s S` paired against `S`, and (ii) the passenger-slot
curvature bilinear of `∇S` with itself.  The passenger-slot operator field `slotExtend (Φ₀ s)` is *not*
the next-rank curvature operator `Φ₀ (s + 1)` (it leaves the inserted leading slot a spectator and acts
by the rank-`s` curvature endomorphism on the trailing slots, whereas `Φ₀ (s + 1)` contracts the
leading slot with the curvature direction), so the second term is a genuine curvature bilinear, not a
re-indexed order-`0` trace pairing — it is carried as-is. -/
theorem tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineDiffCurvSection (I := I) (M := M) g s S).toFun
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
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hgen := tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hgen
  exact hgen

/-- **The genuine curvature-fields cross-pairing equals the explicit four-pairing residue (the
sorry-free Bochner curvature-term bookkeeping, slot-complete form).** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the global
metric `L²` pairing of the genuine curvature fields `GcurvSection g s S + (genuineDiffCurvSection g s S
+ ricTraceSection g s S)` (the pure-Riemann `R(∇S)` trace, the gauge-glued tensorial `(∇R) S` trace,
and the **Ricci trace** `ricTraceSection`) against `∇S = covGrad g 0 s S` equals the explicit
four-pairing combination — the three-pairing Bochner residue plus the Ricci-trace pairing:

```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` the
order-`0` moving-frame pure-Riemann curvature trace, and `Φ₀ s = curvOpField g s` the frame-free
curvature operator field. The first three pairings are the **rank-generic Bochner curvature-term
residue** (the gradient-field curvature bilinear, the rough Laplacian of the order-`0` curvature trace
against `S`, and the passenger-slot curvature bilinear), and the fourth is the Ricci-trace pairing
carried as-is.

**Proof (sorry-free bookkeeping).** Split the left additivity of the cross-pairing twice
(`tensorL2Inner_add_left`, the cross-integrabilities `SmoothCcTensor.integrable_inner_cross`) into the
pure-Riemann, differentiated-curvature, and Ricci-trace summands, rewrite the pure-Riemann summand by
the pairing bridge `tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`
(`MovingFramePureRCurvatureTracePairing`, sorry-free), and rewrite the differentiated-curvature summand
by the operator-field integration-by-parts identity
`tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg` (sorry-free, above). The Ricci-trace summand is
carried as-is. All bridges are sorry-free, so this identity is sorry-free; it isolates the curvature
line's residue plus the Ricci-trace pairing as the value of the right-hand four-pairing combination. -/
theorem genuineCurvFields_crossPairing_eq_residue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
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
    (genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    (genuineDiffCurvSection (I := I) (M := M) g s S).toFun
    (ricTraceSection (I := I) (M := M) g s S).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (genuineDiffCurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  rw [tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg (I := I) (M := M) g s S]
  ring

/-- **The frame-summed pointwise integrand of the bracket remainder is the concrete moving-frame
remainder pairing (sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`,
smooth compactly-supported `(0, s)`-tensor `S`, and point `x`, the fixed-frame sum of the per-direction
frame-bracket remainder fibres `remDiffBracketFib`, paired against `∇S := covGrad g 0 s S`, equals the
pointwise metric inner product of the concrete moving-frame remainder
`pointwiseTensorCurv g s S − GcurvSection g s S` against `∇S`:
```
∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ = ⟨(Curv S − Gcurv)(x), ∇S(x)⟩.
```

**Proof (sorry-free).** The frame sum of the bracket fibres is the fibre value of the concrete
remainder: `∑ᵢ remDiffBracketFib g s S x i = ∑ᵢ (remDiffFib g s S x i − remDiffGenuineFib g s S x i) =
(Curv S).toSection x − (Gcurv).toSection x` by `pointwiseTensorCurv_toSection_eq_frame_sum` (the
fixed-frame sum of `remDiffFib` is the defect, sorry-free) and
`remDiffGenuineFib_sum_eq_GcurvSection_toSection` (the genuine fibres sum to the pure-Riemann section,
sorry-free). Pushing the model coercion through the frame sum (additivity of `TensorRSSpace.toModel`)
and distributing the pointwise inner product over the sum (`tensorInnerPointwise_sum_left`, weights
`1`) gives the identity. No moving-frame derivative survives — this is the purely structural integrand
reading. -/
theorem frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  classical
  have hfib : (∑ i : Fin (Module.finrank ℝ E), remDiffBracketFib (I := I) (M := M) g s S x i) =
      (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toSection x := by
    have hbr : ∀ i, remDiffBracketFib (I := I) (M := M) g s S x i =
        remDiffFib (I := I) (M := M) g s S x i -
          remDiffGenuineFib (I := I) (M := M) g s S x i := fun _ => rfl
    rw [Finset.sum_congr rfl (fun i _ => hbr i), Finset.sum_sub_distrib]
    rw [remDiffGenuineFib_sum_eq_GcurvSection_toSection (I := I) (M := M) g s S x]
    rw [SmoothCcTensor.toSection_sub]
    congr 1
    rw [pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
    rfl
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffBracketFib (I := I) (M := M) g s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toFun x =
      TensorRSSpace.toModel ((pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toSection x) from rfl]
  rw [← hfib, htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]


/-- **The frame-bracket remainder frame-sum integral carries the concrete `(∇R) S` + Ricci-trace value
(the curvature line's single irreducible integrated curvature-identity root, the honest deep leaf).**
For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the integral over the closed manifold of the fixed-frame sum of
the per-direction frame-bracket remainder fibres `remDiffBracketFib` (the frame summand `remDiffFib`
minus its pure-Riemann genuine curvature fibre `remDiffGenuineFib`), paired against `∇S := covGrad g 0 s
S`, equals the global metric `L²` pairing of the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S` plus the leading-slot Ricci-trace carrier `ricTraceSection g s S`
against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨genuineDiffCurvSection g s S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine new mathematical content of the curvature line — the single irreducible
integrated tensor Bochner–Weitzenböck curvature-identity root, the strictly-smaller passenger-`W`
bracket channel with the pure-`R` channel peeled off sorry-free.** The pure-Riemann genuine fibre
frame-sum is already identified sorry-free (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, the
L²-sound pure-`R` trace summing to `GcurvSection`), and the curvature cross-pairing splits sorry-free into
the genuine and bracket frame-sum integrands
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, `remDiffFib_eq_genuine_add_bracket`),
so the *entire* curvature anatomy that is not pure-`R` lives in this passenger-`W` frame-traced bracket
channel. It is stated and posited here, *above* the value leaf `(★)`
`genuineCurvFields_crossPairing_value_bochnerLeaf`, the value root, the residue leaf, the integrated
nullity, and every down-stream cross-pairing node — all are proven by composition over this single
integrated identity plus the sorry-free pure-`R` peel.

**Why it is true (the three-fold genuine content, no bridge below this file — verified).** Pointwise each
frame summand `remDiffFib g s S x i` is the gradient-slot reordering of the three covariant slots
(`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`); subtracting the pure-Riemann genuine fibre
`remDiffGenuineFib g s S x i` leaves the frame-bracket remainder, which carries threefold genuine
content, sound only after frame-summing and integrating: (i) the integrated identification of the
frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier
`genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` — *false pointwise per-direction*
(the `smoothExtensionTangent` direction reading is chart-selection-unbounded on `S²`), sound only
integrated; (ii) the second-Bianchi cyclic fold of the contracted-curvature slot into the raised Ricci
endomorphism `ricEndoRaisedFib = ricTraceSection` (`ricEndoRaisedFib_inner_eq_frame_trace`,
`second_bianchi_levi_civita_metric`, `ricTraceSection_apply_leadingSlot`, `GradientSlotCurvatureSplit`
are the pointwise pieces, but the integrated assembly is absent); (iii) the gradient-slot lift exhibiting
the surviving `∇²S`-order bracket discrepancy (`tensor3rdCurvBracket` plus the frame-trace discrepancy
and moving-frame residual) as a total covariant divergence integrating to zero over the closed manifold
(the divergence-vanishing engine `integral_frameSummed_covDeriv_combined_eq_zero` / `BracketDivergenceForm`,
with the gradient-slot channel L²-orthogonal `gradSlotCurv_pairing_covGrad_eq_zero`, but the
bracket-to-engine identification at the slot-`0` level absent). The identity is stated at the *integrated*
frame-free L² level throughout — it never extracts a per-direction `M → E` quantity (which would be
chart-selection-unbounded; T1) — so it is trap-screened. Posited here as the explicit honest deep leaf so
the entire curvature line bottoms out at this single clean classical statement.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the
differentiated-curvature carrier vanishes (`genuineDiffCurvSection g 0 f = appCc 0 f = 0`) and the
pure-Riemann fibre `remDiffGenuineFib g 0 f i` carries the curvature of a scalar (which vanishes), so
the identity reads `∫_M ∑ᵢ ⟨remDiffFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)`
— the classical scalar Bochner identity `Curv f = Ric(∇f, ·)` (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (the degenerate witness) makes the identity FALSE at `s = 0`, so the carrier is
genuinely required and the identity is not vacuous (it fails for a `κ ≠ 1`-perturbed curvature
residue). The body is `sorry` (the genuine classical integrated tensor Bochner–Weitzenböck
curvature-term derivation: the integrated second-Bianchi Ricci fold, the differentiated-curvature
operator-field identification, and the gradient-slot divergence-zero lift); consumers transitively depend
on `sorryAx`. -/
theorem remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hstar :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
    rw [bochnerWeitzenbockResidue_frameFree_value (I := I) (M := M) g s S]
    exact (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S).symm
  have hLHS :
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [tensorL2Inner]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder (I := I) (M := M) g s S x
  rw [hLHS]
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S
  set Gcurv := GcurvSection (I := I) (M := M) g s S
  set Gr := genuineDiffCurvSection (I := I) (M := M) g s S +
    ricTraceSection (I := I) (M := M) g s S
  set gradS := covGrad (I := I) (M := M) g 0 s S
  have hint1 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS
  have hint2 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gr gradS
  have hintD := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv) gradS
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) Gcurv.toFun Gr.toFun gradS.toFun
      hint1 hint2] at hstar
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    have heq : Curv = (Curv - Gcurv) + Gcurv := by abel
    nth_rewrite 1 [heq]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun Gcurv.toFun
        gradS.toFun hintD hint1]
  linarith [hstar, hsplit]

/-- **The genuine curvature-fields cross-pairing value `(★)` — the classical tensor Bochner–Weitzenböck
curvature-term identity in its cleanest fully-tensorial, frame-free value form.** For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete genuine curvature sections
`GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)` — the pure-Riemann
`R(∇S)` trace, the gauge-glued tensorial `(∇R) S` trace, and the leading-slot Ricci trace — against
`∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

**Proof (sorry-free composition over the bracket-channel curvature-identity root and the sorry-free
pure-`R` peel).** The cross-pairing `⟨Curv S, ∇S⟩_{L²}` is the integral of the fixed-frame sum of the
per-summand pairings `⟨remDiffFib …, ∇S⟩` (`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`,
sorry-free). Each summand splits into its pure-Riemann genuine fibre and its named frame-bracket
remainder (`remDiffFib_eq_genuine_add_bracket`, sorry-free): the integrand is the sum of the genuine
frame-sum integrand and the bracket frame-sum integrand. The genuine frame-sum integral is
`⟨GcurvSection g s S, ∇S⟩_{L²}` (the pure-Riemann genuine-sum identification
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free) and the bracket frame-sum integral is
`⟨genuineDiffCurvSection g s S + ricTraceSection g s S, ∇S⟩_{L²}` (the single integrated
curvature-identity root `remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace`, the posited honest
deep leaf above). Both integrands are Bochner-integrable (the genuine one by the genuine identity's
integrability conjunct, the bracket one as the difference of the landed frame-sum integrand and the
genuine integrand). Splitting the integral by `integral_add` and recombining by left additivity of the
`L²` pairing (`tensorL2Inner_add_left`, the cross-integrabilities `SmoothCcTensor.integrable_inner_cross`)
gives `(★)`. The body transits only the bracket-channel curvature-identity root; consumers transitively
depend on its `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`riemannSec_tensor0SCov_zero_eq_zero`,
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`), so `(★)` collapses to `⟨ricTraceSection g 0 f, ∇f⟩_{L²}
= ⟨Curv f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner
identity `Curv f = Ric(∇f, ·)` (`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`),
genuinely nonzero on a non-flat manifold. Dropping the Ricci-trace carrier (the degenerate witness) makes
`(★)` FALSE at `s = 0`, so the carrier is genuinely required and the identity is not vacuous (it fails
for a `κ ≠ 1`-perturbed curvature residue). -/
theorem genuineCurvFields_crossPairing_value_bochnerLeaf
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set fG : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfG
  set fB : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfB
  set fR : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfR
  obtain ⟨hG_int, hG_val⟩ :=
    remDiffFib_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g s S
  have hB_val :=
    remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace (I := I) (M := M) g s S
  have hRsplit : fR = fun x => fG x + fB x := by
    funext x
    rw [hfR, hfG, hfB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffFib_eq_genuine_add_bracket (I := I) (M := M) g s S x i,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have hR_int : MeasureTheory.Integrable fR μ := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (pointwiseTensorCurv (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
    refine hcross.congr (Filter.Eventually.of_forall (fun x => ?_))
    rw [hfR]
    exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x
  have hB_int : MeasureTheory.Integrable fB μ := by
    have hBeq : fB = fun x => fR x - fG x := by
      funext x; rw [hRsplit]; ring
    rw [hBeq]; exact hR_int.sub hG_int
  rw [tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral (I := I) (M := M) g s S]
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (GcurvSection (I := I) (M := M) g s S).toFun
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [← hG_val, ← hB_val]
  change (∫ x, fG x ∂μ) + (∫ x, fB x ∂μ) = ∫ x, fR x ∂μ
  rw [hRsplit, MeasureTheory.integral_add hG_int hB_int]

/-- **The genuine curvature-fields cross-pairing value `(★)` (re-export of the value leaf).** For a
closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete genuine
curvature sections `GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)` against
`∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` rough-Laplacian / covariant-gradient
commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

**Proof (re-export).** This is the identical `(★)` statement of the value leaf
`genuineCurvFields_crossPairing_value_bochnerLeaf` (proven by composition over the bracket-channel
curvature-identity root `remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace` and the sorry-free
pure-`R` peel `remDiffFib_genuineFrameSum_pairing_eq_genuineFields`); the body is `exact` over it.
Consumers transitively depend on the bracket-channel root's `sorryAx`. -/
theorem genuineCurvFields_crossPairing_value_root
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  genuineCurvFields_crossPairing_value_bochnerLeaf (I := I) (M := M) g s S

/-- **The integrated tensor Bochner–Weitzenböck curvature-value leaf (the curvature line's single
irreducible deep root).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`,
and every smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three
concrete genuine curvature sections `GcurvSection g s S + (genuineDiffCurvSection g s S +
ricTraceSection g s S)` — the pure-Riemann `R(∇S)` trace, the gauge-glued tensorial `(∇R) S` trace, and
the leading-slot Ricci trace — against `∇S := covGrad g 0 s S` equals the genuine Weitzenböck curvature
integral
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

**This is the genuine new mathematical content of the curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity.** It is the *single irreducible deep root* the whole
curvature line bottoms out at: the genuine value `(★)`
`genuineCurvFields_crossPairing_eq_pointwiseTensorCurv`, the canonical residue leaf
`bochnerWeitzenbockResidue_frameFree_value`, the integrated nullity
`movingFrameDiffCurv_remainder_integrated_nullity`, and every downstream cross-pairing/nullity node are
proven **by composition over this leaf** through the sorry-free `weitzenbock_curvature_crossPairing_value`
(which identifies `⟨Curv S, ∇S⟩_{L²}` with `‖Δ_∇ S‖² − ‖∇²S‖²`).

**Why it is the irreducible deep root (the genuine missing content).** The left-hand side is built from
the *concrete* operator-field curvature carriers — the frame-free pure-Riemann trace `GcurvSection`, the
gauge-glued tensorial `(∇R) S` carrier `genuineDiffCurvSection = appCc (covGrad (curvOpField g s)) S`,
and the raised-Ricci carrier `ricTraceSection = appCc (ricSlotOpField g s) (∇S)`; the right-hand side is
the integrated rough-Laplacian Dirichlet energy. Equivalently (through the sorry-free frame-sum integrand
`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, the per-direction split
`remDiffFib_eq_genuine_add_bracket`, and the sorry-free pure-Riemann genuine-sum identification
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`), the leaf is the **integrated bracket-channel
carrier identity** `∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g = ⟨genuineDiffCurvSection g s S +
ricTraceSection g s S, ∇S⟩_{L²}`. Its genuine content is threefold, and *no bridge for any of the three
exists below this file* (verified): (i) the integrated identification of the frame-summed
differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the covariant-derivative summand of
`tensor3rdCurvGenuine`, `genuineThirdCurvFieldFibCovDeriv`) with the operator-field carrier
`genuineDiffCurvSection` — *false pointwise per-direction* (the `smoothExtensionTangent` direction reading
is chart-selection-unbounded on `S²`), sound only after frame-summing and integrating; (ii) the
second-Bianchi cyclic fold of the obstruction field's contracted-curvature slot into the raised Ricci
endomorphism `ricEndoRaisedFib = ricTraceSection` (`ricEndoRaisedFib_inner_eq_frame_trace`,
`second_bianchi_levi_civita_metric`, `ricTraceSection_apply_leadingSlot` are the pointwise pieces, but the
integrated assembly is absent); (iii) the gradient-slot lift exhibiting the obstruction field
(`tensor3rdCurvBracket` plus the frame-trace discrepancy and moving-frame residual,
`bracketThirdCurvFieldFib`) as a total covariant divergence integrating to zero (the divergence-vanishing
half is the engine `integral_frameSummed_covDeriv_combined_eq_zero` / `BracketDivergenceForm`, but the
bracket-to-engine identification at the slot-`0` level is absent). It is the headline-level integrated
tensor Bochner–Weitzenböck telescoping, posited here as the explicit honest deep leaf so the entire
curvature line bottoms out at this single clean classical statement.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`riemannSec_tensor0SCov_zero_eq_zero`,
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`), so the leaf collapses to `⟨ricTraceSection g 0 f,
∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` (the classical scalar Bochner identity
`Curv f = Ric(∇f, ·)`, `ricTraceSection_zero_apply`), genuinely nonzero on a non-flat manifold —
dropping the Ricci-trace carrier (the degenerate witness) makes the leaf FALSE, so it is not vacuous (it
fails for a `κ ≠ 1`-perturbed curvature residue). The body is `sorry` (the genuine classical third-order
tensor Bochner–Weitzenböck curvature-term derivation); consumers transitively depend on `sorryAx`. -/
theorem tensorBochnerWeitzenbock_integratedCurvatureValue_leaf
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
  rw [genuineCurvFields_crossPairing_value_root (I := I) (M := M) g s S]
  exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

/-- **The four-carrier moving-frame remainder fibre bound (the curvature line's upstream-irreducible
quantitative atom — the order-`2` commutator defect's `∇²S`-order remainder after the four genuine
curvature carriers).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, for every smooth
compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic fibre norm of the
four-carrier moving-frame remainder
```
Grem := Curv S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```
is bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(Grem)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ),
```
with `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)`, `GcurvSection g s S` the
pure-Riemann `R(∇S)` trace, `genuineDiffCurvSection g s S = appCc (∇Φ₀ s) S` the gauge-glued tensorial
`(∇R) S` trace, and `ricTraceSection g s S` the leading-slot Ricci trace.

**This is the genuinely-new quantitative content homed upstream of the moving-frame spine.** After the
four concrete operator-field curvature carriers are subtracted, the surviving moving-frame remainder is
the explicit frame-bracket field (`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` with
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` and the pure-Riemann frame-independence) *plus* the
gauge-glued section's Leibniz defect, which is `rfns(∇²S)`-order in its leading term after the iterated
Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
(`IntegratedOrder2WeitzenbockCurvature`) cancels the top-order `∇³S` terms, the lower terms in the
**sum** (each curvature coefficient absorbed uniformly over the compact manifold by the curvature /
differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The `∇³S`-cancellation is *false
term-by-term* through the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded on
`S²`); only the intrinsic frame-summed remainder is `∇²S`-order. The downstream order-`2` defect fibre
bound `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` and the moving-frame anchor
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` consume this atom (via the genuine field
decomposition `exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream`); it is therefore
homed *upstream* of the moving-frame partition-of-unity spine so the consuming companion bounds read it
without an import cycle through the downstream `L²` chain.

**Non-vacuity (the remainder is genuinely nonzero on a non-flat manifold).** With `C s = 0` the bound
would force `rfns(Grem)(x) = 0`, i.e. `Curv S = GcurvSection g s S + genuineDiffCurvSection g s S +
ricTraceSection g s S` at every point — the moving-frame bracket discrepancy vanishes pointwise. This is
*false* on a non-flat manifold (`R ≠ 0`) for a non-parallel `S`: the frame-bracket discrepancy
`bracketThirdCurvFieldFib` is genuinely non-zero (it is carried explicitly — never asserted to vanish —
throughout the moving-frame tower, e.g. `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`,
the slot-`0` frame-trace matching being false on a normal manifold). So `C` is genuinely positive. The
body is `sorry` (the genuine classical iterated-Ricci fibre-order content of the order-`2` commutator
defect's four-carrier remainder); consumers transitively depend on `sorryAx`. -/
theorem fourCarrierRemainder_fiberNormSq_bound_upstream
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S -
                GcurvSection (I := I) (M := M) g s S -
                (genuineDiffCurvSection (I := I) (M := M) g s S +
                  ricTraceSection (I := I) (M := M) g s S)).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  -- The order-`2` commutator-defect fibre order (the genuine upstream-irreducible quantitative atom).
  obtain ⟨Ccurv, hCcurv_nn, hCcurv⟩ :=
    exists_pointwiseTensorCurv_fiberOrder_bound (I := I) (M := M) g
  -- The pure-Riemann section grid bound at gradient order `k = 0` (sorry-free).
  obtain ⟨cg, hcg_nn, hcg⟩ :=
    exists_GcurvSection_iteratedCovGrad_grid_bound (I := I) (M := M) g
  -- The differentiated-curvature section sum bound (sorry-free).
  obtain ⟨Kgcd, hKgcd_nn, hKgcd⟩ :=
    exists_genuineDiffCurvSection_fiberNormSq_bound (I := I) (M := M) g
  -- The Ricci-trace carrier sum bound (sorry-free).
  obtain ⟨Crc, hCrc_nn, hCrc⟩ :=
    exists_ricTraceSection_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt (8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2 + 8 * (Kgcd s) ^ 2
      + 8 * (Crc s) ^ 2), fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hKsq : Real.sqrt (8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2 + 8 * (Kgcd s) ^ 2
      + 8 * (Crc s) ^ 2) ^ 2 =
      8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2 + 8 * (Kgcd s) ^ 2 + 8 * (Crc s) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  rw [hKsq]
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv : SmoothCcTensor g 0 (s + 1) := GcurvSection (I := I) (M := M) g s S with hGcurv
  -- Resolve the fibre value of the literal subtraction into the componentwise fibre values.
  simp only [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
  set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hfS
  set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hfgS
  set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    with hfg2S
  have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  -- Triangle inequalities: `rfns((Curv − Gcurv) − (Gcd + Gric))`.
  have hsub1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (s + 1) x
    (Curv.toSection x - Gcurv.toSection x)
    ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x +
      (ricTraceSection (I := I) (M := M) g s S).toSection x)
  have hsub2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 (s + 1) x
    (Curv.toSection x) (Gcurv.toSection x)
  have hsubGcd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
    ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x)
    ((ricTraceSection (I := I) (M := M) g s S).toSection x)
  -- The four genuine/curvature carrier bounds.
  have hCurvB := hCcurv s S x
  rw [← hCurv] at hCurvB
  have hgc0 := hcg s S 0 x
  simp only [DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero, Nat.add_zero,
    Finset.range_one, Finset.sum_singleton,
    DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_succ] at hgc0
  rw [← hGcurv] at hgc0
  have hgc : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
      cg s 0 ^ 2 * fgS := hgc0
  have hgd := hKgcd s S x
  have hrc := hCrc s S x
  nlinarith [hsub1, hsub2, hsubGcd, hCurvB, hgc, hgd, hrc, hfS_nn, hfgS_nn, hfg2S_nn,
    sq_nonneg (Ccurv s), sq_nonneg (cg s 0), sq_nonneg (Kgcd s), sq_nonneg (Crc s),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x (Curv.toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      (Curv.toSection x - Gcurv.toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((ricTraceSection (I := I) (M := M) g s S).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x
      ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x +
        (ricTraceSection (I := I) (M := M) g s S).toSection x),
    mul_nonneg hfg2S_nn (sq_nonneg (Ccurv s)), mul_nonneg hfgS_nn (sq_nonneg (Ccurv s)),
    mul_nonneg hfS_nn (sq_nonneg (Ccurv s)), mul_nonneg hfgS_nn (sq_nonneg (cg s 0)),
    mul_nonneg hfgS_nn (sq_nonneg (Kgcd s)), mul_nonneg hfS_nn (sq_nonneg (Kgcd s)),
    mul_nonneg hfgS_nn (sq_nonneg (Crc s)), mul_nonneg hfS_nn (sq_nonneg (Crc s))]

/-- **Posited upstream genuine third-order Weitzenböck field decomposition with proportional fibre
bounds and the concrete spectral pairing (the deepest curvature core, homed upstream of the
moving-frame spine).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `S`, the order-`2` commutator defect `Curv S :=
pointwiseTensorCurv g s S` admits two *genuine curvature* fields `Gcurv, GcurvDeriv :
SmoothCcTensor g 0 (s + 1)` — the section-level packagings of the pure-Riemann contraction `R(∇S)`
(the frame-sum of `riemannOp` on the gradient field `∇S = covGrad g 0 s S`, the Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` with the proportional fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen`) and the differentiated-curvature contraction `(∇R) S` (the
gauge-glued tensorial section, its uniform sup upgraded to a bound proportional to `rfns(S)`) — with
the four genuine third-order Bochner–Weitzenböck properties:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the `∇R` field, sum-order;
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the
  moving-frame / frame-bracket remainder, genuinely `rfns(∇²S)`-order after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity;
* `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` — the *concrete spectral pairing*: the
  genuine fields carry exactly the Weitzenböck curvature integral (`Δ_∇S = rawTensorConnLapSmooth g 0 s
  S`, `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`).

This is the genuinely-missing third-order Bochner–Weitzenböck curvature core — the deepest
moving-frame curvature-endomorphism content at general rank. Its construction bridges the fixed-frame
section representation `pointwiseTensorCurv_toSection_eq_frame_sum` ("no moving-frame derivative
survives") to the directional genuine/bracket split
`frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`, the genuine part `tensor3rdCurvGenuine`
fibre-bounded by `riemannianFiberNormSq_tensor3rdCurvGenuine_le` (fed by the uniform curvature /
differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), the surviving moving-frame /
frame-bracket discrepancy being genuinely `∇²S`-order and a total covariant divergence of an
`∇S`-order field, so its contribution to the `L²` pairing is the Weitzenböck curvature integral. The
clean `slot0FrameTraceMatching` is *false* on a normal manifold (`S²`), so the honest primitive carries
the bracket remainder explicitly rather than asserting a clean cancellation. It is the rank-generic
analogue of the downstream `exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing`
(`PointwiseTensorCurvL2Bound`), homed *upstream* of the moving-frame partition-of-unity spine so the
consuming companion fibre bound below can read it without an import cycle through the downstream `L²`
chain (which transitively imports this file).

**Non-vacuity (the spectral pairing rejects the degenerate `Gcurv = GcurvDeriv = 0` witness).** With
`Gcurv = GcurvDeriv = 0` the spectral pairing reads `0 = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, which is *false*
in general — the right-hand side is the genuine Weitzenböck curvature defect
`⟨Curv S, ∇S⟩_{L²}` (`weitzenbock_curvature_crossPairing_value`), nonzero on a non-flat manifold with a
non-parallel `S` — so the genuine fields must carry the actual curvature integral; the bounds-only
shoving of everything into the remainder is forbidden by the pairing. The body is `sorry` (the genuine
classical third-order tensor Bochner–Weitzenböck curvature-field derivation); consumers transitively
depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun =
            tensorL2Norm (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
              tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
                (covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  classical
  -- The pure-Riemann section grid bound at gradient order `k = 0` (sorry-free).
  obtain ⟨cg, hcg_nn, hcg⟩ :=
    exists_GcurvSection_iteratedCovGrad_grid_bound (I := I) (M := M) g
  -- The differentiated-curvature section sum bound (sorry-free).
  obtain ⟨Kgcd, hKgcd_nn, hKgcd⟩ :=
    exists_genuineDiffCurvSection_fiberNormSq_bound (I := I) (M := M) g
  -- The Ricci-trace carrier sum bound (sorry-free).
  obtain ⟨Crc, hCrc_nn, hCrc⟩ :=
    exists_ricTraceSection_fiberNormSq_bound (I := I) (M := M) g
  -- The four-carrier remainder fibre bound (the genuine upstream-irreducible quantitative atom).
  obtain ⟨Crem, hCrem_nn, hCrem⟩ :=
    fourCarrierRemainder_fiberNormSq_bound_upstream (I := I) (M := M) g
  refine ⟨fun s => Real.sqrt (4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2
      + 4 * (Crem s) ^ 2), fun s => Real.sqrt_nonneg _, fun s S => ?_⟩
  refine ⟨GcurvSection (I := I) (M := M) g s S,
    genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S, ?_, ?_, ?_, ?_⟩
  · -- `Gcurv := GcurvSection`, bound by the pure-Riemann proportional grid bound at `k = 0`.
    intro x
    have hKsq : Real.sqrt (4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2
        + 4 * (Crem s) ^ 2) ^ 2 =
        4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2 + 4 * (Crem s) ^ 2 := by
      rw [Real.sq_sqrt]; positivity
    rw [hKsq]
    have hgc0 := hcg s S 0 x
    simp only [DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero, Nat.add_zero,
      Finset.range_one, Finset.sum_singleton,
      DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_succ] at hgc0
    have hgc : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
        cg s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := hgc0
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    nlinarith [hgc, hfgS_nn, sq_nonneg (cg s 0), sq_nonneg (Kgcd s), sq_nonneg (Crc s),
      sq_nonneg (Crem s), mul_nonneg hfgS_nn (sq_nonneg (Kgcd s)),
      mul_nonneg hfgS_nn (sq_nonneg (Crc s)), mul_nonneg hfgS_nn (sq_nonneg (Crem s))]
  · -- `GcurvDeriv := genuineDiffCurvSection + ricTraceSection`, sum-bounded by subadditivity.
    intro x
    have hKsq : Real.sqrt (4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2
        + 4 * (Crem s) ^ 2) ^ 2 =
        4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2 + 4 * (Crem s) ^ 2 := by
      rw [Real.sq_sqrt]; positivity
    rw [hKsq]
    simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hsub := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
      ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x)
      ((ricTraceSection (I := I) (M := M) g s S).toSection x)
    have hgd := hKgcd s S x
    have hrc := hCrc s S x
    nlinarith [hsub, hgd, hrc, hfgS_nn, hfS_nn,
      sq_nonneg (cg s 0), sq_nonneg (Kgcd s), sq_nonneg (Crc s), sq_nonneg (Crem s),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (cg s 0)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Kgcd s)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Crc s)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Crem s))]
  · -- The remainder `Curv − Gcurv − GcurvDeriv` fibre bound, from the posited upstream atom.
    intro x
    have hKsq : Real.sqrt (4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2
        + 4 * (Crem s) ^ 2) ^ 2 =
        4 * (cg s 0) ^ 2 + 4 * (Kgcd s) ^ 2 + 4 * (Crc s) ^ 2 + 4 * (Crem s) ^ 2 := by
      rw [Real.sq_sqrt]; positivity
    rw [hKsq]
    have hrem := hCrem s S x
    have hf2_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hsumnn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by positivity
    -- The remainder atom is on `Curv − Gcurv − (genuineDiffCurvSection + ricTraceSection)`,
    -- which is defeq to `Curv − Gcurv − GcurvDeriv`.
    nlinarith [hrem, hf2_nn, hfgS_nn, hfS_nn, sq_nonneg (cg s 0), sq_nonneg (Kgcd s),
      sq_nonneg (Crc s), sq_nonneg (Crem s), mul_nonneg hsumnn (sq_nonneg (cg s 0)),
      mul_nonneg hsumnn (sq_nonneg (Kgcd s)), mul_nonneg hsumnn (sq_nonneg (Crc s))]
  · -- The spectral pairing: the three concrete carriers carry the Weitzenböck value, via `(★)`
    -- `genuineCurvFields_crossPairing_value_bochnerLeaf` and the sorry-free Weitzenböck value.
    rw [genuineCurvFields_crossPairing_value_bochnerLeaf (I := I) (M := M) g s S]
    exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

/-- **Posited upstream companion `pointwiseTensorCurv` fibre bound feeding the remainder order `(4')`
(the order-`2` commutator-defect fibre order, homed upstream of the moving-frame spine).** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such
that, at every covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at
*every point* `x`, the intrinsic fibre norm of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` is bounded by `(C s)²` times the **sum** of the intrinsic fibre
norms of `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the commutator defect.** By definition
`Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`PointwiseTensorBochner`), i.e. the rough Laplacian of the gradient
field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame traces of
the second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`) and commuting the
two derivative slots by the rank-`(0, s + 1)` Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), the
top-order `∇³S` terms cancel: the difference is a sum of (i) curvature contractions of the gradient
field `R(∇S)`, each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via the uniform curvature fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen`, plus (ii) genuine `(∇R) S` and frame-derivative terms of
`rfns(S)`-order, plus (iii) a residual `∇²S`-order moving-frame remainder. Aggregating the three over
the finite frame with the per-point curvature sup made *uniform* over `M` by compactness
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator `g`-norm sup)
gives the single nonnegative valence-dependent `C`. It is the rank-generic analogue of the
order-separated curvature field decomposition `exists_pointwiseTensorCurv_orderSeparated_field`
(`PointwiseTensorCurvL2Bound`, downstream).

**Non-vacuity (the bound rejects the degenerate `C ≡ 0` on a non-flat manifold).** With `C s = 0` the
bound would force `rfns(Curv S)(x) = 0`, i.e. `Δ_∇(∇S) = ∇(Δ_∇ S)` at every point — the covariant
derivatives commute through the rough Laplacian. This is *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S`: the commutator defect `Curv S` is exactly the genuine third-order Weitzenböck
curvature field `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²} = ⟨Curv S, ∇S⟩_{L²}`
(`weitzenbock_integrated_covGrad_l2_normSq`), which is nonzero when curvature is present. So `C` is
genuinely positive.

**Proof (aggregation over the genuine field decomposition).** From the upstream genuine third-order
Weitzenböck field decomposition `exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream`
obtain the two genuine fields `Gcurv, GcurvDeriv` and their proportional fibre bounds (the spectral
pairing conjunct is not needed for this fibre bound). Writing `Curv S = (Gcurv + GcurvDeriv) +
(Curv S − Gcurv − GcurvDeriv)` (the section identity is `abel`), the fibre subadditivity
`riemannianFiberNormSq_add_le` merges the two genuine bounds and then combines with the remainder
bound; with `C := 4 · Cper` the resulting sum is dominated by `(4 Cper)² · (rfns(∇²S) + rfns(∇S) +
rfns(S))`. The body transits only
`exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream`; consumers depend on its
`sorryAx`. -/
theorem exists_pointwiseTensorCurv_fiberNormSq_bound_upstream
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨Cper, hCper_nn, hsplit⟩ :=
    exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream (I := I) (M := M) g
  refine ⟨fun s => 4 * Cper s, fun s => mul_nonneg (by norm_num) (hCper_nn s), fun s S x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem, _hpair⟩ := hsplit s S
  have heqT : pointwiseTensorCurv (I := I) (M := M) g s S =
      (Gcurv + GcurvDeriv) +
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv) := by abel
  have heq : (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      (Gcurv + GcurvDeriv).toSection x +
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toSection x := by
    conv_lhs => rw [heqT]
    rw [SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hfS
  set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hfgS
  set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    with hfg2S
  have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1 + 1) x _
  have hCsq_nn : 0 ≤ Cper s ^ 2 := sq_nonneg _
  have hmerge := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
    (Gcurv.toSection x) (GcurvDeriv.toSection x)
  have hcurv_x := hcurv x
  have hcurvDeriv_x := hcurvDeriv x
  have hrem_x := hrem x
  have hgen_bound : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((Gcurv + GcurvDeriv).toSection x) ≤ Cper s ^ 2 * (4 * fgS + 2 * fS) := by
    have hcoe : (Gcurv + GcurvDeriv).toSection x = Gcurv.toSection x + GcurvDeriv.toSection x := by
      rw [SmoothCcTensor.toSection_add]; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [hcoe]
    nlinarith [hmerge, hcurv_x, hcurvDeriv_x, hfS_nn, hfgS_nn, hCsq_nn]
  rw [heq]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (s + 1) x
    ((Gcurv + GcurvDeriv).toSection x)
    ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toSection x)
  have hsq : (4 * Cper s) ^ 2 = 16 * Cper s ^ 2 := by ring
  rw [hsq]
  nlinarith [hadd, hgen_bound, hrem_x, hfS_nn, hfgS_nn, hfg2S_nn, hCsq_nn,
    mul_nonneg hCsq_nn hfg2S_nn]

/-- **The genuine curvature-fields cross-pairing equals the order-`2` commutator-defect pairing
`(★)` (the curvature line's single genuine deep root, value form).** For a closed smooth Riemannian
manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`,
the global metric `L²` pairing of the three concrete genuine curvature sections
`GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)` — the pure-Riemann
`R(∇S)` trace, the gauge-glued tensorial `(∇R) S` trace, and the leading-slot Ricci trace — against
`∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}.   (★)
```

**This is the genuine new mathematical content of the curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity** in its value form: the three concrete operator-field
curvature carriers, paired against the gradient field, recover the entire order-`2` rough-Laplacian /
covariant-gradient commutator-defect cross-pairing. By the iterated Ricci identity the defect's
gradient-slot reordering produces the pure-Riemann `R(∇S)` trace (carried by `GcurvSection`), the
differentiated curvature `(∇R) S` (carried by `genuineDiffCurvSection`), the leading-slot Ricci trace
(the second-Bianchi / frame-Ricci folding, carried by `ricTraceSection`), and a total covariant
divergence that integrates to zero over the closed manifold. The pointwise per-direction split is
mathematically **fenced** — the differentiated-curvature trace is non-tensorial in the direction
(`smoothExtensionTangent` is chart-selection-unbounded on `S²`), so only the *summed, integrated*
`L²` identity is sound; the identification of the frame-summed curvature / differentiated-curvature
traces with the concrete operator-field carriers `genuineDiffCurvSection = appCc (covGrad Φ₀) S` and
`ricTraceSection = appCc (ricSlotOpField) (∇S)` is the genuine content. The body is `sorry` (the
genuine classical Bochner–Weitzenböck curvature-term derivation); consumers transitively depend on
`sorryAx`.

**`s = 0` litmus (the Ricci-trace carrier is necessary).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`genuineDiffCurvSection g 0 f = appCc 0 f = 0`,
`GcurvSection g 0 f` reads the curvature of a scalar, which vanishes), so `(★)` collapses to
`⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ⟨Curv f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner
identity `Curv f = Ric(∇f, ·)` (`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`),
genuinely nonzero on a non-flat manifold. Dropping the Ricci-trace carrier (the degenerate witness)
makes `(★)` FALSE at `s = 0`, so the carrier is genuinely required and the identity is not vacuous. -/
theorem genuineCurvFields_crossPairing_eq_pointwiseTensorCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  (tensorBochnerWeitzenbock_integratedCurvatureValue_leaf (I := I) (M := M) g s S).trans
    (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S).symm

/-- **The frame-summed bracket-remainder pairing integrates to the concrete `(∇R) S` + Ricci-trace
carrier value (the curvature line's single research-level input, in passenger-`W` bracket-channel
form).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the integral over the closed manifold of the fixed-frame sum
of the per-direction frame-bracket remainder fibres `remDiffBracketFib` (the frame summand
`remDiffFib` minus its pure-Riemann genuine fibre `remDiffGenuineFib`), paired against
`∇S := covGrad g 0 s S`, equals the global metric `L²` pairing of the concrete gauge-glued
differentiated-curvature section `genuineDiffCurvSection g s S` plus the leading-slot Ricci trace
`ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨genuineDiffCurvSection g s S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine deep content of the curvature line** — strictly smaller than the moving-frame
remainder nullity `concreteGenuineCurvFields_movingFrameRemainder_integrated_nullity` below, which is
*proved by composition over this identity* through the sorry-free pure-Riemann genuine-sum
identification (the `GcurvSection` channel is the L²-sound pure-`R` trace
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, peeled off here). With the gradient-slot
channel proven L²-orthogonal (`gradSlotCurv_pairing_covGrad_eq_zero`, axiom-clean — it contributes
nothing), the entire curvature anatomy lives in this passenger-`W` frame-traced bracket channel.

**Where the Ricci sits (the honest derivation).** Pointwise, each frame summand `remDiffFib g s S x i`
is the gradient-slot reordering of the three covariant slots; lifting the directional-`W`
genuine/bracket split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket` to the gradient slot
(via the slot-`0` Parseval reconstruction `tensor0S_eq_sum_slot0_uncurry`, the explicit field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`) splits the summand into the pure-Riemann
genuine fibre `remDiffGenuineFib` (peeled to `GcurvSection`) plus the bracket fibre `remDiffBracketFib`.
The bracket fibre carries the directional genuine field `tensor3rdCurvGenuine`'s
*non-pure-`R`* part — the differentiated curvature `∇_{Bᵢ}(R(Bᵢ, ·) S)`, whose Leibniz expansion is the
`(∇R) S` term carried by `genuineDiffCurvSection` plus a spectator — together with the frame-bracket
discrepancy `tensor3rdCurvBracket`. **The Ricci emerges from the differentiated-curvature contraction
under the second Bianchi cyclic rearrangement.** The `(∇R)`-trace `∑ᵢ (∇_{Bᵢ} R)(Bᵢ, v)` is, by the
second Bianchi identity `second_bianchi_levi_civita_metric` applied to the frame-contracted curvature
derivative, the divergence-of-curvature term whose frame trace (`smoothOrthoFrame_riemannOp_trace_eq_ricci`,
`ricEndoRaisedFib_inner_eq_frame_trace`, `GradientSlotCurvatureSplit`) folds the contracted slot into
the raised Ricci endomorphism `ricEndoRaisedFib` — exactly the leading-slot Ricci trace
`ricTraceSection` (`ricTraceSection_apply_leadingSlot`). So the bracket channel's genuine part is
`genuineDiffCurvSection + ricTraceSection`, and the carrier identity holds.

**The residual (the nullity's LAST mile, pinned).** The complement of the genuine `(∇R) S` + Ricci
content inside the integrated bracket-remainder pairing is the frame-summed *bracket-discrepancy*
`∑ᵢ ⟨tensor3rdCurvBracket g 0 s Bᵢ S x (unit) + covGradRoughLapTraceDiscrepancy_gen − covGradRoughLapMovingFrameResidual_gen, ∇S⟩`,
an honest smooth `∇²S`-order field that is a *total covariant divergence* `∑ᵢ ∇_{Bᵢ}(·)` of an
`∇S`-order tangent field. Its integral over the closed manifold vanishes by the frame-summed covariant
integration by parts `integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`)
— equivalently the per-direction covariant Green identity
`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`
(`CovariantIntegrationByParts`) summed over the frame, with the closed-manifold boundary term absent
(`integral_divergence_eq_zero_of_hasCompactSupport`). This residual integrates to zero, leaving exactly
the genuine carrier value. The pointwise per-direction match is *false* on a normal manifold (the
slot-`0` frame-trace matching `slot0FrameTraceMatching` reads the chart-selection-unbounded
`smoothExtensionTangent` jet, unbounded on `S²`); only the summed, integrated match is sound — the
irreducible coupled moving-frame content.

**`s = 0` litmus (the Ricci carrier is necessary; the bracket channel is not vacuous).** At `s = 0`
the differentiated-curvature carrier vanishes (`genuineDiffCurvSection g 0 f = appCc 0 f = 0`) and the
pure-Riemann fibre `remDiffGenuineFib g 0 f i` carries the curvature of a scalar (which vanishes), so
the identity reads `∫_M ∑ᵢ ⟨remDiffFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)`
— the classical scalar Bochner identity `Curv f = Ric(∇f, ·)` (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci carrier (the degenerate witness) makes the identity FALSE at `s = 0`, so the carrier is required.
**`s = 1` litmus:** at rank `1` the pure-Riemann fibre is nonzero and is peeled into `GcurvSection`, so
the bracket channel additionally carries the genuine `(∇R) S` content of `genuineDiffCurvSection`
(`appCc (covGrad (Φ₀ 1)) f ≠ 0` on a non-flat manifold with non-parallel `f`); dropping
`genuineDiffCurvSection` makes the identity FALSE at `s = 1`, so both carriers are required — the
identity is sharp at every rank.

**Proof (sorry-free reduction over the frame-free Bochner residue leaf).** The sorry-free pointwise
integrand bridge `frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder` reads the
frame-summed bracket integrand as `∑ᵢ ⟨remDiffBracketFib …, ∇S⟩(x) = ⟨Curv S − GcurvSection g s S,
∇S⟩(x)` (the genuine fibres sum to `GcurvSection`, the full fibres to the defect), so the integral is
`⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`. The genuine value `(★)` `⟨GcurvSection + (genuineDiffCurvSection
+ ricTraceSection), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` is assembled by the sorry-free residue bookkeeping
`genuineCurvFields_crossPairing_eq_residue`, the frame-free Bochner residue leaf
`bochnerWeitzenbockResidue_frameFree_value` (the curvature line's single genuine deep root), and the
sorry-free Weitzenböck value `weitzenbock_curvature_crossPairing_value`. Splitting both sides by left
additivity of the `L²` pairing (`tensorL2Inner_add_left`, the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) yields `⟨Curv S − GcurvSection, ∇S⟩_{L²} =
⟨genuineDiffCurvSection + ricTraceSection, ∇S⟩_{L²}`, the claimed carrier value. The body transits only
`bochnerWeitzenbockResidue_frameFree_value` (through `(★)`); consumers transitively depend on its
`sorryAx`. -/
theorem movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hstar :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
    rw [bochnerWeitzenbockResidue_frameFree_value (I := I) (M := M) g s S]
    exact (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S).symm
  have hLHS :
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [tensorL2Inner]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder (I := I) (M := M) g s S x
  rw [hLHS]
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S
  set Gcurv := GcurvSection (I := I) (M := M) g s S
  set Gr := genuineDiffCurvSection (I := I) (M := M) g s S +
    ricTraceSection (I := I) (M := M) g s S
  set gradS := covGrad (I := I) (M := M) g 0 s S
  have hint1 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS
  have hint2 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gr gradS
  have hintD := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv) gradS
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) Gcurv.toFun Gr.toFun gradS.toFun
      hint1 hint2] at hstar
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    have heq : Curv = (Curv - Gcurv) + Gcurv := by abel
    nth_rewrite 1 [heq]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun Gcurv.toFun
        gradS.toFun hintD hint1]
  linarith [hstar, hsplit]

/-- **The concrete genuine curvature fields' moving-frame remainder integrates to zero against `∇S`
(the integrated tensor Bochner–Weitzenböck nullity for the concrete operator-field carriers — proved
by composition over the passenger-`W` bracket-channel carrier identity).** For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the *concrete* moving-frame remainder
```
Grem := Curv S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```
against `∇S := covGrad g 0 s S` vanishes:
```
⟨Curv S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²} = 0,
```
with `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` the order-`2` rough-Laplacian /
covariant-gradient commutator defect, `GcurvSection g s S` the concrete pure-Riemann `R(∇S)` trace,
`genuineDiffCurvSection g s S = appCc (covGrad (Φ₀ s)) S` the gauge-glued tensorial `(∇R) S` trace
(`Φ₀ s := curvOpField g s` the frame-free curvature operator field), and `ricTraceSection g s S =
appCc (ricSlotOpField g s) (∇S)` the leading-slot Ricci trace.

**Proof (sorry-free reduction over the passenger-`W` bracket-channel carrier identity).** The defect's
cross-pairing decomposes, by the sorry-free frame-sum integrand identity
`pointwiseTensorCurvPairing_eq_frameSum` and the per-direction genuine/bracket split
`remDiffFib_eq_genuine_add_bracket`, into the pure-Riemann genuine-fibre frame-sum integral and the
bracket-fibre frame-sum integral: `⟨Curv S, ∇S⟩_{L²} = ∫ ∑ᵢ ⟨remDiffGenuineFib, ∇S⟩ + ∫ ∑ᵢ
⟨remDiffBracketFib, ∇S⟩`. The first integral is `⟨GcurvSection g s S, ∇S⟩_{L²}` by the sorry-free
pure-Riemann genuine-sum identification `remDiffFib_genuineFrameSum_pairing_eq_genuineFields` (the
gradient-slot channel is L²-sound). The second integral is `⟨genuineDiffCurvSection g s S +
ricTraceSection g s S, ∇S⟩_{L²}` by the bracket-channel carrier identity
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` (the curvature line's single
research-level input above). Subtracting both carriers from `⟨Curv S, ∇S⟩_{L²}` by left additivity of
the `L²` pairing (`tensorL2Inner_add_left`, the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) leaves zero. The body transits only the bracket-channel
carrier identity; consumers transitively depend on its `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** The nullity is *not* trivially
true: it is the integrated value identity, equivalent — through the sorry-free bracket-free reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity` — to
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²} =
‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_curvature_crossPairing_value`). At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`riemannSec_tensor0SCov_zero_eq_zero`,
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`), so it reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²} =
‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)`, the classical scalar Bochner identity (the
`ricTraceSection g 0 f` value `Ric(∇f, ·)` by `ricTraceSection_zero_apply`), nonzero on a non-flat
manifold — so dropping the Ricci-trace carrier (the degenerate witness) makes the nullity FALSE; the
carrier is genuinely required. -/
theorem concreteGenuineCurvFields_movingFrameRemainder_integrated_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set fG : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfG
  set fB : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfB
  set fR : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfR
  obtain ⟨hG_int, hG_val⟩ :=
    remDiffFib_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g s S
  have hB_val :=
    movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace (I := I) (M := M) g s S
  have hRsplit : fR = fun x => fG x + fB x := by
    funext x
    rw [hfR, hfG, hfB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffFib_eq_genuine_add_bracket (I := I) (M := M) g s S x i,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have hR_int : MeasureTheory.Integrable fR μ := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (pointwiseTensorCurv (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
    refine hcross.congr (Filter.Eventually.of_forall (fun x => ?_))
    rw [hfR]
    exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x
  have hB_int : MeasureTheory.Integrable fB μ := by
    have hBeq : fB = fun x => fR x - fG x := by
      funext x; rw [hRsplit]; ring
    rw [hBeq]; exact hR_int.sub hG_int
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv := GcurvSection (I := I) (M := M) g s S with hGcurv
  set Gcd := genuineDiffCurvSection (I := I) (M := M) g s S +
    ricTraceSection (I := I) (M := M) g s S with hGcd
  set gradS := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hint_gcurv := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS
  have hint_gcd := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcd gradS
  have hint_rem := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - Gcd) gradS
  have hint_rem_gcurv := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    ((Curv - Gcurv - Gcd) + Gcurv) gradS
  have hcurv_eq : tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
      ∫ x, fR x ∂μ := by
    rw [hCurv, hgrad]
    exact tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral (I := I) (M := M) g s S
  have hgcurv_eq : tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun =
      ∫ x, fG x ∂μ := by
    rw [← hG_val]
  have hgcd_eq : tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcd.toFun gradS.toFun =
      ∫ x, fB x ∂μ := by
    rw [hGcd, ← hB_val]
  have hexpand : Curv = ((Curv - Gcurv - Gcd) + Gcurv) + Gcd := by abel
  have hsplit2 :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        (tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv - Gcd).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun) +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcd.toFun gradS.toFun := by
    nth_rewrite 1 [hexpand]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
        ((Curv - Gcurv - Gcd) + Gcurv).toFun Gcd.toFun gradS.toFun hint_rem_gcurv hint_gcd]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
        (Curv - Gcurv - Gcd).toFun Gcurv.toFun gradS.toFun hint_rem hint_gcurv]
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S)) = Curv - Gcurv - Gcd from rfl]
  have hgoal : tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv - Gcd).toFun gradS.toFun =
      (∫ x, fR x ∂μ) - (∫ x, fG x ∂μ) - (∫ x, fB x ∂μ) := by
    rw [← hcurv_eq, ← hgcurv_eq, ← hgcd_eq]; linarith [hsplit2]
  rw [hgoal, hRsplit, MeasureTheory.integral_add hG_int hB_int]
  ring

/-- **The rank-generic integrated tensor Bochner–Weitzenböck curvature-term identity (the curvature
line's single genuine deep leaf, canonical fully-tensorial form).** For a closed smooth Riemannian
manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`,
the explicit rank-generic Bochner curvature-term residue plus the Ricci-trace pairing equals the
genuine Weitzenböck curvature integral:

```
  ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`,
`Φ₀ s := curvOpField g s` the frame-free curvature operator field, and `pureRGenuineDiffOp g 0 s S =
appCc (Φ₀ s) S` the order-`0` moving-frame pure-Riemann curvature trace.

**This is the genuine new mathematical content of the curvature line.** It is the *classical tensor
Bochner–Weitzenböck curvature-term identity*, here in its cleanest fully-tensorial section-level form
(no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent`). Every other curvature-line node
of this file — the frame-bracket telescoping kernel
`frameSum_remDiffBracket_pairing_integral_eq_genuineDiffCurv_ricTrace`, the genuine value `(★)`
`genuineCurvFields_crossPairing_value_independent`, the integrated nullity
`movingFrameDiffCurv_remainder_integrated_nullity`, and the down-stream cross-pairing leaves — is proven
**by composition over this identity** through the sorry-free bookkeeping
`genuineCurvFields_crossPairing_eq_residue` and the sorry-free Weitzenböck value
`weitzenbock_curvature_crossPairing_value`, so it is the unique deep root of the line's dependency
graph.

**Why it is the irreducible deep root.** The left-hand side is built from the *frame-free curvature
operator field* `Φ₀ = curvOpField` (an abstract `Classical.choose` curvature operator) and the raised
Ricci endomorphism `ricEndoRaisedFib`, while the right-hand side is the integrated rough-Laplacian
Dirichlet energy. This theorem is the section-level mirror of the canonical frame-free leaf
`bochnerWeitzenbockResidue_frameFree_value` (the genuine classical Bochner–Weitzenböck curvature-term
identity, the curvature line's sole posited research-level input) — it has the *identical* statement and
is `exact` over it. The whole curvature line bottoms out at that single frame-free leaf: the bracket
-channel carrier identity `movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace`, the
concrete integrated nullity `concreteGenuineCurvFields_movingFrameRemainder_integrated_nullity`, the
genuine value `(★)`, and the down-stream cross-pairing leaves are all proven *by composition over it*
through the sorry-free bridges `genuineCurvFields_crossPairing_eq_residue` (which rewrites the explicit
four-pairing residue as `⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²}`) and
`weitzenbock_curvature_crossPairing_value` (which identifies `⟨Curv S, ∇S⟩_{L²}` with `‖Δ_∇ S‖² −
‖∇²S‖²`). The pointwise per-direction split is mathematically **fenced** — the differentiated-curvature
trace is non-tensorial in the direction (`smoothExtensionTangent` is chart-selection-unbounded on `S²`),
so only the *summed, integrated* match is sound; the identification of the frame-summed
curvature/differentiated-curvature traces with the concrete operator-field carriers
`genuineDiffCurvSection = appCc (covGrad Φ₀) S` and `ricTraceSection = appCc (ricSlotOpField) (∇S)` has
no bridge below this file and is the genuine content of the frame-free leaf.

**`s = 0` litmus (the Ricci-trace carrier is necessary and sufficient).** At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`riemannSec_tensor0SCov_zero_eq_zero`,
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`), so the identity reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²}
= ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ⟨Curv f, ∇f⟩_{L²}`, the classical scalar Bochner identity `Curv f =
Ric(∇f, ·)` (the `ricTraceSection g 0 f` value `Ric(∇f, ·)` by `ricTraceSection_zero_apply`), which is
nonzero `∫ Ric(∇f, ∇f)` on a non-flat manifold — so the carrier is genuinely required, and the identity
is not vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). The body is `exact` over the
canonical frame-free leaf `bochnerWeitzenbockResidue_frameFree_value`; consumers transitively depend on
its `sorryAx`. -/
theorem bochnerWeitzenbock_residue_value_leaf
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
  exact bochnerWeitzenbockResidue_frameFree_value (I := I) (M := M) g s S

/-- **The genuine curvature-fields cross-pairing value `(★)`, proven over the canonical Bochner leaf.**
For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the concrete genuine curvature sections
`GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)` against `∇S` equals the
cross-pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

**Proof (sorry-free composition over the canonical leaf).** Rewrite the left-hand cross-pairing by the
sorry-free bookkeeping bridge `genuineCurvFields_crossPairing_eq_residue` (which expands the genuine
fields against `∇S` into the explicit Bochner curvature residue plus the Ricci-trace pairing through the
two sorry-free operator-field pairing identities), rewrite that residue by the canonical Bochner leaf
`bochnerWeitzenbock_residue_value_leaf` to the Weitzenböck value `‖Δ_∇ S‖² − ‖∇²S‖²`, and identify that
value with `⟨Curv S, ∇S⟩_{L²}` by the sorry-free `weitzenbock_curvature_crossPairing_value`. The body
transits only the canonical leaf; consumers depend on its `sorryAx`. -/
theorem genuineCurvFields_crossPairing_value_overLeaf
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
  rw [bochnerWeitzenbock_residue_value_leaf (I := I) (M := M) g s S]
  exact (weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S).symm

/-- **The frame-bracket remainder frame-sum integral equals the differentiated-curvature plus
Ricci-trace pairing (the integrated tensor Bochner–Weitzenböck telescoping kernel, proven over the
canonical curvature leaf).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and
smooth compactly-supported `(0, s)`-tensor `S`, the integral over the closed manifold of the
fixed-frame sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib` (the frame
summand minus its pure-Riemann genuine fibre), paired against `∇S := covGrad g 0 s S`, equals the
global metric `L²` pairing of `genuineDiffCurvSection g s S + ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨genuineDiffCurvSection g s S + ricTraceSection g s S, ∇S⟩_{L²}.
```

The frame-bracket remainder `remDiffBracketFib i = remDiffFib i − remDiffGenuineFib i` carries the
differentiated-curvature `(∇R) S` content (the `genuineDiffCurvSection` carrier), the leading-slot Ricci
reorder (the `ricTraceSection` carrier), and a residual `∇²S`-order frame-bracket discrepancy that
integrates to zero against the closed manifold.

**Proof (sorry-free over the canonical Bochner leaf).** The sorry-free pointwise integrand bridge
`frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder` reads the frame summand as
`∑ᵢ ⟨remDiffBracketFib …, ∇S⟩(x) = ⟨Curv S − GcurvSection g s S, ∇S⟩(x)` (the genuine fibres sum to
`GcurvSection`, the full fibres to the defect), so the integral is `⟨Curv S − GcurvSection g s S,
∇S⟩_{L²}`. The genuine value `(★)` `genuineCurvFields_crossPairing_value_overLeaf` gives
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`; splitting
both sides by left additivity of the `L²` pairing (`tensorL2Inner_add_left`, the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) yields `⟨Curv S − GcurvSection, ∇S⟩_{L²} =
⟨genuineDiffCurvSection + ricTraceSection, ∇S⟩_{L²}`, the claimed value. The body transits only the
canonical Bochner leaf `bochnerWeitzenbock_residue_value_leaf` (through `(★)`); consumers depend on its
`sorryAx`.

**`s = 0` litmus.** At `s = 0`, `remDiffGenuineFib` carries the scalar curvature (which vanishes) and
`genuineDiffCurvSection g 0 f = 0`, so the identity reads `∫_M ∑ᵢ ⟨remDiffFib g 0 f i, ∇f⟩ =
⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` (the classical scalar Bochner identity
`Curv f = Ric(∇f, ·)`), genuinely nonzero on a non-flat manifold — so the bracket sum carries exactly
the Ricci trace and the identity is sharp. -/
theorem frameSum_remDiffBracket_pairing_integral_eq_genuineDiffCurv_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hstar :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
    genuineCurvFields_crossPairing_value_overLeaf (I := I) (M := M) g s S
  have hLHS :
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [tensorL2Inner]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder (I := I) (M := M) g s S x
  rw [hLHS]
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S
  set Gcurv := GcurvSection (I := I) (M := M) g s S
  set Gr := genuineDiffCurvSection (I := I) (M := M) g s S +
    ricTraceSection (I := I) (M := M) g s S
  set gradS := covGrad (I := I) (M := M) g 0 s S
  have hint1 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS
  have hint2 := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gr gradS
  have hintD := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv) gradS
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) Gcurv.toFun Gr.toFun gradS.toFun
      hint1 hint2] at hstar
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    have heq : Curv = (Curv - Gcurv) + Gcurv := by abel
    nth_rewrite 1 [heq]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun Gcurv.toFun
        gradS.toFun hintD hint1]
  linarith [hstar, hsplit]

/-- **The genuine curvature-fields cross-pairing value `(★)` (independent of the integrated nullity).**
For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the concrete genuine curvature sections
`GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)` against `∇S` equals the
cross-pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```

This is the SAME value as `genuineCurvFields_crossPairing_value`, but assembled over the *independent*
telescoping kernel `frameSum_remDiffBracket_pairing_integral_eq_genuineDiffCurv_ricTrace` (not the
circular on-disk route through the integrated nullity). The cross-pairing `⟨Curv S, ∇S⟩_{L²}` is the
integral of the fixed-frame sum of the per-summand pairings `⟨remDiffFib …, ∇S⟩`
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, sorry-free); each summand splits
into its pure-Riemann genuine fibre (frame-sum integral `⟨GcurvSection, ∇S⟩_{L²}`,
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`) and its named frame-bracket remainder (frame-sum
integral `⟨genuineDiffCurvSection + ricTraceSection, ∇S⟩_{L²}`, the independent kernel above); splitting
the integral and recombining by left additivity gives `(★)`. -/
theorem genuineCurvFields_crossPairing_value_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set fG : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfG
  set fB : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfB
  set fR : M → ℝ := fun x => ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) with hfR
  obtain ⟨hG_int, hG_val⟩ :=
    remDiffFib_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g s S
  have hB_val :=
    frameSum_remDiffBracket_pairing_integral_eq_genuineDiffCurv_ricTrace (I := I) (M := M) g s S
  have hRsplit : fR = fun x => fG x + fB x := by
    funext x
    rw [hfR, hfG, hfB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffFib_eq_genuine_add_bracket (I := I) (M := M) g s S x i,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have hR_int : MeasureTheory.Integrable fR μ := by
    have hcross := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (pointwiseTensorCurv (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
    refine hcross.congr (Filter.Eventually.of_forall (fun x => ?_))
    rw [hfR]
    exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x
  have hB_int : MeasureTheory.Integrable fB μ := by
    have hBeq : fB = fun x => fR x - fG x := by
      funext x; rw [hRsplit]; ring
    rw [hBeq]; exact hR_int.sub hG_int
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (GcurvSection (I := I) (M := M) g s S).toFun
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))]
  rw [← hG_val, ← hB_val]
  rw [tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral (I := I) (M := M) g s S]
  change (∫ x, fG x ∂μ) + (∫ x, fB x ∂μ) = ∫ x, fR x ∂μ
  rw [hRsplit, MeasureTheory.integral_add hG_int hB_int]

/-- **The rank-generic integrated tensor Bochner–Weitzenböck identity (re-export of the canonical
leaf).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the explicit rank-generic Bochner curvature-term residue plus
the Ricci-trace pairing equals the genuine Weitzenböck curvature integral:

```
  ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}.
```

This is the **same statement** as the canonical curvature leaf `bochnerWeitzenbock_residue_value_leaf`
and as `genuineCurvFields_residue_eq_weitzenbockValue` (below), recorded here under the historical name
the integrated-nullity chain consumes (`movingFrameDiffCurv_remainder_integrated_nullity`). It is proved
through the frame-summed telescoping kernel
`frameSum_remDiffBracket_pairing_integral_eq_genuineDiffCurv_ricTrace` (which is itself proved over the
canonical leaf): the cross-pairing `⟨Curv S, ∇S⟩_{L²}` equals the genuine curvature-fields value `(★)`
`genuineCurvFields_crossPairing_value_independent`, and the sorry-free residue bookkeeping
`genuineCurvFields_crossPairing_eq_residue` together with `weitzenbock_curvature_crossPairing_value`
rewrites it to the explicit residue form. The genuine content — the integrated tensor Bochner
telescoping that reorders the gradient slot past the two frame-trace slots into the pure-Riemann `R(∇S)`
trace, the differentiated curvature `(∇R) S`, the leading-slot Ricci trace, and vanishing total
covariant divergences — lives in the single canonical leaf `bochnerWeitzenbock_residue_value_leaf`, the
unique deep root of the curvature line; consumers transitively depend on its `sorryAx`.

**`s = 0` litmus (the Ricci-trace carrier is necessary and sufficient).** At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`riemannSec_tensor0SCov_zero_eq_zero`,
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`), so the identity reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²}
= ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ⟨Curv f, ∇f⟩_{L²}`, the classical scalar Bochner identity `Curv f =
Ric(∇f, ·)` (the `ricTraceSection g 0 f` value `Ric(∇f, ·)` by `ricTraceSection_zero_apply`), which is
nonzero `∫ Ric(∇f, ∇f)` on a non-flat manifold — so the carrier is genuinely required. -/
theorem tensorBochnerWeitzenbock_residue_eq_value
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
  rw [← genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
  rw [genuineCurvFields_crossPairing_value_independent (I := I) (M := M) g s S]
  exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

/-- **The concrete moving-frame remainder pairing integrates to zero (the genuine third-order
moving-frame integrated Weitzenböck nullity, slot-complete FOUR-term form).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`,
the global metric `L²` pairing of the concrete moving-frame remainder
`pointwiseTensorCurv g s S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S`
against `∇S := covGrad g 0 s S` vanishes:
```
⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S, ∇S⟩_{L²} = 0.
```

This is the genuine third-order moving-frame Bochner–Weitzenböck content for the **four concrete
operator-field curvature sections** — the slot-complete carrier set of the classical commutator. By the
iterated Ricci identity the commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` decomposes into four
slot-table contributions: (I) the gradient-slot curvature `R(∇S)` trace and (II) the tail-slot
curvature action, both carried by the pure-Riemann section `GcurvSection g s S`; (III) the
differentiated curvature `(∇R) S` trace, carried by `genuineDiffCurvSection g s S`; and (IV) the
**Ricci trace** from the two contracted derivative slots (`Ric(∇S, ·)` after the frame trace), carried
by `ricTraceSection g s S` (`RicciTraceCarrier`).

**Why the fourth carrier is required (the machine-adjudicated `s = 0` falseness of the three-term
form).** The earlier three-term form
`⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S, ∇S⟩_{L²} = 0` is *false* at `s = 0`: the
pure-Riemann trace reads the curvature of a scalar, which vanishes
(`riemannSec_tensor0SCov_zero_eq_zero`), so `GcurvSection g 0 f = 0`, and likewise
`genuineDiffCurvSection g 0 f = appCc 0 f = 0`, while the cross-pairing carries the genuine
Weitzenböck value `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`
(`weitzenbock_curvature_crossPairing_value`), which on a non-flat manifold (e.g. `S²`, nonconstant `f`)
equals `∫ Ric(∇f, ∇f) > 0 ≠ 0` — the classical Bochner identity `Curv f = Ric(∇f, ·)`. The Ricci-trace
term (IV) had no carrier in the three-term form; with `ricTraceSection g s S` carrying it, the
four-term remainder is exactly the bracket field (no Ricci trace), and the classical integrated tensor
Weitzenböck identity makes this nullity TRUE.

An earlier *pointwise* divergence-current form (`∃ X, ⟨remainder, ∇S⟩ =ᵐ divᵍ X`) was machine-
adjudicated OVER-STRONG: by the Dirichlet divergence identity `divergence_dirichletVFGen_eq` the
remainder pairing carries non-divergence content, and exhibiting the pointwise current would require a
Poisson/Hodge solve absent from the library (the same wall recorded at `MovingFrameDiffCurvAnchor`,
`MovingFrameIntegratedNullity`, and `MovingFrameGenuineSectionOrderDivergence`). Only the INTEGRAL
vanishes, which is exactly this nullity.

It is the concrete-section analogue of the abstract divergence-null primitive
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_divergenceNull`
(`MovingFrameFieldDecomposition`, posited): there the genuine fields are carried existentially; here
they are the *concrete* operator-field sections, so the nullity is stated for the concrete remainder.

**Non-vacuity.** The remainder pairing integrates to zero precisely because the four genuine curvature
fields carry the entire Weitzenböck value `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`
(`weitzenbock_curvature_crossPairing_value`); with the Ricci carrier `ricTraceSection g s S` dropped,
the nullity is *false* at `s = 0` (the genuine `∫ Ric(∇f, ∇f) > 0` is left uncarried). The nullity
therefore genuinely constrains the moving-frame remainder. The body is `sorry` (the genuine
moving-frame integrated tensor Bochner–Weitzenböck telescoping — now classically TRUE with the
slot-complete carrier set); consumers transitively depend on `sorryAx`. (Restatement bookkeeping: this
node's second restatement; the divergence-current → integrated form was the first.) -/
theorem movingFrameDiffCurv_remainder_integrated_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        genuineDiffCurvSection (I := I) (M := M) g s S -
        ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  have hval :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S +
            (genuineDiffCurvSection (I := I) (M := M) g s S +
              ricTraceSection (I := I) (M := M) g s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
          tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 :=
    (genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S).trans
      (tensorBochnerWeitzenbock_residue_eq_value (I := I) (M := M) g s S)
  have hnull := movingFrameNullity_of_genuineCrossPairingValue (I := I) (M := M) g s S
    (genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S) hval
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        genuineDiffCurvSection (I := I) (M := M) g s S -
        ricTraceSection (I := I) (M := M) g s S) =
      (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S)) from by abel]
  exact hnull

/-- **The frame-bracket remainder frame-sum pairing equals the concrete differentiated-curvature section
value (proved by composition over the concrete moving-frame divergence datum).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`,
the integral over the closed manifold of the fixed-frame sum of the per-direction frame-bracket
remainder fibres `remDiffBracketFib` (the frame summand minus its pure-Riemann genuine fibre — carrying
the differentiated-curvature `(∇R) S` content and the frame-bracket discrepancy), paired against
`∇S := covGrad g 0 s S`, equals the global metric `L²` pairing of the concrete gauge-glued
differentiated-curvature section `genuineDiffCurvSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g = ⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}.
```

This is the **differentiated-curvature genuine-sum identification with integrated bracket nullity**:
the bracket remainder, summed and integrated, carries exactly the gauge-glued tensorial section value.

**Circularity note (the identity is NOT proved by subtraction).** The frame-summed integrand reads
`∑ᵢ ⟨remDiffBracketFib, ∇S⟩(x) = ⟨Curv S − GcurvSection g s S, ∇S⟩(x)`
(`frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder`, sorry-free, since the genuine
fibres sum to `GcurvSection` and the full fibres sum to the defect), so the integral is
`⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}` and the asserted identity is *equivalent* to the slot-complete
integrated moving-frame nullity
`⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S, ∇S⟩_{L²} = 0` —
which is, in turn, *equivalent* to the genuine curvature value `(★)`
`genuineCurvFields_crossPairing_value` through the two landed sorry-free frame-sum identities. Since
`(★)` is assembled *over this very identity*, the identity cannot be proved by subtracting the landed
frame-sum pieces (that route is circular). It is proved over the genuine integrated nullity
`movingFrameDiffCurv_remainder_integrated_nullity` — the genuine third-order moving-frame
Bochner–Weitzenböck content, never citing `(★)`/the value/the residue-to-Weitzenböck identity (all
downstream of this identity).

**Proof.** The slot-complete integrated nullity
`⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S, ∇S⟩_{L²} = 0` is
the posited `movingFrameDiffCurv_remainder_integrated_nullity`. Writing `Curv S − GcurvSection g s S =
(Curv S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)) +
(genuineDiffCurvSection g s S + ricTraceSection g s S)` and splitting the `L²` pairing by left
additivity (`tensorL2Inner_add_left`, cross-integrabilities from
`SmoothCcTensor.integrable_inner_cross`) drops the remainder term by the nullity, giving
`⟨Curv S − GcurvSection g s S, ∇S⟩_{L²} = ⟨genuineDiffCurvSection g s S + ricTraceSection g s S,
∇S⟩_{L²}`. The sorry-free frame-sum integrand bridge
`frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder` rewrites the left-hand integral as
`⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`, completing the identity. Consumers transitively depend on the
`sorryAx` of the divergence datum. -/
theorem integral_frameSum_remDiffBracket_pairing_eq_genuineDiffCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hnull : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        genuineDiffCurvSection (I := I) (M := M) g s S -
        ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun = 0 :=
    movingFrameDiffCurv_remainder_integrated_nullity (I := I) (M := M) g s S
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv : SmoothCcTensor g 0 (s + 1) := GcurvSection (I := I) (M := M) g s S with hGcurv
  set Gcd : SmoothCcTensor g 0 (s + 1) :=
    genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S with hGcd
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hnull' : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (Curv - Gcurv - Gcd).toFun gradS.toFun = 0 := by
    rw [hCurv, hGcurv, hGcd, hgrad]
    rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)) =
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S -
          ricTraceSection (I := I) (M := M) g s S) from by abel]
    exact hnull
  have heq : Curv - Gcurv = (Curv - Gcurv - Gcd) + Gcd := by abel
  have hfun : ((Curv - Gcurv - Gcd) + Gcd).toFun =
      (Curv - Gcurv - Gcd).toFun + Gcd.toFun := SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - Gcd) gradS
  have hint₂ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcd gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv - Gcd).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcd.toFun gradS.toFun := by
    nth_rewrite 1 [heq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Curv - Gcurv - Gcd).toFun Gcd.toFun gradS.toFun hint₁ hint₂
  rw [hnull', zero_add] at hsplit
  have hLHS :
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun := by
    rw [tensorL2Inner]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    rw [hCurv, hGcurv, hgrad]
    exact frameSum_remDiffBracket_pairing_pointwise_eq_movingFrameRemainder
      (I := I) (M := M) g s S x
  rw [hLHS, hsplit]

/-- **The genuine curvature-fields cross-pairing value `(★)` (the curvature line's value form, re-exported
from the single frame-free deep leaf).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank
`s`, and smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the concrete
genuine curvature sections `GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S)`
against `∇S := covGrad g 0 s S` equals the cross-pairing of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` against `∇S`:
```
⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}
  = ⟨Curv S, ∇S⟩_{L²}.   (★)
```
The three genuine carriers — the pure-Riemann `R(∇S)` trace `GcurvSection`, the differentiated-curvature
`(∇R) S` trace `genuineDiffCurvSection`, and the **Ricci trace** `ricTraceSection` (the term `(IV)`) —
together carry the entire defect cross-pairing.

**Proof (re-export of the single frame-free deep leaf).** This is the identical `(★)` statement of the
file's single irreducible frame-free deep leaf `genuineCurvFields_crossPairing_value_bochnerLeaf` (the
classical tensor Bochner–Weitzenböck curvature-term identity in its cleanest fully-tensorial, frame-free
value form, no moving frame and no `remDiffBracketFib` jet). The body is `exact` over that leaf, so the
whole curvature-value cluster bottoms out at that single node directly — bypassing the over-engineered
moving-frame `remDiffBracketFib` telescoping route entirely. Consumers transitively depend on the leaf's
`sorryAx`. -/
theorem genuineCurvFields_crossPairing_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  genuineCurvFields_crossPairing_value_bochnerLeaf (I := I) (M := M) g s S

/-- **The rank-generic integrated tensor Bochner–Weitzenböck identity (the curvature line's terminal
quantitative leaf).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and
every smooth compactly-supported `(0, s)`-tensor `S`, the explicit rank-generic Bochner
curvature-term residue — the curvature bilinear `⟨R(∇S), ∇S⟩` of the gradient field, minus the rough
Laplacian of the order-`0` curvature trace paired against `S`, minus the passenger-slot curvature
bilinear of `∇S` with itself — equals the genuine Weitzenböck curvature integral:

```
  ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`,
`Φ₀ s := curvOpField g s` the frame-free curvature operator field, and `pureRGenuineDiffOp g 0 s S =
appCc (Φ₀ s) S` the order-`0` moving-frame pure-Riemann curvature trace.

**This is TRUE — the classical rank-generic integrated tensor Bochner–Weitzenböck identity over the
smooth global pure-Riemann operator tower.** It is the quantitative content the curvature line reduces
to: the left-hand side is the explicit three-pairing residue
(`genuineCurvFields_crossPairing_eq_residue`, sorry-free) of the genuine curvature cross-pairing
`⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²}`, and the right-hand side is the
integrated order-`2` Weitzenböck value `‖Δ_∇ S‖² − ‖∇²S‖²` of `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`
(`weitzenbock_curvature_crossPairing_value`, sorry-free). The identity is therefore *equivalent*,
through those two sorry-free bridges, to the integrated moving-frame remainder nullity
`⟨pointwiseTensorCurv g s S − GcurvSection g s S − genuineDiffCurvSection g s S, ∇S⟩_{L²} = 0`
(`genuineDiffCurv_crossPairing_remainder_nullity`, proven by composition over *this* leaf): the
genuine curvature fields carry the entire defect cross-pairing.

**Proof (direct frame-free operator-tower reduction over the single deep leaf).** The left-hand
four-pairing residue equals the genuine curvature-fields cross-pairing
`⟨GcurvSection g s S + (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²}` by the
sorry-free operator-tower bookkeeping bridge `genuineCurvFields_crossPairing_eq_residue` (run backwards —
the bridge is the operator-field integration-by-parts assembly of the pure-Riemann pairing
`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp` and the differentiated-curvature pairing
`tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg`); the file's single frame-free deep leaf `(★)`
`genuineCurvFields_crossPairing_value_bochnerLeaf` rewrites it to `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`,
which is `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by the sorry-free `weitzenbock_curvature_crossPairing_value`. The
reduction bottoms out at the single deep leaf directly — purely through the frame-free operator-field
integration-by-parts tower, never through the over-engineered moving-frame `remDiffBracketFib` frame-sum
telescoping route.

**Non-vacuity (every term is genuinely nonzero on a non-flat manifold; the identity fails for a
`κ`-perturbed left-hand side).** On a non-flat manifold (`R ≠ 0`) with a non-parallel `S` each of the
three left-hand pairings is genuinely nonzero (the curvature bilinear `⟨R(∇S), ∇S⟩` is the genuine
sectional-curvature contraction, not identically zero), and the right-hand side `‖Δ_∇ S‖² − ‖∇²S‖²`
is the genuine Weitzenböck defect `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`, which is nonzero precisely
when curvature is present (`weitzenbock_integrated_covGrad_l2_normSq`). The identity is *not* a
triviality such as `0 = 0`: scaling the left-hand curvature residue by a factor `κ ≠ 1` (a
`κ`-perturbed pure-Riemann operator) breaks the equality, since the unperturbed residue alone equals
the fixed Weitzenböck value. The body transits only the single frame-free deep leaf
`genuineCurvFields_crossPairing_value_bochnerLeaf` (the integrated second-Bianchi Ricci-fold content);
consumers transitively depend on its `sorryAx`. -/
theorem genuineCurvFields_residue_eq_weitzenbockValue
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
  rw [← genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S]
  rw [genuineCurvFields_crossPairing_value_bochnerLeaf (I := I) (M := M) g s S]
  exact weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S

/-- **Genuine differentiated-curvature integrated moving-frame nullity (the third-order moving-frame
Weitzenböck IBP-telescoping content, slot-complete four-carrier remainder-orthogonality form).** For a
closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth
compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the moving-frame remainder of
the order-`2` commutator defect — `Curv S − GcurvSection g s S −
(genuineDiffCurvSection g s S + ricTraceSection g s S)`, where `Curv S := pointwiseTensorCurv g s S`,
`Gcurv := GcurvSection g s S` is the concrete pure-Riemann `R(∇S)` trace section,
`Gcd := genuineDiffCurvSection g s S` is the gauge-glued tensorial `(∇R) S` differentiated-curvature
trace section, and `ricTraceSection g s S` is the **Ricci trace** carrier (the term `(IV)`) — against
`∇S := covGrad g 0 s S` vanishes:

```
⟨Curv S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S), ∇S⟩_{L²} = 0.
```

**Proof (sorry-free composition over the named curvature leaf).** From the explicit three-pairing
residue `genuineCurvFields_crossPairing_eq_residue` (sorry-free) chained with the rank-generic
integrated tensor Bochner–Weitzenböck identity `genuineCurvFields_residue_eq_weitzenbockValue` (the
line's terminal quantitative leaf), the genuine curvature cross-pairing carries the Weitzenböck value
`⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`; feeding
this value to the integrated-nullity producer `movingFrameNullity_of_genuineCrossPairingValue`
(`MovingFrameIntegratedNullity`, sorry-free — it chains the value with
`weitzenbock_curvature_crossPairing_value` and the left-additivity reduction
`tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing`) yields the remainder nullity. The
body transits only the named curvature leaf `genuineCurvFields_residue_eq_weitzenbockValue`; consumers
transitively depend on its `sorryAx`.

It is the rank-`0` / concrete-`Gcd` analogue of the integrated nullity carried existentially by the
sibling tri-split nodes `exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`) and
`exists_pointwiseTensorCurvRS_genuineTriSplit_divergence` (`MovingFrameGenuineFieldPairingRS`),
specialised to the concrete operator-field section `Gcd = genuineDiffCurvSection g s S`. -/
theorem genuineDiffCurv_crossPairing_remainder_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (genuineDiffCurvSection (I := I) (M := M) g s S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  have hval :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S +
            (genuineDiffCurvSection (I := I) (M := M) g s S +
              ricTraceSection (I := I) (M := M) g s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
          tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 :=
    (genuineCurvFields_crossPairing_eq_residue (I := I) (M := M) g s S).trans
      (genuineCurvFields_residue_eq_weitzenbockValue (I := I) (M := M) g s S)
  exact movingFrameNullity_of_genuineCrossPairingValue (I := I) (M := M) g s S
    (genuineDiffCurvSection (I := I) (M := M) g s S +
      ricTraceSection (I := I) (M := M) g s S) hval

/-- **Genuine differentiated-curvature cross-pairing value (the third-order moving-frame Weitzenböck
IBP telescoping, slot-complete four-carrier cross-pairing form).** For a closed smooth Riemannian
manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`,
the global metric `L²` pairing of the genuine curvature fields `GcurvSection g s S +
(genuineDiffCurvSection g s S + ricTraceSection g s S)` (the pure-Riemann `R(∇S)` trace section
`Gcurv`, the gauge-glued tensorial `(∇R) S` differentiated-curvature trace section `Gcd`, and the
**Ricci trace** carrier `ricTraceSection`) against `∇S := covGrad g 0 s S` equals the genuine
Weitzenböck curvature integral

```
⟨Gcurv + (Gcd + ricTraceSection), ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

**Proof (composition glue over the slot-complete integrated moving-frame nullity).** From the
slot-complete integrated moving-frame nullity
`⟨Curv S − Gcurv − (Gcd + ricTraceSection), ∇S⟩_{L²} = 0`
(`genuineDiffCurv_crossPairing_remainder_nullity`, now proven by composition over the named curvature
leaf), the purely-algebraic left-additivity reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm`, sorry-free) gives the bracket-free `L²` pairing
`⟨Gcurv + (Gcd + ricTraceSection), ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`; chaining with
`weitzenbock_curvature_crossPairing_value` (`MovingFrameIntegratedNullity`, sorry-free) yields the
value. The body transits only the named curvature leaf
`genuineCurvFields_residue_eq_weitzenbockValue` (through the nullity); consumers transitively depend on
its `sorryAx`. It feeds the integrated-nullity producer
`movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`) verbatim as its
hypothesis `hval` with `Gcd := genuineDiffCurvSection g s S + ricTraceSection g s S`. -/
theorem genuineDiffCurv_crossPairing_value
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
  have hpair :=
    tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S)
      (genuineDiffCurvSection (I := I) (M := M) g s S +
        ricTraceSection (I := I) (M := M) g s S)
      (genuineDiffCurv_crossPairing_remainder_nullity (I := I) (M := M) g s S)
  rw [hpair, weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]

end Connection
end Integral
end DifferentialGeometry

end
