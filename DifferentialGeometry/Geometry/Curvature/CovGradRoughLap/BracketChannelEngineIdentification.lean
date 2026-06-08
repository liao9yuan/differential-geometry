import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The frame-free curvature operator field and the bracket-channel divergence-engine identification

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this is the most-upstream node
of the rank-generic tensor Bochner–Weitzenböck curvature line. It homes the **frame-free curvature
operator field** `Φ₀ s := curvOpField g s` and the single genuinely-irreducible **bracket-channel
divergence-engine identification**: the integral over the closed manifold of the fixed-frame sum of the
per-direction frame-bracket remainder fibres `remDiffBracketFib` (the frame summand `remDiffFib` minus its
pure-Riemann genuine curvature fibre `remDiffGenuineFib`), paired against `∇S := covGrad g 0 s S`, carries
exactly the differentiated-curvature operator-field trace plus the leading-slot Ricci trace.

* `curvOpField g s` — the fixed smooth `(s, s)`-operator field whose operator-field action recovers the
  order-`0` moving-frame pure-Riemann curvature endomorphism `pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W`
  (`exists_pureRGenuineDiffOp_base_appCc`). It is the curvature coefficient whose covariant derivative
  carries the differentiated-curvature `(∇R)` content; a pure `Classical.choose` definition with no
  downstream dependency, homed here so the whole curvature line shares it without a forward reference into
  the downstream moving-frame value anchor.

* `bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace` — the **bracket-channel divergence-engine
  identification** (the curvature line's single irreducible deep leaf). It is the strictly-smaller,
  passenger-`W` frame-traced bracket channel with the pure-`R` channel peeled off sorry-free: the genuine
  classical Bochner technique that has no sorry-free bridge — the integrated identification of the
  frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier
  `appCc (covGrad g s s (Φ₀ s)) S`, the second-Bianchi cyclic fold of the leading slot into the raised
  Ricci endomorphism, and the gradient-slot `∇²S`-order bracket discrepancy integrating to zero over the
  closed manifold. It is the upstream-homed, divergence-engine-justified leaf over which the downstream
  value anchor's genuine cross-pairing value `(★)` is proved by composition; it is proved bottom-up from
  the frame-summed covariant divergence engine, NOT from the downstream value `(★)`, so the architectural
  circle is never re-entered.

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
content. It is a pure `Classical.choose` definition (no downstream dependency), homed at the most-upstream
curvature node so the curvature line shares it. -/
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

/-- **The bracket-channel divergence-engine identification (the curvature line's single irreducible deep
leaf, the strictly-smaller bracket-channel form — the genuine classical leaf, homed at the most-upstream
curvature node).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every
smooth compactly-supported `(0, s)`-tensor `S`, the integral over the closed manifold of the fixed-frame
sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib` (the frame summand
`remDiffFib` minus its pure-Riemann genuine curvature fibre `remDiffGenuineFib`,
`MovingFrameRemainderFrameSumBridge`), paired against `∇S := covGrad g 0 s S`, equals the global metric
`L²` pairing of the differentiated-curvature operator-field trace `appCc (covGrad g s s (Φ₀ s)) S` (the
`(∇R) S` field, `Φ₀ s := curvOpField g s`) plus the leading-slot Ricci-trace carrier `ricTraceSection g s
S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine new mathematical content of the entire curvature line — the single irreducible
integrated tensor Bochner–Weitzenböck curvature-identity root, the strictly-smaller passenger-`W` bracket
channel with the pure-`R` channel peeled off sorry-free.** The pure-Riemann genuine fibre frame-sum is
already identified sorry-free (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, the `L²`-sound
pure-`R` trace summing to `GcurvSection`), and the curvature cross-pairing splits sorry-free into the
genuine and bracket frame-sum integrands
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, `remDiffFib_eq_genuine_add_bracket`), so
the *entire* curvature anatomy that is not pure-`R` lives in this passenger-`W` frame-traced bracket
channel. It is the verbatim statement (with the carrier `appCc (covGrad g s s (Φ₀ s)) S` `defeq` to the
downstream value anchor's `diffCurvOpFieldSection g s S`) of the value anchor's
`frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace` and of the moving-frame spine's
`remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace`, here hoisted to the most-upstream curvature
node so that node's genuine cross-pairing value `(★)` is proved by composition over this single integrated
identity plus the sorry-free pure-`R` peel — and so the architectural circle is never re-entered.

**The three-fold genuine content it carries (proved bottom-up from the divergence engine, never from the
downstream value `(★)`).** Pointwise each frame summand `remDiffFib g s S x i` is the gradient-slot
reordering of the three covariant slots; subtracting the pure-Riemann genuine fibre `remDiffGenuineFib g s
S x i` leaves the frame-bracket remainder, which carries threefold genuine content, sound only after
frame-summing and integrating:
(i) the integrated identification of the frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·)
S)` with the operator-field carrier `appCc (covGrad g s s (Φ₀ s)) S` — *false pointwise per-direction*
(the `smoothExtensionTangent` direction reading is chart-selection-unbounded on `S²`), sound only
integrated;
(ii) the second-Bianchi cyclic fold of the contracted-curvature slot into the raised Ricci endomorphism
`ricEndoRaisedFib = ricTraceSection` (`ricEndoRaisedFib_inner_eq_frame_trace`,
`second_bianchi_levi_civita_metric`, `ricTraceSection_apply_leadingSlot`, `contracted_second_bianchi` are
the pointwise pieces); and
(iii) the gradient-slot lift exhibiting the surviving `∇²S`-order bracket discrepancy
(`tensor3rdCurvBracket`) as a total covariant divergence integrating to zero over the closed manifold (the
frame-summed covariant divergence engine `integral_frameSummed_covDeriv_combined_eq_zero` /
`integral_frameSummed_bracketCovDeriv_combined_eq_zero`, with the gradient-slot channel `L²`-orthogonal
`gradSlotCurv_pairing_covGrad_eq_zero`).
These three are mathematically *coupled* and sound only summed-and-integrated; the per-direction
differentiated-curvature trace differs from the operator-field carrier by exactly the bracket discrepancy
of (iii), which integrates to zero only when summed, so no one of (i)/(ii)/(iii) is a true free-standing
integral identity; only their joint *integrated* value is sound. The identity is stated at the
*integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E` quantity (which
would be chart-selection-unbounded; T1) — so it is trap-screened. The body is `sorry` (the genuine
classical integrated tensor Bochner–Weitzenböck curvature-term derivation: the integrated second-Bianchi
Ricci fold, the differentiated-curvature operator-field identification, and the gradient-slot
divergence-zero lift, all over the frame-summed covariant divergence engine); consumers transitively
depend on `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on
the empty curvature slot, the curvature of a scalar), so the identity collapses to
`∫_M ∑ᵢ ⟨remDiffBracketFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the classical
scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes the identity FALSE at
`s = 0`, so the carrier is genuinely required and the node is not vacuous (it fails for a `κ ≠ 1`-perturbed
curvature residue). -/
theorem bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace
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
  sorry

end Connection
end Integral
end DifferentialGeometry

end
