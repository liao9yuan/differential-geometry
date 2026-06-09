import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP

/-!
# The frame-free curvature operator field and the differentiated-curvature operator-field identification

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this is the **most-upstream node**
of the rank-generic tensor Bochner–Weitzenböck curvature line. It homes the **frame-free curvature
operator field** `Φ₀ s := curvOpField g s` together with the single genuinely-irreducible
**differentiated-curvature operator-field identification** of the curvature line — the `(∇R) S` value
identity bridging the three concrete genuine curvature carriers to the integrated Weitzenböck Dirichlet
defect. Both are homed here, *above* the bracket-channel divergence-engine node
`BracketChannelEngineIdentification`, so the whole curvature line shares `curvOpField` and bottoms out at
this single clean classical value identity without any downstream forward reference.

* `curvOpField g s` — the fixed smooth `(s, s)`-operator field whose operator-field action recovers the
  order-`0` moving-frame pure-Riemann curvature endomorphism `pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W`
  (`exists_pureRGenuineDiffOp_base_appCc`). It is the curvature coefficient whose covariant derivative
  carries the differentiated-curvature `(∇R)` content; a pure `Classical.choose` definition with no
  downstream dependency, homed at the most-upstream curvature node so the whole curvature line shares it.

* `appCc_curvOpField_eq_pureRGenuineDiffOp` — the defining `Classical.choose` spec of `curvOpField`: the
  operator-field action of `Φ₀ s` on a smooth compactly-supported `(0, s)`-tensor `S` recovers the
  order-`0` moving-frame pure-Riemann curvature trace `pureRGenuineDiffOp g 0 s S`. This is the identity
  through which the differentiated operator field `covGrad (Φ₀ s)` and its passenger-slot extension
  `slotExtend (Φ₀ s)` are identified with the curvature-derivative content.

* `bochnerWeitzenbockCurvatureValue_diffCurvOpField_leaf` — the **differentiated-curvature operator-field
  value identification** (the curvature line's single irreducible genuine-math leaf, in its cleanest
  fully-tensorial frame-free operator-field value form). For every covariant rank `s` and smooth
  compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete genuine
  operator-field curvature carriers — the pure-Riemann `R(∇S)` trace `GcurvSection g s S`, the
  differentiated-curvature `(∇R) S` operator-field trace `appCc (covGrad g s s (Φ₀ s)) S`, and the
  leading-slot Ricci trace `ricTraceSection g s S` — against `∇S := covGrad g 0 s S` equals the genuine
  Weitzenböck curvature integral `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`:
  ```
  ⟨GcurvSection g s S + (appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S), ∇S⟩_{L²}
    = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}.
  ```
  This is the genuine new mathematical content of the entire rank-generic curvature line — the classical
  tensor Bochner–Weitzenböck curvature-term identity. By the iterated Ricci identity the order-`2`
  rough-Laplacian / covariant-gradient commutator defect's gradient-slot reordering produces (I) the
  pure-Riemann `R(∇S)` trace (the carrier `GcurvSection g s S`), (II) the differentiated curvature
  `(∇R) S` (the operator-field carrier `appCc (covGrad g s s (Φ₀ s)) S` — the integrated identification of
  the frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the carrier), and (III) the
  leading-slot Ricci trace (the second-Bianchi cyclic fold of the contracted slot into the raised Ricci
  endomorphism, the carrier `ricTraceSection g s S`), plus a residual `∇²S`-order frame-bracket
  discrepancy that is a total covariant divergence integrating to zero over the closed manifold.

  **Why the integrated value, not the pointwise per-direction match.** The differentiated-curvature trace
  `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its per-direction fibre realisation
  reads the `smoothExtensionTangent` jet of the frame direction (the slot-wise frame-traced Ricci/Bianchi
  fold `nablaTensorCurv_frame_trace_eq_nablaRicci`, `DifferentiatedSlotwiseCurvature`), which is
  chart-selection-unbounded on `S²` (T1) — so the `∇³S`-cancellation and divergence form are *false
  term-by-term*. Only the *summed, integrated* match is sound, and that sound integrated content is exactly
  this value identity. The integrated divergence-vanishing half is supplied by the frame-summed covariant
  integration-by-parts engine `integral_frameSummed_covDeriv_combined_eq_zero`
  (`MovingFrameIntegratedNullity`); the second-Bianchi Ricci fold by `nablaTensorCurv_frame_trace_eq_nablaRicci`
  / `contracted_second_bianchi`; but the three pieces are mathematically *coupled* (the per-direction
  differentiated-curvature trace differs from the operator-field carrier by exactly the bracket discrepancy
  of the third piece, which integrates to zero only when summed), so no one of them is a true
  free-standing integral identity — only their joint *integrated* value is sound, and that single joint
  value is this leaf. The identity is stated at the *integrated* frame-free `L²` level throughout — it
  never extracts a per-direction `M → E` quantity — so it is trap-screened. The body is `sorry` (the
  genuine classical coupled integrated curvature derivation); consumers transitively depend on `sorryAx`.

  **Non-vacuity (the `s = 0` Bochner litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann
  and differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the curvature of a scalar, which
  vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the empty curvature slot), so
  the value collapses to `⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)`
  — the classical scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
  `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
  Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes the value FALSE at
  `s = 0`, so the carrier is genuinely required and the identity is not vacuous (it fails for a
  `κ ≠ 1`-perturbed curvature residue).

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
open DifferentialGeometry.Integral.DivergenceTheorem
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

/-- **The differentiated-curvature operator-field value identification (the curvature line's single
irreducible genuine-math leaf, in its cleanest three-section operator-field value form).** For a closed
smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete genuine operator-field curvature
carriers — the pure-Riemann `R(∇S)` trace `GcurvSection g s S`, the differentiated-curvature `(∇R) S`
operator-field trace `appCc (covGrad g s s (Φ₀ s)) S` (`Φ₀ s := curvOpField g s`), and the leading-slot
Ricci trace `ricTraceSection g s S` — against `∇S := covGrad g 0 s S` equals the genuine Weitzenböck
curvature integral `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`:
```
⟨GcurvSection g s S + (appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S), ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

**This is the genuine new mathematical content of the entire rank-generic curvature line — the classical
tensor Bochner–Weitzenböck curvature-term identity, in its cleanest fully-tensorial frame-free
operator-field value form** (no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent` jet). By
the iterated Ricci identity the order-`2` rough-Laplacian / covariant-gradient commutator defect's
gradient-slot reordering produces (I) the pure-Riemann `R(∇S)` trace (the carrier `GcurvSection g s S`),
(II) the differentiated curvature `(∇R) S` (the operator-field carrier `appCc (covGrad g s s (Φ₀ s)) S`,
the coupled integrated identification of the frame-summed trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the
carrier), and (III) the leading-slot Ricci trace (the second-Bianchi cyclic fold of the contracted slot
into the raised Ricci endomorphism `ricTraceSection g s S`), plus a residual `∇²S`-order frame-bracket
discrepancy that is a total covariant divergence integrating to zero over the closed manifold.

**Why the integrated value, not the pointwise per-direction match.** The differentiated-curvature trace
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its per-direction fibre realisation reads
the `smoothExtensionTangent` jet of the frame direction (the slot-wise frame-traced Ricci/Bianchi fold
`nablaTensorCurv_frame_trace_eq_nablaRicci`, `DifferentiatedSlotwiseCurvature`, with the contracted second
Bianchi identity `contracted_second_bianchi`), which is chart-selection-unbounded on `S²` (T1) — so the
`∇³S`-cancellation and divergence form are *false term-by-term*. The integrated divergence-vanishing half
is supplied by the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`); but the three pieces
(II) / (III) / the gradient-slot bracket-discrepancy lift are mathematically *coupled* (the per-direction
differentiated-curvature trace differs from the operator-field carrier by exactly the bracket discrepancy
of the third piece, which integrates to zero only when summed), so no one of them is a true free-standing
integral identity — only their joint *integrated* value is sound, and that single joint value is this
leaf. The identity is stated at the *integrated* frame-free `L²` level throughout — it never extracts a
per-direction `M → E` quantity — so it is trap-screened. Over this single leaf the bracket-channel
divergence-engine identification `bracketChannelRemainder_integral_eq_diffCurvOpField_ricTrace`, the
frame-free residue root `bochnerWeitzenbockResidue_pureRForm_value_root`, the four-carrier nullity, and
every downstream cross-pairing node of `BracketChannelEngineIdentification` follow by sorry-free
operator-field integration-by-parts bookkeeping.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier — each carrier is necessary).** At
`s = 0` the pure-Riemann and differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the
curvature of a scalar, which vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the
empty curvature slot), so the value collapses to `⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} −
‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner–Lichnerowicz identity
(`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a
non-flat manifold. Dropping the Ricci-trace carrier (perturbing the curvature to flat, the degenerate
witness) makes the value FALSE at `s = 0`, so the carrier is genuinely required and the identity is not
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). The body is `sorry` (the genuine classical
coupled integrated curvature derivation: the differentiated-curvature operator-field identification, the
integrated second-Bianchi Ricci fold, and the gradient-slot bracket-discrepancy divergence-zero lift);
consumers transitively depend on `sorryAx`. -/
theorem bochnerWeitzenbockCurvatureValue_diffCurvOpField_leaf
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
  sorry

end Connection
end Integral
end DifferentialGeometry

end
