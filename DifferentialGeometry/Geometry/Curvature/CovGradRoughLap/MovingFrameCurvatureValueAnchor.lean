import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity

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
  Weitzenböck Dirichlet defect `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`. This is the genuine classical content;
  it is posited here as the explicit honest leaf so the four-carrier integrated nullity
  `fourCarrierMovingFrameRemainder_integrated_nullity` (`BracketDiscrepancyNullity`) is proved by
  composition over it through the sorry-free integrated-nullity producer
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
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). The body is `sorry` (the genuine classical
integrated tensor Bochner–Weitzenböck curvature-term derivation: the integrated second-Bianchi Ricci
fold and the differentiated-curvature operator-field identification, sound only under the integral);
consumers transitively depend on `sorryAx`. -/
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
  sorry

end Connection
end Integral
end DifferentialGeometry

end
