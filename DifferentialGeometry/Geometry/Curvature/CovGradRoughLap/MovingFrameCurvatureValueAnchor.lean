import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

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

/-- **Posited genuine differentiated-curvature identification (the curvature line's single irreducible
deep root, strictly-smaller bracket-channel form).** For a closed smooth Riemannian manifold `(M, g)`,
every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the integral over the
closed manifold of the fixed-frame sum of the per-direction frame-bracket remainder fibres
`remDiffBracketFib` (the frame summand `remDiffFib` minus its pure-Riemann genuine curvature fibre
`remDiffGenuineFib`, `MovingFrameRemainderFrameSumBridge`), paired against `∇S := covGrad g 0 s S`, equals
the global metric `L²` pairing of the differentiated-curvature operator-field trace
`appCc (∇Φ₀ s) S` (the `(∇R) S` field, `∇Φ₀ s := covGrad g s s (curvOpField g s)`) plus the leading-slot
Ricci-trace carrier `ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine, strictly-smaller, irreducible integrated content of the whole curvature line — the
passenger-`W` frame-traced bracket channel with the pure-Riemann channel peeled off.** It is posited here
at the most-upstream curvature-value node so the integrated tensor Bochner–Weitzenböck value
`curvatureValue_genuineFields_eq_weitzenbock` (and, downstream, every cross-pairing leaf of the
moving-frame spine) is proved by composition over it through the sorry-free residue bookkeeping below: the
pure-Riemann `R(∇S)` cross-pairing splits off
(`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`,
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`,
`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, all sorry-free), the
differentiated-curvature operator-field pairing is rearranged through the genuine integration-by-parts
identity `tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (the operator-field B-rule, sorry-free), and the
integrated order-`2` Weitzenböck value `weitzenbock_curvature_crossPairing_value` (sorry-free) supplies the
spectral right-hand side.

**Why it is the genuine missing content.** It carries the classical Bochner technique that has no sorry-free
bridge: the identification of the frame-summed differentiated curvature `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the
operator-field carrier `appCc (∇Φ₀) S`, the second-Bianchi / frame-Ricci folding of the leading slot into
`ricTraceSection`, and the gradient-slot bracket discrepancy integrating to zero over the closed manifold.
The differentiated-curvature trace is **non-tensorial in the direction** — its per-direction fibre reading
uses the `smoothExtensionTangent` jet, which is chart-selection-unbounded on `S²` — so the per-direction
split and divergence form are *false term-by-term*; only the *summed, integrated* match is sound, and that
sound integrated content is exactly this identity. The identity is stated at the *integrated* frame-free
`L²` level throughout (it never extracts a per-direction `M → E` quantity), so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on
the empty curvature slot, the curvature of a scalar), so the identity collapses to
`∫_M ∑ᵢ ⟨remDiffBracketFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the classical
scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes the identity FALSE at
`s = 0`, so the carrier is genuinely required and the node is not vacuous. The body is `sorry` (the genuine
classical integrated derivation: the differentiated-curvature operator-field identification, the integrated
second-Bianchi Ricci fold, and the gradient-slot divergence-zero lift); consumers transitively depend on
`sorryAx`. -/
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
  sorry

/-- **The integrated tensor Bochner–Weitzenböck curvature-term residue value (frame-free operator-field
form), proved by composition over the bracket-channel root.** For a closed smooth Riemannian manifold
`(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the explicit
four-pairing curvature residue — the gradient-field pure-Riemann curvature bilinear, the rough Laplacian of
the order-`0` curvature trace against `S`, the passenger-slot curvature bilinear, and the leading-slot
Ricci-trace pairing — equals the genuine Weitzenböck curvature integral
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`. The reduction peels off the pure-Riemann `R(∇S)` channel and the
operator-field integration-by-parts bookkeeping sorry-free, leaving the entire non-pure-Riemann curvature
anatomy in the single posited bracket-channel root
`frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace`. (This mirrors the frame-free residue
identity that the downstream spine `BracketDiscrepancyNullity` records, hoisted here to the most-upstream
curvature-value node so this file is the line's single deep root.) -/
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
  rw [hGval', frameBracketRemainder_integral_eq_diffCurvOpField_ricTrace (I := I) (M := M) g s S]
  rw [← tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  have hIBP := tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g s
    (curvOpField (I := I) (M := M) g s) S
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
      (ricTraceSection (I := I) (M := M) g s S).toFun gradS.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) _ gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) _ gradS)]
  rw [hIBP]
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S := by
    have := appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
    simpa using this
  rw [hbase, hgradS]
  simp only [Nat.add_zero]
  ring

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
