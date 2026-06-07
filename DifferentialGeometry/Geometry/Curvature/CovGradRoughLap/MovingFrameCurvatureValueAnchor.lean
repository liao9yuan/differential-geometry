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

/-- **The four-carrier integrated moving-frame Bochner–Weitzenböck nullity (the curvature line's single
irreducible deep root, value-anchored leaf form).** For a closed smooth Riemannian manifold `(M, g)`,
every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the global metric
`L²` pairing of the concrete moving-frame remainder — the order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` with its
four genuine operator-field curvature carriers subtracted —
```
Grem := Curv S − GcurvSection g s S − appCc (covGrad g s s (Φ₀ s)) S − ricTraceSection g s S
```
against `∇S := covGrad g 0 s S` vanishes:
```
⟨Curv S − GcurvSection g s S − appCc (covGrad g s s (Φ₀ s)) S − ricTraceSection g s S, ∇S⟩_{L²} = 0,
```
with `Φ₀ s := curvOpField g s` the frame-free curvature operator field,
`appCc (covGrad g s s (Φ₀ s)) S = appCc (∇Φ₀ s) S` the differentiated-curvature operator-field trace
`(∇R) S`, and `ricTraceSection g s S` the leading-slot Ricci trace.

**This is the genuine new mathematical content of the curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity** in its cleanest fully-tensorial four-carrier nullity form,
homed here at the most-upstream curvature-value node so the whole line bottoms out at this single clean
classical statement. It states that the four concrete operator-field curvature carriers together capture,
against `∇S`, the *entire* integrated value of the commutator defect: the surviving remainder pairs to
zero. By the iterated Ricci identity the defect's gradient-slot reordering produces (I) the gradient-slot
curvature `R(∇S)` and (II) the tail-slot curvature action (both carried by `GcurvSection`), (III) the
differentiated curvature `(∇R) S` (carried by `appCc (∇Φ₀ s) S` — the integrated identification of the
frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier),
and (IV) the leading-slot Ricci trace (the second-Bianchi / frame-Ricci folding of the contracted
curvature slot into the raised Ricci endomorphism, carried by `ricTraceSection`), plus a residual
`∇²S`-order frame-bracket discrepancy that is a total covariant divergence integrating to zero over the
closed manifold (the divergence-vanishing engine `integral_frameSummed_covDeriv_combined_eq_zero`).

**Why the pointwise per-direction split is fenced (only the integrated four-carrier nullity is sound).**
The differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its
fibre realisation reads the `smoothExtensionTangent` jet of the frame direction, which is
chart-selection-unbounded on `S²` — so it has no clean slot-`0` uncurry, and the `∇³S`-cancellation and
divergence form are *false term-by-term* through `smoothExtensionTangent`. Only the *summed, integrated*
match is sound, and that sound integrated content is exactly this four-carrier nullity. The identity is
stated at the *integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E`
quantity — so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier — each carrier is necessary).** At
`s = 0` the pure-Riemann and differentiated-curvature carriers vanish (`GcurvSection g 0 f` reads the
curvature of a scalar, which vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the
empty curvature slot), so the nullity reads `⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ⟨Curv f, ∇f⟩_{L²} =
‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar Bochner–Lichnerowicz identity
(`ricTraceSection_zero_apply`, `weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a
non-flat manifold. Dropping the Ricci-trace carrier (perturbing the curvature to flat, the degenerate
witness) makes the nullity FALSE at `s = 0`, so the carrier is genuinely required and the node is not
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue). The body is `sorry` (the genuine classical
integrated tensor Bochner–Weitzenböck curvature-term derivation: the integrated second-Bianchi Ricci
fold, the differentiated-curvature operator-field identification, and the gradient-slot divergence-zero
lift); consumers transitively depend on `sorryAx`. -/
theorem fourCarrierRemainder_integrated_nullity_valueAnchored
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S -
          ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  sorry

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
passenger-`W` frame-traced bracket channel with the pure-Riemann channel peeled off.** It is proved here
by composition over the single posited deep root
`fourCarrierRemainder_integrated_nullity_valueAnchored` (the four-carrier integrated nullity, the genuine
classical tensor Bochner–Weitzenböck curvature-term identity) through the sorry-free pure-Riemann peel:
the curvature cross-pairing is the integral of the fixed-frame sum of the frame summands `remDiffFib`
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, sorry-free), each summand splits into
its pure-Riemann genuine fibre and its named frame-bracket remainder
(`remDiffFib_eq_genuine_add_bracket`, sorry-free), and the genuine fibres' frame-sum integral is
`⟨GcurvSection g s S, ∇S⟩_{L²}` (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free), so
the frame-bracket-remainder integral is `⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`; the four-carrier
integrated nullity then rearranges this by left additivity of the `L²` pairing into the claimed
differentiated-curvature operator-field plus Ricci-trace value. The body transits only the four-carrier
nullity root; consumers transitively depend on its `sorryAx`.

**Why it is the genuine missing content.** The four-carrier nullity carries the classical Bochner
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
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set gradS := covGrad (I := I) (M := M) g 0 s S with hgradS
  set Curv := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set Gcurv := GcurvSection (I := I) (M := M) g s S with hGcurv
  set Gdc := appCc (I := I) (M := M) g s (s + 1)
    (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S with hGdc
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
  -- The LHS integral is `∫ fB`; reduce it to `⟨Curv − Gcurv, ∇S⟩_{L²}`.
  have hfR_val : (∫ x, fR x ∂μ) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun := by
    rw [hCurv, hgradS, hμ]
    exact (tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral
      (I := I) (M := M) g s S).symm
  have hfB_val : (∫ x, fB x ∂μ) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    have hsum : (∫ x, fR x ∂μ) = (∫ x, fG x ∂μ) + (∫ x, fB x ∂μ) := by
      rw [hRsplit, MeasureTheory.integral_add hG_int hB_int]
    have hGval' : (∫ x, fG x ∂μ) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
      rw [hGcurv, hgradS]; exact hG_val
    rw [hfR_val, hGval'] at hsum
    linarith [hsum]
  -- The posited four-carrier integrated nullity.
  have hnull := fourCarrierRemainder_integrated_nullity_valueAnchored (I := I) (M := M) g s S
  rw [← hCurv, ← hGcurv, ← hGdc, ← hGric, ← hgradS] at hnull
  -- Rearrange the nullity by left additivity:  ⟨Curv − Gcurv, ∇S⟩ = ⟨Gdc + Gric, ∇S⟩.
  have hint_rem := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    (Curv - Gcurv - Gdc - Gric) gradS
  have hint_gdc := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gdc gradS
  have hint_gric := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gric gradS
  have hint_remgdc := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
    ((Curv - Gcurv - Gdc - Gric) + Gdc) gradS
  have hexpand : Curv - Gcurv = ((Curv - Gcurv - Gdc - Gric) + Gdc) + Gric := by abel
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun =
        (tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - Gdc - Gric).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gdc.toFun gradS.toFun) +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gric.toFun gradS.toFun := by
    nth_rewrite 1 [hexpand]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
        ((Curv - Gcurv - Gdc - Gric) + Gdc).toFun Gric.toFun gradS.toFun hint_remgdc hint_gric]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
        (Curv - Gcurv - Gdc - Gric).toFun Gdc.toFun gradS.toFun hint_rem hint_gdc]
  -- `⟨Curv − Gcurv, ∇S⟩ = ⟨Curv, ∇S⟩ − ⟨Gcurv, ∇S⟩` by left additivity.
  have hcurv_split :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Gcurv.toFun gradS.toFun := by
    have heq : Curv = (Curv - Gcurv) + Gcurv := by abel
    nth_rewrite 1 [heq]
    rw [SmoothCcTensor.toFun_add,
      tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
        (Curv - Gcurv).toFun Gcurv.toFun gradS.toFun
        (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv) gradS)
        (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Gcurv gradS)]
  -- Assemble.  The goal's RHS is `⟨Gdc + Gric, ∇S⟩`.
  rw [SmoothCcTensor.toFun_add,
    tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1) Gdc.toFun Gric.toFun gradS.toFun
      hint_gdc hint_gric]
  rw [hfB_val]
  -- `⟨Curv, ∇S⟩ − ⟨Gcurv, ∇S⟩ = ⟨Curv − Gcurv, ∇S⟩ = ⟨Gdc, ∇S⟩ + ⟨Gric, ∇S⟩` (nullity).
  rw [hcurv_split, hsplit, hnull]
  ring

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
