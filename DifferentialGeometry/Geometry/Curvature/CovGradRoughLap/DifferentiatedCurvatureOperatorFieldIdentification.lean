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
  free-standing integral identity — only their joint *integrated* value is sound. The identity is stated at
  the *integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E` quantity —
  so it is trap-screened. It is proved sorry-free over the moving-frame remainder nullity
  `movingFrameNullity_diffCurvOpField_leaf` (the three-section carrier's remainder is `L²`-orthogonal to
  `∇S`), which is itself proved sorry-free over the single strictly-smaller bracket-channel deep root
  `bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace` by the sorry-free pure-Riemann genuine-sum
  identification and left additivity of the `L²` pairing; consumers transitively depend on that root's
  `sorryAx`.

* `bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace` — the **bracket-channel integrated deep
  root** (the curvature line's single irreducible genuine content, in its strictly-smaller form). The
  integral of the fixed-frame sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib`
  against `∇S` equals `⟨appCc (∇Φ₀ s) S + ricTraceSection g s S, ∇S⟩_{L²}` — the differentiated-curvature
  operator-field trace `(∇R) S` plus the leading-slot Ricci trace, the bracket channel with the
  pure-Riemann channel peeled off. Its content is the coupled (i) frame-summed differentiated-curvature
  trace = operator-field carrier identification, (ii) second-Bianchi Ricci fold, and (iii) bracket
  discrepancy = total covariant divergence → 0. The body is `sorry` (the genuine classical coupled
  integrated bracket channel, sound only under the integral by T1); consumers transitively depend on
  `sorryAx`.

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

/-- **The frame-bracket remainder frame-sum integral carries the differentiated-curvature operator-field
trace plus the leading-slot Ricci trace (the curvature line's single irreducible integrated deep root, in
its strictly-smaller bracket-channel form).** For a closed smooth Riemannian manifold `(M, g)`, every
covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the integral over the closed
manifold of the fixed-frame sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib`
(the frame summand `remDiffFib` minus its pure-Riemann genuine curvature fibre `remDiffGenuineFib`,
`MovingFrameRemainderFrameSumBridge`), paired against `∇S := covGrad g 0 s S`, equals the global metric
`L²` pairing of the differentiated-curvature operator-field trace `appCc (∇Φ₀ s) S` (the `(∇R) S` field,
`∇Φ₀ s := covGrad g s s (curvOpField g s)`) plus the leading-slot Ricci-trace carrier `ricTraceSection g s
S` against `∇S`:

```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine, strictly-smaller, irreducible integrated content of the entire curvature line — the
bracket channel with the pure-Riemann channel peeled off.** The moving-frame remainder nullity
`movingFrameNullity_diffCurvOpField_leaf` (and through it the operator-field value leaf
`bochnerWeitzenbockCurvatureValue_diffCurvOpField_leaf`) is proved *sorry-free over this node* (below) by
the sorry-free pure-Riemann genuine-sum identification (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`,
the gradient-slot channel is `L²`-sound) and left additivity of the `L²` pairing. The genuine three-fold
integrated content this node carries is (i) the identification of the frame-summed differentiated-curvature
trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier `appCc (∇Φ₀ s) S` (the operator-field
B-rule, `OperatorFieldPairingIBP`), (ii) the second-Bianchi / frame-Ricci cyclic fold of the contracted
slot into the raised Ricci endomorphism `ricTraceSection g s S` (`ContractedBianchi`,
`DifferentiatedSlotwiseCurvature`), and (iii) the residual frame-bracket discrepancy being a total
covariant divergence integrating to zero over the closed manifold (`integral_frameSummed_covDeriv_combined_eq_zero`,
`BracketDivergenceForm`). The differentiated-curvature trace is non-tensorial in the direction (its
per-direction fibre reads the `smoothExtensionTangent` jet, chart-selection-unbounded on `S²`, T1) — so the
identity is sound only at the *summed, integrated* `L²` level; it never extracts a per-direction `M → E`
quantity, so it is trap-screened. The body is `sorry` (the genuine classical coupled integrated bracket
channel); consumers transitively depend on `sorryAx`.

**`s = 0` litmus (the Ricci-trace carrier is necessary).** At `s = 0` the differentiated-curvature carrier
vanishes (`appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator on the empty curvature slot), so the
identity collapses to `∫_M ∑ᵢ ⟨remDiffBracketFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} =
∫ Ric(∇f, ∇f)` — the classical scalar Bochner–Lichnerowicz identity, genuinely nonzero on a non-flat
manifold; dropping the Ricci-trace carrier (the degenerate witness) makes it FALSE, so the carrier is
genuinely required and the node is not vacuous. -/
theorem bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace
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

/-- **The moving-frame remainder nullity for the three-section differentiated-curvature operator-field
carrier (the genuine integrated Bochner–Weitzenböck content).** For a closed smooth Riemannian manifold
`(M, g)`, every covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the global
metric `L²` pairing of the moving-frame remainder

```
Curv S − GcurvSection g s S − (appCc g s (s+1) (∇(Φ₀ s)) S + ricTraceSection g s S)
```

(`Curv S := pointwiseTensorCurv g s S`, the order-`2` rough-Laplacian / covariant-gradient commutator
defect; `Φ₀ s := curvOpField g s`, the differentiated-curvature operator field; `∇(Φ₀ s) := covGrad g s s
(Φ₀ s)`) against `∇S := covGrad g 0 s S` vanishes:

```
⟨Curv S − GcurvSection g s S − (appCc g s (s+1) (∇(Φ₀ s)) S + ricTraceSection g s S), ∇S⟩_{L²} = 0.
```

This is the genuine content the operator-field value leaf
`bochnerWeitzenbockCurvatureValue_diffCurvOpField_leaf` consumes: the moving-frame remainder of the
three-section carrier `Gcd := appCc g s (s+1) (∇(Φ₀ s)) S + ricTraceSection g s S` is `L²`-orthogonal to
`∇S`. It is the genuine classical coupled integrated Bochner–Weitzenböck derivation — the frame-summed
differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` equals the operator-field carrier `appCc g s (s+1)
(∇(Φ₀ s)) S` (integrated identification), the second-Bianchi cyclic fold contributes the raised Ricci
endomorphism `ricTraceSection g s S`, and the residual frame-bracket discrepancy is a total covariant
divergence integrating to zero over the closed manifold. The per-direction differentiated-curvature trace
is non-tensorial (it reads the `smoothExtensionTangent` frame jet, chart-selection-unbounded on `S²`, T1),
so the identity is sound only at the *summed, integrated* `L²` level — it never extracts a per-direction
`M → E` quantity.

**Proof (sorry-free reduction to the strictly-smaller bracket-channel root).** The curvature
cross-pairing `⟨Curv S, ∇S⟩_{L²}` is the integral of the fixed-frame sum of the per-summand pairings
`∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩` (`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`,
sorry-free); each summand splits into its pure-Riemann genuine fibre and its frame-bracket remainder fibre
(`remDiffFib_eq_genuine_add_bracket`, sorry-free). The genuine frame-sum integral is `⟨GcurvSection g s S,
∇S⟩_{L²}` (`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free, the `L²`-sound pure-`R`
channel) and the bracket frame-sum integral is `⟨appCc (∇Φ₀ s) S + ricTraceSection g s S, ∇S⟩_{L²}` by the
bracket-channel root `bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace` (the single irreducible
deep root above). Subtracting both carriers from `⟨Curv S, ∇S⟩_{L²}` by left additivity of the `L²`
pairing (`tensorL2Inner_add_left`, the cross-integrabilities `SmoothCcTensor.integrable_inner_cross`)
leaves zero. The body transits only the bracket-channel root; consumers transitively depend on its
`sorryAx`. -/
theorem movingFrameNullity_diffCurvOpField_leaf
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          (appCc (I := I) (M := M) g s (s + 1)
              (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
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
    bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace (I := I) (M := M) g s S
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
  set Gcd := appCc (I := I) (M := M) g s (s + 1)
      (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
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
        (appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
          ricTraceSection (I := I) (M := M) g s S)) = Curv - Gcurv - Gcd from rfl]
  have hgoal : tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Curv - Gcurv - Gcd).toFun gradS.toFun =
      (∫ x, fR x ∂μ) - (∫ x, fG x ∂μ) - (∫ x, fB x ∂μ) := by
    rw [← hcurv_eq, ← hgcurv_eq, ← hgcd_eq]; linarith [hsplit2]
  rw [hgoal, hRsplit, MeasureTheory.integral_add hG_int hB_int]
  ring

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
value. The identity is stated at the *integrated* frame-free `L²` level throughout — it never extracts a
per-direction `M → E` quantity — so it is trap-screened. Over this value the bracket-channel
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
vacuous (it fails for a `κ ≠ 1`-perturbed curvature residue).

**Proof (sorry-free reduction to the moving-frame remainder nullity).** The moving-frame remainder
nullity `movingFrameNullity_diffCurvOpField_leaf` (the three-section carrier's remainder is `L²`-orthogonal
to `∇S`) gives, through the sorry-free left-additivity bracket-free reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm`), the bracket-free pairing `⟨GcurvSection g s S + (appCc (∇Φ₀ s) S +
ricTraceSection g s S), ∇S⟩_{L²} = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`, which the sorry-free Weitzenböck
value `weitzenbock_curvature_crossPairing_value` (`MovingFrameIntegratedNullity`) rewrites as
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`. The genuine integrated curvature content (the differentiated-curvature
operator-field identification, the integrated second-Bianchi Ricci fold, and the gradient-slot
bracket-discrepancy divergence-zero lift) lives in the single strictly-smaller bracket-channel deep root
`bracketChannelFrameSum_integral_eq_diffCurvOpField_ricTrace` (above), which the nullity transits;
consumers transitively depend on its `sorryAx`. -/
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
  have hpair :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S +
            (appCc (I := I) (M := M) g s (s + 1)
                (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
              ricTraceSection (I := I) (M := M) g s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
    tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S)
      (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
        ricTraceSection (I := I) (M := M) g s S)
      (movingFrameNullity_diffCurvOpField_leaf (I := I) (M := M) g s S)
  rw [hpair, weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]

end Connection
end Integral
end DifferentialGeometry

end
