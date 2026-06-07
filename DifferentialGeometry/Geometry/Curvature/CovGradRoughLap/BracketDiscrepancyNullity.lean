import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The frame-free curvature operator field, the frame-bracket divergence nullity, and the integrated
tensor Bochner–Weitzenböck curvature-term residue (the curvature line's single irreducible deep root)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this upstream file homes three
pieces of the third-order tensor Bochner–Weitzenböck curvature line, *above* the moving-frame
differentiated-curvature spine `MovingFrameDiffCurvTraceSection`:

* `curvOpField g s` — the **frame-free curvature operator field** `Φ₀ s`, the fixed smooth
  `(s, s)`-operator field whose operator-field action recovers the order-`0` moving-frame pure-Riemann
  curvature endomorphism `pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W` (`exists_pureRGenuineDiffOp_base_appCc`).
  It is the curvature coefficient whose covariant derivative carries the differentiated-curvature `(∇R)`
  content; it is a pure `Classical.choose` definition with no downstream dependency, so it is homed here
  for the curvature line to share.

* `frameBracket_combined_divergence_integral_eq_zero` — the **frame-summed frame-bracket covariant
  Green nullity**: for any two `g_x`-orthonormal-frame-bracket-indexed families of direction fields and
  once-derived tensors, the frame-summed covariant Leibniz combination
  `∑ᵢ ∫ ( ⟨∇_{Vᵢ}(Wᵢ), Z⟩ + ⟨Wᵢ, ∇_{Vᵢ} Z⟩ + ⟨Wᵢ, Z⟩ · divᵍ Vᵢ )` integrates to zero. This is the
  *honest* divergence-vanishing content underneath the frame-bracket discrepancy
  `tensor3rdCurvBracket = ∑ᵢ [ ∇_{[Bᵢ,W]}(∇_{Bᵢ}T) + ∇_{Bᵢ}(∇_{[Bᵢ,W]}T) ]`: paired against `∇S` and
  integrated, the bracket discrepancy is the *first slot* `∑ᵢ ⟨∇_{Vᵢ}(Wᵢ), ∇S⟩` of this combination, so
  it equals the negative of the IBP-partner terms — a total covariant divergence whose integral over the
  closed boundaryless manifold vanishes (it is *not* zero by itself; only the full Green combination is).
  It is the frame-bracket reading of the divergence engine `integral_frameSummed_covDeriv_combined_eq_zero`
  (`MovingFrameIntegratedNullity`).

* `bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace` — the **strictly-smaller bracket-channel
  integrated root** (the genuine missing content). The integral of the fixed-frame sum of the
  frame-bracket remainder fibres `remDiffBracketFib` (the frame summand `remDiffFib` minus its pure-Riemann
  genuine fibre), paired against `∇S`, equals `⟨appCc (∇Φ₀ s) S + ricTraceSection g s S, ∇S⟩_{L²}` — the
  differentiated-curvature operator-field trace `(∇R) S` plus the leading-slot Ricci trace. This is the
  bracket channel with the pure-Riemann channel peeled off: the identification of the frame-summed
  differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier `appCc (∇Φ₀) S`,
  the second-Bianchi / frame-Ricci fold into `ricTraceSection`, and the gradient-slot bracket discrepancy
  integrating to zero. The differentiated-curvature trace is **non-tensorial** in the direction
  (`smoothExtensionTangent` chart-selection-unbounded on `S²`), so only the *summed, integrated* match is
  sound; the genuine identification requires the non-tensorial differentiated-curvature anchor
  (`MovingFrameDiffCurvAnchor`, `MovingFrameDifferentiatedCurvatureSection`) and has no sorry-free bridge
  below this file. The body is `sorry` (the genuine classical derivation); consumers transitively depend
  on `sorryAx`.

* `bochnerWeitzenbockResidue_frameFree_value` — the **integrated tensor Bochner–Weitzenböck
  curvature-term residue identity**, the curvature line's deep root, in its cleanest fully-tensorial
  *frame-free* operator-field form (no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent`):
  ```
    ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
      − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
      − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
      + ⟨ricTraceSection g s S, ∇S⟩_{L²}
    = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}.
  ```
  This is proven **sorry-free by reduction to the bracket-channel root above**: the integrated order-`2`
  Weitzenböck value `weitzenbock_curvature_crossPairing_value` supplies the right-hand side as
  `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²} = ∫ ∑ᵢ ⟨remDiffFib …, ∇S⟩` (sorry-free), the frame summand splits
  into its pure-Riemann genuine fibre and its bracket remainder
  (`remDiffFib_eq_genuine_add_bracket`, `remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free),
  the bracket integral is the bracket-channel root, and on the left the pure-Riemann pairing
  (`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`) and the differentiated-curvature
  operator-field pairing (the integration-by-parts identity `tensorL2Inner_appCc_covGrad_covGrad_eq_neg`)
  match it term by term. The remaining genuine content is entirely in the bracket-channel root above.

The whole curvature line of `MovingFrameDiffCurvTraceSection` — the frame-bracket telescoping kernel,
the genuine cross-pairing value `(★)`, the integrated nullity, and every down-stream cross-pairing node —
is proven **by composition over `bochnerWeitzenbockResidue_frameFree_value`** through the sorry-free
bookkeeping `genuineCurvFields_crossPairing_eq_residue` (which rewrites the four-pairing residue as
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²}`) and the sorry-free Weitzenböck
value `weitzenbock_curvature_crossPairing_value`; that residue identity in turn bottoms out at the single
bracket-channel root above, homed here so the spine consumes it without a forward reference.

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

/-- **The frame-summed frame-bracket covariant Green nullity (the honest divergence-vanishing pillar).**
For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a finite index family `ι`, smooth
tangent direction fields `V i`, smooth once-derived `(r, s)`-tensor sections `W i`, and a fixed
`(r, s)`-tensor section `Z`, the frame-summed metric-lowered covariant Leibniz combination integrates to
zero:
```
∑ᵢ ∫_M ( ⟨∇_{V i}(W i), Z⟩ + ⟨W i, ∇_{V i} Z⟩ + ⟨W i, Z⟩ · divᵍ (V i) ) dvolᵍ = 0.
```

This is the *honest* divergence-vanishing content underneath the frame-bracket discrepancy
`tensor3rdCurvBracket g r s W T x = ∑ᵢ ( ∇_{[Bᵢ,W]}(∇_{Bᵢ}T) + ∇_{Bᵢ}(∇_{[Bᵢ,W]}T) )`
(`Bochner/PointwiseTensorBochner`). Read against `∇S` and integrated, the bracket discrepancy is the
*first slot* `∑ᵢ ⟨∇_{V i}(W i), ∇S⟩` of this combination (with `V i := [Bᵢ, W]`, `W i := ∇_{Bᵢ}T`, and
the companion family `V i := Bᵢ`, `W i := ∇_{[Bᵢ,W]}T`), so it equals the **negative of the IBP-partner
terms** `−∑ᵢ ( ⟨W i, ∇_{V i}(∇S)⟩ + ⟨W i, ∇S⟩ · divᵍ (V i) )` — a total covariant divergence whose
integral over the closed boundaryless manifold vanishes. The bracket pairing is therefore **not zero by
itself**; only the full Green combination is. This lemma is the frame-bracket reading of the divergence
engine `integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`), recorded here
for the curvature line to consume. -/
theorem frameBracket_combined_divergence_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g r s V W Z

/-- **The frame-bracket remainder frame-sum integral carries the differentiated-curvature operator-field
trace plus the Ricci trace (the curvature line's single irreducible integrated deep root, in its
strictly-smaller bracket-channel form).** For a closed smooth Riemannian manifold `(M, g)`, every
covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the integral over the
closed manifold of the fixed-frame sum of the per-direction frame-bracket remainder fibres
`remDiffBracketFib` (the frame summand `remDiffFib` minus its pure-Riemann genuine curvature fibre
`remDiffGenuineFib`, `MovingFrameRemainderFrameSumBridge`), paired against `∇S := covGrad g 0 s S`,
equals the global metric `L²` pairing of the differentiated-curvature operator-field trace
`appCc (∇Φ₀ s) S` (the `(∇R) S` field, `∇Φ₀ s := covGrad g s s (curvOpField g s)`) plus the leading-slot
Ricci-trace carrier `ricTraceSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = ⟨appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}.
```

**This is the genuine, strictly-smaller, irreducible integrated content underneath the frame-free residue
`bochnerWeitzenbockResidue_frameFree_value` below — the bracket channel with the pure-Riemann channel
peeled off.** The frame-free residue is reduced to *this* node sorry-free (below): the pure-Riemann
`R(∇S)` cross-pairing `⟨GcurvSection g s S, ∇S⟩_{L²} = ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}`
splits off (`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`,
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, `tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`,
all sorry-free), the differentiated-curvature operator-field pairing is rearranged through the genuine
integration-by-parts identity `tensorL2Inner_appCc_covGrad_covGrad_eq_neg`
(`appCc (∇Φ₀ s) S = covGrad g 0 s (pureRGenuineDiffOp g 0 s S) − appCc (slotExtend (Φ₀ s)) (∇S)`,
the operator-field B-rule, sorry-free), and the integrated order-`2` Weitzenböck value
`weitzenbock_curvature_crossPairing_value` (`⟨pointwiseTensorCurv g s S, ∇S⟩_{L²} = ‖Δ_∇S‖² − ‖∇²S‖²`,
sorry-free) supplies the right-hand side. So this single node is *equivalent*, through that sorry-free
bookkeeping, to the frame-free residue — and isolates the entire non-pure-Riemann curvature anatomy in
the passenger-`W` frame-traced **bracket channel**.

**Why it is the irreducible root (the genuine missing content, no bridge below this file).** The
identification of the frame-summed differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the
operator-field carrier `appCc (∇Φ₀ s) S`, together with the second-Bianchi cyclic fold of the
contracted-curvature slot into the raised Ricci endomorphism `ricTraceSection` and the gradient-slot
bracket discrepancy integrating to zero, is the classical Bochner–Weitzenböck curvature-term derivation.
The pointwise per-direction split is mathematically **fenced**: the differentiated-curvature trace is
**non-tensorial in the direction** — its fibre realisation reads the `smoothExtensionTangent` jet of the
frame direction, which is chart-selection-unbounded on `S²` (`MovingFrameDifferentiatedCurvatureSection`,
`MovingFrameDiffCurvAnchor`), so it has no clean slot-`0` uncurry and only the *summed, integrated* match
is sound. The genuine identification therefore requires the non-tensorial differentiated-curvature anchor
(the tensorial `covGradCurvatureContraction` summed over a frozen frame and glued across a finite chart
cover by a smooth partition of unity), which is the genuinely-new analytic content of the curvature line
and has no sorry-free bridge below this file. The body is `sorry` (the genuine classical integrated
tensor Bochner–Weitzenböck curvature-term derivation); consumers transitively depend on `sorryAx`.

**`s = 0` litmus (the Ricci-trace carrier is necessary and sufficient).** At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the zero operator
on the empty curvature slot, the curvature of a scalar), so the identity collapses to
`∫_M ∑ᵢ ⟨remDiffBracketFib g 0 f i, ∇f⟩ = ⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ∫ Ric(∇f, ∇f)` — the
classical scalar Bochner–Lichnerowicz identity (`ricTraceSection_zero_apply`,
`weitzenbock_curvature_crossPairing_value`), genuinely nonzero on a non-flat manifold. Dropping the
Ricci-trace carrier (perturbing the curvature to flat, the degenerate witness) makes the identity FALSE
at `s = 0`, so the carrier is genuinely required and the node is not vacuous (it fails for a
`κ ≠ 1`-perturbed curvature residue). The identity is stated at the *integrated* frame-free `L²` level
throughout — it never extracts a per-direction `M → E` quantity — so it is trap-screened. -/
theorem bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace
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

/-- **The integrated tensor Bochner–Weitzenböck curvature-term residue identity (the curvature line's
single irreducible deep root, frame-free form).** For a closed smooth Riemannian manifold `(M, g)`, every
covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the explicit four-pairing
curvature residue — built from the *frame-free* curvature operator field `Φ₀ s := curvOpField g s`, the
raised Ricci endomorphism (via `ricTraceSection`), and the rough Laplacian — equals the genuine
Weitzenböck curvature integral:
```
  ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
    − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ := rawTensorConnLapSmooth g 0 s`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`,
`pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` the order-`0` pure-Riemann curvature trace.

**This is the genuine new mathematical content of the curvature line — the classical tensor
Bochner–Weitzenböck curvature-term identity.** It is stated here in its cleanest fully-tensorial,
*frame-free* operator-field form (no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent`
jet). Every curvature-line node of the moving-frame spine `MovingFrameDiffCurvTraceSection` — the
frame-bracket remainder kernel `remDiffBracketFrameSum_integral_eq_genuineDiffCurv_ricTrace`, the genuine
value `(★)` `genuineCurvFields_crossPairing_value`, the integrated nullity
`movingFrameDiffCurv_remainder_integrated_nullity`, and the down-stream cross-pairing leaves — is proven
**by composition over this identity** through the sorry-free bookkeeping
`genuineCurvFields_crossPairing_eq_residue` (which rewrites the four-pairing residue as
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²}`) and the sorry-free Weitzenböck
value `weitzenbock_curvature_crossPairing_value` (which identifies `⟨Curv S, ∇S⟩_{L²}` with
`‖Δ_∇ S‖² − ‖∇²S‖²`). It is the unique deep root of the line's dependency graph, homed upstream so the
spine consumes it without a forward reference.

**Proof (sorry-free reduction to the strictly-smaller bracket-channel root).** The right-hand side is
the integrated order-`2` Weitzenböck value `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`
(`weitzenbock_curvature_crossPairing_value`, sorry-free), which is the integral of the fixed-frame sum of
the per-summand pairings `∑ᵢ ⟨remDiffFib g s S x i, ∇S⟩`
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`, sorry-free). Each frame summand splits
into its pure-Riemann genuine fibre `remDiffGenuineFib` and its named bracket remainder `remDiffBracketFib`
(`remDiffFib_eq_genuine_add_bracket`, sorry-free), and the integral splits accordingly: the genuine
frame-sum integral is `⟨GcurvSection g s S, ∇S⟩_{L²}`
(`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`, sorry-free) and the bracket frame-sum integral is
`⟨appCc (∇Φ₀ s) S + ricTraceSection g s S, ∇S⟩_{L²}` by the single strictly-smaller bracket-channel root
`bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace` above. On the left, the pure-Riemann
pairing `⟨GcurvSection g s S, ∇S⟩_{L²}` is the first residue pairing
(`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`, sorry-free), and the differentiated-curvature
operator-field pairing `⟨appCc (∇Φ₀ s) S, ∇S⟩_{L²}` is the second-and-third residue pairings combined by
the genuine integration-by-parts identity `tensorL2Inner_appCc_covGrad_covGrad_eq_neg`
(`appCc Φ₀ S = pureRGenuineDiffOp g 0 s S`, the base spec; the operator-field B-rule, sorry-free). The
two sides match by `ring`.

**Why the bracket-channel root is the genuine missing content.** The left-hand side is built from the
frame-free curvature operator `Φ₀ = curvOpField` (an abstract `Classical.choose` curvature operator) and
the raised Ricci endomorphism, while the right-hand side is the integrated rough-Laplacian Dirichlet
energy. The reduction above peels off the pure-Riemann `R(∇S)` trace and the operator-field
integration-by-parts bookkeeping sorry-free, isolating the entire non-pure-Riemann curvature anatomy in
the single bracket-channel root `bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace`. That
root carries the classical Bochner technique that has no sorry-free bridge below this file: the
identification of the frame-summed differentiated curvature `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the
operator-field carrier `appCc (∇Φ₀) S`, the second-Bianchi / frame-Ricci folding of the leading slot into
`ricTraceSection`, and the gradient-slot bracket discrepancy integrating to zero. The pointwise
per-direction split is mathematically **fenced** — the differentiated-curvature trace is non-tensorial in
the direction (`smoothExtensionTangent` is chart-selection-unbounded on `S²`), so only the *summed,
integrated* match is sound. The genuine identification requires the non-tensorial differentiated-curvature
anchor (`MovingFrameDiffCurvAnchor`, `MovingFrameDifferentiatedCurvatureSection`); consumers transitively
depend on its `sorryAx` through the bracket-channel root above.

**`s = 0` litmus (the Ricci-trace carrier is necessary and sufficient).** At `s = 0` the pure-Riemann
and differentiated-curvature carriers vanish (`pureRGenuineDiffOp g 0 0 f` is the curvature of a scalar,
which vanishes; `Φ₀ 0 = curvOpField g 0` acts as the zero operator on the empty slot), so the identity
collapses to the gradient-field curvature bilinear plus the Ricci pairing equalling the Weitzenböck
energy — the classical scalar Bochner formula `‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)`
(`ricTraceSection_zero_apply`), genuinely nonzero on a non-flat manifold. Dropping the Ricci-trace
carrier (perturbing the curvature to flat, the degenerate witness) makes the identity FALSE at `s = 0`,
so the carrier is genuinely required and the identity is not vacuous (it fails for a `κ ≠ 1`-perturbed
curvature residue). -/
theorem bochnerWeitzenbockResidue_frameFree_value
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
  rw [hGval', bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace (I := I) (M := M) g s S]
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

end Connection
end Integral
end DifferentialGeometry

end
