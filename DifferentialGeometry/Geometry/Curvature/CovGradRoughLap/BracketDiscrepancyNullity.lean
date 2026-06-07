import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing

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

* `bochnerWeitzenbockResidue_frameFree_value` — the **integrated tensor Bochner–Weitzenböck
  curvature-term residue identity**, the curvature line's single irreducible deep root, in its cleanest
  fully-tensorial *frame-free* operator-field form (no moving frame, no `remDiffBracketFib`, no
  `smoothExtensionTangent`):
  ```
    ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}
      − ⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
      − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}
      + ⟨ricTraceSection g s S, ∇S⟩_{L²}
    = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}.
  ```
  This is the genuine classical third-order Bochner–Weitzenböck curvature-term identity: the order-`2`
  rough-Laplacian / covariant-gradient commutator defect's gradient-slot reordering into the pure-Riemann
  `R(∇S)` trace (the first pairing), the differentiated curvature `(∇R) S` (the integration-by-parts
  bookkeeping of the second and third pairings, the operator-field IBP
  `tensorL2Inner_appCc_covGrad_covGrad_eq_neg`), the leading-slot Ricci trace (the second-Bianchi /
  frame-Ricci folding, the fourth pairing), and a total covariant divergence that integrates to zero (the
  frame-bracket Green nullity above). The pointwise per-direction split is mathematically **fenced** — the
  differentiated-curvature trace is non-tensorial in the direction (`smoothExtensionTangent` is
  chart-selection-unbounded on `S²`), so only the *summed, integrated* match is sound; the identification
  of the frame-summed differentiated-curvature trace with the operator-field carrier `appCc (∇Φ₀) S` has
  no bridge below this file and is the genuine content. The body is `sorry` (the genuine classical
  derivation); consumers transitively depend on `sorryAx`.

The whole curvature line of `MovingFrameDiffCurvTraceSection` — the frame-bracket telescoping kernel,
the genuine cross-pairing value `(★)`, the integrated nullity, and every down-stream cross-pairing node —
is proven **by composition over this single frame-free leaf** through the sorry-free bookkeeping
`genuineCurvFields_crossPairing_eq_residue` (which rewrites the four-pairing residue as
`⟨GcurvSection + (genuineDiffCurvSection + ricTraceSection), ∇S⟩_{L²}`) and the sorry-free Weitzenböck
value `weitzenbock_curvature_crossPairing_value`. It is the unique deep root of the line's dependency
graph, homed here so the spine consumes it without a forward reference and the whole line bottoms out at
this clean classical statement.

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

**Why it is the irreducible deep root (the genuine missing content).** The left-hand side is built from
the frame-free curvature operator `Φ₀ = curvOpField` (an abstract `Classical.choose` curvature operator)
and the raised Ricci endomorphism, while the right-hand side is the integrated rough-Laplacian Dirichlet
energy. Identifying the two is the classical Bochner technique: the order-`2` commutator defect's
gradient-slot reordering into (i) the pure-Riemann `R(∇S)` trace (the first pairing,
`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`), (ii) the differentiated curvature `(∇R) S`
(the integration-by-parts bookkeeping of the second and third pairings, the operator-field IBP
`tensorL2Inner_appCc_covGrad_covGrad_eq_neg`), (iii) the leading-slot Ricci trace (the second-Bianchi /
frame-Ricci folding of the fourth pairing, `contracted_second_bianchi`,
`ricEndoRaisedFib_inner_eq_frame_trace`, `ricTraceSection_apply_leadingSlot`), and (iv) a total covariant
divergence integrating to zero (`frameBracket_combined_divergence_integral_eq_zero` above). The pointwise
per-direction split is mathematically **fenced** — the differentiated-curvature trace is non-tensorial in
the direction (`smoothExtensionTangent` is chart-selection-unbounded on `S²`), so only the *summed,
integrated* match is sound; the identification of the frame-summed differentiated-curvature trace
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` with the operator-field carrier `appCc (∇Φ₀) S` has no bridge below this file and
is the genuine content. The body is `sorry` (the genuine classical third-order tensor Bochner–Weitzenböck
curvature-term derivation); consumers transitively depend on `sorryAx`.

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
  sorry

end Connection
end Integral
end DifferentialGeometry

end
