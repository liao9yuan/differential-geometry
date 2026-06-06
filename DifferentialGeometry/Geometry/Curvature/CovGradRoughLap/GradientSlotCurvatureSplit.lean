import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity

/-!
# The gradient-slot curvature lift of the order-`2` rough-Laplacian commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file develops the
**gradient-slot lift** of the rank-generic order-`2` rough-Laplacian / covariant-gradient commutator
defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`).

The per-direction `W`-form split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(`Bochner/PointwiseTensorBochner`) reads the third-covariant-derivative defect with the curvature
acting through the *passenger* direction `W`. The gradient-slot lift is the complementary reading: the
curvature / derivative action that hits the **leading (gradient) slot** `X₀` of `∇S` — the slot the
`W`-form never touches. Splitting the leading slot of `∇S` past the rough-Laplacian frame-trace slots
by the Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) and reading the resulting
tensor-curvature by the slot-wise formula produces the slot table's class `(I)` (leading-slot pure
curvature `R(∇S)`) and class `(IV)` (the Bochner–Lichnerowicz Ricci trace `Ric(∇S)`).

## The gradient-slot curvature object

`gradSlotCurv g s S X W x` is the section-level Riemann curvature of the **gradient field** in
unit-evaluation form: `riemannSec (tensor0SCovariantDerivative (s + 1)) X W (∇S-as-unit-field) x`,
where the gradient field is the unit-evaluated gradient `unitGradFieldGen g s S` (whose slot-`0` curry
reads the directional covariant derivative of `S`). It is the curvature acting on the `(0, s + 1)`-tensor
`∇S`, so by the slot-wise formula its curvature direction `W` becomes the **leading/gradient slot** of
`∇S`. By the bundled Ricci identity it is the antisymmetric Hessian defect of `∇S`.

## Main results

* `baseSlotCurv_eq_riemannOp` — the base-tangent slot curvature is the bundled tangent Riemann operator:
  `baseSlotCurv g X W x u = R(X x, W x) u` (the `riemannSec = riemannOp` bridge on a smooth extension).
* `gradSlotCurv_toModel_eq_baseSlot_sum` — the **gradient-slot reading** (class `(I)` + tail): the
  gradient-slot curvature object, read on a tuple, is the negated base-slot sum of `∇S` across its
  `s + 1` slots, each with the leading curvature direction `R(X, W)` inserted.
* `gradSlotCurv_toModel_eq_leading_add_tail` — the **gradient-slot split**: the base-slot sum split into
  the leading (slot-`0`, gradient) class-`(I)` term `(∇S)(R(X, W)(u 0), …)` plus the tail-slot sum.
* `ricEndoRaisedFib_inner_eq_frame_trace` — the **frame-trace → raised-Ricci bridge** (class `(IV)`):
  `⟨ricEndoRaisedFib v, w⟩_g = ∑ᵢ ⟨R(Bᵢ, v) w, Bᵢ⟩_g`, the orthonormal frame trace of the curvature's
  derivative-direction slot folding into the raised Ricci endomorphism (`smoothOrthoFrame_riemannOp_trace_eq_ricci`).
* `ricTraceSection_apply_leadingSlot` — the **general-rank Ricci-trace carrier reading** (class `(IV)`):
  the unit-evaluated Ricci-trace carrier `ricTraceSection g s S` reads `∇S` with the leading slot
  precomposed by the raised Ricci endomorphism `ricEndoRaisedFib`, generalising the `s = 0` Bochner
  litmus `ricTraceSection_zero_apply` to arbitrary covariant rank.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). `Ric := ricciTensor g` is the Ricci tensor of
the Levi-Civita connection (`RicciConnection`). All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq`. The covariant gradient `covGrad g 0 s` raises the rank `(0, s) → (0, s + 1)`,
currying the new tangent direction as the leading covariant slot.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
/-- **The base-tangent slot curvature is the bundled tangent Riemann operator.** For smooth tangent
fields `X, W`, a point `x`, and a slot vector `u`, the base-tangent slot curvature `baseSlotCurv`
(the section-level `riemannSec` of the Levi-Civita connection along a smooth extension of `u`) is the
bundled tangent Riemann operator `riemannOp (LeviCivita g)` on the fibre values:
```
baseSlotCurv g X W x u = R(X x, W x) u.
```
This is `riemannSec_eq_riemannOp_smooth` for the Levi-Civita connection at the smooth extension
`smoothExtensionTangent x u` (whose value at `x` is `u`, `smoothExtensionTangent_eq`). -/
theorem baseSlotCurv_eq_riemannOp
    (g : SmoothRiemannianMetric I M)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    baseSlotCurv (I := I) g X W x u =
      riemannOp (LeviCivita (I := I) g) x (X x) (W x) u := by
  rw [baseSlotCurv]
  rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g) X.contMDiff W.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) x u)]
  rw [smoothExtensionTangent_eq (I := I) x u]

/-- **The gradient-slot curvature object.** The section-level Riemann curvature of the unit-evaluated
gradient field `unitGradFieldGen g s S` (the `(0, s + 1)`-valued section whose slot-`0` curry reads the
directional covariant derivative of `S`), along smooth tangent fields `X, W`, at a point `x`:
```
gradSlotCurv g s S X W x := riemannSec (tensor0SCovariantDerivative (s + 1)) X W (∇S-as-unit-field) x.
```
This is the curvature acting on the `(0, s + 1)`-tensor `∇S`; its curvature direction `W` enters the
leading (gradient) slot of `∇S` under the slot-wise formula. By the bundled Ricci identity it is the
antisymmetric Hessian defect of the gradient field — the gradient-slot reading of the order-`2`
commutator defect, complementary to the passenger-`W` reading `Tensor3rdCurv`. -/
def gradSlotCurv (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace (s + 1) I x :=
  riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
    (fun b => X b) (fun b => W b) (unitGradFieldGen (I := I) (M := M) g s S) x

/-- **The gradient-slot reading (base-slot sum form).** The gradient-slot curvature object, read on a
covariant tuple `u : Fin (s + 1) → T_x M`, is the negated base-slot sum of the unit-evaluated gradient
field `∇S = unitGradFieldGen g s S` across all `s + 1` covariant slots, each slot's vector replaced by
the leading curvature direction `baseSlotCurv g X W x` of that slot:
```
toModel (gradSlotCurv g s S X W x) u
  = − ∑ₖ toModel (∇S x) (update u k (R(X, W)(u k))).
```
This is the `r = 0` slot-wise tensor curvature formula `riemannSec_tensorCov_baseSlot_eval` applied to
the gradient field. The slot-`0` summand is the leading (gradient) slot — the class-`(I)` content. -/
theorem gradSlotCurv_toModel_eq_baseSlot_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - ∑ k : Fin (s + 1),
          Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) := by
  rw [gradSlotCurv]
  exact riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g (s + 1) X W
    (unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S) x u

/-- **The gradient-slot split (leading class-`(I)` term + tail).** The gradient-slot curvature object,
read on a tuple `u`, splits as the negation of the **leading (slot-`0`, gradient) curvature term** plus
the **tail-slot sum**:
```
toModel (gradSlotCurv g s S X W x) u
  = − [ toModel (∇S x) (update u 0 (R(X, W)(u 0)))
        + ∑ₖ toModel (∇S x) (update u k.succ (R(X, W)(u k.succ))) ].
```
The leading term `toModel (∇S x) (update u 0 (R(X, W)(u 0)))` is the class-`(I)` gradient-slot pure
curvature `R(∇S)`; the tail sum carries the class-`(II)` passenger-slot curvature. Proof: split the
`Fin (s + 1)` base-slot sum at the leading index via `Fin.sum_univ_succ`. -/
theorem gradSlotCurv_toModel_eq_leading_add_tail
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0))) +
          ∑ k : Fin s,
            Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u k.succ
                (baseSlotCurv (I := I) g X W x (u k.succ)))) := by
  rw [gradSlotCurv_toModel_eq_baseSlot_sum, Fin.sum_univ_succ]

/-- The smooth `g_x`-orthonormal frame field `smoothOrthoFrame g x i` packaged as a bundled smooth
section `Cₛ^∞⟮I; E, TM⟯`, the form the rough-Laplacian frame-trace feeds into the gradient-slot
curvature object. Its smoothness is `smoothOrthoFrame_smooth`. -/
def orthoFrameSec (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x i)

@[simp] lemma orthoFrameSec_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    orthoFrameSec (I := I) (M := M) g x i b = smoothOrthoFrame (I := I) g x i b := rfl

/-- **The frame-summed gradient-slot reading (engine-shaped survivor form).** Summing the gradient-slot
curvature object over the rough-Laplacian `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` placed
in the curvature's first slot, the reading on a tuple `u` is the frame sum of the per-direction
gradient-slot split, with each base-slot curvature resolved into the bundled tangent Riemann operator:
```
∑ᵢ toModel (gradSlotCurv g s S Bᵢ W x) u
  = ∑ᵢ − [ toModel (∇S x) (update u 0 (R(Bᵢ, W)(u 0)))
           + ∑ₖ toModel (∇S x) (update u k.succ (R(Bᵢ, W)(u k.succ))) ].
```
This exposes what survives the frame sum: the **leading-slot** term `toModel (∇S x) (update u 0 (R(Bᵢ,
W)(u 0)))` carries the class-`(I)` pure curvature and, with the metric trace
`ricEndoRaisedFib_inner_eq_frame_trace`, folds into the class-`(IV)` Bochner Ricci trace `Ric(∇S)`
(the carrier `ricTraceSection`, `ricTraceSection_apply_leadingSlot`); the tail sum carries the class-`(II)`
passenger-slot curvature. Proof: the per-direction split `gradSlotCurv_toModel_eq_leading_add_tail` under
the frame sum, with `baseSlotCurv_eq_riemannOp` rewriting each base-slot curvature. -/
theorem gradSlotCurv_frameSum_toModel_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (gradSlotCurv (I := I) (M := M) g s S (orthoFrameSec (I := I) (M := M) g x i) W x) u) =
      ∑ i : Fin (Module.finrank ℝ E),
        - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u 0
                (riemannOp (LeviCivita (I := I) g) x
                  (smoothOrthoFrame (I := I) g x i x) (W x) (u 0))) +
            ∑ k : Fin s,
              Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
                (Function.update u k.succ
                  (riemannOp (LeviCivita (I := I) g) x
                    (smoothOrthoFrame (I := I) g x i x) (W x) (u k.succ)))) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gradSlotCurv_toModel_eq_leading_add_tail]
  congr 1
  congr 1
  · congr 1
    rw [baseSlotCurv_eq_riemannOp]
    rfl
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    rw [baseSlotCurv_eq_riemannOp]
    rfl

/-- **The frame-trace → raised-Ricci bridge (class `(IV)`).** The defining metric pairing of the raised
Ricci endomorphism `ricEndoRaisedFib g x` equals the `g_x`-orthonormal frame trace of the curvature's
derivative-direction slot:
```
⟨ricEndoRaisedFib g x v, w⟩_g = ∑ᵢ ⟨R(Bᵢ, v) w, Bᵢ⟩_g,   Bᵢ := smoothOrthoFrame g x i.
```
This is the class-`(IV)` content: summing the curvature `R(Bᵢ, ·)` over the rough-Laplacian frame, with
the curvature's first slot contracted against the frame by the metric, produces the Bochner–Lichnerowicz
Ricci trace `Ric`, which is exactly the raised Ricci endomorphism's metric pairing. Proof: the raised
Ricci endomorphism's defining identity `inner_ricEndoRaisedFib` (`⟨ricEndoRaisedFib v, w⟩ = Ric(v, w)`)
composed with the orthonormal-trace Ricci formula `smoothOrthoFrame_riemannOp_trace_eq_ricci`. -/
theorem ricEndoRaisedFib_inner_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (ricEndoRaisedFib (I := I) g x v) w =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) := by
  rw [inner_ricEndoRaisedFib (I := I) (M := M) g x v w,
    smoothOrthoFrame_riemannOp_trace_eq_ricci (I := I) (M := M) g x v w]

/-- **The general-rank Ricci-trace carrier reading (class `(IV)`).** For a smooth compactly-supported
`(0, s)`-tensor `S`, the unit-`(0, 0)`-evaluation of the Ricci-trace carrier `ricTraceSection g s S`,
read on a tuple `Fin.cons v0 vs`, equals the unit-evaluation of `∇S = covGrad g 0 s S` with the
**leading slot** precomposed by the raised Ricci endomorphism `ricEndoRaisedFib g x`:
```
toModel ((ricTraceSection g s S)(unit)) (v0 ::ᵥ vs)
  = toModel ((∇S)(unit)) (ricEndoRaisedFib g x v0 ::ᵥ vs).
```
This is the term-`(IV)` Bochner–Lichnerowicz Ricci trace `Ric(∇S)` contracted against the gradient slot,
at *arbitrary* covariant rank. It generalises the scalar `s = 0` Bochner litmus `ricTraceSection_zero_apply`
to all ranks; with `ricEndoRaisedFib_inner_eq_frame_trace` the raised slot is the orthonormal frame trace
of the curvature, identifying this carrier with the class-`(IV)` content of the gradient-slot lift.

**Proof.** The carrier's unit-section is the composition `ricSlotOpFib g s x` of the leading-slot
raised-Ricci operator with `(∇S) x (unit)` (`ricTraceSection_toSection`, `ricSlotOpField_toSection`).
The leading-slot read `ricSlotOpFib_apply_eval` reads `v0` off the leading slot, applies
`ricEndoRaisedFib g x`, and evaluates the curried gradient slot at the resulting direction and `vs`; the
right-hand side is then the curry-evaluation `tensor0S_curry_apply_eval` read backwards. -/
theorem ricTraceSection_apply_leadingSlot
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (ricTraceSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (ricEndoRaisedFib (I := I) g x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricTraceSection (I := I) (M := M) g s S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ricSlotOpFib (I := I) (M := M) g s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [ricTraceSection_toSection, ricSlotOpField_toSection]
    rfl
  rw [hval]
  rw [ricSlotOpFib_apply_eval (I := I) (M := M) g s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x v0) vs]

end Connection
end Integral
end DifferentialGeometry

end
