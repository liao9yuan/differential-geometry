import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameDiffCurvTraceSection

/-!
# The operator-field carrier ↔ frame-summed differentiated-curvature trace bridge

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file relates the two
presentations of the differentiated-curvature contraction `∑ᵢ (∇_{Bᵢ} R)(Bᵢ, ·) S`:

* **the operator-field carrier** `genuineDiffCurvSection g s S = appCc (covGrad (Φ₀ s)) S`
  (`MovingFrameDiffCurvTraceSection`), the gauge-glued tensorial `(∇R) S` field, the operator-field
  action of the covariant derivative of the *frame-free* curvature operator field
  `Φ₀ s := curvOpField g s`; and
* **the frame-summed differentiated curvature trace** — the covariant derivative of the order-`0`
  pure-Riemann curvature operator trace `pureRGenuineDiffOp g 0 s S`, whose value is the explicit
  *bundle*-curvature frame trace `∑ᵢ R^{(0,m)}(Bᵢ, ·)(slot0_{Bᵢ} S)` over the moving orthonormal frame
  `Bᵢ := smoothOrthoFrame g x i` (`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`).

## What the `curvOpField` choose-spec actually pins (the `Φ₀` value anatomy)

`curvOpField g s = (Classical.choose (exists_pureRGenuineDiffOp_base_appCc g)) s` is the abstract
curvature operator field whose operator-field action recovers the order-`0` moving-frame pure-Riemann
curvature endomorphism: `appCc (curvOpField g s) S = pureRGenuineDiffOp g 0 s S`
(`curvOpField_appCc_eq_pureRGenuineDiffOp`). Its *value* is pinned, at rank `m + 1` and at the unit, to
the **frame-summed bundle curvature trace** `∑ᵢ R^{(0,m)}(Bᵢ, v 0)(slot0_{Bᵢ} S)` — the genuine
`g`-metric curvature trace `∑ᵢ R(Bᵢ, ·)` acting through the slot-`0` reading of `S`, built from `g` and
the Levi-Civita curvature alone (no `smoothExtensionTangent` jet); see
`curvOpField_appCc_unit_eval_eq_riemannOp_frameTrace`.

## The bridge and the paired corollary

The carrier `genuineDiffCurvSection g s S` is the *covariant derivative* of that order-`0` curvature
trace, with the passenger-slot curvature spectator `R(∇S)` removed — pointwise, in unit-evaluated form:
```
(genuineDiffCurvSection g s S)(x)(d)(cons v0 vs)
  = (∇_{v0}(pureRGenuineDiffOp g 0 s S))(x)(d)(vs) − (Φ₀ s)(∇_{v0}S(x)(d))(vs)
```
(`genuineDiffCurvSection_unit_eval_eq_covGrad_pureR_sub_spectator`, the section-level B-rule inversion of
`MovingFrameDiffCurvTraceSection`). Reading the `∇`-of-the-pure-`R`-trace through the frame-trace value
anatomy exhibits the carrier as the differentiated frame-summed bundle-curvature trace minus the
spectator — the operator-field / differentiated-trace identification the curvature-line assembly reads.

The form the assembly consumes is the **integrated** one: the `L²` pairing
`⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}` is the operator-field integration-by-parts value
`−⟨Δ_∇(pureRGenuineDiffOp g 0 s S), S⟩_{L²} − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}`
(`tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg_pureR_form`), with the rough Laplacian
`Δ_∇ := rawTensorConnLapSmooth g 0 s` of the frame-summed order-`0` trace paired against `S`. The
pointwise per-direction match of the carrier with the *slot-wise* differentiated-curvature trace
(through `smoothExtensionTangent`) is *false* on a normal manifold and is unbounded on `S²`; only this
summed/integrated operator-field form is sound, and it is the irreducible content of the integrated
tensor Bochner–Weitzenböck identity assembled downstream.

## Litmus

At `s = 0` the carrier vanishes (`genuineDiffCurvSection_zero_eq_zero`: the scalar order-`0` curvature
operator is the zero operator, so its covariant derivative carries nothing), and the paired value is
`0`. At `s = m + 1` on a non-flat manifold with non-parallel `S` the carrier is genuinely nonzero (the
`(∇R) S` content is present) and the frame-trace value anatomy is nonzero, so the identification is
nontrivial.

## Convention

Geometer convention `Δ_∇ = ∑ⱼ ∇²_{Bⱼ, Bⱼ}` (frame trace), `R = riemannOp`/`riemannSec`. `slot0_{Bᵢ} S
:= tensor0S_curry s x (S(x)⟨unit⟩) (Bᵢ)` is the slot-`0` reading of `S` along `Bᵢ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
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

/-- **The `curvOpField` choose-spec base identity.** The operator-field action of the frame-free
curvature operator field `Φ₀ s := curvOpField g s` on a smooth compactly-supported `(0, s)`-tensor `S`
is the order-`0` moving-frame pure-Riemann curvature operator trace `pureRGenuineDiffOp g 0 s S`:
```
appCc (curvOpField g s) S = pureRGenuineDiffOp g 0 s S.
```
This is the defining `Classical.choose` spec of `curvOpField` (`exists_pureRGenuineDiffOp_base_appCc`),
re-exposed in the curvature-line vocabulary: it is the order-`0` content `Φ₀ s` carries — the
frame-summed curvature trace `∑ᵢ R(Bᵢ, ·)` acting through the slot-`0` reading of `S`, whose explicit
value is `curvOpField_appCc_unit_eval_eq_riemannOp_frameTrace`. -/
theorem curvOpField_appCc_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm

/-- **The `Φ₀` value anatomy: the order-`0` `curvOpField` trace is the frame-summed bundle curvature
contraction of the slot-`0` slice.** For covariant rank `m + 1`, the unit-evaluated value of the
operator-field action `appCc (curvOpField g (m + 1)) S = pureRGenuineDiffOp g 0 (m + 1) S` is the
moving-frame sum (over `Bᵢ := smoothOrthoFrame g x i`, orthonormal at `x`) of the `(0, m)`-tensor bundle
curvature `R^{(0,m)} = riemannOp (tensor0SCov m)` in the leading curvature direction `Bᵢ` and the
gradient direction `v 0`, contracted against the slot-`0` slice `tensor0S_curry m x (S(x)⟨unit⟩) (Bᵢ)`
of `S`, read on the trailing tuple:
```
(appCc (curvOpField g (m + 1)) S)(x)(unit)(v)
  = ∑ᵢ toModel(R^{(0,m)}(Bᵢ, v 0)(slot0_{Bᵢ} S))(tail v).
```
This is *what the choose-spec pins* — the genuine `g`-metric curvature trace `∑ᵢ R(Bᵢ, ·)` acting
through the slot-`0` reading of `S`, frame-free in value (built from `g` and the Levi-Civita curvature
alone, no `smoothExtensionTangent` jet). Rewriting `appCc (curvOpField g (m + 1)) S` to
`pureRGenuineDiffOp g 0 (m + 1) S` by `curvOpField_appCc_eq_pureRGenuineDiffOp` and reading the value by
`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`. -/
theorem curvOpField_appCc_unit_eval_eq_riemannOp_frameTrace
    (g : SmoothRiemannianMetric I M) (m : ℕ) (S : SmoothCcTensor g 0 (m + 1)) (x : M)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          (appCc (I := I) (M := M) g ((m + 1) + 0) ((m + 1) + 0)
            (curvOpField (I := I) (M := M) g (m + 1)) S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (smoothOrthoFrame (I := I) g x i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from S.toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x i x)))
          (Matrix.vecTail v) := by
  rw [show (appCc (I := I) (M := M) g ((m + 1) + 0) ((m + 1) + 0)
        (curvOpField (I := I) (M := M) g (m + 1)) S) =
      pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) S from
    curvOpField_appCc_eq_pureRGenuineDiffOp (I := I) (M := M) g (m + 1) S]
  exact pureRGenuineDiffOp_zero_succ_toSection_unit_eval (I := I) (M := M) g m S x v

/-- **The carrier ↔ differentiated-pure-`R`-trace pointwise identification (the operator-field
differentiated-curvature idiom).** For covariant rank `s`, point `x`, base `(0, 0)`-tensor `d`, gradient
direction `v0`, and trailing tuple `vs`, the gauge-glued tensorial differentiated-curvature carrier
`genuineDiffCurvSection g s S` (the `(∇R) S` field, `appCc (covGrad (Φ₀ s)) S`) is, in unit-evaluated
form, the directional covariant derivative of the order-`0` pure-Riemann curvature trace
`pureRGenuineDiffOp g 0 s S` (whose value is the frame-summed bundle curvature trace
`∑ᵢ R(Bᵢ, ·)(slot0_{Bᵢ} S)`, `curvOpField_appCc_unit_eval_eq_riemannOp_frameTrace`) with the
passenger-slot curvature spectator `(Φ₀ s)(∇_{v0} S)` removed:
```
(genuineDiffCurvSection g s S)(x)(d)(cons v0 vs)
  = (∇_{v0}(pureRGenuineDiffOp g 0 s S))(x)(d)(vs) − (Φ₀ s)(∇_{v0}S(x)(d))(vs).
```
This is the section-level B-rule inversion
`covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator`
(`MovingFrameDiffCurvTraceSection`, sorry-free) rearranged to isolate the carrier: it identifies the
operator-field carrier `appCc (covGrad Φ₀) S` with the *differentiated* frame-summed pure-`R` trace
minus the `R(∇S)` spectator — the `(∇R)`-on-`S` summand of `∇(∑ᵢ R(Bᵢ, ·) S)`.

The covariant derivative `∇_{v0}(pureRGenuineDiffOp g 0 s S)` is carried as a single covariant
derivative of the (frame-free in value) order-`0` trace; its further pointwise unfolding into the
slot-wise base-tangent differentiated curvature `∑ₖ (∇_{v0} R)(slot k)` — through a `smoothExtensionTangent`
direction reading — is the chart-selection-unbounded moving-frame content that is *false* pointwise on a
normal manifold (sound only after frame-summing and integrating), and is the genuine content of the
downstream integrated Bochner–Weitzenböck identity. -/
theorem genuineDiffCurvSection_unit_eval_eq_covGrad_pureR_sub_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  have h := covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (I := I) (M := M) g s S x d v0 vs
  rw [h]
  ring

/-- **The integrated carrier pairing in operator-field form (the form the curvature-line assembly
consumes).** For covariant rank `s` and smooth compactly-supported `(0, s)`-tensor `S`, the global
metric `L²` pairing of the differentiated-curvature carrier `genuineDiffCurvSection g s S` against
`∇S = covGrad g 0 s S` is the operator-field integration-by-parts value
```
⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}
  = −⟨Δ_∇(pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²},
```
with `Δ_∇ := rawTensorConnLapSmooth g 0 s` the rough connection Laplacian (the frame trace
`∑ⱼ ∇²_{Bⱼ, Bⱼ}`) and `pureRGenuineDiffOp g 0 s S = appCc (curvOpField g s) S` the order-`0` frame-summed
pure-Riemann curvature trace (the frame-trace value `curvOpField_appCc_unit_eval_eq_riemannOp_frameTrace`).
This expresses the carrier's cross-pairing through the rough Laplacian of the *frame-summed* curvature
trace paired against `S` and the passenger-slot curvature bilinear of `∇S`.

This is the **integrated** differentiated-curvature pairing the curvature-line assembly reads: the
pointwise per-direction match of the carrier with the slot-wise differentiated-curvature trace is *false*
on a normal manifold (the `smoothExtensionTangent` direction reading is chart-selection-unbounded on
`S²`), so only this summed, integrated operator-field form is sound. It is the differentiated-curvature
integration-by-parts identity `tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg`
(`MovingFrameDiffCurvTraceSection`, sorry-free) re-homed in the curvature-line bridge, with the order-`0`
trace exhibited as the frame-summed curvature operator action.

**`s = 0` litmus.** At scalar rank the carrier vanishes (`genuineDiffCurvSection_zero_eq_zero`), so the
left-hand pairing is `0`; on the right both terms vanish (the order-`0` scalar trace
`pureRGenuineDiffOp g 0 0 f = 0`, and the passenger-slot action of `curvOpField g 0 = 0` is `0`),
consistent with the scalar Bochner content carrying the differentiated curvature entirely in the
Ricci-trace channel downstream. -/
theorem tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg_pureR_form
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
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg (I := I) (M := M) g s S

end Connection
end Integral
end DifferentialGeometry

end
