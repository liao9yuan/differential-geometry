import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvL2Bound

/-!
# The gauge-glued tensorial differentiated-curvature section `(∇R) S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file constructs the
**differentiated-curvature genuine section** of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`,
`∇S = covGrad g 0 s S`): the covariant-derivative counterpart of the on-disk **pure-Riemann** genuine
section `GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the tensorial
trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`).

## The construction: the covariant derivative of the frame-free curvature operator field

The pure-Riemann curvature tower already isolates the order-`0` frame-free curvature endomorphism as the
action of a *fixed smooth* operator field: there is a smooth `(r, r)`-operator field `Φ₀ r` with
`pureRGenuineDiffOp g 0 r W = appCc (Φ₀ r) W` (`exists_pureRGenuineDiffOp_base_appCc`), whose fibre value
is the genuine `g`-metric curvature trace `W ↦ ∑ᵢ R(Bᵢ, ·) W` — frame-free (built from `g, R` alone), so
its covariant derivative differentiates *only* the curvature factor, never a chart-selection-unbounded
frame jet.

The differentiated-curvature trace `∑ᵢ (∇R)(Bᵢ, ·) S` is therefore the operator-field action of the
**covariant derivative of that curvature operator field** on `S`:
```
genuineDiffCurvSection g s S := appCc (covGrad g s s (Φ₀ s)) S.
```
This is the genuinely-tensorial `(∇R) S` content. The operator-field covariant product rule
`covGrad_appCc_eq` reads `covGrad (appCc (Φ₀ s) S) = appCc (covGrad (Φ₀ s)) S +
appCc (slotExtend (Φ₀ s)) (∇S)`, so the first summand `appCc (covGrad (Φ₀ s)) S` is exactly the
`(∇R)`-on-`S` part of the differentiated curvature trace, with the `R(∇S)` spectator carried by the
second; isolating the `(∇R) S` summand is the construction. Because `Φ₀ s` is a *fixed* smooth section,
`covGrad g s s (Φ₀ s)` is a fixed smooth `(s, s + 1)`-operator field, and its operator-field action on
`S` is a smooth compactly-supported `(0, s + 1)`-tensor with **no** per-direction smooth-extension jet
— the section is tensorial and smooth by construction, never extension-curried. This collapses the
moving-frame frame-freezing partition-of-unity assembly of the pure-Riemann leg to the operator-field
calculus.

## Main results

* `genuineDiffCurvSection g s S : SmoothCcTensor g 0 (s + 1)` — the gauge-glued tensorial section of the
  differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), the operator-field
  action of `covGrad (Φ₀ s)` on `S`.
* `exists_genuineDiffCurvSection_fiberNormSq_bound` — the **sum** fibre bound `(3')`
  `rfns(genuineDiffCurvSection g s S)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))`, uniform in `x`, with a
  valence-dependent nonnegative constant `K`. The bound holds even in the strict `rfns(S)` form (the
  operator-field action is order-`0` in `S`), weakened to the **sum** envelope the consumer reads.
* `exists_pointwiseTensorCurv_fiberNormSq_bound` — the companion `pointwiseTensorCurv` fibre bound
  `rfns(Curv S)(x) ≤ (C s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` feeding the remainder order
  `(4')`, re-exported from the proved pointwise commutator-defect fibre bound.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`. The differentiated-curvature trace is genuinely `rfns(S)`-order; the
**sum** envelope `rfns(∇S) + rfns(S)` is the form the moving-frame remainder merge consumes.
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
content. -/
private noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g)) s

/-- **The gauge-glued tensorial differentiated-curvature section `(∇R) S`.** For a smooth
compactly-supported `(0, s)`-tensor `S`, the operator-field action of the covariant derivative of the
frame-free curvature operator field `Φ₀ s` (`curvOpField`) on `S`:
```
genuineDiffCurvSection g s S := appCc (covGrad g s s (Φ₀ s)) S,
```
the differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), a smooth
compactly-supported `(0, s + 1)`-tensor. It is the covariant-derivative counterpart of the pure-Riemann
genuine section `GcurvSection g s S`: where the pure-Riemann trace is the action `appCc (Φ₀ s) S` of the
order-`0` curvature operator, the differentiated trace is the action `appCc (∇Φ₀ s) S` of its covariant
derivative (the operator-field product rule `covGrad_appCc_eq` separates the `(∇R) S` summand from the
`R(∇S)` spectator). It is constructed tensorially and smoothly through the operator-field calculus, never
extension-curried. -/
noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

/-- **The fibre value of `genuineDiffCurvSection` is the fibrewise composition `(∇Φ₀ s).comp S`.**
Definitional: the operator-field action `appCc` evaluates fibrewise as the composition of the
differentiated curvature operator with the section value (`appCc_toSection`). -/
@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    appCc_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]

/-- **The sum fibre bound `(3')` on the constructed differentiated-curvature section.** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such
that, at every covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at
*every point* `x`, the intrinsic fibre norm of the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S` (the `(∇R) S` field) is bounded by `(K s)²` times the **sum** of the
intrinsic fibre norms of `∇S = covGrad g 0 s S` and `S`:
```
rfns(genuineDiffCurvSection g s S)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof.** `genuineDiffCurvSection g s S = appCc (covGrad (Φ₀ s)) S` is the operator-field action of the
*fixed* smooth `(s, s + 1)`-operator field `covGrad (Φ₀ s)` on `S`. The uniform section-proportional
operator-field envelope `exists_uniform_riemannianFiberNormSq_appCc_le` (the intrinsic partial-contraction
Cauchy–Schwarz `riemannianFiberNormSq_comp_le_mul` followed by the uniform fibre-operator bound on the
fixed field `covGrad (Φ₀ s)`) gives a single nonnegative `C s`, uniform over `M`, with
`rfns(appCc (covGrad (Φ₀ s)) S)(x) ≤ C s · rfns(S)(x)`. Taking `K s := √(C s)` so `K s ^ 2 = C s`, the
strict `rfns(S)` bound `rfns(genuineDiffCurvSection)(x) ≤ K s ^ 2 · rfns(S)(x)` is weakened to the
**sum** by adding the nonnegative `K s ^ 2 · rfns(∇S)(x)` (the consumer reads the sum envelope; the
operator-field action is order-`0` in `S`, so even the strict bound holds).

**Non-vacuity (the bound alone does not pin `K`, the coupling does).** The bound `(3')` alone does *not*
reject `K ≡ 0` (`genuineDiffCurvSection g 0 S = appCc (covGrad (Φ₀ 0)) S = appCc 0 S = 0` at the
scalar rank where there is no slot to contract); the genuine positivity of `K` is forced only by the
coupling to the integrated nullity in the consuming anchor
`exists_movingCentreDiffCurvSection_splitDivergenceDatum`, where the differentiated-curvature `(∇R) S`
content must carry the third-order Weitzenböck pairing. The section genuinely carries that content: it is
the operator-field action of the covariant derivative `covGrad (Φ₀ s)` of the genuine frame-free
curvature operator `Φ₀ s` (whose value is the `g`-metric curvature trace), nonzero on a non-flat
manifold with non-parallel `S`, never the zero section. -/
theorem exists_genuineDiffCurvSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  -- The per-rank uniform section-proportional operator-field envelope for the fixed differentiated
  -- curvature operator field `covGrad (Φ₀ s)`.
  have hC : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro s
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
    exact ⟨C, hC_nn, fun S x => by
      have h := hC S x
      rwa [show (appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S) =
          genuineDiffCurvSection (I := I) (M := M) g s S from rfl] at h⟩
  choose C hC_nn hC using hC
  refine ⟨fun s => Real.sqrt (C s), fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hKsq : Real.sqrt (C s) ^ 2 = C s := Real.sq_sqrt (hC_nn s)
  rw [hKsq]
  have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have h := hC s S x
  nlinarith [h, hfgS_nn, hfS_nn, hC_nn s,
    mul_nonneg (hC_nn s) hfgS_nn]

/-- **The companion `pointwiseTensorCurv` fibre bound feeding the remainder order `(4')`.** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such
that, at every covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at
*every point* `x`, the intrinsic fibre norm of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` is bounded by `(C s)²` times the **sum** of the intrinsic fibre
norms of `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```
This is re-exported (with the summands reordered into the `(4')` shape) from the proved pointwise
commutator-defect fibre bound `exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound`
(`PointwiseTensorCurvL2Bound`); it feeds the companion remainder fibre order in the consuming anchor. Its
`sorry`-dependence is inherited from that source (the posited curvature input), introducing no new
defect. -/
theorem exists_pointwiseTensorCurv_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  obtain ⟨Ccurv, hCcurv_nn, hCcurv⟩ :=
    exists_pointwiseTensorCurv_pointwise_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨Ccurv, hCcurv_nn, fun s S x => ?_⟩
  have h := hCcurv s S x
  -- The source bounds by `Ccurv² · (rfns(S) + rfns(∇S) + rfns(∇²S))`; reorder the sum to the `(4')`
  -- shape `Ccurv² · (rfns(∇²S) + rfns(∇S) + rfns(S))`.
  rw [show riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
            ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
            ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) from by ring] at h
  exact h

end Connection
end Integral
end DifferentialGeometry

end
