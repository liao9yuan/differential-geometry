import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP

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
* `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` — the companion `pointwiseTensorCurv` fibre
  bound `rfns(Curv S)(x) ≤ (C s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` feeding the remainder
  order `(4')`, the order-`2` commutator-defect fibre order homed *upstream* of the moving-frame spine
  (posited, so the consuming anchor stays upstream of the downstream `L²` bound, no import cycle).
* `genuineDiffCurv_crossPairing_remainder_nullity` — the genuine integrated moving-frame nullity for the
  concrete section, `⟨pointwiseTensorCurv g s S − GcurvSection g s S − genuineDiffCurvSection g s S,
  ∇S⟩_{L²} = 0`: the third-order moving-frame Weitzenböck IBP-telescoping content (the moving-frame
  remainder, including the gauge-glued section's Leibniz defect, telescopes into a total covariant
  divergence whose integral over the closed manifold vanishes), **posited** as the genuine
  differentiated-curvature leaf of the curvature line.
* `genuineDiffCurv_crossPairing_value` — the genuine differentiated-curvature cross-pairing value
  `⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`,
  **proved by composition** over `genuineDiffCurv_crossPairing_remainder_nullity` (the
  left-additivity bracket-free-pairing reduction
  `tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity` chained
  with the sorry-free Weitzenböck value `weitzenbock_curvature_crossPairing_value`), feeding the
  integrated-nullity producer `movingFrameNullity_of_genuineCrossPairingValue` verbatim with
  `Gcd := genuineDiffCurvSection g s S`.
* `tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg` — the differentiated-curvature cross-pairing's
  integration-by-parts formula `⟨Gcd, ∇S⟩_{L²} = −⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²} −
  ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²}`, the operator-field integration-by-parts identity
  `tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) specialised to the frame-free
  curvature operator field, expressing `⟨Gcd, ∇S⟩_{L²}` through the rough Laplacian of the order-`0`
  curvature trace and the passenger-slot curvature bilinear of `∇S` (sorry-free).

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

/-- **Posited upstream companion `pointwiseTensorCurv` fibre bound feeding the remainder order `(4')`
(the order-`2` commutator-defect fibre order, homed upstream of the moving-frame spine).** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such
that, at every covariant rank `s`, for every smooth compactly-supported `(0, s)`-tensor `S`, and at
*every point* `x`, the intrinsic fibre norm of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` is bounded by `(C s)²` times the **sum** of the intrinsic fibre
norms of `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the commutator defect.** By definition
`Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`PointwiseTensorBochner`), i.e. the rough Laplacian of the gradient
field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame traces of
the second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`) and commuting the
two derivative slots by the rank-`(0, s + 1)` Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), the
top-order `∇³S` terms cancel: the difference is a sum of (i) curvature contractions of the gradient
field `R(∇S)`, each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via the uniform curvature fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen`, plus (ii) genuine `(∇R) S` and frame-derivative terms of
`rfns(S)`-order, plus (iii) a residual `∇²S`-order moving-frame remainder. Aggregating the three over
the finite frame with the per-point curvature sup made *uniform* over `M` by compactness
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator `g`-norm sup)
gives the single nonnegative valence-dependent `C`. The full quantitative aggregation is the order-`2`
commutator-defect curvature input; it is posited here (homed *upstream* of the moving-frame
partition-of-unity spine so the anchor below can consume it without an import cycle through the
downstream `L²` bound). It is the rank-generic analogue of the order-separated curvature field
decomposition `exists_pointwiseTensorCurv_orderSeparated_field` (`PointwiseTensorCurvL2Bound`,
downstream, posited `sorry`).

**Non-vacuity (the bound rejects the degenerate `C ≡ 0` on a non-flat manifold).** With `C s = 0` the
bound would force `rfns(Curv S)(x) = 0`, i.e. `Δ_∇(∇S) = ∇(Δ_∇ S)` at every point — the covariant
derivatives commute through the rough Laplacian. This is *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S`: the commutator defect `Curv S` is exactly the genuine third-order Weitzenböck
curvature field `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²} = ⟨Curv S, ∇S⟩_{L²}`
(`weitzenbock_integrated_covGrad_l2_normSq`), which is nonzero when curvature is present. So `C` is
genuinely positive. The body is `sorry`; consumers transitively depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurv_fiberNormSq_bound_upstream
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
  sorry

/-- **Posited genuine differentiated-curvature integrated moving-frame nullity (the third-order
moving-frame Weitzenböck IBP-telescoping content, in remainder-orthogonality form).** For a closed
smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the moving-frame remainder of the order-`2`
commutator defect — `Curv S − GcurvSection g s S − genuineDiffCurvSection g s S`, where
`Curv S := pointwiseTensorCurv g s S`, `Gcurv := GcurvSection g s S` is the concrete pure-Riemann
`R(∇S)` trace section and `Gcd := genuineDiffCurvSection g s S` is the gauge-glued tensorial `(∇R) S`
differentiated-curvature trace section — against `∇S := covGrad g 0 s S` vanishes:

```
⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S, ∇S⟩_{L²} = 0.
```

**Why this is TRUE — the moving-frame remainder is a total covariant divergence.** The order-`2`
commutator defect splits (in the slot-`0` witness frame,
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`,
`PointwiseTensorBochnerFieldSplit`) into the genuine third-order curvature field and the moving-frame /
frame-bracket remainder; the genuine field splits further
(`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`) into the pure-Riemann `R(∇S)` trace (reconstructing
`Gcurv = GcurvSection g s S`, `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`) and the
differentiated-curvature `(∇R) S` trace `genuineThirdCurvFieldFibCovDeriv`. The gauge-glued tensorial
`Gcd = genuineDiffCurvSection g s S` (the operator-field action `appCc (covGrad (Φ₀ s)) S` of the
covariant derivative of the frame-free curvature operator `Φ₀ s`) carries the `(∇R) S` content up to a
Leibniz defect; subtracting `Gcurv + Gcd` from `Curv S` leaves the frame-bracket field together with
that Leibniz defect — both of which, paired against `∇S` and summed over the `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i`, telescope into a total covariant divergence
(`integral_frameSummed_covDeriv_combined_eq_zero`, `integral_tensorInner_covDeriv_combined_eq_zero`,
`CovariantIntegrationByParts`) of an honest smooth `∇S`-order tangent field whose integral over the
closed manifold vanishes (`integral_divergence_eq_zero_of_hasCompactSupport`). The `∇³S`-cancellation
and the divergence form are *false term-by-term* through `smoothExtensionTangent`; only the tensorial
frame-summed remainder is `∇²S`-order and a total covariant divergence. This is the genuine third-order
moving-frame Weitzenböck IBP-telescoping content for the *concrete* section — the irreducible
differentiated-curvature leaf of the curvature line, posited here. It is the rank-`0` /
concrete-`Gcd` analogue of the integrated nullity carried existentially by the sibling tri-split nodes
`exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`) and `exists_pointwiseTensorCurvRS_genuineTriSplit_divergence`
(`MovingFrameGenuineFieldPairingRS`, posited `sorry`), specialised to the concrete operator-field
section `Gcd = genuineDiffCurvSection g s S` rather than an existentially-chosen field; the producer
chains of those siblings depend on `exists_movingCentreDiffCurvSection_splitDivergenceDatum`
(`MovingFrameDiffCurvAnchor`), which consumes *this* node, so this is the genuine source — not a
consequence — of the concrete-section nullity.

**Non-vacuity (the nullity rejects the degenerate `Gcd = 0` on a non-flat manifold — and is distinct
from the value `genuineDiffCurv_crossPairing_value` it proves).** This is the *orthogonality of the
moving-frame remainder* — an integrated `= 0` — not a value equality, so it is genuine mathematical
input (no hypothesis-packaging: its conclusion is `⟨Grem, ∇S⟩_{L²} = 0`, not the value
`‖Δ_∇ S‖² − ‖∇²S‖²` that the downstream theorem concludes). With `genuineDiffCurvSection g s S = 0`
it would force `⟨Curv S − GcurvSection g s S, ∇S⟩_{L²} = 0`, i.e. the pure-Riemann pairing
`⟨GcurvSection g s S, ∇S⟩_{L²}` alone carries `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`
(`weitzenbock_curvature_crossPairing_value`); *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S`, where the differentiated-curvature `(∇R) S` content is genuinely missing from the
pure-Riemann trace. So the differentiated-curvature section `Gcd` genuinely carries the missing `(∇R) S`
content. The body is `sorry`; consumers transitively depend on `sorryAx`. -/
theorem genuineDiffCurv_crossPairing_remainder_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  sorry

/-- **Genuine differentiated-curvature cross-pairing value (the third-order moving-frame Weitzenböck
IBP telescoping, in cross-pairing form).** For a closed smooth Riemannian manifold `(M, g)`, every
covariant rank `s`, and every smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²`
pairing of the genuine curvature fields `GcurvSection g s S + genuineDiffCurvSection g s S` (the
pure-Riemann `R(∇S)` trace section `Gcurv` plus the gauge-glued tensorial `(∇R) S`
differentiated-curvature trace section `Gcd`) against `∇S := covGrad g 0 s S` equals the genuine
Weitzenböck curvature integral

```
⟨Gcurv + Gcd, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

**Proof (composition glue over the integrated moving-frame nullity, sorry-free downstream).** The
genuine fields carry the entire defect cross-pairing: from the integrated moving-frame nullity
`⟨Curv S − Gcurv − Gcd, ∇S⟩_{L²} = 0` (`genuineDiffCurv_crossPairing_remainder_nullity`, the posited
third-order Weitzenböck IBP-telescoping content for the concrete section), the purely-algebraic
left-additivity reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm`, sorry-free) gives the bracket-free `L²` pairing
`⟨Gcurv + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`; chaining with `weitzenbock_curvature_crossPairing_value`
(`MovingFrameIntegratedNullity`, sorry-free — the integrated order-`2` Weitzenböck identity
`⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`) yields the value. The body thus transits only the
posited integrated-nullity leaf `genuineDiffCurv_crossPairing_remainder_nullity`; consumers
transitively depend on its `sorryAx`. It feeds the integrated-nullity producer
`movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`) verbatim as its
hypothesis `hval` with `Gcd := genuineDiffCurvSection g s S`. -/
theorem genuineDiffCurv_crossPairing_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S +
          genuineDiffCurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  have hpair :=
    tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S)
      (genuineDiffCurvSection (I := I) (M := M) g s S)
      (genuineDiffCurv_crossPairing_remainder_nullity (I := I) (M := M) g s S)
  rw [hpair, weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]

/-- **The differentiated-curvature cross-pairing's integration-by-parts formula (the tensorial
bookkeeping for the concrete `(∇R) S` section).** For a closed smooth Riemannian manifold `(M, g)`,
covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing
of the gauge-glued tensorial differentiated-curvature section `genuineDiffCurvSection g s S` (the
`(∇R) S` field, the operator-field action `appCc (∇Φ₀ s) S`) against `∇S = covGrad g 0 s S` is

```
⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}
  = −⟨Δ_∇ (pureRGenuineDiffOp g 0 s S), S⟩_{L²}
    − ⟨appCc (slotExtend (Φ₀ s)) (∇S), ∇S⟩_{L²},
```

with `Δ_∇ := rawTensorConnLapSmooth g 0 s` the rough connection Laplacian, `pureRGenuineDiffOp g 0 s S`
the order-`0` moving-frame pure-Riemann curvature trace (the action `appCc (Φ₀ s) S` of the curvature
operator field `Φ₀ s := curvOpField g s`), and `∇S := covGrad g 0 s S`.

**Proof.** This is the operator-field integration-by-parts identity
`tensorL2Inner_appCc_covGrad_covGrad_eq_neg` (`OperatorFieldPairingIBP`) specialised to the frame-free
curvature operator field `Φ₀ s = curvOpField g s`.  The differentiated-action `appCc (∇Φ₀ s) S` is
`genuineDiffCurvSection g s S` by definition, and the order-`0` action `appCc (Φ₀ s) S` is
`pureRGenuineDiffOp g 0 s S` by the operator-field base identity
`exists_pureRGenuineDiffOp_base_appCc` (the `Classical.choose` spec defining `curvOpField`).

This expresses the differentiated-curvature cross-pairing in terms of (i) the rough Laplacian of the
order-`0` curvature trace `pureRGenuineDiffOp g 0 s S` paired against `S`, and (ii) the passenger-slot
curvature bilinear of `∇S` with itself.  The passenger-slot operator field `slotExtend (Φ₀ s)` is *not*
the next-rank curvature operator `Φ₀ (s + 1)` (it leaves the inserted leading slot a spectator and acts
by the rank-`s` curvature endomorphism on the trailing slots, whereas `Φ₀ (s + 1)` contracts the
leading slot with the curvature direction), so the second term is a genuine curvature bilinear, not a
re-indexed order-`0` trace pairing — it is carried as-is. -/
theorem tensorL2Inner_genuineDiffCurvSection_covGrad_eq_neg
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
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hgen := tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hgen
  exact hgen

end Connection
end Integral
end DifferentialGeometry

end
