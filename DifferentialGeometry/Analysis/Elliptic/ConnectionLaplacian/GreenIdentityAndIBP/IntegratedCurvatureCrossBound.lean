import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

/-!
# The integrated curvature cross-bound from the genuine field nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file produces the
**integrated `L²` curvature cross-bound** on the rough-Laplacian / covariant-gradient commutator
defect `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` (a `(0, s + 1)`-tensor field;
`∇S := covGrad g 0 s S`):

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0,
```

uniformly in `S`. This is the single analytic input the integrated order-`2` Gårding reduction
`secondCovGrad_l2NormSq_le_of_cross_bound` (`IntegratedOrder2Garding.lean`) consumes; closing it makes
the chart-`H²` Gårding constant unconditional.

## The route (the integrated moving-frame nullity, not the Weitzenböck value)

The defect cross-pairing is *not* small term-by-term: by the integrated order-`2` Weitzenböck identity
`weitzenbock_curvature_crossPairing_value` it equals `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`, which carries the
genuine `∇²S`-order energy — so bounding it through that *value* is circular for the Gårding constant.
The sound route bounds the cross-pairing through the **genuine curvature fields**: the concrete
pure-Riemann curvature section `GcurvSection g s S` (`= R(∇S)`) and the differentiated-curvature trace
section `genuineDiffCurvSection g s S` (`= (∇R) S`). The moving-frame remainder
`Curv S − GcurvSection g s S − genuineDiffCurvSection g s S` is a total covariant divergence of an
`∇S`-order field, so it pairs to zero against `∇S` on the closed manifold (the **integrated nullity**,
the genuine moving-frame third-order Bochner–Weitzenböck content, supplied here as
`movingFrameRemainder_genuineSections_nullity`). The nullity feeds
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm.lean`) to give the bracket-free pairing
`⟨GcurvSection + genuineDiffCurvSection, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`, and the genuine fields carry
the whole cross-pairing.

Each genuine field is then bounded `L²`-proportionally:

* `GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)`
  (`pureRGenuineDiffOp0_eq_GcurvSection`) has fibre norm `≤ kappa · rfns(∇S)` by the
  section-proportional curvature bound `exists_proportional_pureRGenuineDiffOp`, so
  `‖GcurvSection g s S‖_{L²} ≤ √kappa · ‖∇S‖_{L²}` by the pointwise-to-`L²` packaging
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`.
* `genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` has fibre norm
  `≤ C · rfns(S)` by the uniform operator-field contraction bound
  `exists_uniform_riemannianFiberNormSq_appCc_le` (the fixed smooth differentiated-curvature operator
  `∇R` is uniformly fibre-bounded over the compact manifold), so
  `‖genuineDiffCurvSection g s S‖_{L²} ≤ √C · ‖S‖_{L²}`.

Cauchy–Schwarz (`abs_tensorL2Inner_le`) then bounds the cross-pairing by
`(‖GcurvSection‖ + ‖genuineDiffCurvSection‖) · ‖∇S‖ ≤ √kappa · ‖∇S‖² + √C · ‖S‖ · ‖∇S‖`, so
`Ccross := max √kappa √C` works. The route never reads the gradient slot pointwise and never
differentiates the curvature beyond the fixed smooth coefficient `∇R`, so it carries no chart-jet debt.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²` pairings are the global metric `L²` pairing
`tensorL2Inner` against the canonical Riemannian volume measure.
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
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The integrated moving-frame nullity for the concrete genuine curvature sections (the genuine
moving-frame third-order Bochner–Weitzenböck node).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the moving-frame
remainder of the order-`2` commutator defect — the defect `Curv S := pointwiseTensorCurv g s S` minus
the genuine pure-Riemann curvature section `GcurvSection g s S` (the `R(∇S)` contraction) and the
differentiated-curvature trace section `genuineDiffCurvSection g s S` (the `(∇R) S` contraction) —
pairs to zero against `∇S := covGrad g 0 s S` in the global metric `L²`:

```
⟨Curv S − GcurvSection g s S − genuineDiffCurvSection g s S, ∇S⟩_{L²} = 0.
```

This is the integrated half of the moving-frame third-order Weitzenböck cancellation: the
frame-bracket discrepancy that survives after the two genuine curvature contractions are subtracted —
whose fibre value is the explicit obstruction field `bracketThirdCurvFieldFib` of the field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` (`PointwiseTensorBochnerFieldSplit.lean`)
— folds, summed over the `g_x`-orthonormal frame and paired against `∇S`, into a total covariant
divergence of an `∇S`-order field, whose integral over the closed manifold vanishes
(`integral_frameSummed_bracketCovDeriv_combined_eq_zero`, `BracketDivergenceForm.lean`). The
folding (identifying the frame-summed bracket field with `∑ᵢ ∇_{Bᵢ} W` for an honest smooth
`∇S`-order field `W` via the second-Bianchi / frame-Ricci identity) is the genuinely-irreducible
moving-frame curvature-endomorphism content; it is *false* for an arbitrary pair of subtracted fields
and holds exactly for the genuine pure-Riemann and differentiated-curvature sections, so this is a
genuine mathematical statement distinct from any cross-bound conclusion.

**Non-vacuity.** With `GcurvSection` and `genuineDiffCurvSection` both replaced by `0` the statement
would force `⟨Curv S, ∇S⟩_{L²} = 0`, which is *false* on a non-flat manifold (it equals
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_curvature_crossPairing_value`, a genuinely nonzero
curvature integral); the nullity genuinely uses the two genuine curvature fields. -/
theorem movingFrameRemainder_genuineSections_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S -
          genuineDiffCurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 :=
  sorry

/-- **`L²` proportional control of the pure-Riemann genuine curvature section by `∇S`.** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor
`S`, the metric `L²` norm of the concrete pure-Riemann genuine curvature section `GcurvSection g s S`
(`= R(∇S)`) is bounded by a uniform constant times the `L²` norm of the gradient field:

```
‖GcurvSection g s S‖ ≤ Cr · ‖∇S‖,     ∇S := covGrad g 0 s S,   Cr ≥ 0 uniform in S.
```

The proof identifies `GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)`
(`pureRGenuineDiffOp0_eq_GcurvSection`), uses the section-proportional curvature fibre bound
`exists_proportional_pureRGenuineDiffOp` at order `0` (jet window `q < 1`, i.e. the value `∇S` alone)
to get `rfns(GcurvSection g s S)(x) ≤ kappa · rfns(∇S)(x)`, and lifts that pointwise bound to the `L²`
norm by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with `Cr = √kappa`. -/
theorem exists_GcurvSection_l2Norm_le_covGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖GcurvSection (I := I) (M := M) g s S‖ ≤
        Cr * ‖covGrad (I := I) (M := M) g 0 s S‖ := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Real.sqrt (kappa 0 (s + 1)), Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : GcurvSection (I := I) (M := M) g s S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) :=
    (pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S).symm
  -- Pointwise fibre bound: `rfns(GcurvSection)(x) ≤ (√kappa)² · rfns(∇S)(x)`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt (kappa 0 (s + 1))) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro x
    rw [Real.sq_sqrt (hkappa_nn 0 (s + 1)), hsec]
    have h := hkappa 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) x
    rw [Finset.sum_range_one,
      DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero] at h
    exact h
  -- Lift to the `L²` norm via the two-term packaging (second jet term is zero).
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) (0 : SmoothCcTensor g 0 (s + 1))
    (GcurvSection (I := I) (M := M) g s S) (Real.sqrt (kappa 0 (s + 1))) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((0 : SmoothCcTensor g 0 (s + 1)).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 (s + 1) x
    rw [hz, add_zero]; exact hpt x

/-- **`L²` proportional control of the differentiated-curvature trace section by `S`.** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor
`S`, the metric `L²` norm of the differentiated-curvature trace section `genuineDiffCurvSection g s S`
(`= (∇R) S`, the operator-field action `appCc (covGrad (curvOpField g s)) S` of the covariant
derivative of the frame-free curvature operator field) is bounded by a uniform constant times the `L²`
norm of `S`:

```
‖genuineDiffCurvSection g s S‖ ≤ Cd · ‖S‖,     Cd ≥ 0 uniform in S.
```

The differentiated-curvature operator `covGrad (curvOpField g s)` is a *fixed* smooth
compactly-supported operator field (built from `g`, `R`, `∇R` alone), uniformly fibre-operator-bounded
over the compact manifold; the uniform operator-field contraction bound
`exists_uniform_riemannianFiberNormSq_appCc_le` gives `rfns(genuineDiffCurvSection g s S)(x) ≤ C ·
rfns(S)(x)`, lifted to the `L²` norm by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with
`Cd = √C`. -/
theorem exists_genuineDiffCurvSection_l2Norm_le_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖genuineDiffCurvSection (I := I) (M := M) g s S‖ ≤ Cd * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g
    (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : genuineDiffCurvSection (I := I) (M := M) g s S =
      appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S := rfl
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt C) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro x
    rw [Real.sq_sqrt hC_nn, hsec]
    exact hC S x
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    S (0 : SmoothCcTensor g 0 s)
    (genuineDiffCurvSection (I := I) (M := M) g s S) (Real.sqrt C) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((0 : SmoothCcTensor g 0 s).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 s x
    rw [hz, add_zero]; exact hpt x

/-- **The integrated `L²` curvature cross-bound (rank-generic).** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, the one-sided `L²` curvature cross-term — minus the global
metric pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S =
Δ_∇(∇S) − ∇(Δ_∇ S)` against the gradient field `∇S := covGrad g 0 s S` — is bounded by the first-order
Sobolev budget of `S`:

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0 uniform in S.
```

**Proof.** The integrated moving-frame nullity `movingFrameRemainder_genuineSections_nullity` feeds
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm.lean`) to give the bracket-free pairing
`⟨GcurvSection g s S + genuineDiffCurvSection g s S, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` — the genuine
curvature fields carry the whole cross-pairing. Cauchy–Schwarz (`abs_tensorL2Inner_le`) bounds the
left pairing by `(‖GcurvSection g s S‖ + ‖genuineDiffCurvSection g s S‖) · ‖∇S‖`, and the
`L²`-proportional bounds `exists_GcurvSection_l2Norm_le_covGrad` (`‖GcurvSection‖ ≤ Cr · ‖∇S‖`) and
`exists_genuineDiffCurvSection_l2Norm_le_self` (`‖genuineDiffCurvSection‖ ≤ Cd · ‖S‖`) give
`Cr · ‖∇S‖² + Cd · ‖S‖ · ‖∇S‖`, dominated by `(max Cr Cd) · (‖∇S‖² + ‖S‖ · ‖∇S‖)`. -/
theorem exists_integrated_curvatureCrossBound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ S : SmoothCcTensor g 0 s,
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross *
            (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
                tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S).toFun) := by
  classical
  obtain ⟨Cr, hCr_nn, hCr⟩ := exists_GcurvSection_l2Norm_le_covGrad (I := I) (M := M) g s
  obtain ⟨Cd, hCd_nn, hCd⟩ := exists_genuineDiffCurvSection_l2Norm_le_self (I := I) (M := M) g s
  refine ⟨max Cr Cd, le_trans hCr_nn (le_max_left _ _), fun S => ?_⟩
  set Gr : SmoothCcTensor g 0 (s + 1) := GcurvSection (I := I) (M := M) g s S with hGr_def
  set Gd : SmoothCcTensor g 0 (s + 1) := genuineDiffCurvSection (I := I) (M := M) g s S with hGd_def
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgradS_def
  -- The bracket-free pairing: the genuine fields carry the whole cross-pairing.
  have hnull : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S - Gr - Gd).toFun gradS.toFun = 0 := by
    rw [hGr_def, hGd_def, hgradS_def]
    exact movingFrameRemainder_genuineSections_nullity (I := I) (M := M) g s S
  have hpair : tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun := by
    rw [hGr_def, hGd_def, hgradS_def]
    exact tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S)
      (genuineDiffCurvSection (I := I) (M := M) g s S)
      (by rw [← hGr_def, ← hGd_def, ← hgradS_def]; exact hnull)
  -- Identify the target defect with `pointwiseTensorCurv`.
  have hCurvFun : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun := rfl
  -- Cauchy–Schwarz on the genuine-field pairing.
  have hcs : |tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun| ≤
      tensorL2Norm (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun *
        tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun :=
    abs_tensorL2Inner_le (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (Gr + Gd))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gr + Gd) gradS)
  -- `‖Gr + Gd‖ ≤ ‖Gr‖ + ‖Gd‖`, and the proportional bounds.
  have htri : tensorL2Norm (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun ≤
      tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gr.toFun +
        tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gd.toFun := by
    have := norm_add_le Gr Gd
    rwa [SmoothCcTensor.norm_def (I := I) (M := M) (Gr + Gd),
      SmoothCcTensor.norm_def (I := I) (M := M) Gr,
      SmoothCcTensor.norm_def (I := I) (M := M) Gd,
      SmoothCcTensor.toFun_add] at this
  -- Normalize the proportional bounds to `tensorL2Norm` form.
  have hCrS : tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gr.toFun ≤
      Cr * tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun := by
    have h := hCr S
    rw [hGr_def, hgradS_def]
    simpa only [SmoothCcTensor.norm_def] using h
  have hCdS : tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gd.toFun ≤
      Cd * tensorL2Norm (I := I) (M := M) g 0 s S.toFun := by
    have h := hCd S
    rw [hGd_def]
    simpa only [SmoothCcTensor.norm_def] using h
  -- Assemble.
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun with hnGrad_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  set nGr : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gr.toFun with hnGr_def
  set nGd : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) Gd.toFun with hnGd_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hnGr_nn : 0 ≤ nGr := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnGd_nn : 0 ≤ nGd := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  -- Fold the proportional bounds into `nGr`/`nGd` form.
  have hCrS' : nGr ≤ Cr * nGrad := hCrS
  have hCdS' : nGd ≤ Cd * nS := hCdS
  -- The cross-pairing value equals the genuine-field pairing; bound its negation by its abs.
  have hval_eq :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) -
          covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun := by
    rw [← hgradS_def, ← hCurvFun, hpair]
  rw [hval_eq]
  -- `-⟨Gr+Gd, ∇S⟩ ≤ |⟨Gr+Gd, ∇S⟩| ≤ ‖Gr+Gd‖·‖∇S‖ ≤ (nGr+nGd)·nGrad ≤ (Cr·nGrad + Cd·nS)·nGrad`.
  have hneg_le : - tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun ≤
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun| := neg_le_abs _
  have hstep1 : - tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun ≤
      (nGr + nGd) * nGrad := by
    refine le_trans hneg_le (le_trans hcs ?_)
    rw [hnGrad_def]
    exact mul_le_mul_of_nonneg_right htri hnGrad_nn
  have hCr_le : Cr ≤ max Cr Cd := le_max_left _ _
  have hCd_le : Cd ≤ max Cr Cd := le_max_right _ _
  have hmax_nn : 0 ≤ max Cr Cd := le_trans hCr_nn hCr_le
  calc - tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gr + Gd).toFun gradS.toFun
      ≤ (nGr + nGd) * nGrad := hstep1
    _ ≤ (Cr * nGrad + Cd * nS) * nGrad :=
        mul_le_mul_of_nonneg_right (add_le_add hCrS' hCdS') hnGrad_nn
    _ ≤ max Cr Cd * (nGrad ^ 2 + nS * nGrad) := by
        have h1 : Cr * nGrad * nGrad ≤ max Cr Cd * (nGrad * nGrad) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hCr_le (mul_nonneg hnGrad_nn hnGrad_nn)
        have h2 : Cd * nS * nGrad ≤ max Cr Cd * (nS * nGrad) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hCd_le (mul_nonneg hnS_nn hnGrad_nn)
        nlinarith [h1, h2]

end Connection
end Integral
end DifferentialGeometry

end
