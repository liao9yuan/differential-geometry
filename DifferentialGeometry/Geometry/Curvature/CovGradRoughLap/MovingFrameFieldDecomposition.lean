import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovariantIntegrationByParts
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameWeitzenbockRemainder

/-!
# The genuine moving-frame third-order Weitzenböck field decomposition (order-separated form)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
deepest classical moving-frame curvature-endomorphism primitive of the rank-generic order-`2`
rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`): the
**order-separated genuine curvature field decomposition** of `Curv S` into its two genuine
curvature contributions (the pure-Riemann field `R(∇S)`, genuinely `rfns(∇S)`-order, and the
differentiated-curvature field `(∇R) S`, genuinely `rfns(S)`-order) together with a moving-frame
remainder that is genuinely `rfns(∇²S)`-order *and* integrates to zero against `∇S`.

This is the genuine moving-frame third-order Bochner–Weitzenböck content at general rank. It is the
single primitive `pointwiseTensorCurv_genuineFields_bracketFree_curvatureCore` is assembled from (the
bracket-free `L²` pairing follows from the integrated divergence-nullity recorded here by left
additivity of the `L²` pairing), and through it the entire genuine-field tower of
`PointwiseTensorCurvL2Bound.lean` (`exists_pointwiseTensorCurv_genuineFields_proportional_spectralPairing`
and its consumers). It is posited here as the precise genuine curvature primitive (`sorry`), to be
discharged by the orchestrator.
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

/-- **Posited genuine moving-frame third-order Bochner–Weitzenböck field decomposition
(order-separated genuine fields, `∇²S`-order remainder, integrated divergence-nullity).** For a
closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` admits
two *genuine curvature* fields `Gcurv, GcurvDeriv : SmoothCcTensor g 0 (s + 1)` — the section-level
packagings of the pure-Riemann contraction `R(∇S)` (the frame-sum of `riemannOp` on the gradient
field `∇S = covGrad g 0 s S`) and the differentiated-curvature contraction `(∇R) S`
(`covGradCurvatureContraction`) — with the three order-separated fibre bounds and the integrated
divergence-nullity of the moving-frame remainder `Curv S − Gcurv − GcurvDeriv`:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the `∇R` field, sum-order (the
  gauge-glued tensorial differentiated-curvature section, Leibniz defect in the sum);
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the
  moving-frame / frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order
  Weitzenböck cancellation of the top-order `∇³S` terms by the iterated Ricci identity, with the
  lower Leibniz-defect terms in the sum;
* `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0` — the integrated divergence-nullity: the moving-frame
  remainder is a total covariant divergence of an `∇S`-order field, so it integrates by parts to
  zero against `∇S`.

**Why this is TRUE.** Fibrewise, `pointwiseTensorCurv_toSection_eq_frame_sum` reads
`Curv S (x) = ∑ᵢ [∇²_{Bᵢ,Bᵢ}(∇S)(x) − covGradBundleEquiv (∇·∇²_{Bᵢ,Bᵢ} S)(x)]` over the
`g_x`-orthonormal frame `Bᵢ = smoothOrthoFrame g x i`. Reconstructing the `(0, s + 1)` field from
its slot-`0` curried slices (`riemannianFiberNormSq_succ_eq_sum_slot0Curry`) and applying the
directional genuine/bracket split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(`Tensor3rdCurv_eq_genuine_add_bracket`,
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen`) to each slice expresses
`Curv S = Gcurv + GcurvDeriv + (moving-frame remainder)`, with `Gcurv` the frame-sum of the
pure-Riemann contraction `riemannOp (tensorCov g 0 (s+1)) x Bᵢ · (∇S(x))` (the Ricci identity on
the gradient field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), `GcurvDeriv` the frame-sum
of `covGradCurvatureContraction`, and the remainder `tensor3rdCurvBracket` plus the frame-trace
discrepancy `covGradRoughLapTraceDiscrepancy` and the moving-frame residual
`covGradRoughLapMovingFrameResidual`.

* The fibre bound on `Gcurv` is `rfns(∇S)`-order: each summand is a bundled curvature operator on
  `∇S(x)`, fibre-bounded by `riemannOp_covGrad_fiberNormSq_le_gen`
  (`rfns(R_x(v, w)(∇S)) ≤ Cx · g(v,v) · g(w,w) · rfns(∇S)`); the per-point curvature constant `Cx`
  and the frame Gram scalars are continuous on the compact `M`, so their sup gives a single uniform
  proportional constant `(Cper s)²` (the order-separated form of `exists_uniform_…_riemannOp_bound`,
  upgraded from a uniform constant to a bound proportional to `rfns(∇S)`).
* The fibre bound on `GcurvDeriv` is `rfns(S)`-order: it is the covariant gradient of the curvature
  contraction of `S`, fibre-bounded proportional to `rfns(S)` by the order-separated form of
  `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`.
* The remainder bound is `rfns(∇²S)`-order: after the genuine curvature contractions are removed, the
  surviving moving-frame / frame-bracket discrepancy carries the bracket-jet `[Bᵢ, W]`, which is a
  contraction of the smooth frame data against the second covariant derivative `∇²S`; its top-order
  `∇³S` terms cancel by the iterated Ricci identity, leaving a genuinely `∇²S`-order tensorial field
  (`riemannianFiberNormSq_tensor3rdCurvGenuine_le` controls the genuine part; the bracket fibre order
  controls the discrepancy). This cancellation is *false term-by-term* through
  `smoothExtensionTangent`; only the tensorial sum is `∇²S`-order — the irreducible moving-frame
  content.
* The integrated divergence-nullity is the covariant Green / integration-by-parts identity: the
  moving-frame remainder is a total covariant divergence `∑ᵢ ∇_{Bᵢ}(⟨·, ·⟩)` of an `∇S`-order field,
  so `integral_tensorInner_tangentAction_add_smul_divergence_eq_zero` (equivalently the rank-generic
  Green identity `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`) integrates it to zero
  against `∇S`.

**Non-vacuity.** The zero witness `Gcurv = GcurvDeriv = 0` is rejected: the remainder bound would
then read `rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)`, which is *false* (the defect genuinely carries the
`rfns(S)` and `rfns(∇S)` orders too), and the nullity would read `⟨Curv S, ∇S⟩_{L²} = 0`, which
equals `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_integrated_covGrad_l2_normSq` and is *false* on
a non-flat manifold. So the genuine curvature fields must carry the actual curvature content.

This is the deepest moving-frame curvature-endomorphism content at general rank; it is posited here
as the precise genuine curvature primitive and discharged by the orchestrator. -/
theorem exists_pointwiseTensorCurv_movingFrameField_orderSeparated_divergenceNull
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  classical
  obtain ⟨Cper, hCper_nn, hfields⟩ :=
    pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, Grem, hsplit, hcurv, hcurvDeriv, hrem, hnull⟩ := hfields s S
  have hGrem_eq :
      Grem = pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv := by
    rw [hsplit]; abel
  refine ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, ?_, ?_⟩
  · intro x
    have hx := hrem x
    rwa [hGrem_eq] at hx
  · rw [← hGrem_eq]; exact hnull

end Connection
end Integral
end DifferentialGeometry

end
