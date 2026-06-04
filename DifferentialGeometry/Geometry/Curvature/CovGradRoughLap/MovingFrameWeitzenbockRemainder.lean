import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovariantIntegrationByParts

/-!
# The genuine moving-frame third-order Weitzenböck remainder (named-field divergence form)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
single genuinely-irreducible moving-frame curvature-endomorphism primitive underneath the
rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`): the
**named-field** form of the genuine third-order Bochner–Weitzenböck decomposition, in which the
commutator defect is exhibited as an honest section-level sum of two genuine curvature fields and a
single moving-frame remainder field whose `L²` pairing against `∇S` vanishes.

This is the strictly-more-primitive curvature primitive: it records the genuine third-order
Weitzenböck content as the **named three-field split** `Curv S = Gcurv + GcurvDeriv + Grem` (an
explicit section equality, not an anonymous subtraction), with the three order-separated fibre
bounds and the integrated divergence-nullity `⟨Grem, ∇S⟩_{L²} = 0`. The order-separated
*divergence-null* form
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_divergenceNull` (which states the same
content with the anonymous subtraction `Curv S − Gcurv − GcurvDeriv` in place of the named field
`Grem`) is *proved* from this named form by identifying the anonymous subtraction with `Grem` (the
section identity is `abel`) and transferring the three fibre bounds and the integrated nullity
verbatim.
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

/-- **Posited genuine moving-frame third-order Bochner–Weitzenböck remainder (named-field
divergence form).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(0, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` admits a *named three-field* split into two genuine curvature
contraction fields `Gcurv, GcurvDeriv` and a single moving-frame remainder field `Grem`, all smooth
compactly-supported `(0, s + 1)`-tensors:

```
Curv S = Gcurv + GcurvDeriv + Grem,
```

with the four genuine third-order Weitzenböck properties:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-Riemann field `R(∇S)`, the frame-sum of the
  bundled curvature operator `riemannOp (tensorCov g 0 (s + 1))` on the gradient field
  `∇S = covGrad g 0 s S` (the Ricci identity on the gradient field
  `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), fibre-bounded `rfns(∇S)`-order by the
  proportional per-point curvature bound `riemannOp_covGrad_fiberNormSq_le_gen` upgraded to a single
  uniform proportional constant over the compact `M` (the per-point curvature operator norm and the
  frame Gram scalars are continuous, hence sup-bounded);
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · rfns(S)(x)` — the differentiated-curvature field `(∇R) S`, the
  frame-sum of `covGradCurvatureContraction`, fibre-bounded `rfns(S)`-order by the uniform
  differentiated-curvature sup `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`
  upgraded to a bound proportional to `rfns(S)`;
* `rfns(Grem)(x) ≤ (Cper s)² · rfns(∇²S)(x)` — the moving-frame / frame-bracket remainder
  (`tensor3rdCurvBracket` plus the frame-trace discrepancy and the moving-frame residual), genuinely
  `rfns(∇²S)`-order after the third-order Weitzenböck cancellation of the top-order `∇³S` terms by
  the iterated Ricci identity (`riemannianFiberNormSq_tensor3rdCurvGenuine_le` controls the genuine
  part; the bracket fibre order controls the discrepancy);
* `⟨Grem, ∇S⟩_{L²} = 0` — the integrated divergence-nullity: the moving-frame remainder is a total
  covariant divergence of an `∇S`-order field, so it integrates by parts to zero against `∇S` by the
  covariant integration-by-parts identity
  `integral_tensorInner_tangentAction_add_smul_divergence_eq_zero` (equivalently the rank-generic
  covariant Green identity `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`).

**Why this is TRUE.** Fibrewise, `pointwiseTensorCurv_toSection_eq_frame_sum` reads
`Curv S (x) = ∑ᵢ [∇²_{Bᵢ,Bᵢ}(∇S)(x) − covGradBundleEquiv (∇·∇²_{Bᵢ,Bᵢ} S)(x)]` over the
`g_x`-orthonormal frame `Bᵢ = smoothOrthoFrame g x i`. Reconstructing the `(0, s + 1)` field from its
slot-`0` curried slices (`riemannianFiberNormSq_succ_eq_sum_slot0Curry`) and applying the directional
genuine/bracket split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(`Tensor3rdCurv_eq_genuine_add_bracket`) to each slice expresses
`Curv S = Gcurv + GcurvDeriv + Grem`, with `Gcurv` the frame-sum of the pure-Riemann contraction
`riemannOp (tensorCov g 0 (s + 1)) x Bᵢ · (∇S(x))`, `GcurvDeriv` the frame-sum of
`covGradCurvatureContraction`, and `Grem` the bracket remainder (`tensor3rdCurvBracket` plus the
frame-trace discrepancy `covGradRoughLapTraceDiscrepancy` and the moving-frame residual
`covGradRoughLapMovingFrameResidual`). The genuine fields are fibre-bounded by the proportional
curvature / differentiated-curvature bounds (uniformized over the compact `M`); the remainder is
`∇²S`-order after the third-order Weitzenböck cancellation, and is a total covariant divergence of an
`∇S`-order field, so its `L²` pairing against `∇S` vanishes by the covariant Green / integration-by-
parts identity. This `∇³S`-cancellation is *false term-by-term* through `smoothExtensionTangent`;
only the tensorial sum is `∇²S`-order — the irreducible moving-frame content.

**Non-vacuity.** The zero witness `Gcurv = GcurvDeriv = 0`, `Grem = Curv S` is rejected: the
`Grem`-bound would read `rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)`, which is *false* (the defect genuinely
carries the `rfns(S)` and `rfns(∇S)` orders too), and the nullity would read `⟨Curv S, ∇S⟩_{L²} = 0`,
which equals `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_integrated_covGrad_l2_normSq` and is *false*
on a non-flat manifold. So the genuine curvature fields must carry the actual curvature content.

This is the genuinely-irreducible moving-frame curvature-endomorphism content at general rank,
posited here as the precise named-field divergence primitive and discharged by the orchestrator: its
construction requires the rank-generic moving-frame third-order Weitzenböck apparatus — the
general-rank curried-defect decomposition (the `_gen` lift of
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual`), the uniform-over-`M` proportional
curvature / differentiated-curvature bounds, and the divergence-form identification of the bracket
remainder — none of which is yet built at general rank in the library. -/
theorem pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcurv GcurvDeriv Grem : SmoothCcTensor g 0 (s + 1),
          pointwiseTensorCurv (I := I) (M := M) g s S = Gcurv + GcurvDeriv + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Grem.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x)) ∧
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
