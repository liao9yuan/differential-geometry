import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovariantIntegrationByParts
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineSectionOrderDivergence

/-!
# The genuine moving-frame third-order field decomposition (bracket-free-pairing form)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
strictly-more-primitive **bracket-free-pairing** form of the genuine moving-frame third-order
Bochner–Weitzenböck field decomposition of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`). It exhibits, at
every covariant rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, two genuine
curvature contraction fields `Gcurv, GcurvDeriv : SmoothCcTensor g 0 (s + 1)` — the section-level
packagings of the pure-Riemann contraction `R(∇S)` (the frame-sum of `riemannOp` on the gradient
field `∇S`) and the differentiated-curvature contraction `(∇R) S` (`covGradCurvatureContraction`) —
together with the three order-separated fibre bounds and the **bracket-free `L²` pairing**

```
⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}.
```

The bracket-free pairing is the integrated half of the moving-frame Weitzenböck cancellation: the
moving-frame remainder `Curv S − Gcurv − GcurvDeriv` is a total covariant divergence of an
`∇S`-order field, so it integrates by parts to zero against `∇S`, leaving the genuine fields to
carry the entire cross-pairing.

This bracket-free-pairing form is the precise primitive consumed by
`pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder`: the named-remainder field
`Grem := Curv S − Gcurv − GcurvDeriv`, with its integrated divergence-nullity
`⟨Grem, ∇S⟩_{L²} = 0`, is recovered from this pairing form through the purely-algebraic
bracket-free-pairing nullity reduction `tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing`
(left additivity of the `L²` pairing). The three order-separated fibre bounds transfer verbatim.

It is posited here as the precise genuine curvature primitive (`sorry`), to be discharged by the
orchestrator; see its docstring for the precise truth justification and the moving-frame curvature
apparatus it is constructed from.
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
(order-separated genuine fields, `∇²S`-order remainder, bracket-free `L²` pairing).** For a closed
smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` admits
two *genuine curvature* fields `Gcurv, GcurvDeriv : SmoothCcTensor g 0 (s + 1)` — the section-level
packagings of the pure-Riemann contraction `R(∇S)` (the frame-sum of the bundled curvature operator
`riemannOp (tensorCov g 0 (s + 1))` on the gradient field `∇S = covGrad g 0 s S`) and the
differentiated-curvature contraction `(∇R) S` (`covGradCurvatureContraction`) — with the three
order-separated fibre bounds and the bracket-free `L²` pairing:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the `∇R` field, sum-order (the
  gauge-glued tensorial differentiated-curvature section, the Leibniz defect absorbed in the sum);
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the
  moving-frame / frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order
  Weitzenböck cancellation of the top-order `∇³S` terms by the iterated Ricci identity, with the lower
  Leibniz-defect terms in the sum;
* `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` — the bracket-free `L²` pairing: the
  moving-frame remainder is a total covariant divergence of an `∇S`-order field, so it integrates
  by parts to zero against `∇S`, leaving the genuine fields to carry the entire cross-pairing.

**Why this is TRUE.** Fibrewise, `pointwiseTensorCurv_toSection_eq_frame_sum` reads
`Curv S (x) = ∑ᵢ [∇²_{Bᵢ,Bᵢ}(∇S)(x) − covGradBundleEquiv (∇·∇²_{Bᵢ,Bᵢ} S)(x)]` over the
`g_x`-orthonormal frame `Bᵢ = smoothOrthoFrame g x i`. Reconstructing the `(0, s + 1)` field from
its slot-`0` curried slices (`riemannianFiberNormSq_succ_eq_sum_slot0Curry`) and applying the
directional genuine/bracket split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(`Tensor3rdCurv_eq_genuine_add_bracket`,
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen`) to each slice — exactly the
explicit field-level split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` — expresses
`Curv S = Gcurv + GcurvDeriv + (moving-frame remainder)`, with `Gcurv` the frame-sum of the
pure-Riemann contraction `riemannOp (tensorCov g 0 (s + 1)) x Bᵢ · (∇S(x))` (the Ricci identity on
the gradient field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), `GcurvDeriv` the frame-sum
of `covGradCurvatureContraction`, and the remainder the bracket field `bracketThirdCurvFieldFib`
(`tensor3rdCurvBracket` plus the frame-trace discrepancy `covGradRoughLapTraceDiscrepancy_gen` and
the moving-frame residual `covGradRoughLapMovingFrameResidual_gen`).

* The fibre bound on `Gcurv` is `rfns(∇S)`-order: each summand is a bundled curvature operator on
  `∇S(x)`, fibre-bounded by the proportional curvature bound `riemannOp_covGrad_fiberNormSq_le_gen`
  uniformised over the compact `M` to a single proportional constant by
  `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` (the per-point curvature
  operator norm and the frame Gram scalars are continuous), summed over the orthonormal frame.
* The fibre bound on `GcurvDeriv` is `rfns(S)`-order: it is the covariant gradient of the curvature
  contraction of `S`, fibre-bounded proportional to `rfns(S)` by the uniform differentiated-curvature
  sup `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`.
* The remainder bound is `rfns(∇²S)`-order: after the genuine curvature contractions are removed,
  the surviving moving-frame / frame-bracket discrepancy carries the bracket-jet `[Bᵢ, W]`, a
  contraction of the smooth frame data against `∇²S`; its top-order `∇³S` terms cancel by the
  iterated Ricci identity, leaving a genuinely `∇²S`-order tensorial field
  (`riemannianFiberNormSq_tensor3rdCurvGenuine_le` controls the genuine part; the bracket fibre order
  controls the discrepancy). This cancellation is *false term-by-term* through
  `smoothExtensionTangent`; only the tensorial sum is `∇²S`-order — the irreducible moving-frame
  content.
* The bracket-free pairing is the covariant Green / integration-by-parts identity: the moving-frame
  remainder is a total covariant divergence `∑ᵢ ∇_{Bᵢ}(·)` of an `∇S`-order field, so
  `integral_tensorInner_tangentAction_add_smul_divergence_eq_zero` (summed over the orthonormal
  frame) integrates it to zero against `∇S`, leaving the genuine fields `Gcurv + GcurvDeriv` to
  carry the entire cross-pairing `⟨Curv S, ∇S⟩_{L²}`.

**Non-vacuity.** The zero witness `Gcurv = GcurvDeriv = 0` is rejected: the remainder bound would
then read `rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)`, which is *false* (the defect genuinely carries the
`rfns(S)` and `rfns(∇S)` orders too), and the bracket-free pairing would read `0 = ⟨Curv S, ∇S⟩_{L²}`,
which equals `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_integrated_covGrad_l2_normSq` and is
*false* on a non-flat manifold. So the genuine curvature fields must carry the actual curvature
content.

This is the deepest moving-frame curvature-endomorphism content at general rank; it is posited here
as the precise genuine curvature primitive and discharged by the orchestrator. Its construction
requires the rank-generic moving-frame third-order Weitzenböck apparatus — the section-level
smoothness packaging of the genuine curvature traces `R(∇S)` and `(∇R) S` (the intrinsic metric
trace of the curvature contractions, smooth by the same route that makes `rawTensorConnLap` smooth),
the uniform-over-`M` proportional curvature / differentiated-curvature bounds, and the
divergence-form / covariant-Green integration of the bracket remainder — assembled from the explicit
field-level split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`. -/
theorem exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing
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
          tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun =
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  obtain ⟨Cper, hCper_nn, hdata⟩ :=
    exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence (I := I) (M := M) g
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hGScurv, hGcd, hGrem, hnull⟩ := hdata s S
  -- Instantiate `Gcurv := GcurvSection` (the concrete sound pure-Riemann section) and
  -- `GcurvDeriv := Gcd` (the existential differentiated-curvature field of the intrinsic tri-split).
  -- The moving-frame remainder `Curv S − GcurvSection − Gcd` is exactly `Grem` by the section split.
  have hrem_eq : pointwiseTensorCurv (I := I) (M := M) g s S -
      GcurvSection (I := I) (M := M) g s S - Gcd = Grem := by
    rw [hsplit]; abel
  refine ⟨GcurvSection (I := I) (M := M) g s S, Gcd, hGScurv, hGcd, fun x => ?_, ?_⟩
  · -- Remainder fibre bound: `rfns((Curv − GcurvSection − Gcd).toSection x) = rfns(Grem.toSection x)`.
    rw [hrem_eq]; exact hGrem x
  · -- Bracket-free pairing: the moving-frame remainder `Curv S − GcurvSection − Gcd = Grem` pairs to
    -- zero against `∇S` (the integrated nullity `hnull`), so the genuine fields carry the cross-pairing.
    refine tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
      (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S) Gcd ?_
    rw [hrem_eq]; exact hnull

end Connection
end Integral
end DifferentialGeometry

end
