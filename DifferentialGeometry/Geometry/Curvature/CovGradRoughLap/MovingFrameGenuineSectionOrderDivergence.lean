import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup

/-!
# Order bounds and the moving-frame divergence datum for the genuine curvature sections

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
single genuinely-irreducible moving-frame curvature-endomorphism producer underneath the
rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`), stated directly
on the *concrete* genuine curvature sections `GcurvSection g s S` and `GcurvDerivSection g s S` of
`MovingFrameCurvatureTraceSmooth` (the slot-`0` assemblies of the moving-frame genuine traces
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` and `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`).

It packages exactly the two genuine moving-frame ingredients that the bracket-free-pairing form of
the genuine third-order Weitzenböck field decomposition consumes but cannot derive from below:

* the three **order-separated fibre bounds** on the two genuine sections and on the moving-frame
  remainder `Curv S − GcurvSection − GcurvDerivSection`, with a single valence-dependent
  proportional constant `Cper`; and
* the **moving-frame divergence datum** — an honest smooth `∇S`-order tangent vector field `X` whose
  metric divergence `divᵍ X` agrees almost everywhere with the pointwise metric inner product
  `⟨Curv S − GcurvSection − GcurvDerivSection, ∇S⟩` of the moving-frame remainder against `∇S`.

The bracket-free `L²` pairing `⟨GcurvSection + GcurvDerivSection, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` is
then *not* posited: it is recovered from this divergence datum by the closed-manifold covariant
integration-by-parts reduction
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_pointwise_divergence`
(`MovingFrameRemainderDivergenceForm`) in
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`.

It is posited here as the single precise genuine curvature primitive (`sorry`), to be discharged by
the orchestrator; see its docstring for the precise truth justification, the moving-frame curvature
apparatus it is built from, and the non-vacuity certificate.
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

/-- **Posited genuine moving-frame producer: order bounds and the divergence datum for the concrete
genuine curvature sections.** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and
for every smooth compactly-supported `(0, s)`-tensor `S`, the two concrete genuine curvature sections
`GcurvSection g s S` and `GcurvDerivSection g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0`
assemblies of the moving-frame genuine traces `R(∇S) = ∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` and
`(∇R) S = ∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`) of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` satisfy the three order-separated fibre bounds and admit the
moving-frame divergence datum:

* `rfns(GcurvSection)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDerivSection)(x) ≤ (Cper s)² · rfns(S)(x)` — the `∇R` field, genuinely `rfns(S)`-order;
* `rfns(Curv S − GcurvSection − GcurvDerivSection)(x) ≤ (Cper s)² · rfns(∇²S)(x)` — the moving-frame /
  frame-bracket remainder, genuinely `rfns(∇²S)`-order after the third-order Weitzenböck cancellation
  of the top-order `∇³S` terms by the iterated Ricci identity;
* there is a smooth tangent vector field `X` with
  `⟨Curv S − GcurvSection − GcurvDerivSection, ∇S⟩(x) =ᵐ divᵍ X(x)` — the moving-frame remainder,
  paired against `∇S`, telescopes (frame-summed) into a total covariant divergence of an `∇S`-order
  field.

**Why this is TRUE.** Fibrewise, `pointwiseTensorCurv_toSection_eq_frame_sum` reads
`Curv S (x) = ∑ᵢ [∇²_{Bᵢ,Bᵢ}(∇S)(x) − covGradBundleEquiv (∇·∇²_{Bᵢ,Bᵢ} S)(x)]` over the
`g_x`-orthonormal frame `Bᵢ = smoothOrthoFrame g x i`. The committed field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` reads the slot-`0` curried fibre value of
`Curv S` as `genuineThirdCurvFieldFib + bracketThirdCurvFieldFib` in a witness `g_x`-orthonormal frame
`e`, and `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` /
`GcurvDerivSection_toSection_eq_genuineThirdCurvFieldFibCovDeriv` /
`GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField` identify the fibre values of
the two sections (and their sum) with the pure-Riemann / differentiated-curvature parts (and the
whole) of the genuine field.

* The fibre bound on `GcurvSection` is `rfns(∇S)`-order: each summand is the bundled curvature
  operator `riemannOp (tensorCov g 0 (s + 1)) x Bᵢ · (∇S(x))` (the Ricci identity on the gradient
  field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), fibre-bounded by the proportional
  curvature bound `riemannOp_covGrad_fiberNormSq_le_gen` uniformised over the compact `M` to a single
  proportional constant by `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` (the
  per-point curvature operator norm and the frame Gram scalars are continuous), summed over the
  orthonormal frame and reassembled through the slot-`0` Parseval reconstruction
  `riemannianFiberNormSq_succ_eq_sum_slot0Curry`.
* The fibre bound on `GcurvDerivSection` is `rfns(S)`-order: it is the covariant gradient of the
  curvature contraction of `S`, fibre-bounded proportional to `rfns(S)` by the uniform
  differentiated-curvature sup `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`.
* The remainder bound is `rfns(∇²S)`-order: after the genuine curvature contractions are removed, the
  surviving moving-frame / frame-bracket discrepancy carries the bracket-jet `[Bᵢ, W]`, a contraction
  of the smooth frame data against `∇²S`; its top-order `∇³S` terms cancel by the iterated Ricci
  identity, leaving a genuinely `∇²S`-order tensorial field
  (`riemannianFiberNormSq_tensor3rdCurvGenuine_le` controls the genuine part; the bracket fibre order
  controls the discrepancy). This cancellation is *false term-by-term* through
  `smoothExtensionTangent`; only the tensorial sum is `∇²S`-order — the irreducible moving-frame
  content.
* The divergence datum is the covariant Green / integration-by-parts identity: the moving-frame
  remainder is a total covariant divergence `∑ᵢ ∇_{Bᵢ}(·)` of an `∇S`-order field, so
  `integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`
  (`CovariantIntegrationByParts`), summed over the orthonormal frame, exhibits its pointwise pairing
  against `∇S` as a metric divergence `divᵍ X` of an honest smooth `∇S`-order tangent field `X`. The
  remainder is *false term-by-term* through `smoothExtensionTangent` (the bracket's first summand
  `∑ᵢ ∇_{[Bᵢ, W]}(∇_{Bᵢ} T)` is not itself a `Bᵢ`-divergence); only the frame-summed remainder,
  paired against `∇S`, telescopes into a total covariant divergence — the irreducible moving-frame
  content.

**Non-vacuity.** The genuine sections cannot be replaced by the zero data: with the divergence datum,
the bracket-free pairing recovered downstream reads
`⟨GcurvSection + GcurvDerivSection, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`, which equals
`‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` by `weitzenbock_integrated_covGrad_l2_normSq` and is *false* on a non-flat
manifold if the genuine fields vanished; and the remainder bound
`rfns(Curv S) ≤ (Cper s)² · rfns(∇²S)` is *false* if `GcurvSection = GcurvDerivSection = 0` (the defect
genuinely carries the `rfns(S)` and `rfns(∇S)` orders too). The divergence datum itself is *false* for
an arbitrary pair of fields — it holds exactly for the genuine curvature sections, so it is a genuine
geometric fact, not a posited universal.

This is the deepest moving-frame curvature-endomorphism content at general rank; it is posited here as
the single precise genuine curvature primitive and discharged by the orchestrator. Its construction
requires the rank-generic moving-frame third-order Weitzenböck apparatus — the slot-`0` Parseval
reconstruction of the fibre norm of the genuine sections, the uniform-over-`M` proportional curvature /
differentiated-curvature bounds, and the divergence-form / covariant-Green integration of the bracket
remainder — assembled from the explicit field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` and the section fibre-match suite
`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` /
`GcurvDerivSection_toSection_eq_genuineThirdCurvFieldFibCovDeriv`. -/
theorem exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
          Cper s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ∧
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((GcurvDerivSection (I := I) (M := M) g s S).toSection x) ≤
          Cper s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S -
                GcurvSection (I := I) (M := M) g s S -
                GcurvDerivSection (I := I) (M := M) g s S).toSection x) ≤
          Cper s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x)) ∧
        ∃ X : ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I),
          (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                ((pointwiseTensorCurv (I := I) (M := M) g s S -
                    GcurvSection (I := I) (M := M) g s S -
                    GcurvDerivSection (I := I) (M := M) g s S).toFun x)
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
            =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
          (fun x : M => divergence_g (I := I) g X x) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
