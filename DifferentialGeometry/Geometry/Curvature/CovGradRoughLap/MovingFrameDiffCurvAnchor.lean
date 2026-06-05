import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm

/-!
# The coupled differentiated-curvature section `(∇R) S` with its order-`2` remainder and divergence
current

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible coupled moving-frame curvature-endomorphism content of the rank-generic order-`2`
rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`), over the concrete
pure-Riemann genuine section `Gcurv := GcurvSection g s S` (`MovingFrameCurvatureTraceSmooth`, the
slot-`0` assembly of the *tensorial* trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, whose frame-free curvature-jet grid
is already discharged by `exists_GcurvSection_iteratedCovGrad_grid_bound`,
`FrozenFramePureRCurvatureTower`).

## The deepest atom: the genuine `(∇R) S` field with its divergence current

The genuine third-order Weitzenböck field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`Geometry/Curvature/Bochner/PointwiseTensorBochnerFieldSplit`) reads, in the slot-`0` witness frame,
`Curv` as the sum of the genuine third-order curvature field `genuineThirdCurvFieldFib` and the bracket
field `bracketThirdCurvFieldFib`; the genuine field itself splits
(`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`) into the pure-Riemann part
`genuineThirdCurvFieldFibPureR` (the tensorial `R(∇S)` trace, frame-free, reconstructing the concrete
`GcurvSection`) and the differentiated-curvature part `genuineThirdCurvFieldFibCovDeriv` (the
`(∇R) S = ∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` trace). The differentiated-curvature trace is **non-tensorial** in the
direction — its on-disk fibre realisation `genuineThirdCurvFieldFibCovDeriv` reads the
`smoothExtensionTangent` jet of the frame direction, so it is frame- and chart-selection-dependent, has
**no** clean slot-`0` uncurry (a per-direction packaging is the unsound object documented at
`Order2Defect/SlotSplitBound`). The smooth moving-centre `(0, s + 1)`-tensor `Gcd` that carries the
`(∇R) S` content must therefore be assembled *tensorially* and *existentially* — never extension-curried
— and the precise normalisation that makes the companion remainder `Curv − Gcurv − Gcd` genuinely
**second-order** is the one for which the subtraction leaves exactly the bracket field plus a frame-summed
total covariant divergence (the `∇³S` top-order terms cancelled by the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, `IntegratedOrder2WeitzenbockCurvature`).

This coupling — the existential tensorial section `Gcd`, its `rfns(∇S) + rfns(S)`-order (sum) fibre
bound, the companion remainder's `rfns(∇²S)`-sum fibre bound, **and** the smooth `∇S`-order tangent
*divergence current* `X` whose metric divergence reproduces the remainder's pointwise pairing against
`∇S` — cannot be factored into independent standalone lemmas: the divergence-current property is a
property of *the specific* `Gcd` (the frame-summed bracket field is a total covariant divergence only
for the genuine curvature fields, *false* term-by-term through `smoothExtensionTangent` and *false* for
an arbitrary bounded field). It is therefore the single irreducible coupled differentiated-curvature
node, isolated here, and is the covariant-derivative analogue of the on-disk pure-Riemann
`GcurvSection`: where the pure-Riemann trace is tensorial and hence concretely constructible, the
differentiated-curvature trace is non-tensorial and hence carried as this coupled existential. Its shape
mirrors the order-`m` sibling `exists_pointwiseTensorCurv_diffCurvAndRemainder_gradedCurvJet`
(`OrderSeparatedCurvatureJet`, the graded-in-`k` version) at gradient order `k = 0`, additionally
exposing the divergence current `X` that the integrated nullity consumes.

## Main result

* `exists_movingCentreDiffCurvSection_divergenceDatum` — the posited coupled differentiated-curvature
  primitive: a *valence-dependent* nonnegative constant `K : ℕ → ℝ` and, at every rank `s` and smooth
  compactly-supported `(0, s)`-tensor `S`, a smooth compactly-supported `(0, s + 1)`-tensor `Gcd`
  together with a smooth tangent vector field `X` for which the **sum** fibre bound on `Gcd`, the
  **sum** fibre bound on the companion remainder `Curv − Gcurv − Gcd`, and the **pointwise divergence
  datum** `⟨Curv − Gcurv − Gcd, ∇S⟩ =ᵐ divᵍ X` all hold. The integrated nullity `(2)` of
  `exists_movingCentreDiffCurvSection_fiberNormSq_bound`
  (`MovingFrameDifferentiatedCurvatureSection`) is then **derived** from this datum by the
  closed-manifold divergence theorem
  (`tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence`,
  `MovingFrameRemainderDivergenceForm`), so that the differentiated-curvature section primitive's
  integrated half is a *theorem over this analytic atom*, not a separate posit.
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

/-- **Posited coupled differentiated-curvature section `(∇R) S` with its order-`2` remainder fibre
bound and its divergence current.** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for
every smooth compactly-supported `(0, s)`-tensor `S`, there is a smooth compactly-supported
`(0, s + 1)`-tensor `Gcd` — the **tensorial, existentially-carried** (never extension-curried) smooth
moving-centre section of the differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the
`(∇R) S` field) — together with a smooth tangent vector field `X`, for which, writing
`Curv := pointwiseTensorCurv g s S`, `Gcurv := GcurvSection g s S` (the concrete pure-Riemann section),
`∇S := covGrad g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the **three coupled facts**
hold:
* `(3')` the **sum** fibre bound on the constructed section
  `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )`;
* `(4')` the **sum** fibre bound on the companion moving-frame remainder `Curv − Gcurv − Gcd`,
  `rfns(Curv − Gcurv − Gcd)(x) ≤ (K s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) )`; and
* `(div)` the **pointwise divergence datum** for that same companion remainder: the metric divergence
  `divᵍ X` agrees almost everywhere with the pointwise metric inner product
  `⟨Curv − Gcurv − Gcd, ∇S⟩` of the remainder against `∇S`.

**Why this is TRUE — the gauge-glued tensorial `(∇R) S` section and its divergence current.** The
genuine third-order Weitzenböck field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
reads `Curv` (in the slot-`0` witness frame) as `genuineThirdCurvFieldFib + bracketThirdCurvFieldFib`,
and the genuine field splits (`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`) into the pure-Riemann
`R(∇S)` trace (the concrete `Gcurv = GcurvSection`, frame-free) and the differentiated-curvature
`(∇R) S` trace `genuineThirdCurvFieldFibCovDeriv`. The latter is non-tensorial (its on-disk fibre
realisation reads the `smoothExtensionTangent` jet, frame-dependent) and so has no clean slot-`0`
uncurry; the smooth section `Gcd` carrying its content is assembled *tensorially* from the frame-traced
curvature-contraction building block `covGradCurvatureContraction`
(`Analysis/.../UniformCurvatureSup`, the smooth `∇(R(X, Y) Z)` for fixed smooth tangent fields `X, Y`)
summed over a frozen orthonormal frame and partition-of-unity-glued across a finite chart cover (the
frozen-frame fibre value agreeing on overlaps because the contraction reads only the *values* of the
frame, exactly as for the pure-Riemann section
`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection`). `(3')` is the frame-summed `∇R` sup
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), the **sum** envelope absorbing the
Leibniz defect between this gauge-glued tensorial section and the genuine non-tensorial `(∇R) S` trace
(the strict `rfns(S)` bound is *unachievable* — the genuine trace's extension jet is non-tensorial, so
the defect cannot be made to vanish). With `Gcd` this tensorial section, the unit fibre value of
`Curv − Gcurv − Gcd` is the bracket field plus the Leibniz defect, `rfns(∇²S)`-order in its leading
term after the iterated Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` cancels the
top-order `∇³S` terms — the **sum** bound `(4')`. `(div)` is the frame-summed covariant integration by
parts: the moving-frame remainder, paired against `∇S` and summed over the `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i`, telescopes into the total covariant divergence
(`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`,
`CovariantIntegrationByParts`) of an honest smooth `∇S`-order tangent field `X` — the gauge-glued
`Gcd`'s defect is itself a total covariant divergence against `∇S`. The `∇³S`-cancellation and the
divergence form are *false term-by-term* through `smoothExtensionTangent`; only the tensorial
frame-summed remainder is `∇²S`-order and a total divergence — the irreducible coupled moving-frame
content.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound `(3')` alone does not reject `Gcd = 0`, but
the COUPLING does. With `Gcd = 0` and any `X`, `(div)` reads `⟨Curv − Gcurv, ∇S⟩ =ᵐ divᵍ X`, whose
integral over the closed manifold forces `⟨Curv − Gcurv, ∇S⟩_{L²} = 0`
(`integral_divergence_eq_zero_of_hasCompactSupport`), i.e.
`⟨Curv, ∇S⟩_{L²} = ⟨Gcurv, ∇S⟩_{L²}`; but the genuine Weitzenböck value
`⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`) is *not*
carried by the pure-Riemann pairing `⟨Gcurv, ∇S⟩_{L²}` alone on a non-flat manifold (the
differentiated-curvature `(∇R) S` content is genuinely missing), a contradiction; and `(4')` with
`Gcd = 0` would read `rfns(Curv − Gcurv) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since the
`(∇R) S` content is genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd` and the
current `X` must carry the actual third-order Weitzenböck content; the constant family is genuinely
positive. It is posited here as the precise coupled differentiated-curvature primitive (the
covariant-derivative analogue of the on-disk pure-Riemann `GcurvSection`, gauge-glued, coupled to its
companion remainder's order bound and its divergence current); consumers transitively depend on
`sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_divergenceDatum
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ (Gcd : SmoothCcTensor g 0 (s + 1))
          (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S -
                  GcurvSection (I := I) (M := M) g s S - Gcd).toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (s + 1)
                    (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                    ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))) ∧
          (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                ((pointwiseTensorCurv (I := I) (M := M) g s S -
                    GcurvSection (I := I) (M := M) g s S - Gcd).toFun x)
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
            =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
          (fun x : M => divergence_g (I := I) g X x) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
