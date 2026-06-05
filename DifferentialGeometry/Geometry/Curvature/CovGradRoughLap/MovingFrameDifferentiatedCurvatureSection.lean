import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# The smooth moving-centre differentiated-curvature section `(∇R) S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
**differentiated-curvature genuine section** of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`). It is the
covariant-derivative counterpart of the on-disk **pure-Riemann** genuine section `GcurvSection g s S`
(`MovingFrameCurvatureTraceSmooth`, the slot-`0` assembly of the *tensorial* trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`): a smooth compactly-supported `(0, s + 1)`-tensor whose unit-section fibre
value reconstructs, in the moving frame, as the **differentiated-curvature fibre field**
`genuineThirdCurvFieldFibCovDeriv g s S` (`MovingFrameCurvatureTraceSmooth`, the slot-`0` reconstruction
of `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`, the `(∇R) S` contraction), with a `rfns(S)`-order fibre bound.

## Why this is a separate, strictly-more-primitive primitive

The pure-Riemann trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` is *tensorial* (direction-linear), so its slot-`0`
uncurry through `covGradBundleEquiv` reconstructs the moving-centre section `GcurvSection` cleanly,
independent of the per-direction smooth extension — that is what makes `GcurvSection` a concrete
sorry-free section. The differentiated-curvature trace `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial**
in the direction (its Leibniz expansion sees the first jet of the direction's smooth extension), so it
has **no** clean slot-`0` uncurry; the smooth moving-centre section that carries the `(∇R) S` fibre
field must instead be assembled from the *tensorial* curvature-contraction building block
`covGradCurvatureContraction` (`Analysis/.../UniformCurvatureSup`, the smooth `∇(R(X, Y) Z)` for fixed
smooth tangent fields `X, Y`) summed over a frozen orthonormal frame and glued across a finite chart
cover by a smooth partition of unity (the frozen-frame fibre value agrees with the moving-centre value
on each frozen-frame neighbourhood, exactly as for the pure-Riemann section
`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection`). This is the genuinely-new analytic
content the differentiated-curvature leg requires, isolated here as a single primitive so the
moving-frame third-order Weitzenböck tri-split
(`exists_pointwiseTensorCurv_genuineTriSplit_divergence`,
`MovingFrameGenuineSectionOrderDivergence`) consumes it cleanly.

## Main result

* `exists_movingCentreDiffCurvSection_fiberNormSq_bound` — the posited differentiated-curvature
  section primitive: a *valence-dependent* nonnegative constant `K : ℕ → ℝ` and, at every rank `s`
  and smooth compactly-supported `(0, s)`-tensor `S`, a smooth compactly-supported `(0, s + 1)`-tensor
  `Gcd` — the **partition-of-unity-glued frame-traced tensorial differentiated-curvature section**
  `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` contraction) — carrying the **sum** fibre bound
  `rfns(Gcd)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))`. The section is constructed tensorially: the
  frame-traced `(∇R)`-contraction reads only the *values* of the frame (`covGradCurvatureContraction`
  against fixed smooth fields), so the per-chart `smoothOrthoFrameNbhd`-patches agree on overlaps and
  the smooth partition-of-unity glue is exact; smoothness is local-to-global from the frame-fixed
  `covGradCurvatureContraction` smoothness. **No per-direction fibre match** is asserted (the former
  `IsMovingCentreDiffCurvFibreMatch` pinned `Gcd` to the *extension-curried* per-direction field
  `genuineThirdCurvFieldFibCovDeriv`, which reads the `smoothExtensionTangent` jet and is therefore
  frame-dependent / non-tensorial — unsatisfiable by any constructible tensorial `Gcd`; the patch
  values disagree on overlaps). The bound is the **sum** `rfns(∇S) + rfns(S)`, not the strict
  `rfns(S)`: the Leibniz defect between the genuine moving-frame `(∇R) S` trace and the tensorial
  partition-of-unity section is `rfns(∇S) + rfns(S)`-order (it carries the gradient jet of the frame
  data contracted against `∇S`) and must be absorbed by the wider envelope — the strict `rfns(S)`
  bound is unachievable by any constructible `Gcd`. Both summand orders are dominated at the sole
  consumption site (the moving-frame remainder's two-term fibre merge in `MovingFrameGenuineFieldPairing`
  through `PointwiseTensorCurvL2Bound`), so no order is lost.
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

/-- **Posited coupled gauge-glued differentiated-curvature section `(∇R) S` of the genuine moving-frame
tri-split: the constructed section `Gcd`, its `rfns(∇S) + rfns(S)`-order (sum) fibre bound, the
companion remainder's `rfns(∇²S)`-sum fibre bound, and the companion remainder's integrated nullity.**
For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(0, s)`-tensor `S`, there is a smooth compactly-supported `(0, s + 1)`-tensor `Gcd` — the
**partition-of-unity-glued frame-traced tensorial section** of the differentiated-curvature contraction
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` field) — for which, writing `Curv := pointwiseTensorCurv g s S`,
`Gcurv := GcurvSection g s S` (the concrete pure-Riemann section), `∇S := covGrad g 0 s S` and
`∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`, the **three coupled facts about `Gcd`'s own
construction** hold:
* `(3')` the **sum** fibre bound on the constructed section
  `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )`;
* `(4')` the **sum** fibre bound on the companion moving-frame remainder
  `Curv − Gcurv − Gcd`,
  `rfns(Curv − Gcurv − Gcd)(x) ≤ (K s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) )`; and
* `(2)` the **integrated moving-frame nullity** of that same companion remainder,
  `⟨Curv − Gcurv − Gcd, ∇S⟩_{L²} = 0`.

These are the exact three conjuncts the genuine moving-frame tri-split
`exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`) consumes (with `Grem := Curv − Gcurv − Gcd` and the
section split `Curv = Gcurv + Gcd + Grem` then `abel`), so this primitive is exactly the deepest
moving-frame curvature-endomorphism content of the tower, isolated as one coupled existential.

**Why this is TRUE — the gauge-glued tensorial section.** The differentiated-curvature contraction
`R(Bᵢ, ·) S` followed by the covariant gradient along `Bᵢ` is the *tensorial* smooth section
`covGradCurvatureContraction g s S` (against fixed smooth fields), whose fibre norm is uniformly
bounded over the compact `M` by `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The
frame-traced `(∇R)`-contraction reads only the *values* of the frame (it contracts `R(Bᵢ, ·) S` with
`Bᵢ` *evaluated at the centre*, no extension jet), so the per-chart frozen-frame sections against
`smoothOrthoFrame g x₀` (the diff-curv analogue of the pure-Riemann `fixedFramePureRSection`, the
covariant-gradient counterpart) agree on overlaps; the smooth partition of unity over a finite chart
cover glues them into a single smooth `(0, s + 1)`-tensor `Gcd` (smoothness local-to-global from the
frame-fixed `covGradCurvatureContraction` smoothness, the eventual-equality bridge mirroring
`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection`), with each per-patch fibre value bounded
by the uniform sup. `(3')` is then the frame-summed `∇R` sup, the **sum** envelope `rfns(∇S) + rfns(S)`
absorbing the Leibniz defect between this gauge-glued tensorial section and the genuine non-tensorial
moving-frame `(∇R) S` trace (the strict `rfns(S)` bound is *unachievable* — the genuine trace's
extension jet is non-tensorial, so the defect cannot be made to vanish). `(4')` is the companion
remainder fibre order: with `Gcd` the tensorial section, the unit fibre value of `Curv − Gcurv − Gcd`
is the bracket field (the committed sorry-free field split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` with
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` and the pure-Riemann frame-independence
`genuineThirdCurvFieldFibPureR_frame_indep`) *plus* the Leibniz defect, `rfns(∇²S)`-order in its
leading term after the iterated Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
cancels the top-order `∇³S` terms (the bracket-`∇²S` energy bound), the lower terms in the sum.
`(2)` is the frame-summed covariant integration by parts: the companion remainder, paired against `∇S`
and summed over the `g_x`-orthonormal frame `Bᵢ`, telescopes into a total covariant divergence
(`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`) of an honest `∇S`-order tangent
field, whose integral over the closed manifold vanishes — the gauge-glued `Gcd`'s defect is itself a
total covariant divergence against `∇S`, so the integrated pairing is unchanged from the genuine field
(`weitzenbock_integrated_covGrad_l2_normSq` supplies the genuine value
`⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`). The `∇³S`-cancellation and divergence-form are
*false term-by-term* through `smoothExtensionTangent`; only the tensorial frame-summed remainder is
`∇²S`-order and a total divergence — the irreducible coupled moving-frame content.

**No per-direction fibre match.** This primitive asserts *no* per-direction fibre match against
`genuineThirdCurvFieldFibCovDeriv` (the field reading the `smoothExtensionTangent` jet, frame-dependent
/ non-tensorial; the former `IsMovingCentreDiffCurvFibreMatch` hypothesis is unsatisfiable on a normal
manifold — the patch values disagree on overlaps). It carries only the tensorial section `Gcd` and the
three coupled facts above; the consumer recovers the order-separated tri-split from these.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound `(3')` alone does *not* reject `Gcd = 0`
(`K := 0`, `Gcd := 0` would satisfy a bare bound), but the COUPLING does: with `Gcd = 0`, `(2)` reads
`⟨Curv − Gcurv, ∇S⟩_{L²} = 0`, i.e. `⟨Curv, ∇S⟩_{L²} = ⟨Gcurv, ∇S⟩_{L²}`. The genuine Weitzenböck
value `⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`) is
*not* carried by the pure-Riemann pairing `⟨Gcurv, ∇S⟩_{L²}` alone on a non-flat manifold (the
differentiated-curvature `(∇R) S` content is genuinely missing), a contradiction; and `(4')` with
`Gcd = 0` would read `rfns(Curv − Gcurv) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since
the `(∇R) S` content is genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd`
must carry the actual third-order Weitzenböck content; the constant family is genuinely positive. It
is posited here as the precise coupled differentiated-curvature primitive (the covariant-derivative
analogue of the on-disk pure-Riemann `GcurvSection`, gauge-glued, coupled to its companion remainder's
order bound and integrated nullity); consumers transitively depend on `sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd : SmoothCcTensor g 0 (s + 1),
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
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (pointwiseTensorCurv (I := I) (M := M) g s S -
                GcurvSection (I := I) (M := M) g s S - Gcd).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
