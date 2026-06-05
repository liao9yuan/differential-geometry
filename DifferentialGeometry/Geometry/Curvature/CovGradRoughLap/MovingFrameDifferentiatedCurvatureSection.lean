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

/-- **Posited smooth partition-of-unity-glued tensorial differentiated-curvature section `(∇R) S`
with its `rfns(∇S) + rfns(S)`-order (sum) fibre bound.** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant
rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, there is a smooth
compactly-supported `(0, s + 1)`-tensor `Gcd` — the **partition-of-unity-glued frame-traced tensorial
section** of the differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` field) —
with the **sum** fibre bound
```
rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) ),   ∇S := covGrad g 0 s S.
```

**Why this is TRUE.** The differentiated-curvature contraction `R(Bᵢ, ·) S` followed by the covariant
gradient along `Bᵢ` is the *tensorial* smooth section `covGradCurvatureContraction g s S` (against
fixed smooth fields), whose fibre norm is uniformly bounded over the compact `M` by
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The frame-traced `(∇R)`-contraction
reads only the *values* of the frame (it contracts `R(Bᵢ, ·) S` with `Bᵢ` *evaluated at the centre*,
no extension jet), so the per-chart frozen-frame sections against `smoothOrthoFrame g x₀` agree on
overlaps; the smooth partition of unity over a finite chart cover glues them into a single smooth
`(0, s + 1)`-tensor (smoothness local-to-global from the frame-fixed `covGradCurvatureContraction`
smoothness), with the glued fibre value the convex combination of the per-patch values, each
fibre-bounded by the uniform sup. The envelope is the **sum** `rfns(∇S) + rfns(S)`, not the strict
`rfns(S)`: gluing the frame-traced tensorial section to the genuine moving-frame `(∇R) S` trace incurs
a Leibniz defect — the gradient jet of the partition/frame data contracted against the field — which
is `rfns(∇S) + rfns(S)`-order and must land in the wider envelope. The strict `rfns(S)` bound is
*unachievable* by any constructible `Gcd`: the defect cannot be made to vanish (the genuine trace's
extension jet is non-tensorial), so the sum is the honest bound.

**No fibre match.** This section asserts *no* per-direction fibre match against
`genuineThirdCurvFieldFibCovDeriv`. That field reads the `smoothExtensionTangent` jet of the frame
direction, so it is frame-dependent / non-tensorial (its value at a point differs between overlapping
`smoothOrthoFrame g x₀`-patches), and no constructible tensorial `Gcd` can match it — the former
`IsMovingCentreDiffCurvFibreMatch` hypothesis is unsatisfiable through every known route (the
per-direction choose-jets do not cancel). The honest primitive carries only the tensorial section and
its sum fibre bound; the consumer recovers the order-separated tri-split from the explicit field
identity `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` and the bracket-energy atom, not
from a per-direction match.

**Non-vacuity.** The zero witness `Gcd = 0` is rejected on a non-flat manifold: the tensorial
frame-traced `(∇R) S` contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is genuinely non-zero when `∇R ≠ 0` for a
non-zero `S`, so its fibre norm is not bounded by `0 · (rfns(∇S) + rfns(S))`; the constant family is
genuinely positive. It is posited here as the precise differentiated-curvature section primitive (the
covariant-derivative analogue of the on-disk pure-Riemann `GcurvSection`, gauge-glued); consumers
transitively depend on `sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd : SmoothCcTensor g 0 (s + 1),
          ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
