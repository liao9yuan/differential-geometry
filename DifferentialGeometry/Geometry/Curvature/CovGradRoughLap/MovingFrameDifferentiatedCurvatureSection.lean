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
  `Gcd` with the `rfns(S)`-order fibre bound `rfns(Gcd)(x) ≤ (K s)² · rfns(S)(x)` and the
  moving-frame fibre match `Gcd.toSection x (unit) (cons w m) = genuineThirdCurvFieldFibCovDeriv g s S
  x e w m` against the moving frame `e = smoothOrthoFrame g x`. The fibre match pins `Gcd` to the
  genuine `(∇R) S` field; the bound is `rfns(S)`-order because `(∇R) S` is the covariant gradient of
  the curvature contraction of `S` (`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`),
  uniform over the compact `M`.
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

/-- **Posited smooth moving-centre differentiated-curvature section `(∇R) S` with its `rfns(S)`-order
fibre bound and moving-frame fibre match.** For a closed smooth Riemannian manifold `(M, g)` there is
a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and
for every smooth compactly-supported `(0, s)`-tensor `S`, there is a smooth compactly-supported
`(0, s + 1)`-tensor `Gcd` — the section-level packaging of the differentiated-curvature contraction
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` field) — with:

* the `rfns(S)`-order fibre bound `rfns(Gcd)(x) ≤ (K s)² · rfns(S)(x)` at every `x`; and
* the **moving-frame fibre match**: at every `x` there is a `g_x`-orthonormal frame `e` (the moving
  frame `smoothOrthoFrame g x` at its centre) in which the unit-section fibre value of `Gcd`
  reconstructs as the differentiated-curvature fibre field `genuineThirdCurvFieldFibCovDeriv g s S x e`:
  ```
  toModel (Gcd.toSection x (unit)) (Fin.cons w m) = genuineThirdCurvFieldFibCovDeriv g s S x e w m.
  ```

**Why this is TRUE.** The differentiated-curvature contraction `R(Bᵢ, ·) S` followed by the covariant
gradient along `Bᵢ` is the tensorial smooth section `covGradCurvatureContraction g s S` (against fixed
smooth fields), whose fibre norm is uniformly bounded over the compact `M` by
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, proportional to `rfns(S)`. Assembling
the frame sum over a frozen orthonormal frame and gluing across a finite chart cover by a smooth
partition of unity produces a smooth `(0, s + 1)`-tensor whose moving-centre fibre value matches the
non-tensorial differentiated-curvature fibre field `genuineThirdCurvFieldFibCovDeriv g s S` on each
frozen-frame neighbourhood (exactly as the pure-Riemann section `GcurvSection` matches its frozen-frame
version `fixedFramePureRSection` on `smoothOrthoFrameNbhd`,
`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection`); the partition weights sum to one, so the
glued value is the moving-centre field, and the fibre norm of the glued section is the convex
combination of the per-patch fibre norms, each `rfns(S)`-bounded by the uniform sup. The `rfns(S)`
order — not `rfns(∇S)` — is genuine: the differentiated curvature `∇R` already carries the
differentiation, so only the undifferentiated `S` remains contracted (the gradient slot of `∇S` is
*not* contracted, unlike the pure-Riemann leg).

**Non-vacuity.** The zero witness `Gcd = 0` is rejected by the moving-frame fibre match: it would force
`genuineThirdCurvFieldFibCovDeriv g s S x e w m = 0` for all `w, m`, i.e. the differentiated-curvature
contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` vanishes — false on a non-flat manifold with non-parallel
curvature (`∇R ≠ 0`) for a non-zero `S`. So the section genuinely carries the `(∇R) S` content; the
bound genuinely envelopes the per-point differentiated-curvature operator norm. It is posited here as
the precise differentiated-curvature section primitive (the covariant-derivative analogue of the
on-disk pure-Riemann `GcurvSection`); consumers transitively depend on `sorryAx`. -/
theorem exists_movingCentreDiffCurvSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
        ∃ Gcd : SmoothCcTensor g 0 (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) ∧
          ∀ x : M, ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
            n = Module.finrank ℝ (TangentSpace I x) ∧
            (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
            ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
              Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                    Gcd.toSection x) (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
                genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
