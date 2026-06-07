import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# The fibre order of the order-`2` rough-Laplacian / covariant-gradient commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible quantitative fibre atom of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`): **the defect is
order-`≤ 2` in `S`**, with a *valence-dependent* uniform fibre bound by the sum of the fibre norms of
`∇²S`, `∇S` and `S`.

## Why this is the irreducible fibre atom (the iterated Ricci identity controls the defect)

By definition `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`Bochner/PointwiseTensorBochner`), the rough Laplacian of
the gradient field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame
traces of the second covariant derivative and commuting the two derivative slots by the rank-`(0, s + 1)`
Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`),
the top-order `∇³S` terms cancel: the difference is a sum of curvature contractions of the gradient field
`R(∇S)` (each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via the uniform curvature fibre bound
`riemannOp_covGrad_fiberNormSq_le_gen`), plus genuine `(∇R) S` and frame-derivative terms of
`rfns(S)`-order, plus a residual `∇²S`-order moving-frame remainder (`tensor3rdCurvBracket`, the
frame-bracket discrepancy of the field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`).
Aggregating the three over the finite frame with the per-point curvature sup made *uniform* over `M` by
compactness (`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator
`g`-norm sup) gives the single nonnegative valence-dependent constant `C`. The `∇³S`-cancellation is
*false term-by-term* through the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded
on `S²`); only the intrinsic frame-summed defect is `∇²S`-order.

## Main result

* `exists_pointwiseTensorCurv_fiberOrder_bound` — the **order-`2` commutator-defect fibre order**: a
  *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that at every covariant rank `s`, every
  smooth compactly-supported `(0, s)`-tensor `S`, and *every point* `x`,
  ```
  rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
  ```
  It is the genuine quantitative fibre atom of the curvature line, homed *upstream* of the moving-frame
  spine so the four-carrier remainder fibre bound and the genuine-fields fibre decomposition consume it
  without an import cycle through the downstream `L²` chain.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq` (`rfns`).
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

/-- **The order-`2` commutator-defect fibre order (the curvature line's irreducible quantitative atom,
posited upstream of the moving-frame spine).** For a closed smooth Riemannian manifold `(M, g)` there is
a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, for every
smooth compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic fibre norm of the
order-`2` rough-Laplacian / covariant-gradient commutator defect `Curv S := pointwiseTensorCurv g s S` is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S = covGrad g 0 (s + 1)
(covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the commutator defect.** By definition
`Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`Bochner/PointwiseTensorBochner`), the rough Laplacian of the gradient
field minus the gradient of the rough Laplacian. Reading both as fixed-`g`-orthonormal-frame traces of
the second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`) and commuting the two
derivative slots by the rank-`(0, s + 1)` Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
(`IntegratedOrder2WeitzenbockCurvature`), the top-order `∇³S` terms cancel: the difference is a sum of
(i) curvature contractions of the gradient field `R(∇S)`, each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via
the uniform curvature fibre bound `riemannOp_covGrad_fiberNormSq_le_gen`, plus (ii) genuine `(∇R) S` and
frame-derivative terms of `rfns(S)`-order (the `tensor3rdCurvGenuine` covariant-derivative summand), plus
(iii) a residual `∇²S`-order moving-frame remainder (`tensor3rdCurvBracket`, the frame-bracket discrepancy
of the field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`). Aggregating the three
over the finite frame with the per-point curvature sup made *uniform* over `M` by compactness
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the curvature-operator `g`-norm sup)
gives the single nonnegative valence-dependent `C`.

**Why the pointwise per-direction split is fenced.** The `∇³S`-cancellation is *false term-by-term*
through the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded on `S²`); only the
intrinsic frame-summed defect is `∇²S`-order. The bound is stated for the intrinsic fibre norm `rfns` of
the single tensor `pointwiseTensorCurv g s S` throughout — it never extracts a per-direction `M → E`
quantity — so it is trap-screened.

**Non-vacuity (the bound rejects the degenerate `C ≡ 0` on a non-flat manifold).** With `C s = 0` the
bound would force `rfns(Curv S)(x) = 0`, i.e. `Δ_∇(∇S) = ∇(Δ_∇ S)` at every point — the covariant
derivatives commute through the rough Laplacian. This is *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S`: the commutator defect `Curv S` is exactly the genuine third-order Weitzenböck curvature
field `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_integrated_covGrad_l2_normSq`),
nonzero when curvature is present. So `C` is genuinely positive. The body is `sorry` (the genuine
classical iterated-Ricci fibre-order content of the order-`2` commutator defect — the top-order `∇³S`
cancellation followed by the uniform curvature / differentiated-curvature sups); consumers transitively
depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurv_fiberOrder_bound
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

end Connection
end Integral
end DifferentialGeometry

end
