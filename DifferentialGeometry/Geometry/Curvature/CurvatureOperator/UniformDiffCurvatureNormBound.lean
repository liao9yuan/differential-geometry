import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentitySmoothFrame

/-!
# Compact-uniform intrinsic `g`-norm bound for the frame-summed differentiated curvature operator

For a closed smooth Riemannian manifold `(M, g)`, the frame-summed acted-slot substitution operator
of the differentiated base-tangent curvature,
```
W_{x, a} := nablaBaseSlotCurvFrameSumCLM g (fun i => B_i) B_a x,
    B_i := smoothOrthoFrame g x i,    B_a := smoothOrthoFrame g x a,
```
is the tangent endomorphism `w ↦ ∑_i (∇_{B_i} R)(B_i, B_a) w`, the first-slot divergence of the
Riemann curvature read in the `g_x`-orthonormal frame and contracted against the fixed direction
`B_a`. This is the `(∇R) · S` arm's tangent multiplier in the moving-frame Bochner–Weitzenböck
first-order curvature bound.

This file records the **compact-uniform intrinsic `g`-operator bound** of `W_{x, a}`: there is a single
nonnegative constant `Kw`, independent of the base point `x` and the frame index `a`, with
```
g.inner x (W_{x, a} u) (W_{x, a} u) ≤ Kw · g.inner x u u    for all u : T_x M.
```
It is the differentiated-curvature analogue of the base-curvature bound
`exists_uniform_riemannOp_LeviCivita_gNorm_bound`, with the orthonormal frame's unit Gram
simplification `g(B_i, B_i) = g(B_a, B_a) = 1` already folded in. The constant is the compact sup of
the smooth `∇R` operator field over `M`: `∇R` is a smooth section of a finite-rank tensor bundle on
the compact manifold, so its `g`-operator size is bounded; patching the pointwise chart-`α`
differentiated-curvature bound over the finite chart-atlas partition of unity (exactly as the
base-curvature bound is patched) yields the global constant.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Compact-uniform intrinsic `g`-norm bound for the frame-summed differentiated curvature
operator.** For a smooth Riemannian metric `g` on a closed manifold `M`, there is a single
nonnegative constant `Kw`, independent of the base point `x` and the second-slot frame index `a`, with
```
g.inner x (W_{x, a} u) (W_{x, a} u) ≤ Kw · g.inner x u u    for all x, a, u,
```
where `W_{x, a} := nablaBaseSlotCurvFrameSumCLM g (fun i => smoothOrthoFrame g x i)
(smoothOrthoFrame g x a) x` is the frame-summed differentiated base-tangent curvature operator
`w ↦ ∑_i (∇_{B_i} R)(B_i, B_a) w`. The bound is stated entirely through the intrinsic `g`-fibre norms
`‖·‖_g² = g.inner x · ·`, with the `g_x`-orthonormal frame's unit Gram normalisation `g(B_i, B_i) =
g(B_a, B_a) = 1` already absorbed into the constant.

This is the once-differentiated companion of `exists_uniform_riemannOp_LeviCivita_gNorm_bound`. The
constant is the compact sup of the smooth `∇R` operator field over `M`: `∇R` is a smooth section of a
finite-rank tensor bundle on the compact manifold, so its `g`-operator size is bounded; patching the
pointwise chart-`α` differentiated-curvature `g`-bound over the finite chart-atlas partition of unity
(exactly the base-curvature route, one covariant derivative higher) yields the global constant. -/
theorem exists_uniform_nablaCurvSec_LeviCivita_gNorm_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kw : ℝ, 0 ≤ Kw ∧
      ∀ (x : M) (a : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
        g.inner x
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u)
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u) ≤
          Kw * g.inner x u u :=
  sorry

end Connection
end Integral
end DifferentialGeometry

end
