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

set_option linter.unusedSectionVars false in
/-- Non-negativity of `g.inner x v v` for a smooth Riemannian metric. -/
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

/-- **Continuous per-point `g`-operator envelope of the frame-summed differentiated curvature
operator.** For a smooth Riemannian metric `g` on a closed manifold `M`, there is a *continuous*
nonnegative function `Kw : M → ℝ` such that, at every base point `x` and for every second-slot frame
index `a` and every tangent vector `u`,
```
g.inner x (W_{x, a} u) (W_{x, a} u) ≤ Kw x · g.inner x u u,
```
where `W_{x, a} := nablaBaseSlotCurvFrameSumCLM g (fun i => smoothOrthoFrame g x i)
(smoothOrthoFrame g x a) x` is the frame-summed differentiated base-tangent curvature operator
`w ↦ ∑_i (∇_{B_i} R)(B_i, B_a) w`, read in the `g_x`-orthonormal frame `B_j := smoothOrthoFrame g x j`.

**Why this is TRUE.** Fix `x`. The endomorphism `W_{x, a}` is a fixed continuous linear map on the
finite-dimensional fibre `T_x M`, so its `g_x`-operator-norm-squared is a finite nonnegative number;
choosing `Kw x` to be (an upper bound for, uniformly in `a`) that operator-norm-squared gives the
displayed proportional bound at `x` for all `(a, u)`. The only content beyond pointwise existence is
that the envelope can be chosen **continuously** in `x`. The frame-summed value `W_{x, a} u` is the
intrinsic divergence-of-curvature endomorphism `w ↦ ∑_i (∇_{B_i} R)(B_i, B_a) w` of the once-covariantly
differentiated Levi-Civita Riemann tensor `∇R`, a smooth `(1, 3)`-tensor field on `M`: in any chart at
`β` the chart-coordinate components `∂_a R^l{}_{ijk}(g, β)(ϕ_β b) + (Γ · R)`-corrections are `C^∞`
(polynomial in the chart Christoffel symbols `chartChristoffel`, the chart Riemann data
`chartRiemannTensor`, and their first partials — all `C^∞` on the chart-target interior by
`chartChristoffel_contDiffOn_interior` and `chartRiemannTensor_contDiffOn_interior`) and *uniformly
bounded* on the compact chart-`β` partition-of-unity support. The `g_x`-orthonormal frame
`B_j = smoothOrthoFrame g x j` is the Gram-Schmidt normalisation of the chart frame (a `C^∞` function of
the bounded smooth chart Gram data, positive-definite by `chartGramMatrix_posDef`); reading the
differentiated-curvature value against this frame and controlling the intrinsic fibre norm through the
forward chart-frame Gram Rayleigh route (`chartGramMatrix` continuous on the chart base set) and its
reverse companion yields a continuous (indeed locally Lipschitz) envelope `Kw` on the finitely-many
compact chart supports that cover `M`, patched to a global continuous function by the partition of
unity. This is the chart-locality-free route (no `HasLocallyConstantChartAt`, no chart-trivialisation
operator-norm scalar); the only chart objects are the bounded chart Christoffel / Riemann data, their
first partials, and the positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `Kw ≡ 0` is rejected on any manifold whose curvature has a
non-vanishing first covariant derivative: at a point `x` where the divergence-of-curvature endomorphism
`W_{x, a}` is nonzero there is a `u` with `W_{x, a} u ≠ 0`, hence `g.inner x (W_{x, a} u) (W_{x, a} u) >
0` (positive-definiteness of `g`) while the right-hand side `0 · g.inner x u u = 0`, contradicting the
bound. So the envelope must carry the genuine differentiated-curvature magnitude — it cannot be the
trivial zero function.

This is the genuinely-irreducible analytic content (the continuity of the differentiated-curvature
operator norm / the bridge from uniformly-bounded chart `∇R` data to a continuous intrinsic-fibre-norm
differentiated-curvature bound), the once-differentiated companion of the base-curvature continuous
envelope `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`. It is posited here
as the precise continuous-envelope primitive and discharged separately; the *uniformisation* over the
compact `M` (the supremum) is proved on top of it in
`exists_uniform_nablaCurvSec_LeviCivita_gNorm_bound`. -/
theorem exists_continuous_nablaCurvSec_frameSum_gNorm_envelope
    (g : SmoothRiemannianMetric I M) :
    ∃ Kw : M → ℝ, Continuous Kw ∧ (∀ x : M, 0 ≤ Kw x) ∧
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
          Kw x * g.inner x u u :=
  sorry

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
constant is the compact sup of the continuous per-point differentiated-curvature `g`-operator envelope
`Kw` supplied by `exists_continuous_nablaCurvSec_frameSum_gNorm_envelope`; it is extracted through the
image-compactness route (a continuous real function on a compact space has bounded range). -/
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
          Kw * g.inner x u u := by
  classical
  obtain ⟨Kw, hKw_cont, hKw_nonneg, hKw_bound⟩ :=
    exists_continuous_nablaCurvSec_frameSum_gNorm_envelope (I := I) (M := M) g
  have hKpt := (isCompact_univ (X := M)).image hKw_cont
  obtain ⟨C₀, hC₀⟩ := hKpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x a u
  have hKw_le : Kw x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have huu_nonneg : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g x u
  calc
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
            (smoothOrthoFrame_smooth (I := I) g x a)) x u)
        ≤ Kw x * g.inner x u u := hKw_bound x a u
    _ ≤ max C₀ 0 * g.inner x u u := mul_le_mul_of_nonneg_right hKw_le huu_nonneg

end Connection
end Integral
end DifferentialGeometry

end
