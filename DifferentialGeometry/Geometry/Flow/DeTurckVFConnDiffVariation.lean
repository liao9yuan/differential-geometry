import DifferentialGeometry.Geometry.Flow.VectorField

/-!
# The DeTurck vector-field difference via the connection-difference trace

For a fixed background metric `g_bg` and two metrics `g₀`, `g₁` on a smooth manifold `M`,
the DeTurck vector fields `deTurckVF g₁ g_bg` and `deTurckVF g₀ g_bg` differ by an
expression governed by

* the **Christoffel variation** between the two perturbed metrics, encoded as the
  connection-difference tensor `connDiff g₁ g₀` traced against the cometric `g₁⁻¹`, and
* the **cometric difference** `g₁⁻¹ − g₀⁻¹` traced against the fixed background
  connection-difference `connDiff g₀ g_bg`.

This is the Lie-arm structural input to the Ricci–DeTurck linearization: it isolates the
dependence of the DeTurck vector field on a metric perturbation into the connection
variation `connDiff g₁ g₀` plus the inverse-metric variation, both linear-difference
objects.

The algebraic engine is the **cocycle identity** for the connection-difference tensor:
since `connDiff g g'` is the difference `∇^{LC}(g) − ∇^{LC}(g')` of Levi-Civita covariant
derivatives, it is additive in the telescoping sense
`connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`.

## Main results

* `connDiff_cocycle` — the telescoping additivity
  `connDiff g₁ g₂ x w v = connDiff g₁ g₀ x w v + connDiff g₀ g₂ x w v`.
* `deTurckVF_sub_eq_connDiff_trace` — the DeTurck vector-field difference decomposed into
  the cometric-`g₁⁻¹` trace of the Christoffel variation `connDiff g₁ g₀` plus the
  cometric-difference trace of the background connection difference `connDiff g₀ g_bg`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Cocycle (telescoping additivity) for the connection-difference tensor.**

Since `connDiff g g'` is the difference `∇^{LC}(g) − ∇^{LC}(g')` of the two Levi-Civita
covariant derivatives, it telescopes through any intermediate metric `g₀`:
$$
  (\nabla_1 - \nabla_2) \;=\; (\nabla_1 - \nabla_0) + (\nabla_0 - \nabla_2).
$$
The proof realises the bilinear-map argument `w` as the value `σ x` of a smooth tangent
vector field `σ` (via `ContMDiffSection.exists_eq_at`) and applies the evaluation formula
`connDiff_apply` to each of the three connection differences; the Levi-Civita derivatives
of `σ` cancel telescopically. -/
theorem connDiff_cocycle (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    connDiff (I := I) g₁ g₂ x w v =
      connDiff (I := I) g₁ g₀ x w v + connDiff (I := I) g₀ g₂ x w v := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h12 := connDiff_apply (I := I) g₁ g₂ hσ v
  have h10 := connDiff_apply (I := I) g₁ g₀ hσ v
  have h02 := connDiff_apply (I := I) g₀ g₂ hσ v
  rw [hσx] at h12 h10 h02
  rw [h12, h10, h02]
  abel

/-- **The DeTurck vector-field difference via the connection-difference trace.**

For a fixed background metric `g_bg` and two metrics `g₀`, `g₁`, the difference of the
DeTurck vector fields decomposes, at each point `x`, as the sum of

* the cometric-`g₁⁻¹` trace of the **Christoffel variation** `connDiff g₁ g₀` between the
  two perturbed metrics, and
* the **cometric-difference** `g₁⁻¹ − g₀⁻¹` trace of the fixed background
  connection-difference `connDiff g₀ g_bg`,

both expressed in the chart-`x` coordinate frame `e_j = chartBasisVecFiber x j` with
inverse Gram matrices `G_∙^{jk} = chartInvGramMatrix g_∙ x x`:
$$
  W(g_1) - W(g_0)
    \;=\; \sum_{j,k} G_1^{jk}\, A_{10}(e_j, e_k)
        \;+\; \sum_{j,k} \bigl(G_1^{jk} - G_0^{jk}\bigr)\, A_{0,bg}(e_j, e_k),
$$
where `A_{10} = connDiff g₁ g₀ x` and `A_{0,bg} = connDiff g₀ g_bg x`.

This is the Lie-arm linearization input: the metric-perturbation dependence of the DeTurck
vector field is isolated into the connection variation `connDiff g₁ g₀` and the
inverse-metric variation `G₁ − G₀`.  The chart-trace formula `deTurckVF_apply_eq` supplies
each DeTurck vector field as the `g`-trace of its connection difference, and
`connDiff_cocycle` rewrites `connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`. -/
theorem deTurckVF_sub_eq_connDiff_trace
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x -
      (deTurckVF (I := I) g₀ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x j k •
            connDiff (I := I) g₁ g₀ x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x)) +
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g₁ x x j k -
              chartInvGramMatrix (I := I) g₀ x x j k) •
            connDiff (I := I) g₀ g_bg x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x) := by
  classical
  rw [deTurckVF_apply_eq (I := I) g₁ g_bg x, deTurckVF_apply_eq (I := I) g₀ g_bg x]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [connDiff_cocycle (I := I) g₀ g₁ g_bg x
      (chartBasisVecFiber (I := I) x j x) (chartBasisVecFiber (I := I) x k x)]
  rw [smul_add]
  rw [sub_smul]
  abel

end DeTurck
end PDE
end DifferentialGeometry
